// SPDX-License-Identifier: GPL-2.0

/*
 * This driver adds support for perf events to use the Performance
 * Monitor Counter Groups (PMCG) associated with an SMMUv3 node
 * to monitor that node.
 *
 * SMMUv3 PMCG devices are named as smmuv3_pmcg_<phys_addr_page> where
 * <phys_addr_page> is the physical page address of the SMMU PMCG wrapped
 * to 4K boundary. For example, the PMCG at 0xff88840000 is named
 * smmuv3_pmcg_ff88840
 *
 * Filtering by stream id is done by specifying filtering parameters
 * with the event. options are:
 *   filter_enable    - 0 = no filtering, 1 = filtering enabled
 *   filter_span      - 0 = exact match, 1 = pattern match
 *   filter_stream_id - pattern to filter against
 *
 * To match a partial StreamID where the X most-significant bits must match
 * but the Y least-significant bits might differ, STREAMID is programmed
 * with a value that contains:
 *  STREAMID[Y - 1] == 0.
 *  STREAMID[Y - 2:0] == 1 (where Y > 1).
 * The remainder of implemented bits of STREAMID (X bits, from bit Y upwards)
 * contain a value to match from the corresponding bits of event StreamID.
 *
 * Example: perf stat -e smmuv3_pmcg_ff88840/transaction,filter_enable=1,
 *                    filter_span=1,filter_stream_id=0x42/ -a netperf
 * Applies filter pattern 0x42 to transaction events, which means events
 * matching stream ids 0x42 and 0x43 are counted. Further filtering
 * information is available in the SMMU documentation.
 *
 * SMMU events are not attributable to a CPU, so task mode and sampling
 * are not supported.
 */

#include <linux/acpi.h>
#include <linux/acpi_iort.h>
#include <linux/bitfield.h>
#include <linux/bitops.h>
#include <linux/cpumask.h>
#include <linux/device.h>
#include <linux/errno.h>
#include <linux/interrupt.h>
#include <linux/irq.h>
#include <linux/kernel.h>
#include <linux/list.h>
#include <linux/msi.h>
#include <linux/perf_event.h>
#include <linux/platform_device.h>
#include <linux/smp.h>
#include <linux/sysfs.h>
#include <linux/types.h>

#include "uncore_pmu.h"

#define SMMU_PMCG_EVCNTR0               0x0
#define SMMU_PMCG_EVCNTR(n, stride)     (SMMU_PMCG_EVCNTR0 + (n) * (stride))
#define SMMU_PMCG_EVTYPER0              0x400
#define SMMU_PMCG_EVTYPER(n)            (SMMU_PMCG_EVTYPER0 + (n) * 4)
#define SMMU_PMCG_SID_SPAN_SHIFT        29
#define SMMU_PMCG_SMR0                  0xA00
#define SMMU_PMCG_SMR(n)                (SMMU_PMCG_SMR0 + (n) * 4)
#define SMMU_PMCG_CNTENSET0             0xC00
#define SMMU_PMCG_CNTENCLR0             0xC20
#define SMMU_PMCG_INTENSET0             0xC40
#define SMMU_PMCG_INTENCLR0             0xC60
#define SMMU_PMCG_OVSCLR0               0xC80
#define SMMU_PMCG_OVSSET0               0xCC0
#define SMMU_PMCG_CFGR                  0xE00
#define SMMU_PMCG_CFGR_SID_FILTER_TYPE  BIT(23)
#define SMMU_PMCG_CFGR_MSI              BIT(21)
#define SMMU_PMCG_CFGR_RELOC_CTRS       BIT(20)
#define SMMU_PMCG_CFGR_SIZE             GENMASK(13, 8)
#define SMMU_PMCG_CFGR_NCTR             GENMASK(5, 0)
#define SMMU_PMCG_CR                    0xE04
#define SMMU_PMCG_CR_ENABLE             BIT(0)
#define SMMU_PMCG_IIDR                  0xE08
#define SMMU_PMCG_CEID0                 0xE20
#define SMMU_PMCG_CEID1                 0xE28
#define SMMU_PMCG_IRQ_CTRL              0xE50
#define SMMU_PMCG_IRQ_CTRL_IRQEN        BIT(0)
#define SMMU_PMCG_IRQ_CFG0              0xE58
#define SMMU_PMCG_IRQ_CFG1              0xE60
#define SMMU_PMCG_IRQ_CFG2              0xE64

/* MSI config fields */
#define MSI_CFG0_ADDR_MASK              GENMASK_ULL(51, 2)
#define MSI_CFG2_MEMATTR_DEVICE_nGnRE   0x1

#define SMMU_PMCG_DEFAULT_FILTER_SPAN   1
#define SMMU_PMCG_DEFAULT_FILTER_SID    GENMASK(31, 0)

#define SMMU_PMCG_MAX_COUNTERS          64
#define SMMU_PMCG_ARCH_MAX_EVENTS       128

#define SMMU_PMCG_PA_SHIFT              12

#define SMMU_PMCG_EVCNTR_RDONLY         BIT(0)

struct smmu_pmu {
	struct perf_event *events[SMMU_PMCG_MAX_COUNTERS];
	DECLARE_BITMAP(used_counters, SMMU_PMCG_MAX_COUNTERS);
	DECLARE_BITMAP(supported_events, SMMU_PMCG_ARCH_MAX_EVENTS);
	struct uncore_pmu pmu;
	void __iomem *reg_base;
	void __iomem *reloc_base;
	u64 counter_mask;
	u32 options;
	u32 iidr;
	bool global_filter;
};

#define to_smmu_pmu(p) (container_of(to_uncore_pmu(p), struct smmu_pmu, pmu))

#define SMMU_PMU_EVENT_ATTR_EXTRACTOR(_name, _config, _start, _end)        \
	static inline u32 get_##_name(struct perf_event *event)            \
	{                                                                  \
		return FIELD_GET(GENMASK_ULL(_end, _start),                \
				 event->attr._config);                     \
	}                                                                  \

SMMU_PMU_EVENT_ATTR_EXTRACTOR(event, config, 0, 15);
SMMU_PMU_EVENT_ATTR_EXTRACTOR(filter_stream_id, config1, 0, 31);
SMMU_PMU_EVENT_ATTR_EXTRACTOR(filter_span, config1, 32, 32);
SMMU_PMU_EVENT_ATTR_EXTRACTOR(filter_enable, config1, 33, 33);

static inline void smmu_pmu_enable(struct pmu *pmu)
{
	struct smmu_pmu *smmu_pmu = to_smmu_pmu(pmu);

	writel(SMMU_PMCG_IRQ_CTRL_IRQEN,
	       smmu_pmu->reg_base + SMMU_PMCG_IRQ_CTRL);
	writel(SMMU_PMCG_CR_ENABLE, smmu_pmu->reg_base + SMMU_PMCG_CR);
}

static inline void smmu_pmu_disable(struct pmu *pmu)
{
	struct smmu_pmu *smmu_pmu = to_smmu_pmu(pmu);

	writel(0, smmu_pmu->reg_base + SMMU_PMCG_CR);
	writel(0, smmu_pmu->reg_base + SMMU_PMCG_IRQ_CTRL);
}

static inline void smmu_pmu_counter_set_value(struct smmu_pmu *smmu_pmu,
					      u32 idx, u64 value)
{
	if (smmu_pmu->counter_mask & BIT(32))
		writeq(value, smmu_pmu->reloc_base + SMMU_PMCG_EVCNTR(idx, 8));
	else
		writel(value, smmu_pmu->reloc_base + SMMU_PMCG_EVCNTR(idx, 4));
}

static inline u64 smmu_pmu_counter_get_value(struct smmu_pmu *smmu_pmu, u32 idx)
{
	u64 value;

	if (smmu_pmu->counter_mask & BIT(32))
		value = readq(smmu_pmu->reloc_base + SMMU_PMCG_EVCNTR(idx, 8));
	else
		value = readl(smmu_pmu->reloc_base + SMMU_PMCG_EVCNTR(idx, 4));

	return value;
}

static inline void smmu_pmu_counter_enable(struct smmu_pmu *smmu_pmu, u32 idx)
{
	writeq(BIT(idx), smmu_pmu->reg_base + SMMU_PMCG_CNTENSET0);
}

static inline void smmu_pmu_counter_disable(struct smmu_pmu *smmu_pmu, u32 idx)
{
	writeq(BIT(idx), smmu_pmu->reg_base + SMMU_PMCG_CNTENCLR0);
}

static inline void smmu_pmu_interrupt_enable(struct smmu_pmu *smmu_pmu, u32 idx)
{
	writeq(BIT(idx), smmu_pmu->reg_base + SMMU_PMCG_INTENSET0);
}

static inline void smmu_pmu_interrupt_disable(struct smmu_pmu *smmu_pmu,
					      u32 idx)
{
	writeq(BIT(idx), smmu_pmu->reg_base + SMMU_PMCG_INTENCLR0);
}

static inline void smmu_pmu_set_evtyper(struct smmu_pmu *smmu_pmu, u32 idx,
					u32 val)
{
	writel(val, smmu_pmu->reg_base + SMMU_PMCG_EVTYPER(idx));
}

static inline void smmu_pmu_set_smr(struct smmu_pmu *smmu_pmu, u32 idx, u32 val)
{
	writel(val, smmu_pmu->reg_base + SMMU_PMCG_SMR(idx));
}

static void smmu_pmu_event_update(struct perf_event *event)
{
	struct hw_perf_event *hwc = &event->hw;
	struct smmu_pmu *smmu_pmu = to_smmu_pmu(event->pmu);
	u64 delta, prev, now;
	u32 idx = hwc->idx;

	do {
		prev = local64_read(&hwc->prev_count);
		now = smmu_pmu_counter_get_value(smmu_pmu, idx);
	} while (local64_cmpxchg(&hwc->prev_count, prev, now) != prev);

	/* handle overflow. */
	delta = now - prev;
	delta &= smmu_pmu->counter_mask;

	local64_add(delta, &event->count);
}

static void smmu_pmu_set_period(struct smmu_pmu *smmu_pmu,
				struct hw_perf_event *hwc)
{
	u32 idx = hwc->idx;
	u64 new;

	if (smmu_pmu->options & SMMU_PMCG_EVCNTR_RDONLY) {
		/*
		 * On platforms that require this quirk, if the counter starts
		 * at < half_counter value and wraps, the current logic of
		 * handling the overflow may not work. It is expected that,
		 * those platforms will have full 64 counter bits implemented
		 * so that such a possibility is remote(eg: HiSilicon HIP08).
		 */
		new = smmu_pmu_counter_get_value(smmu_pmu, idx);
	} else {
		/*
		 * We limit the max period to half the max counter value
		 * of the counter size, so that even in the case of extreme
		 * interrupt latency the counter will (hopefully) not wrap
		 * past its initial value.
		 */
		new = smmu_pmu->counter_mask >> 1;
		smmu_pmu_counter_set_value(smmu_pmu, idx, new);
	}

	local64_set(&hwc->prev_count, new);
}

static void smmu_pmu_set_event_filter(struct perf_event *event,
				      int idx, u32 span, u32 sid)
{
	struct smmu_pmu *smmu_pmu = to_smmu_pmu(event->pmu);
	u32 evtyper;

	evtyper = get_event(event) | span << SMMU_PMCG_SID_SPAN_SHIFT;
	smmu_pmu_set_evtyper(smmu_pmu, idx, evtyper);
	smmu_pmu_set_smr(smmu_pmu, idx, sid);
}

static bool smmu_pmu_check_global_filter(struct perf_event *curr,
					 struct perf_event *new)
{
	if (get_filter_enable(new) != get_filter_enable(curr))
		return false;

	if (!get_filter_enable(new))
		return true;

	return get_filter_span(new) == get_filter_span(curr) &&
	       get_filter_stream_id(new) == get_filter_stream_id(curr);
}

static int smmu_pmu_apply_event_filter(struct smmu_pmu *smmu_pmu,
				       struct perf_event *event, int idx)
{
	u32 span, sid;
	unsigned int cur_idx, num_ctrs = smmu_pmu->pmu.num_counters;
	bool filter_en = !!get_filter_enable(event);

	span = filter_en ? get_filter_span(event) :
			   SMMU_PMCG_DEFAULT_FILTER_SPAN;
	sid = filter_en ? get_filter_stream_id(event) :
			   SMMU_PMCG_DEFAULT_FILTER_SID;

	cur_idx = find_first_bit(smmu_pmu->used_counters, num_ctrs);
	/*
	 * Per-counter filtering, or scheduling the first globally-filtered
	 * event into an empty PMU so idx == 0 and it works out equivalent.
	 */
	if (!smmu_pmu->global_filter || cur_idx == num_ctrs) {
		smmu_pmu_set_event_filter(event, idx, span, sid);
		return 0;
	}

	/* Otherwise, must match whatever's currently scheduled */
	if (smmu_pmu_check_global_filter(smmu_pmu->events[cur_idx], event)) {
		smmu_pmu_set_evtyper(smmu_pmu, idx, get_event(event));
		return 0;
	}

	return -EAGAIN;
}

static int smmu_pmu_get_event_idx(struct smmu_pmu *smmu_pmu,
				  struct perf_event *event)
{
	int idx, err;
	unsigned int num_ctrs = smmu_pmu->pmu.num_counters;

	idx = find_first_zero_bit(smmu_pmu->used_counters, num_ctrs);
	if (idx == num_ctrs)
		/* The counters are all in use. */
		return -EAGAIN;

	err = smmu_pmu_apply_event_filter(smmu_pmu, event, idx);
	if (err)
		return err;

	set_bit(idx, smmu_pmu->used_counters);

	return idx;
}

static bool smmu_pmu_events_compatible(struct perf_event *curr,
				       struct perf_event *new)
{
	if (new->pmu != curr->pmu)
		return false;

	if (to_smmu_pmu(new->pmu)->global_filter &&
	    !smmu_pmu_check_global_filter(curr, new))
		return false;

	return true;
}

/*
 * Implementation of abstract pmu functionality required by
 * the core perf events code.
 */

static int smmu_pmu_event_init(struct perf_event *event)
{
	struct smmu_pmu *smmu_pmu = to_smmu_pmu(event->pmu);
	struct device *dev = smmu_pmu->pmu.dev;
	struct perf_event *sibling;
	u16 event_id;
	int ret;

	ret = uncore_pmu_event_init(event);
	if (ret)
		return ret;

	/* Verify specified event is supported on this PMU */
	event_id = get_event(event);
	if (event_id < SMMU_PMCG_ARCH_MAX_EVENTS &&
	    (!test_bit(event_id, smmu_pmu->supported_events))) {
		dev_dbg(dev, "Invalid event %d for this PMU\n", event_id);
		return -EINVAL;
	}

	/* Don't allow groups with mixed PMUs, except for s/w events */
	if (!is_software_event(event->group_leader))
		if (!smmu_pmu_events_compatible(event->group_leader, event))
			return -EINVAL;

	for_each_sibling_event(sibling, event->group_leader) {
		if (is_software_event(sibling))
			continue;

		if (!smmu_pmu_events_compatible(sibling, event))
			return -EINVAL;
	}

	return 0;
}

static void smmu_pmu_event_start(struct perf_event *event, int flags)
{
	struct smmu_pmu *smmu_pmu = to_smmu_pmu(event->pmu);
	struct hw_perf_event *hwc = &event->hw;
	int idx = hwc->idx;

	hwc->state = 0;

	smmu_pmu_set_period(smmu_pmu, hwc);

	smmu_pmu_counter_enable(smmu_pmu, idx);
}

static void smmu_pmu_event_stop(struct perf_event *event, int flags)
{
	struct smmu_pmu *smmu_pmu = to_smmu_pmu(event->pmu);
	struct hw_perf_event *hwc = &event->hw;
	int idx = hwc->idx;

	if (hwc->state & PERF_HES_STOPPED)
		return;

	smmu_pmu_counter_disable(smmu_pmu, idx);
	/* As the counter gets updated on _start, ignore PERF_EF_UPDATE */
	smmu_pmu_event_update(event);
	hwc->state |= PERF_HES_STOPPED | PERF_HES_UPTODATE;
}

static int smmu_pmu_event_add(struct perf_event *event, int flags)
{
	struct hw_perf_event *hwc = &event->hw;
	int idx;
	struct smmu_pmu *smmu_pmu = to_smmu_pmu(event->pmu);

	idx = smmu_pmu_get_event_idx(smmu_pmu, event);
	if (idx < 0)
		return idx;

	hwc->idx = idx;
	hwc->state = PERF_HES_STOPPED | PERF_HES_UPTODATE;
	smmu_pmu->events[idx] = event;
	local64_set(&hwc->prev_count, 0);

	smmu_pmu_interrupt_enable(smmu_pmu, idx);

	if (flags & PERF_EF_START)
		smmu_pmu_event_start(event, flags);

	/* Propagate changes to the userspace mapping. */
	perf_event_update_userpage(event);

	return 0;
}

static void smmu_pmu_event_del(struct perf_event *event, int flags)
{
	struct hw_perf_event *hwc = &event->hw;
	struct smmu_pmu *smmu_pmu = to_smmu_pmu(event->pmu);
	int idx = hwc->idx;

	smmu_pmu_event_stop(event, flags | PERF_EF_UPDATE);
	smmu_pmu_interrupt_disable(smmu_pmu, idx);
	smmu_pmu->events[idx] = NULL;
	clear_bit(idx, smmu_pmu->used_counters);

	perf_event_update_userpage(event);
}

static void smmu_pmu_event_read(struct perf_event *event)
{
	smmu_pmu_event_update(event);
}

/* Events */

static ssize_t smmu_pmu_event_show(struct device *dev,
				   struct device_attribute *attr, char *page)
{
	struct perf_pmu_events_attr *pmu_attr;

	pmu_attr = container_of(attr, struct perf_pmu_events_attr, attr);

	return sysfs_emit(page, "event=0x%02llx\n", pmu_attr->id);
}

#define SMMU_EVENT_ATTR(name, config)			\
	PMU_EVENT_ATTR_ID(name, smmu_pmu_event_show, config)

static struct attribute *smmu_pmu_events[] = {
	SMMU_EVENT_ATTR(cycles, 0),
	SMMU_EVENT_ATTR(transaction, 1),
	SMMU_EVENT_ATTR(tlb_miss, 2),
	SMMU_EVENT_ATTR(config_cache_miss, 3),
	SMMU_EVENT_ATTR(trans_table_walk_access, 4),
	SMMU_EVENT_ATTR(config_struct_access, 5),
	SMMU_EVENT_ATTR(pcie_ats_trans_rq, 6),
	SMMU_EVENT_ATTR(pcie_ats_trans_passed, 7),
	NULL
};

static umode_t smmu_pmu_event_is_visible(struct kobject *kobj,
					 struct attribute *attr, int unused)
{
	struct device *dev = kobj_to_dev(kobj);
	struct smmu_pmu *smmu_pmu = to_smmu_pmu(dev_get_drvdata(dev));
	struct perf_pmu_events_attr *pmu_attr;

	pmu_attr = container_of(attr, struct perf_pmu_events_attr, attr.attr);

	if (test_bit(pmu_attr->id, smmu_pmu->supported_events))
		return attr->mode;

	return 0;
}

static const struct attribute_group smmu_pmu_events_group = {
	.name = "events",
	.attrs = smmu_pmu_events,
	.is_visible = smmu_pmu_event_is_visible,
};

static ssize_t smmu_pmu_identifier_attr_show(struct device *dev,
					struct device_attribute *attr,
					char *page)
{
	struct smmu_pmu *smmu_pmu = to_smmu_pmu(dev_get_drvdata(dev));

	return sysfs_emit(page, "0x%08x\n", smmu_pmu->iidr);
}

static umode_t smmu_pmu_identifier_attr_visible(struct kobject *kobj,
						struct attribute *attr,
						int n)
{
	struct device *dev = kobj_to_dev(kobj);
	struct smmu_pmu *smmu_pmu = to_smmu_pmu(dev_get_drvdata(dev));

	if (!smmu_pmu->iidr)
		return 0;
	return attr->mode;
}

static struct device_attribute smmu_pmu_identifier_attr =
	__ATTR(identifier, 0444, smmu_pmu_identifier_attr_show, NULL);

static struct attribute *smmu_pmu_identifier_attrs[] = {
	&smmu_pmu_identifier_attr.attr,
	NULL
};

static const struct attribute_group smmu_pmu_identifier_group = {
	.attrs = smmu_pmu_identifier_attrs,
	.is_visible = smmu_pmu_identifier_attr_visible,
};

/* Formats */
PMU_FORMAT_ATTR(event,		   "config:0-15");
PMU_FORMAT_ATTR(filter_stream_id,  "config1:0-31");
PMU_FORMAT_ATTR(filter_span,	   "config1:32");
PMU_FORMAT_ATTR(filter_enable,	   "config1:33");

static struct attribute *smmu_pmu_formats[] = {
	&format_attr_event.attr,
	&format_attr_filter_stream_id.attr,
	&format_attr_filter_span.attr,
	&format_attr_filter_enable.attr,
	NULL
};

static const struct attribute_group smmu_pmu_format_group = {
	.name = "format",
	.attrs = smmu_pmu_formats,
};

static const struct attribute_group *smmu_pmu_attr_grps[] = {
	&smmu_pmu_events_group,
	&smmu_pmu_format_group,
	&smmu_pmu_identifier_group,
	NULL
};

/*
 * Generic device handlers
 */

static irqreturn_t smmu_pmu_handle_irq(int irq_num, void *data)
{
	struct smmu_pmu *smmu_pmu = data;
	u64 ovsr;
	unsigned int idx;

	ovsr = readq(smmu_pmu->reloc_base + SMMU_PMCG_OVSSET0);
	if (!ovsr)
		return IRQ_NONE;

	writeq(ovsr, smmu_pmu->reloc_base + SMMU_PMCG_OVSCLR0);

	for_each_set_bit(idx, (unsigned long *)&ovsr, smmu_pmu->pmu.num_counters) {
		struct perf_event *event = smmu_pmu->events[idx];
		struct hw_perf_event *hwc;

		if (WARN_ON_ONCE(!event))
			continue;

		smmu_pmu_event_update(event);
		hwc = &event->hw;

		smmu_pmu_set_period(smmu_pmu, hwc);
	}

	return IRQ_HANDLED;
}

static void smmu_pmu_free_msis(void *data)
{
	struct device *dev = data;

	platform_msi_domain_free_irqs(dev);
}

static void smmu_pmu_write_msi_msg(struct msi_desc *desc, struct msi_msg *msg)
{
	phys_addr_t doorbell;
	struct device *dev = msi_desc_to_dev(desc);
	struct smmu_pmu *pmu = dev_get_drvdata(dev);

	doorbell = (((u64)msg->address_hi) << 32) | msg->address_lo;
	doorbell &= MSI_CFG0_ADDR_MASK;

	writeq_relaxed(doorbell, pmu->reg_base + SMMU_PMCG_IRQ_CFG0);
	writel_relaxed(msg->data, pmu->reg_base + SMMU_PMCG_IRQ_CFG1);
	writel_relaxed(MSI_CFG2_MEMATTR_DEVICE_nGnRE,
		       pmu->reg_base + SMMU_PMCG_IRQ_CFG2);
}

static void smmu_pmu_setup_msi(struct smmu_pmu *pmu)
{
	struct msi_desc *desc;
	struct device *dev = pmu->pmu.dev;
	int ret;

	/* Clear MSI address reg */
	writeq_relaxed(0, pmu->reg_base + SMMU_PMCG_IRQ_CFG0);

	/* MSI supported or not */
	if (!(readl(pmu->reg_base + SMMU_PMCG_CFGR) & SMMU_PMCG_CFGR_MSI))
		return;

	ret = platform_msi_domain_alloc_irqs(dev, 1, smmu_pmu_write_msi_msg);
	if (ret) {
		dev_warn(dev, "failed to allocate MSIs\n");
		return;
	}

	desc = first_msi_entry(dev);
	if (desc)
		pmu->pmu.irq = desc->irq;

	/* Add callback to free MSIs on teardown */
	devm_add_action(dev, smmu_pmu_free_msis, dev);
}

static int smmu_pmu_setup_irq(struct smmu_pmu *pmu)
{
	unsigned long flags = IRQF_NOBALANCING | IRQF_SHARED | IRQF_NO_THREAD;
	int irq, ret = -ENXIO;

	smmu_pmu_setup_msi(pmu);

	irq = pmu->pmu.irq;
	if (irq)
		ret = devm_request_irq(pmu->pmu.dev, irq, smmu_pmu_handle_irq,
				       flags, "smmuv3-pmu", pmu);
	return ret;
}

static void smmu_pmu_reset(struct smmu_pmu *smmu_pmu)
{
	u64 counter_present_mask = GENMASK_ULL(smmu_pmu->pmu.num_counters - 1, 0);

	smmu_pmu_disable(&smmu_pmu->pmu.pmu);

	/* Disable counter and interrupt */
	writeq_relaxed(counter_present_mask,
		       smmu_pmu->reg_base + SMMU_PMCG_CNTENCLR0);
	writeq_relaxed(counter_present_mask,
		       smmu_pmu->reg_base + SMMU_PMCG_INTENCLR0);
	writeq_relaxed(counter_present_mask,
		       smmu_pmu->reloc_base + SMMU_PMCG_OVSCLR0);
}

static void smmu_pmu_get_acpi_options(struct smmu_pmu *smmu_pmu)
{
	u32 model;

	model = *(u32 *)dev_get_platdata(smmu_pmu->pmu.dev);

	switch (model) {
	case IORT_SMMU_V3_PMCG_HISI_HIP08:
		/* HiSilicon Erratum 162001800 */
		smmu_pmu->options |= SMMU_PMCG_EVCNTR_RDONLY;
		break;
	}

	dev_notice(smmu_pmu->pmu.dev, "option mask 0x%x\n", smmu_pmu->options);
}

static int smmu_pmu_probe(struct platform_device *pdev)
{
	struct smmu_pmu *smmu_pmu;
	struct resource *res_0;
	u32 cfgr, reg_size;
	u64 ceid_64[2];
	int irq, err;
	char *name;
	struct device *dev = &pdev->dev;

	smmu_pmu = devm_kzalloc(dev, sizeof(*smmu_pmu), GFP_KERNEL);
	if (!smmu_pmu)
		return -ENOMEM;

	smmu_pmu->pmu.dev = &pdev->dev;
	platform_set_drvdata(pdev, smmu_pmu);

	smmu_pmu->pmu.pmu = (struct pmu) {
		.module		= THIS_MODULE,
		.task_ctx_nr    = perf_invalid_context,
		.pmu_enable	= smmu_pmu_enable,
		.pmu_disable	= smmu_pmu_disable,
		.event_init	= smmu_pmu_event_init,
		.add		= smmu_pmu_event_add,
		.del		= smmu_pmu_event_del,
		.start		= smmu_pmu_event_start,
		.stop		= smmu_pmu_event_stop,
		.read		= smmu_pmu_event_read,
		.attr_groups	= smmu_pmu_attr_grps,
		.capabilities	= PERF_PMU_CAP_NO_EXCLUDE,
	};

	smmu_pmu->reg_base = devm_platform_get_and_ioremap_resource(pdev, 0, &res_0);
	if (IS_ERR(smmu_pmu->reg_base))
		return PTR_ERR(smmu_pmu->reg_base);

	cfgr = readl_relaxed(smmu_pmu->reg_base + SMMU_PMCG_CFGR);

	/* Determine if page 1 is present */
	if (cfgr & SMMU_PMCG_CFGR_RELOC_CTRS) {
		smmu_pmu->reloc_base = devm_platform_ioremap_resource(pdev, 1);
		if (IS_ERR(smmu_pmu->reloc_base))
			return PTR_ERR(smmu_pmu->reloc_base);
	} else {
		smmu_pmu->reloc_base = smmu_pmu->reg_base;
	}

	irq = platform_get_irq_optional(pdev, 0);
	if (irq > 0)
		smmu_pmu->pmu.irq = irq;

	ceid_64[0] = readq_relaxed(smmu_pmu->reg_base + SMMU_PMCG_CEID0);
	ceid_64[1] = readq_relaxed(smmu_pmu->reg_base + SMMU_PMCG_CEID1);
	bitmap_from_arr32(smmu_pmu->supported_events, (u32 *)ceid_64,
			  SMMU_PMCG_ARCH_MAX_EVENTS);

	smmu_pmu->pmu.num_counters = FIELD_GET(SMMU_PMCG_CFGR_NCTR, cfgr) + 1;

	smmu_pmu->global_filter = !!(cfgr & SMMU_PMCG_CFGR_SID_FILTER_TYPE);

	reg_size = FIELD_GET(SMMU_PMCG_CFGR_SIZE, cfgr);
	smmu_pmu->counter_mask = GENMASK_ULL(reg_size, 0);

	smmu_pmu_reset(smmu_pmu);

	err = smmu_pmu_setup_irq(smmu_pmu);
	if (err) {
		dev_err(dev, "Setup irq failed, PMU @%pa\n", &res_0->start);
		return err;
	}

	smmu_pmu->iidr = readl_relaxed(smmu_pmu->reg_base + SMMU_PMCG_IIDR);

	name = devm_kasprintf(&pdev->dev, GFP_KERNEL, "smmuv3_pmcg_%llx",
			      (res_0->start) >> SMMU_PMCG_PA_SHIFT);
	if (!name) {
		dev_err(dev, "Create name failed, PMU @%pa\n", &res_0->start);
		return -EINVAL;
	}

	smmu_pmu_get_acpi_options(smmu_pmu);

	err = uncore_pmu_register(&smmu_pmu->pmu, name);
	if (err) {
		dev_err(dev, "Error %d registering PMU @%pa\n",
			err, &res_0->start);
		return err;
	}

	dev_info(dev, "Registered PMU @ %pa using %d counters with %s filter settings\n",
		 &res_0->start, smmu_pmu->pmu.num_counters,
		 smmu_pmu->global_filter ? "Global(Counter0)" :
		 "Individual");

	return 0;
}

static int smmu_pmu_remove(struct platform_device *pdev)
{
	struct smmu_pmu *smmu_pmu = platform_get_drvdata(pdev);

	uncore_pmu_unregister(&smmu_pmu->pmu);

	return 0;
}

static void smmu_pmu_shutdown(struct platform_device *pdev)
{
	struct smmu_pmu *smmu_pmu = platform_get_drvdata(pdev);

	smmu_pmu_disable(&smmu_pmu->pmu.pmu);
}

static struct platform_driver smmu_pmu_driver = {
	.driver = {
		.name = "arm-smmu-v3-pmcg",
		.suppress_bind_attrs = true,
	},
	.probe = smmu_pmu_probe,
	.remove = smmu_pmu_remove,
	.shutdown = smmu_pmu_shutdown,
};
module_platform_driver(smmu_pmu_driver);

MODULE_DESCRIPTION("PMU driver for ARM SMMUv3 Performance Monitors Extension");
MODULE_AUTHOR("Neil Leeder <nleeder@codeaurora.org>");
MODULE_AUTHOR("Shameer Kolothum <shameerali.kolothum.thodi@huawei.com>");
MODULE_LICENSE("GPL v2");
