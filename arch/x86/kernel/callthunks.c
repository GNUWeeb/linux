// SPDX-License-Identifier: GPL-2.0-only

#define pr_fmt(fmt) "callthunks: " fmt

#include <linux/btree.h>
#include <linux/memory.h>
#include <linux/moduleloader.h>
#include <linux/set_memory.h>
#include <linux/vmalloc.h>

#include <asm/alternative.h>
#include <asm/cpu.h>
#include <asm/insn.h>
#include <asm/kexec.h>
#include <asm/nospec-branch.h>
#include <asm/paravirt.h>
#include <asm/sections.h>
#include <asm/switch_to.h>
#include <asm/sync_core.h>
#include <asm/text-patching.h>

#ifdef CONFIG_CALL_THUNKS_DEBUG
static int __initdata_or_module debug_callthunks;

#define prdbg(fmt, args...)					\
do {								\
	if (debug_callthunks)					\
		printk(KERN_DEBUG pr_fmt(fmt), ##args);		\
} while(0)

static int __init debug_thunks(char *str)
{
	debug_callthunks = 1;
	return 1;
}
__setup("debug-callthunks", debug_thunks);
#else
#define prdbg(fmt, args...)	do { } while(0)
#endif

extern s32 __call_sites[], __call_sites_end[];
extern s32 __sym_sites[], __sym_sites_end[];

static struct btree_head64 call_thunks;

static bool thunks_initialized __ro_after_init;
static struct module_layout builtin_layout __ro_after_init;

struct thunk_desc {
	void		*template;
	unsigned int	template_size;
	unsigned int	thunk_size;
};

static struct thunk_desc callthunk_desc __ro_after_init;

struct thunk_mem {
	void			*base;
	unsigned int		size;
	unsigned int		nthunks;
	bool			is_rx;
	struct list_head	list;
	unsigned long		map[0];
};

struct thunk_mem_area {
	struct thunk_mem	*tmem;
	unsigned long		start;
	unsigned long		nthunks;
};

static LIST_HEAD(thunk_mem_list);

extern void error_entry(void);
extern void xen_error_entry(void);
extern void paranoid_entry(void);

static inline bool is_inittext(struct module_layout *layout, void *addr)
{
	if (!layout->mtn.mod)
		return is_kernel_inittext((unsigned long)addr);

	return within_module_init((unsigned long)addr, layout->mtn.mod);
}

static __init_or_module bool skip_addr(void *dest)
{
	if (dest == error_entry)
		return true;
	if (dest == paranoid_entry)
		return true;
	if (dest == xen_error_entry)
		return true;
	/* Does FILL_RSB... */
	if (dest == __switch_to_asm)
		return true;
	/* Accounts directly */
	if (dest == ret_from_fork)
		return true;
#ifdef CONFIG_HOTPLUG_CPU
	if (dest == start_cpu0)
		return true;
#endif
#ifdef CONFIG_FUNCTION_TRACER
	if (dest == __fentry__)
		return true;
#endif
#ifdef CONFIG_KEXEC_CORE
	/* FIXME: Exclude all of this */
	if (dest == relocate_kernel)
		return true;
#endif
	return false;
}

static __init_or_module void *call_get_dest(void *addr)
{
	struct insn insn;
	void *dest;
	int ret;

	ret = insn_decode_kernel(&insn, addr);
	if (ret)
		return ERR_PTR(ret);

	/* Patched out call? */
	if (insn.opcode.bytes[0] != CALL_INSN_OPCODE)
		return NULL;

	dest = addr + insn.length + insn.immediate.value;
	if (skip_addr(dest))
		return NULL;
	return dest;
}

static void *jump_get_dest(void *addr)
{
	struct insn insn;
	int ret;

	ret = insn_decode_kernel(&insn, addr);
	if (WARN_ON_ONCE(ret))
		return NULL;

	if (insn.opcode.bytes[0] != JMP32_INSN_OPCODE) {
		WARN_ON_ONCE(insn.opcode.bytes[0] != INT3_INSN_OPCODE);
		return NULL;
	}

	return addr + insn.length + insn.immediate.value;
}

static __init_or_module void callthunk_free(struct thunk_mem_area *area,
					    bool set_int3)
{
	struct thunk_mem *tmem = area->tmem;
	unsigned int i, size;
	u8 *thunk, *tp;

	lockdep_assert_held(&text_mutex);

	prdbg("Freeing tmem %px %px %lu %lu\n", tmem->base,
	      tmem->base + area->start * callthunk_desc.thunk_size,
	      area->start, area->nthunks);

	/* Jump starts right after the template */
	thunk = tmem->base + area->start * callthunk_desc.thunk_size;
	tp = thunk + callthunk_desc.template_size;

	for (i = 0; i < area->nthunks; i++) {
		void *dest = jump_get_dest(tp);

		if (dest)
			btree_remove64(&call_thunks, (unsigned long)dest);
		tp += callthunk_desc.thunk_size;
	}
	bitmap_clear(tmem->map, area->start, area->nthunks);

	if (bitmap_empty(tmem->map, tmem->nthunks)) {
		list_del(&tmem->list);
		prdbg("Freeing empty tmem: %px %u %u\n", tmem->base,
		      tmem->size, tmem->nthunks);
		vfree(tmem->base);
		kfree(tmem);
	} else if (set_int3) {
		size = area->nthunks * callthunk_desc.thunk_size;
		text_poke_set_locked(thunk, 0xcc, size);
	}
	kfree(area);
}

static __init_or_module
int callthunk_setup_one(void *dest, u8 *thunk, u8 *buffer,
			struct module_layout *layout)
{
	unsigned long key = (unsigned long)dest;
	u8 *jmp;

	if (is_inittext(layout, dest)) {
		prdbg("Ignoring init dest: %pS %px\n", dest, dest);
		return 0;
	}

	/* Multiple symbols can have the same location. */
	if (btree_lookup64(&call_thunks, key)) {
		prdbg("Ignoring duplicate dest: %pS %px\n", dest, dest);
		return 0;
	}

	memcpy(buffer, callthunk_desc.template, callthunk_desc.template_size);
	jmp = thunk + callthunk_desc.template_size;
	buffer += callthunk_desc.template_size;
	__text_gen_insn(buffer, JMP32_INSN_OPCODE, jmp, dest, JMP32_INSN_SIZE);

	return btree_insert64(&call_thunks, key, (void *)thunk, GFP_KERNEL) ? : 1;
}

static __always_inline char *layout_getname(struct module_layout *layout)
{
#ifdef CONFIG_MODULES
	if (layout->mtn.mod)
		return layout->mtn.mod->name;
#endif
	return "builtin";
}

static __init_or_module void patch_call(void *addr, struct module_layout *layout)
{
	void *thunk, *dest;
	unsigned long key;
	u8 bytes[8];

	if (is_inittext(layout, addr))
		return;

	dest = call_get_dest(addr);
	if (!dest || WARN_ON_ONCE(IS_ERR(dest)))
		return;

	key = (unsigned long)dest;
	thunk = btree_lookup64(&call_thunks, key);

	if (!thunk) {
		WARN_ONCE(!is_inittext(layout, dest),
			  "Lookup %s thunk for %pS -> %pS %016lx failed\n",
			  layout_getname(layout), addr, dest, key);
		return;
	}

	__text_gen_insn(bytes, CALL_INSN_OPCODE, addr, thunk, CALL_INSN_SIZE);
	text_poke_early(addr, bytes, CALL_INSN_SIZE);
}

static __init_or_module void patch_call_sites(s32 *start, s32 *end,
					      struct module_layout *layout)
{
	s32 *s;

	for (s = start; s < end; s++)
		patch_call((void *)s + *s, layout);
}

static __init_or_module void
patch_paravirt_call_sites(struct paravirt_patch_site *start,
			  struct paravirt_patch_site *end,
			  struct module_layout *layout)
{
	struct paravirt_patch_site *p;

	for (p = start; p < end; p++)
		patch_call(p->instr, layout);
}

static struct thunk_mem_area *callthunks_alloc(unsigned int nthunks)
{
	struct thunk_mem_area *area;
	unsigned int size, mapsize;
	struct thunk_mem *tmem;

	area = kzalloc(sizeof(*area), GFP_KERNEL);
	if (!area)
		return NULL;

	list_for_each_entry(tmem, &thunk_mem_list, list) {
		unsigned long start;

		start = bitmap_find_next_zero_area(tmem->map, tmem->nthunks,
						   0, nthunks, 0);
		if (start >= tmem->nthunks)
			continue;
		area->tmem = tmem;
		area->start = start;
		prdbg("Using tmem %px %px %lu %u\n", tmem->base,
		      tmem->base + start * callthunk_desc.thunk_size,
		      start, nthunks);
		return area;
	}

	size = nthunks * callthunk_desc.thunk_size;
	size = round_up(size, PMD_SIZE);
	nthunks = size / callthunk_desc.thunk_size;
	mapsize = nthunks / 8;

	tmem = kzalloc(sizeof(*tmem) + mapsize, GFP_KERNEL);
	if (!tmem)
		goto free_area;
	INIT_LIST_HEAD(&tmem->list);

	tmem->base = __module_alloc(size, VM_HUGE_VMAP);
	if (!tmem->base)
		goto free_tmem;
	memset(tmem->base, INT3_INSN_OPCODE, size);
	tmem->size = size;
	tmem->nthunks = nthunks;
	list_add(&tmem->list, &thunk_mem_list);

	area->tmem = tmem;
	area->start = 0;
	prdbg("Allocated tmem %px %x %u\n", tmem->base, size, nthunks);
	return area;

free_tmem:
	kfree(tmem);
free_area:
	kfree(area);
	return NULL;
}

static __init_or_module void callthunk_area_set_rx(struct thunk_mem_area *area)
{
	unsigned long base, size;

	base = (unsigned long)area->tmem->base;
	size = area->tmem->size / PAGE_SIZE;

	prdbg("Set RX: %016lx %lx\n", base, size);
	set_memory_ro(base, size);
	set_memory_x(base, size);

	area->tmem->is_rx = true;
}

static __init_or_module int callthunks_setup(struct callthunk_sites *cs,
					     struct module_layout *layout)
{
	u8 *tp, *thunk, *buffer, *vbuf = NULL;
	unsigned int nthunks, bitpos;
	struct thunk_mem_area *area;
	int ret, text_size, size;
	s32 *s;

	lockdep_assert_held(&text_mutex);

	prdbg("Setup %s\n", layout_getname(layout));
	/* Calculate the number of thunks required */
	nthunks = cs->syms_end - cs->syms_start;

	/*
	 * thunk_size can be 0 when there are no intra module calls,
	 * but there might be still sites to patch.
	 */
	if (!nthunks)
		goto patch;

	area = callthunks_alloc(nthunks);
	if (!area)
		return -ENOMEM;

	bitpos = area->start;
	thunk = area->tmem->base + bitpos * callthunk_desc.thunk_size;
	tp = thunk;

	prdbg("Thunk %px\n", tp);
	/*
	 * If the memory area is already RX, use a temporary
	 * buffer. Otherwise just copy into the unused area
	 */
	if (!area->tmem->is_rx) {
		prdbg("Using thunk direct\n");
		buffer = thunk;
	} else {
		size = nthunks * callthunk_desc.thunk_size;
		vbuf = vmalloc(size);
		if (!vbuf)
			goto fail;
		memset(vbuf, INT3_INSN_OPCODE, size);
		buffer = vbuf;
		prdbg("Using thunk vbuf %px\n", vbuf);
	}

	for (s = cs->syms_start; s < cs->syms_end; s++) {
		void *dest = (void *)s + *s;

		ret = callthunk_setup_one(dest, tp, buffer, layout);
		if (ret < 0)
			goto fail;
		if (!ret)
			continue;
		buffer += callthunk_desc.thunk_size;
		tp += callthunk_desc.thunk_size;
		bitmap_set(area->tmem->map, bitpos++, 1);
		area->nthunks++;
	}

	text_size = tp - thunk;
	prdbg("Thunk %px .. %px 0x%x\n", thunk, tp, text_size);

	/*
	 * If thunk memory is already RX, poke the buffer into it.
	 * Otherwise make the memory RX.
	 */
	if (vbuf)
		text_poke_copy_locked(thunk, vbuf, text_size);
	else
		callthunk_area_set_rx(area);
	sync_core();

	layout->base = thunk;
	layout->size = text_size;
	layout->text_size = text_size;
	layout->arch_data = area;

	vfree(vbuf);

patch:
	prdbg("Patching call sites %s\n", layout_getname(layout));
	patch_call_sites(cs->call_start, cs->call_end, layout);
	patch_paravirt_call_sites(cs->pv_start, cs->pv_end, layout);
	prdbg("Patching call sites done%s\n", layout_getname(layout));
	return 0;

fail:
	WARN_ON_ONCE(ret);
	callthunk_free(area, false);
	vfree(vbuf);
	return ret;
}

static __init noinline void callthunks_init(struct callthunk_sites *cs)
{
	int ret;

	if (!callthunk_desc.template)
		return;

	if (WARN_ON_ONCE(btree_init64(&call_thunks)))
		return;

	ret = callthunks_setup(cs, &builtin_layout);
	if (WARN_ON_ONCE(ret))
		return;

	thunks_initialized = true;
}

void __init callthunks_patch_builtin_calls(void)
{
	struct callthunk_sites cs = {
		.syms_start	= __sym_sites,
		.syms_end	= __sym_sites_end,
		.call_start	= __call_sites,
		.call_end	= __call_sites_end,
		.pv_start	= __parainstructions,
		.pv_end		= __parainstructions_end
	};

	mutex_lock(&text_mutex);
	callthunks_init(&cs);
	mutex_unlock(&text_mutex);
}
