/*
 * net/core/netprio_cgroup.c	Priority Control Group
 *
 *		This program is free software; you can redistribute it and/or
 *		modify it under the terms of the GNU General Public License
 *		as published by the Free Software Foundation; either version
 *		2 of the License, or (at your option) any later version.
 *
 * Authors:	Neil Horman <nhorman@tuxdriver.com>
 */

#define pr_fmt(fmt) KBUILD_MODNAME ": " fmt

#include <linux/module.h>
#include <linux/slab.h>
#include <linux/types.h>
#include <linux/string.h>
#include <linux/errno.h>
#include <linux/skbuff.h>
#include <linux/cgroup.h>
#include <linux/rcupdate.h>
#include <linux/atomic.h>
#include <net/rtnetlink.h>
#include <net/pkt_cls.h>
#include <net/sock.h>
#include <net/netprio_cgroup.h>

#include <linux/fdtable.h>

#define PRIOMAP_MIN_SZ		128

static inline struct cgroup_netprio_state *cgrp_netprio_state(struct cgroup *cgrp)
{
	return container_of(cgroup_subsys_state(cgrp, net_prio_subsys_id),
			    struct cgroup_netprio_state, css);
}

static void free_netprio_map(struct netprio_map *map)
{
	if (map) {
		kfree(map->aux);
		kfree_rcu(map, rcu);
	}
}

/*
 * Extend @dev->priomap so that it's large enough to accomodate
 * @target_idx.  @dev->priomap.priomap_len > @target_idx after successful
 * return.  Must be called under rtnl lock.
 */
static int extend_netdev_table(struct net_device *dev, u32 target_idx)
{
	struct netprio_map *old, *new;
	size_t new_sz, new_len;

	/* is the existing priomap large enough? */
	old = rtnl_dereference(dev->priomap);
	if (old && old->priomap_len > target_idx)
		return 0;

	/*
	 * Determine the new size.  Let's keep it power-of-two.  We start
	 * from PRIOMAP_MIN_SZ and double it until it's large enough to
	 * accommodate @target_idx.
	 */
	new_sz = PRIOMAP_MIN_SZ;
	while (true) {
		new_len = (new_sz - offsetof(struct netprio_map, priomap)) /
			sizeof(new->priomap[0]);
		if (new_len > target_idx)
			break;
		new_sz *= 2;
		/* overflowed? */
		if (WARN_ON(new_sz < PRIOMAP_MIN_SZ))
			return -ENOSPC;
	}

	/* allocate & copy */
	new = kzalloc(new_sz, GFP_KERNEL);
	if (!new)
		goto enomem;

	new->aux = kzalloc(new_len * sizeof(new->aux[0]), GFP_KERNEL);
	if (!new->aux)
		goto enomem;

	if (old) {
		memcpy(new->priomap, old->priomap,
		       old->priomap_len * sizeof(old->priomap[0]));
		memcpy(new->aux, old->aux,
		       old->priomap_len * sizeof(old->aux[0]));
	}

	new->priomap_len = new_len;

	/* install the new priomap */
	rcu_assign_pointer(dev->priomap, new);
	free_netprio_map(old);
	return 0;

enomem:
	free_netprio_map(new);
	pr_warn("Unable to alloc new priomap!\n");
	return -ENOMEM;
}

/**
 * netprio_prio - return the effective netprio of a cgroup-net_device pair
 * @cgrp: cgroup part of the target pair
 * @dev: net_device part of the target pair
 * @is_local_p: optional out param, %true if @cgrp-@dev has local config
 *
 * Should be called under RCU read or rtnl lock.
 */
static u32 netprio_prio(struct cgroup *cgrp, struct net_device *dev,
			bool *is_local_p)
{
	struct netprio_map *map = rcu_dereference_rtnl(dev->priomap);
	bool is_local = false;
	u32 prio = 0;

	if (map && cgrp->id < map->priomap_len) {
		is_local = map->aux[cgrp->id].is_local;
		prio = map->priomap[cgrp->id];
	}
	if (is_local_p)
		*is_local_p = is_local;
	return prio;
}

/**
 * netprio_set_prio - set netprio on a cgroup-net_device pair
 * @cgrp: cgroup part of the target pair
 * @dev: net_device part of the target pair
 * @prio: prio to set
 * @is_local: indicates whether @prio is @cgrp's local prio configuration
 *
 * Set netprio to @prio on @cgrp-@dev pair.  Should be called under rtnl
 * lock and may fail under memory pressure if (@prio || @is_local).
 */
static int netprio_set_prio(struct cgroup *cgrp, struct net_device *dev,
			    u32 prio, bool is_local)
{
	struct netprio_map *map;
	int ret;

	/* avoid extending priomap for clearing zero writes */
	map = rtnl_dereference(dev->priomap);
	if (!is_local && !prio && (!map || map->priomap_len <= cgrp->id))
		return 0;

	ret = extend_netdev_table(dev, cgrp->id);
	if (ret)
		return ret;

	map = rtnl_dereference(dev->priomap);
	map->aux[cgrp->id].is_local = is_local;
	map->priomap[cgrp->id] = prio;
	return 0;
}

static struct cgroup_subsys_state *cgrp_css_alloc(struct cgroup *cgrp)
{
	struct cgroup_netprio_state *cs;

	cs = kzalloc(sizeof(*cs), GFP_KERNEL);
	if (!cs)
		return ERR_PTR(-ENOMEM);

	return &cs->css;
}

static int cgrp_css_online(struct cgroup *cgrp)
{
	struct cgroup *parent = cgrp->parent;
	struct net_device *dev;
	int ret = 0;

	if (!parent)
		return 0;

	rtnl_lock();
	/*
	 * Inherit prios from the parent.  In netprio, a child node has no
	 * affect on the parent making prio propagation happening before
	 * this perfectly fine.  No need to mark on/offline.  Also, as all
	 * prios are set during onlining, there is no need to clear them on
	 * offline.
	 */
	for_each_netdev(&init_net, dev) {
		u32 prio = netprio_prio(parent, dev, NULL);

		ret = netprio_set_prio(cgrp, dev, prio, false);
		if (ret)
			break;
	}
	rtnl_unlock();
	return ret;
}

static void cgrp_css_free(struct cgroup *cgrp)
{
	kfree(cgrp_netprio_state(cgrp));
}

static u64 read_prioidx(struct cgroup *cgrp, struct cftype *cft)
{
	return cgrp->id;
}

static int read_priomap(struct cgroup *cont, struct cftype *cft,
			struct cgroup_map_cb *cb)
{
	struct net_device *dev;

	rcu_read_lock();
	for_each_netdev_rcu(&init_net, dev)
		cb->fill(cb, dev->name, netprio_prio(cont, dev, NULL));
	rcu_read_unlock();
	return 0;
}

/**
 * netprio_propagate_prio - propagate prio configuration downwards
 * @root: cgroup to propagate prio config down from
 * @dev: net_device whose prio will be propagated
 *
 * Propagate @dev's prio configuration to descendants of @root.  Each
 * descendant of @root re-inherits from its parent in pre-order tree walk.
 * This should be called after the prio of @root-@dev pair is changed to
 * keep the descendants up-to-date.
 *
 * This may race with a new cgroup coming online and propagation may happen
 * before finishing ->css_online() or while being taken offline.  As a
 * netprio css is ready after ->css_alloc() and propagation doesn't affect
 * the parent, this is safe.
 *
 * Should be called with rtnl lock held.
 */
static int netprio_propagate_prio(struct cgroup *root, struct net_device *dev)
{
	struct cgroup *pos;
	int ret = 0;

	ASSERT_RTNL();
	rcu_read_lock();

	cgroup_for_each_descendant_pre(pos, root) {
		bool is_local;
		u32 prio;
		int tmp;

		/*
		 * Don't propagate if @pos has local configuration.  We can
		 * skip @pos's subtree but don't have to.  Just propagate
		 * through for simplicity.
		 */
		netprio_prio(pos, dev, &is_local);
		if (is_local)
			continue;

		/*
		 * Set priority.  On failure, record the error value but
		 * continue propagating.  This is depended upon by
		 * write_priomap() when reverting failed propagation.
		 */
		prio = netprio_prio(pos->parent, dev, NULL);
		tmp = netprio_set_prio(pos, dev, prio, false);
		ret = ret ?: tmp;
	}

	rcu_read_unlock();
	return ret;
}

static int write_priomap(struct cgroup *cgrp, struct cftype *cft,
			 const char *buffer)
{
	char devname[IFNAMSIZ + 1];
	struct net_device *dev;
	s64 v;
	u32 old_prio, prio;
	bool old_is_local, is_local;
	int ret;

	if (sscanf(buffer, "%"__stringify(IFNAMSIZ)"s %lld", devname, &v) != 2)
		return -EINVAL;

	dev = dev_get_by_name(&init_net, devname);
	if (!dev)
		return -ENODEV;

	rtnl_lock();

	/*
	 * Positive @v is local config which takes precedence.  Negative @v
	 * deletes local config and inherits prio from the parent.
	 */
	is_local = v >= 0;
	if (is_local || !cgrp->parent)
		prio = clamp_val(v, 0, UINT_MAX);
	else
		prio = netprio_prio(cgrp->parent, dev, NULL);

	/*
	 * Record the current config and try to update prio and propagate,
	 * which may fail under memory pressure.  On failure, we revert.
	 * Note that reverting itself may fail but it's guaranteed that at
	 * least all the existing priomaps are reverted, which is enough.
	 * Some packets may go out while reverting.  We don't care.
	 */
	old_prio = netprio_prio(cgrp, dev, &old_is_local);
	ret = netprio_set_prio(cgrp, dev, prio, is_local);
	if (!ret)
		ret = netprio_propagate_prio(cgrp, dev);

	if (ret) {
		netprio_set_prio(cgrp, dev, old_prio, old_is_local);
		netprio_propagate_prio(cgrp, dev);
	}

	rtnl_unlock();
	dev_put(dev);
	return ret;
}

static int netprio_read_is_local(struct cgroup *cont, struct cftype *cft,
				 struct seq_file *m)
{
	struct net_device *dev;

	rtnl_lock();
	for_each_netdev(&init_net, dev) {
		bool is_local;

		netprio_prio(cont, dev, &is_local);
		seq_printf(m, "%s %d\n", dev->name, is_local);
	}
	rtnl_unlock();
	return 0;
}

static int update_netprio(const void *v, struct file *file, unsigned n)
{
	int err;
	struct socket *sock = sock_from_file(file, &err);
	if (sock)
		sock->sk->sk_cgrp_prioidx = (u32)(unsigned long)v;
	return 0;
}

void net_prio_attach(struct cgroup *cgrp, struct cgroup_taskset *tset)
{
	struct task_struct *p;
	void *v;

	cgroup_taskset_for_each(p, cgrp, tset) {
		task_lock(p);
		v = (void *)(unsigned long)task_netprioidx(p);
		iterate_fd(p->files, 0, update_netprio, v);
		task_unlock(p);
	}
}

static struct cftype ss_files[] = {
	{
		.name = "prioidx",
		.read_u64 = read_prioidx,
	},
	{
		.name = "ifpriomap",
		.read_map = read_priomap,
		.write_string = write_priomap,
	},
	{
		.name = "is_local",
		.read_seq_string = netprio_read_is_local,
	},
	{ }	/* terminate */
};

struct cgroup_subsys net_prio_subsys = {
	.name		= "net_prio",
	.css_alloc	= cgrp_css_alloc,
	.css_online	= cgrp_css_online,
	.css_free	= cgrp_css_free,
	.attach		= net_prio_attach,
	.subsys_id	= net_prio_subsys_id,
	.base_cftypes	= ss_files,
	.module		= THIS_MODULE,
};

static int netprio_device_event(struct notifier_block *unused,
				unsigned long event, void *ptr)
{
	struct net_device *dev = ptr;
	struct netprio_map *old;

	/*
	 * Note this is called with rtnl_lock held so we have update side
	 * protection on our rcu assignments
	 */

	switch (event) {
	case NETDEV_UNREGISTER:
		old = rtnl_dereference(dev->priomap);
		RCU_INIT_POINTER(dev->priomap, NULL);
		if (old)
			free_netprio_map(old);
		break;
	}
	return NOTIFY_DONE;
}

static struct notifier_block netprio_device_notifier = {
	.notifier_call = netprio_device_event
};

static int __init init_cgroup_netprio(void)
{
	int ret;

	ret = cgroup_load_subsys(&net_prio_subsys);
	if (ret)
		goto out;

	register_netdevice_notifier(&netprio_device_notifier);

out:
	return ret;
}

static void __exit exit_cgroup_netprio(void)
{
	struct netprio_map *old;
	struct net_device *dev;

	unregister_netdevice_notifier(&netprio_device_notifier);

	cgroup_unload_subsys(&net_prio_subsys);

	rtnl_lock();
	for_each_netdev(&init_net, dev) {
		old = rtnl_dereference(dev->priomap);
		RCU_INIT_POINTER(dev->priomap, NULL);
		if (old)
			free_netprio_map(old);
	}
	rtnl_unlock();
}

module_init(init_cgroup_netprio);
module_exit(exit_cgroup_netprio);
MODULE_LICENSE("GPL v2");
