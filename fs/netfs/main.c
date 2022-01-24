// SPDX-License-Identifier: GPL-2.0-or-later
/* Network filesystem library.
 *
 * Copyright (C) 2021 Red Hat, Inc. All Rights Reserved.
 * Written by David Howells (dhowells@redhat.com)
 */

#include <linux/module.h>
#include <linux/export.h>
#include <linux/fs.h>
#include <linux/slab.h>
#include <linux/proc_fs.h>
#include <linux/seq_file.h>
#include "internal.h"

/*
 * Check the inode context parameters are sane.
 */
int netfs_sanity_check_ictx(struct address_space *mapping)
{
	struct netfs_i_context *ctx = netfs_i_context(mapping->host);

	BUG_ON(!ctx->wsize);

	return 0;
}

#ifdef CONFIG_PROC_FS
LIST_HEAD(netfs_regions);
DEFINE_SPINLOCK(netfs_regions_lock);

static const char netfs_proc_region_states[] = "PADFC";
static const char *netfs_proc_region_types[] = {
	[NETFS_REGION_ORDINARY]		= "ORD ",
	[NETFS_REGION_DIO]		= "DIOW",
	[NETFS_REGION_DSYNC]		= "DSYN",
};

/*
 * Generate a list of regions in /proc/fs/netfs/regions
 */
static int netfs_regions_seq_show(struct seq_file *m, void *v)
{
	struct netfs_dirty_region *region;

	if (v == &netfs_regions) {
		seq_puts(m,
			 "REGION   REF TYPE S FL DEV   INODE    DIRTY, BOUNDS\n"
			 "======== === ==== = == ===== ======== ==============================\n"
			 );
		return 0;
	}

	region = list_entry(v, struct netfs_dirty_region, proc_link);
	seq_printf(m,
		   "%08x %3d %s %c %2lx %02x:%02x %8x %04llx-%04llx %04llx-%04llx\n",
		   region->debug_id,
		   refcount_read(&region->ref),
		   netfs_proc_region_types[region->type],
		   netfs_proc_region_states[region->state],
		   region->flags,
		   0, 0, 0,
		   region->dirty.start, region->dirty.end,
		   region->bounds.start, region->bounds.end);
	return 0;
}

static void *netfs_regions_seq_start(struct seq_file *m, loff_t *_pos)
	__acquires(rcu)
{
	rcu_read_lock();
	return seq_list_start_head(&netfs_regions, *_pos);
}

static void *netfs_regions_seq_next(struct seq_file *m, void *v, loff_t *_pos)
{
	return seq_list_next(v, &netfs_regions, _pos);
}

static void netfs_regions_seq_stop(struct seq_file *m, void *v)
	__releases(rcu)
{
	rcu_read_unlock();
}

const struct seq_operations netfs_regions_seq_ops = {
	.start  = netfs_regions_seq_start,
	.next   = netfs_regions_seq_next,
	.stop   = netfs_regions_seq_stop,
	.show   = netfs_regions_seq_show,
};
#endif /* CONFIG_PROC_FS */

static int __init netfs_init(void)
{
	if (!proc_mkdir("fs/netfs", NULL))
		goto error;

	if (!proc_create_seq("fs/netfs/regions", S_IFREG | 0444, NULL,
			     &netfs_regions_seq_ops))
		goto error_proc;

	return 0;

error_proc:
	remove_proc_entry("fs/netfs", NULL);
error:
	return -ENOMEM;
}
fs_initcall(netfs_init);

static void __exit netfs_exit(void)
{
	remove_proc_entry("fs/netfs", NULL);
}
module_exit(netfs_exit);
