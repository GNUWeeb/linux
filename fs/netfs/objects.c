// SPDX-License-Identifier: GPL-2.0-only
/* Object lifetime handling and tracing.
 *
 * Copyright (C) 2022 Red Hat, Inc. All Rights Reserved.
 * Written by David Howells (dhowells@redhat.com)
 */

#include <linux/export.h>
#include <linux/slab.h>
#include "internal.h"

atomic_t netfs_region_debug_ids;

static void netfs_init_req_work(struct work_struct *work)
{
	pr_info("New req work queued!\n");
}

/*
 * Allocate an I/O request and initialise it.
 */
struct netfs_io_request *netfs_alloc_request(struct address_space *mapping,
					     struct file *file,
					     loff_t start, size_t len,
					     enum netfs_io_origin origin)
{
	static atomic_t debug_ids;
	struct inode *inode = file ? file_inode(file) : mapping->host;
	struct netfs_inode *ctx = netfs_inode(inode);
	struct netfs_io_request *rreq;
	unsigned int i;
	bool is_dio = (origin == NETFS_DIO_READ || origin == NETFS_DIO_WRITE);
	bool cached = !is_dio && netfs_is_cache_enabled(ctx);
	int ret;

	rreq = kzalloc(ctx->ops->io_request_size ?: sizeof(struct netfs_io_request),
		       GFP_KERNEL);
	if (!rreq)
		return ERR_PTR(-ENOMEM);

	rreq->start	= start;
	rreq->len	= len;
	rreq->origin	= origin;
	rreq->netfs_ops	= ctx->ops;
	rreq->mapping	= mapping;
	rreq->inode	= inode;
	rreq->i_size	= i_size_read(inode);
	rreq->debug_id	= atomic_inc_return(&debug_ids);
	xa_init(&rreq->buffer);
	xa_init(&rreq->bounce);
	rreq->chains	= rreq->chain;
	rreq->nr_chains	= 1;
	for (i = 0; i < ARRAY_SIZE(rreq->chain); i++)
		INIT_LIST_HEAD(&rreq->chain[i].subrequests);
	INIT_LIST_HEAD(&rreq->regions);
	INIT_WORK(&rreq->work, netfs_init_req_work);
	refcount_set(&rreq->ref, 1);

	__set_bit(NETFS_RREQ_IN_PROGRESS, &rreq->flags);
	if (test_bit(NETFS_ICTX_ENCRYPTED, &ctx->flags))
		__set_bit(NETFS_RREQ_CONTENT_ENCRYPTION, &rreq->flags);
	if (cached)
		__set_bit(NETFS_RREQ_WRITE_TO_CACHE, &rreq->flags);
	if (file && file->f_flags & O_NONBLOCK)
		__set_bit(NETFS_RREQ_NONBLOCK, &rreq->flags);
	if (rreq->netfs_ops->init_request) {
		ret = rreq->netfs_ops->init_request(rreq, file);
		if (ret < 0) {
			xa_destroy(&rreq->buffer);
			xa_destroy(&rreq->bounce);
			kfree(rreq);
			return ERR_PTR(ret);
		}
	}

	trace_netfs_rreq_ref(rreq->debug_id, 1, netfs_rreq_trace_new);
	netfs_proc_add_rreq(rreq);
	netfs_stat(&netfs_n_rh_rreq);
	return rreq;
}

void netfs_get_request(struct netfs_io_request *rreq, enum netfs_rreq_ref_trace what)
{
	int r;

	__refcount_inc(&rreq->ref, &r);
	trace_netfs_rreq_ref(rreq->debug_id, r + 1, what);
}

void netfs_clear_subrequests(struct netfs_io_request *rreq, bool was_async)
{
	struct netfs_io_subrequest *subreq;
	unsigned int i;

	for (i = 0; i < rreq->nr_chains; i++) {
		struct netfs_io_chain *chain = &rreq->chains[i];

		while (!list_empty(&chain->subrequests)) {
			subreq = list_first_entry(&chain->subrequests,
						  struct netfs_io_subrequest, chain_link);
			list_del(&subreq->chain_link);
			netfs_put_subrequest(subreq, was_async,
					     netfs_sreq_trace_put_clear);
		}
	}

	if (rreq->chains != rreq->chain)
		kfree(rreq->chains);
}

static void netfs_clear_regions(struct netfs_io_request *rreq)
{
	struct netfs_dirty_region *region;
	struct netfs_inode *ctx = netfs_inode(rreq->inode);

	while ((region = list_first_entry_or_null(
			&rreq->regions, struct netfs_dirty_region, dirty_link))) {
		list_del_init(&region->dirty_link);
		netfs_put_dirty_region(ctx, region, netfs_region_trace_put_clear);
	}
}

static void netfs_free_request(struct work_struct *work)
{
	struct netfs_io_request *rreq =
		container_of(work, struct netfs_io_request, work);
	unsigned int i;

	trace_netfs_rreq(rreq, netfs_rreq_trace_free);
	netfs_proc_del_rreq(rreq);
	netfs_clear_subrequests(rreq, false);
	netfs_clear_regions(rreq);

	if (rreq->netfs_ops->free_request)
		rreq->netfs_ops->free_request(rreq);
	if (rreq->cache_resources.ops)
		rreq->cache_resources.ops->end_operation(&rreq->cache_resources);
	netfs_clear_buffer(&rreq->buffer);
	netfs_clear_buffer(&rreq->bounce);
	if (rreq->direct_bv) {
		for (i = 0; i < rreq->direct_bv_count; i++)
			if (rreq->direct_bv[i].bv_page)
				put_page(rreq->direct_bv[i].bv_page);
		kvfree(rreq->direct_bv);
	}
	kfree_rcu(rreq, rcu);
	netfs_stat_d(&netfs_n_rh_rreq);
}

void netfs_put_request(struct netfs_io_request *rreq, bool was_async,
		       enum netfs_rreq_ref_trace what)
{
	unsigned int debug_id;
	bool dead;
	int r;

	if (rreq) {
		debug_id = rreq->debug_id;
		dead = __refcount_dec_and_test(&rreq->ref, &r);
		trace_netfs_rreq_ref(debug_id, r - 1, what);
		if (dead) {
			if (was_async) {
				INIT_WORK(&rreq->work, netfs_free_request);
				if (!queue_work(system_unbound_wq, &rreq->work))
					BUG();
			} else {
				netfs_free_request(&rreq->work);
			}
		}
	}
}
EXPORT_SYMBOL(netfs_put_request);

static void netfs_init_subreq_work(struct work_struct *work)
{
	pr_info("New subreq work queued!\n");
}

/*
 * Allocate and partially initialise an I/O request structure.
 */
struct netfs_io_subrequest *netfs_alloc_subrequest(struct netfs_io_request *rreq)
{
	struct netfs_io_subrequest *subreq;

	subreq = kzalloc(rreq->netfs_ops->io_subrequest_size ?:
			 sizeof(struct netfs_io_subrequest),
			 GFP_KERNEL);
	if (subreq) {
		INIT_WORK(&subreq->work, netfs_init_subreq_work);
		INIT_LIST_HEAD(&subreq->chain_link);
		refcount_set(&subreq->ref, 2);
		subreq->rreq = rreq;
		netfs_get_request(rreq, netfs_rreq_trace_get_subreq);
		netfs_stat(&netfs_n_rh_sreq);
	}

	return subreq;
}

void netfs_get_subrequest(struct netfs_io_subrequest *subreq,
			  enum netfs_sreq_ref_trace what)
{
	int r;

	__refcount_inc(&subreq->ref, &r);
	trace_netfs_sreq_ref(subreq->rreq->debug_id, subreq->debug_index,
			     subreq->chain, r + 1, what);
}

static void netfs_free_subrequest(struct netfs_io_subrequest *subreq,
				  bool was_async)
{
	struct netfs_io_request *rreq = subreq->rreq;

	trace_netfs_sreq(subreq, netfs_sreq_trace_free);
	kfree(subreq);
	netfs_stat_d(&netfs_n_rh_sreq);
	netfs_put_request(rreq, was_async, netfs_rreq_trace_put_subreq);
}

void netfs_put_subrequest(struct netfs_io_subrequest *subreq, bool was_async,
			  enum netfs_sreq_ref_trace what)
{
	unsigned char chain = subreq->chain;
	unsigned int debug_index = subreq->debug_index;
	unsigned int debug_id = subreq->rreq->debug_id;
	bool dead;
	int r;

	dead = __refcount_dec_and_test(&subreq->ref, &r);
	trace_netfs_sreq_ref(debug_id, debug_index, chain, r - 1, what);
	if (dead)
		netfs_free_subrequest(subreq, was_async);
}
EXPORT_SYMBOL(netfs_put_subrequest);

/*
 * Allocate a dirty region record.
 */
struct netfs_dirty_region *netfs_alloc_dirty_region(gfp_t gfp)
{
	struct netfs_dirty_region *region;

	region = kzalloc(sizeof(struct netfs_dirty_region), gfp);
	if (region) {
		refcount_set(&region->ref, 1);
		INIT_LIST_HEAD(&region->dirty_link);
		INIT_LIST_HEAD(&region->proc_link);
		netfs_stat(&netfs_n_wh_region);
	}
	return region;
}

struct netfs_dirty_region *netfs_get_dirty_region(struct netfs_inode *ctx,
						  struct netfs_dirty_region *region,
						  enum netfs_region_trace what)
{
	int ref;

	__refcount_inc(&region->ref, &ref);
	trace_netfs_ref_region(region->debug_id, ref + 1, what);
	return region;
}

static void netfs_free_dirty_region(struct netfs_inode *ctx,
				    struct netfs_dirty_region *region,
				    enum netfs_region_trace what)
{
	struct netfs_dirty_region *absorbed_by;

	if (region) {
		trace_netfs_ref_region(region->debug_id, 0, netfs_region_trace_free);
		if (!list_empty(&region->proc_link))
			netfs_proc_del_region(region);
		if (ctx->ops->free_dirty_region)
			ctx->ops->free_dirty_region(region);
		BUG_ON(!list_empty(&region->flush_link));
		if (region->group) {
			int nr = atomic_dec_return(&region->group->nr_regions);

			if (nr == 0)
				wake_up_var(&region->group->nr_regions);
			netfs_put_flush_group(ctx, region->group);
		}
		netfs_stat_d(&netfs_n_wh_region);
		absorbed_by = region->absorbed_by;
		kfree(region);
		netfs_put_dirty_region(ctx, absorbed_by,
				       netfs_region_trace_put_absorbed_by);
	}
}

void netfs_put_dirty_region(struct netfs_inode *ctx,
			    struct netfs_dirty_region *region,
			    enum netfs_region_trace what)
{
	bool dead;
	int ref;

	if (!region)
		return;
	dead = __refcount_dec_and_test(&region->ref, &ref);
	trace_netfs_ref_region(region->debug_id, ref - 1, what);
	if (dead) {
		netfs_return_write_credit(region);
		netfs_free_dirty_region(ctx, region, what);
	}
}

/**
 * netfs_new_flush_group - Create a new write flush group
 * @inode: The inode for which this is a flush group.
 * @netfs_priv: Netfs private data to include in the new group
 *
 * Create a new flush group and add it to the top of the inode's group list.
 * Flush groups are used to control the order in which dirty data is written
 * back to the server.
 */
struct netfs_flush_group *netfs_new_flush_group(struct inode *inode, void *netfs_priv)
{
	struct netfs_flush_group *group, *prev;
	struct netfs_inode *ctx = netfs_inode(inode);

	group = kzalloc(sizeof(*group), GFP_KERNEL);
	if (group) {
		group->netfs_priv = netfs_priv;
		INIT_LIST_HEAD(&group->region_list);
		refcount_set(&group->ref, 1);
		netfs_stat(&netfs_n_wh_flush_group);

		spin_lock(&ctx->dirty_lock);
		group->flush_id = ++ctx->flush_counter;

		/* We drop the region count on the old top group so that
		 * writeback can get rid of it.
		 */
		if (!list_empty(&ctx->flush_groups)) {
			prev = list_last_entry(&ctx->flush_groups,
					       struct netfs_flush_group, group_link);
			if (atomic_dec_and_test(&prev->nr_regions))
				wake_up_var(&prev->nr_regions);
		}

		/* We keep the region count elevated on the new group to
		 * prevent wakeups whilst this is the top group.
		 */
		atomic_set(&group->nr_regions, 1);
		list_add_tail(&group->group_link, &ctx->flush_groups);

		spin_unlock(&ctx->dirty_lock);
	}
	return group;
}
EXPORT_SYMBOL(netfs_new_flush_group);

struct netfs_flush_group *netfs_get_flush_group(struct netfs_flush_group *group)
{
	refcount_inc(&group->ref);
	return group;
}

void netfs_put_flush_group(struct netfs_inode *ctx, struct netfs_flush_group *group)
{
	if (group && refcount_dec_and_test(&group->ref)) {
		netfs_stat_d(&netfs_n_wh_flush_group);
		if (ctx->ops->free_flush_group)
			ctx->ops->free_flush_group(ctx, group);
		kfree(group);
	}
}
