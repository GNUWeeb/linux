// SPDX-License-Identifier: GPL-2.0-only
/* Object lifetime handling and tracing.
 *
 * Copyright (C) 2022 Red Hat, Inc. All Rights Reserved.
 * Written by David Howells (dhowells@redhat.com)
 */

#include <linux/export.h>
#include <linux/fs.h>
#include <linux/mm.h>
#include <linux/pagemap.h>
#include <linux/slab.h>
#include <linux/backing-dev.h>
#include "internal.h"

/*
 * Deduct the write credits to be used by this operation from the credits
 * available.  This is used to throttle the generation of write requests.
 */
void netfs_deduct_write_credit(struct netfs_dirty_region *region, size_t credits)
{
	region->credit = credits;
	atomic_long_sub(credits, &netfs_write_credit);
}

/*
 * Return the write credits that were used by this operation to the available
 * credits counter.  This is used to throttle the generation of write requests.
 */
static void netfs_return_write_credit(struct netfs_dirty_region *region)
{
	long c;

	c = atomic_long_add_return(region->credit, &netfs_write_credit);
	if (c > 0 && (long)(c - region->credit) <= 0)
		wake_up_var(&netfs_write_credit);
}

/*
 * Wait for sufficient credit to become available, thereby throttling the
 * creation of write requests.
 */
int netfs_wait_for_credit(struct writeback_control *wbc)
{
	if (atomic_long_read(&netfs_write_credit) <= 0) {
		if (wbc->sync_mode == WB_SYNC_NONE)
			return -EBUSY;
		return wait_var_event_killable(&netfs_write_credit,
					       atomic_long_read(&netfs_write_credit) > 0);
	}

	return 0;
}

/**
 * netfs_new_flush_group - Create a new write flush group
 * @inode: The inode for which this is a flush group.
 * @netfs_priv: Netfs private data to include in the new group
 *
 * Create a new flush group and add it to the tail of the inode's group list.
 * Flush groups are used to control the order in which dirty data is written
 * back to the server.
 *
 * The caller must hold ctx->lock.
 */
struct netfs_flush_group *netfs_new_flush_group(struct inode *inode, void *netfs_priv)
{
	struct netfs_flush_group *group;
	struct netfs_i_context *ctx = netfs_i_context(inode);

	group = kzalloc(sizeof(*group), GFP_KERNEL);
	if (group) {
		group->netfs_priv = netfs_priv;
		INIT_LIST_HEAD(&group->region_list);
		refcount_set(&group->ref, 1);
		netfs_stat(&netfs_n_wh_flush_group);
		spin_lock(&ctx->lock);
		list_add_tail(&group->group_link, &ctx->flush_groups);
		spin_unlock(&ctx->lock);
	}
	return group;
}
EXPORT_SYMBOL(netfs_new_flush_group);

struct netfs_flush_group *netfs_get_flush_group(struct netfs_flush_group *group)
{
	refcount_inc(&group->ref);
	return group;
}

void netfs_put_flush_group(struct netfs_i_context *ctx,
			   struct netfs_flush_group *group)
{
	if (group && refcount_dec_and_test(&group->ref)) {
		netfs_stat_d(&netfs_n_wh_flush_group);
		if (ctx->ops->free_flush_group)
			ctx->ops->free_flush_group(ctx, group);
		kfree(group);
	}
}

struct netfs_dirty_region *netfs_alloc_dirty_region(void)
{
	struct netfs_dirty_region *region;

	region = kzalloc(sizeof(struct netfs_dirty_region), GFP_KERNEL);
	if (region) {
		INIT_LIST_HEAD(&region->proc_link);
		netfs_stat(&netfs_n_wh_region);
	}
	return region;
}

struct netfs_dirty_region *netfs_get_dirty_region(struct netfs_i_context *ctx,
						  struct netfs_dirty_region *region,
						  enum netfs_region_trace what)
{
	int ref;

	__refcount_inc(&region->ref, &ref);
	trace_netfs_ref_region(region->debug_id, ref + 1, what);
	return region;
}

void netfs_free_dirty_region(struct netfs_i_context *ctx,
			     struct netfs_dirty_region *region)
{
	if (region) {
		trace_netfs_ref_region(region->debug_id, 0, netfs_region_trace_free);
		if (!list_empty(&region->proc_link))
			netfs_proc_del_region(region);
		if (ctx->ops->free_dirty_region)
			ctx->ops->free_dirty_region(region);
		netfs_put_flush_group(ctx, region->group);
		netfs_stat_d(&netfs_n_wh_region);
		kfree(region);
	}
}

void netfs_put_dirty_region(struct netfs_i_context *ctx,
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
		if (!list_empty(&region->dirty_link)) {
			spin_lock(&ctx->lock);
			list_del_init(&region->dirty_link);
			spin_unlock(&ctx->lock);
		}
		netfs_return_write_credit(region);
		netfs_free_dirty_region(ctx, region);
	}
}

struct netfs_writeback *netfs_alloc_writeback(struct address_space *mapping,
					      bool is_dio)
{
	static atomic_t debug_ids;
	struct inode *inode = mapping->host;
	struct netfs_i_context *ctx = netfs_i_context(inode);
	struct netfs_writeback *wback;
	bool cached = !is_dio && netfs_is_cache_enabled(ctx);

	wback = kzalloc(sizeof(struct netfs_writeback), GFP_KERNEL);
	if (wback) {
		wback->mapping	= mapping;
		wback->inode	= inode;
		wback->netfs_ops	= ctx->ops;
		wback->debug_id	= atomic_inc_return(&debug_ids);
		if (cached)
			__set_bit(NETFS_WBACK_WRITE_TO_CACHE, &wback->flags);
		xa_init(&wback->buffer);
		INIT_WORK(&wback->work, netfs_writeback_worker);
		INIT_LIST_HEAD(&wback->proc_link);
		INIT_LIST_HEAD(&wback->regions);
		INIT_LIST_HEAD(&wback->writes);
		rwlock_init(&wback->regions_lock);
		refcount_set(&wback->usage, 1);
		atomic_set(&wback->outstanding, 1);

		ctx->ops->init_writeback(wback);

		netfs_stat(&netfs_n_wh_wback);
		trace_netfs_ref_wback(wback->debug_id, 1, netfs_wback_trace_new);
	}

	return wback;
}

void netfs_get_writeback(struct netfs_writeback *wback,
			 enum netfs_wback_trace what)
{
	int ref;

	__refcount_inc(&wback->usage, &ref);
	trace_netfs_ref_wback(wback->debug_id, ref + 1, what);
}

void netfs_free_writeback(struct work_struct *work)
{
	struct netfs_writeback *wback =
		container_of(work, struct netfs_writeback, work);
	struct netfs_dirty_region *region;
	struct netfs_i_context *ctx = netfs_i_context(wback->inode);
	struct folio *folio;
	pgoff_t index;

	if (wback->netfs_priv)
		wback->netfs_ops->cleanup(wback->mapping, wback->netfs_priv);
	trace_netfs_ref_wback(wback->debug_id, 0, netfs_wback_trace_free);
	write_lock(&wback->regions_lock);
	while ((region = list_first_entry_or_null(
			&wback->regions, struct netfs_dirty_region, flush_link))) {
		list_del_init(&region->flush_link);
		netfs_put_dirty_region(ctx, region, netfs_region_trace_put_wback);
	}
	write_unlock(&wback->regions_lock);
	xa_for_each(&wback->buffer, index, folio) {
		folio_put(folio);
	}
	xa_destroy(&wback->buffer);
	kfree(wback);
	netfs_stat_d(&netfs_n_wh_wback);
}

/**
 * netfs_put_writeback - Drop a reference on a writeback slice.
 * @wback: The writeback slice to drop
 * @was_async: True if being called in a non-sleeping context
 * @what: Reason code, to be displayed in trace line
 *
 * Drop a reference on a writeback slice and schedule it for destruction after
 * the last ref is gone.
 */
void netfs_put_writeback(struct netfs_writeback *wback,
			 bool was_async, enum netfs_wback_trace what)
{
	unsigned int debug_id;
	bool dead;
	int ref;

	if (wback) {
		debug_id = wback->debug_id;
		dead = __refcount_dec_and_test(&wback->usage, &ref);
		trace_netfs_ref_wback(debug_id, ref - 1, what);
		if (dead) {
			netfs_proc_del_writeback(wback);
			if (was_async) {
				wback->work.func = netfs_free_writeback;
				if (!queue_work(system_unbound_wq, &wback->work))
					BUG();
			} else {
				netfs_free_writeback(&wback->work);
			}
		}
	}
}
EXPORT_SYMBOL(netfs_put_writeback);

/**
 * netfs_put_write_request - Drop a ref to a write operation
 * @wreq: The request to drop a ref on
 * @was_async: True if being called in a non-sleeping context
 * @what: The trace tag to note.
 *
 * Drop a reference on a write operation and schedule it for destruction after
 * the last ref is gone.
 */
void netfs_put_write_request(struct netfs_write_request *wreq,
			     bool was_async, enum netfs_wback_trace what)
{
	struct netfs_writeback *wback = wreq->wback;
	unsigned int debug_id, debug_index;
	bool dead;
	int ref;

	debug_id = wback->debug_id;
	debug_index = wreq->debug_index;
	dead = __refcount_dec_and_test(&wreq->ref, &ref);
	trace_netfs_ref_wreq(debug_id, debug_index, ref - 1, what);

	if (dead) {
		trace_netfs_wreq(wreq, netfs_wreq_trace_free);
		if (wreq->cache_resources.ops)
			wreq->cache_resources.ops->end_operation(&wreq->cache_resources);
		if (wback->netfs_ops->free_write_request)
			wback->netfs_ops->free_write_request(wreq);
		netfs_put_writeback(wreq->wback, was_async, what);
		kfree(wreq);
	}
}
EXPORT_SYMBOL(netfs_put_write_request);

/**
 * netfs_create_write_request - Create a write operation.
 * @wback: The write request this is storing from.
 * @dest: The destination type
 * @start: Start of the region this write will modify
 * @len: Length of the modification
 * @worker: The worker function to handle the write(s)
 *
 * Allocate a write operation, set it up and add it to the list on a write
 * request.
 */
struct netfs_write_request *netfs_create_write_request(struct netfs_writeback *wback,
						       enum netfs_write_dest dest,
						       loff_t start, size_t len,
						       work_func_t worker)
{
	struct netfs_write_request *wreq;
	struct xarray *buffer;

	wreq = kzalloc(sizeof(struct netfs_write_request), GFP_KERNEL);
	if (wreq) {
		wreq->wback	= wback;
		wreq->dest	= dest;
		wreq->start	= start;
		wreq->len	= len;
		wreq->debug_index = wback->n_ops++;
		INIT_WORK(&wreq->work, worker);
		refcount_set(&wreq->ref, 2);

		switch (wreq->dest) {
		case NETFS_UPLOAD_TO_SERVER:
			netfs_stat(&netfs_n_wh_upload);
			break;
		case NETFS_WRITE_TO_CACHE:
			netfs_stat(&netfs_n_wh_write);
			break;
		default:
			BUG();
		}

		buffer = &wback->mapping->i_pages;
		if (test_bit(NETFS_WBACK_BUFFERED, &wback->flags))
			buffer = &wback->buffer;
		iov_iter_xarray(&wreq->source, WRITE, buffer,
				wback->coverage.start,
				wback->coverage.end - wback->coverage.start);

		trace_netfs_ref_wreq(wback->debug_id, wreq->debug_index,
				     refcount_read(&wreq->ref),
				     netfs_wback_trace_new);
		netfs_get_writeback(wback, netfs_wback_trace_get_for_wreq);
		atomic_inc(&wback->outstanding);
		list_add_tail(&wreq->wback_link, &wback->writes);
		trace_netfs_wreq(wreq, netfs_wreq_trace_new);
	}

	return wreq;
}
EXPORT_SYMBOL(netfs_create_write_request);

/**
 * netfs_get_write_request - Get a ref to a write request
 * @wreq: The request to get a ref on
 * @what: The trace tag to note.
 *
 * Get a reference on a write request.
 */
void netfs_get_write_request(struct netfs_write_request *wreq,
			     enum netfs_wback_trace what)
{
	int ref;

	__refcount_inc(&wreq->ref, &ref);
	trace_netfs_ref_wreq(wreq->wback->debug_id, wreq->debug_index, ref + 1, what);
}
EXPORT_SYMBOL(netfs_get_write_request);
