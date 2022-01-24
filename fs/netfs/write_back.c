// SPDX-License-Identifier: GPL-2.0-only
/* Network filesystem high-level write support.
 *
 * Copyright (C) 2021 Red Hat, Inc. All Rights Reserved.
 * Written by David Howells (dhowells@redhat.com)
 */

#include <linux/fs.h>
#include <linux/mm.h>
#include <linux/pagemap.h>
#include <linux/slab.h>
#include <linux/writeback.h>
#include "internal.h"

static void list_excise(struct list_head *first,
			struct list_head *last)
{
	struct list_head *prev = first->prev, *next = last->next;

	prev->next = next;
	next->prev = prev;
	first->prev = last;
	last->next = first;
}

/*
 * Fix up the dirty list upon completion of write.
 */
static void netfs_fix_up_dirty_list(struct netfs_writeback *wback)
{
	struct netfs_dirty_region *first, *last, *r;
	struct netfs_i_context *ctx = netfs_i_context(wback->inode);
	unsigned long long available_to;
	struct list_head *lower, *upper, *p;

	netfs_end_writeback(wback);

	first = list_first_entry(&wback->regions, struct netfs_dirty_region, flush_link);
	last = list_last_entry(&wback->regions, struct netfs_dirty_region, flush_link);

	spin_lock(&ctx->lock);
	if (wback->coverage.end > ctx->remote_i_size)
		ctx->remote_i_size = wback->coverage.end;

	/* Find the bounds of the region we're going to make available. */
	lower = &ctx->dirty_regions;
	r = first;
	list_for_each_entry_continue_reverse(r, &ctx->dirty_regions, dirty_link) {
		_debug("- back fix %x", r->debug_id);
		if (r->state >= NETFS_REGION_IS_DIRTY) {
			lower = &r->dirty_link;
			break;
		}
	}

	available_to = ULLONG_MAX;
	upper = &ctx->dirty_regions;
	r = last;
	list_for_each_entry_continue(r, &ctx->dirty_regions, dirty_link) {
		_debug("- forw fix %x", r->debug_id);
		if (r->state >= NETFS_REGION_IS_DIRTY) {
			available_to = r->dirty.start;
			upper = &r->dirty_link;
			break;
		}
	}

	/* Remove the sequence of regions we've just written from the dirty
	 * list then poke any waiting writer if they're now cleared to proceed.
	 */
	list_excise(&first->dirty_link, &last->dirty_link);

	for (p = lower->next; p != upper; p = p->next) {
		r = list_entry(p, struct netfs_dirty_region, dirty_link);
		if (r->will_modify_to <= available_to) {
			smp_store_release(&r->state, NETFS_REGION_IS_ACTIVE);
			trace_netfs_dirty(ctx, r, NULL, netfs_dirty_trace_activate);
			wake_up_var(&r->state);
		}
	}

	spin_unlock(&ctx->lock);

	list_for_each_entry(r, &wback->regions, flush_link) {
		smp_store_release(&r->state, NETFS_REGION_IS_COMPLETE);
		trace_netfs_dirty(ctx, r, NULL, netfs_dirty_trace_complete);
		netfs_put_dirty_region(ctx, r, netfs_region_trace_put_written);
	}
}

/*
 * Process a completed write request once all the component operations have
 * been completed.
 */
static void netfs_write_completed(struct netfs_writeback *wback, bool was_async)
{
	struct netfs_write_request *wreq;
	struct netfs_i_context *ctx = netfs_i_context(wback->inode);

	_enter("%x[]", wback->debug_id);

	list_for_each_entry(wreq, &wback->writes, wback_link) {
		if (!wreq->error)
			continue;
		switch (wreq->dest) {
		case NETFS_UPLOAD_TO_SERVER:
			/* Depending on the type of failure, this may prevent
			 * writeback completion unless we're in disconnected
			 * mode.
			 */
			if (!wback->error)
				wback->error = wreq->error;
			break;

		case NETFS_WRITE_TO_CACHE:
			/* Failure doesn't prevent writeback completion unless
			 * we're in disconnected mode.
			 */
			if (wreq->error != -ENOBUFS)
				ctx->ops->invalidate_cache(wback);
			break;

		default:
			WARN_ON_ONCE(1);
			if (!wback->error)
				wback->error = -EIO;
			return;
		}
	}

	if (wback->error)
		netfs_redirty_folios(wback);
	else
		netfs_fix_up_dirty_list(wback);

	while ((wreq = list_first_entry_or_null(&wback->writes,
						struct netfs_write_request, wback_link))) {
		list_del_init(&wreq->wback_link);
		netfs_put_write_request(wreq, false, netfs_wback_trace_put_cleanup);
	}

	netfs_put_writeback(wback, was_async, netfs_wback_trace_put_for_outstanding);
}

/*
 * Deal with the completion of writing the data to the cache.
 */
void netfs_write_request_completed(void *_op, ssize_t transferred_or_error,
				   bool was_async)
{
	struct netfs_write_request *wreq = _op;
	struct netfs_writeback *wback = wreq->wback;

	_enter("%x[%x] %zd", wback->debug_id, wreq->debug_index, transferred_or_error);

	if (IS_ERR_VALUE(transferred_or_error))
		wreq->error = transferred_or_error;
	switch (wreq->dest) {
	case NETFS_UPLOAD_TO_SERVER:
		if (wreq->error)
			netfs_stat(&netfs_n_wh_upload_failed);
		else
			netfs_stat(&netfs_n_wh_upload_done);
		break;
	case NETFS_WRITE_TO_CACHE:
		if (wreq->error)
			netfs_stat(&netfs_n_wh_write_failed);
		else
			netfs_stat(&netfs_n_wh_write_done);
		break;
	case NETFS_INVALID_WRITE:
		break;
	}

	trace_netfs_wreq(wreq, netfs_wreq_trace_complete);
	if (atomic_dec_and_test(&wback->outstanding))
		netfs_write_completed(wback, was_async);
}
EXPORT_SYMBOL(netfs_write_request_completed);

static void netfs_write_to_cache_op(struct netfs_write_request *wreq)
{
	struct netfs_cache_resources *cres = &wreq->cache_resources;

	trace_netfs_wreq(wreq, netfs_wreq_trace_submit);

	cres->ops->write(cres, wreq->start, &wreq->source,
			 netfs_write_request_completed, wreq);
}

static void netfs_write_to_cache_op_worker(struct work_struct *work)
{
	struct netfs_write_request *wreq =
		container_of(work, struct netfs_write_request, work);

	netfs_write_to_cache_op(wreq);
	netfs_put_write_request(wreq, false, netfs_wback_trace_put_wreq_work);
}

/**
 * netfs_queue_write_request - Queue a write request for attention
 * @wreq: The write request to be queued
 *
 * Queue the specified write request for processing by a worker thread.  We
 * pass the caller's ref on the request to the worker thread.
 */
void netfs_queue_write_request(struct netfs_write_request *wreq)
{
	if (!queue_work(system_unbound_wq, &wreq->work))
		netfs_put_write_request(wreq, false, netfs_wback_trace_put_wip);
}
EXPORT_SYMBOL(netfs_queue_write_request);

/*
 * Set up a op for writing to the cache.
 */
static void netfs_set_up_write_to_cache(struct netfs_writeback *wback)
{
	struct netfs_cache_resources *cres;
	struct netfs_write_request *wreq;
	struct fscache_cookie *cookie = netfs_i_cookie(wback->inode);
	loff_t start = wback->coverage.start;
	size_t len = wback->coverage.end - wback->coverage.start;
	int ret;

	if (!fscache_cookie_enabled(cookie)) {
		clear_bit(NETFS_WBACK_WRITE_TO_CACHE, &wback->flags);
		return;
	}

	wreq = netfs_create_write_request(wback, NETFS_WRITE_TO_CACHE, start, len,
					  netfs_write_to_cache_op_worker);
	if (!wreq)
		return;

	cres = &wreq->cache_resources;
	ret = fscache_begin_write_operation(cres, cookie);
	if (ret < 0) {
		netfs_write_request_completed(wreq, ret, false);
		netfs_put_write_request(wreq, false, netfs_wback_trace_put_discard);
		return;
	}

	ret = cres->ops->prepare_write(cres, &start, &len, i_size_read(wback->inode),
				       true);
	if (ret < 0) {
		netfs_write_request_completed(wreq, ret, false);
		netfs_put_write_request(wreq, false, netfs_wback_trace_put_discard);
		return;
	}

	netfs_queue_write_request(wreq);
}

/*
 * Process a write request.
 *
 * All the folios in the bounding box have had a ref taken on them and those
 * covering the dirty region have been marked as being written back and their
 * dirty bits provisionally cleared.
 */
static void netfs_writeback(struct netfs_writeback *wback)
{
	struct netfs_i_context *ctx = netfs_i_context(wback->inode);

	_enter("");

	/* ->outstanding > 0 carries a ref */
	netfs_get_writeback(wback, netfs_wback_trace_get_for_outstanding);

	if (test_bit(NETFS_ICTX_ENCRYPTED, &ctx->flags) &&
	    !netfs_wback_encrypt(wback))
		goto out;

	/* We need to write all of the region to the cache */
	if (test_bit(NETFS_WBACK_WRITE_TO_CACHE, &wback->flags))
		netfs_set_up_write_to_cache(wback);

	/* However, we don't necessarily write all of the region to the server.
	 * Caching of reads is being managed this way also.
	 */
	if (test_bit(NETFS_WBACK_UPLOAD_TO_SERVER, &wback->flags))
		ctx->ops->create_write_requests(wback);

out:
	if (atomic_dec_and_test(&wback->outstanding))
		netfs_write_completed(wback, false);
}

void netfs_writeback_worker(struct work_struct *work)
{
	struct netfs_writeback *wback =
		container_of(work, struct netfs_writeback, work);

	netfs_see_writeback(wback, netfs_wback_trace_see_work);
	netfs_writeback(wback);
	netfs_put_writeback(wback, false, netfs_wback_trace_put_work);
}

static void netfs_set_folios_writeback_work(struct work_struct *work)
{
	struct netfs_writeback *wback =
		container_of(work, struct netfs_writeback, work);

	netfs_see_writeback(wback, netfs_wback_trace_see_work);
	if (netfs_lock_folios(wback, true) == 0) {
		netfs_mark_folios_for_writeback(wback, wback->first, wback->last);
		netfs_unlock_folios(wback->mapping, wback->first, wback->last);
		wback->work.func = netfs_writeback_worker;
	}

	if (!queue_work(system_unbound_wq, &wback->work))
		BUG();
}

/*
 * Begin the process of writing out a chunk of data.
 *
 * We are given a write request that holds a series of dirty regions and
 * (partially) covers a sequence of folios, all of which are present.  We need
 * to perform the following steps:
 *
 * (1) Lock all the folios, unmark them as being dirty (if so marked and if not
 *     shared with out-of-scope dirty regions), mark them as undergoing
 *     writeback and unlock them again.
 *
 * (2) If encrypting, create an output buffer and encrypt each block of the
 *     data into it, otherwise the output buffer will point to the original
 *     folios.
 *
 * (3) If the data is to be cached, set up a write op for the entire output
 *     buffer to the cache, if the cache wants to accept it.
 *
 * (4) If the data is to be uploaded (ie. not merely cached):
 *
 *     (a) If the data is to be compressed, create a compression buffer and
 *         compress the data into it.
 *
 *     (b) For each destination we want to upload to, set up write ops to write
 *         to that destination.  We may need multiple writes if the data is not
 *         contiguous or the span exceeds wsize for a server.
 */
static int netfs_begin_write(struct netfs_writeback *wback, bool may_wait)
{
	int ret;

	trace_netfs_wback(wback);

	ret = netfs_lock_folios(wback, may_wait);
	if (ret < 0) {
		wback->work.func = netfs_set_folios_writeback_work;
		if (!queue_work(system_unbound_wq, &wback->work))
			BUG();
	} else {
		netfs_mark_folios_for_writeback(wback, wback->first, wback->last);
		netfs_unlock_folios(wback->mapping, wback->first, wback->last);
		if (!queue_work(system_unbound_wq, &wback->work))
			BUG();
	}
	_leave(" = %lu", wback->last - wback->first + 1);
	return wback->last - wback->first + 1;
}

/*
 * Split the front off of a dirty region.  We don't want to over-modify the
 * tail region if it's currently active.
 */
static struct netfs_dirty_region *netfs_split_off_front(
	struct netfs_i_context *ctx,
	struct netfs_dirty_region *region,
	struct netfs_dirty_region **spare,
	unsigned long long pos)
{
	struct netfs_dirty_region *front = *spare;

	*spare = NULL;
	*front = *region;
	front->dirty.end = pos;
	region->dirty.start = pos;
	front->debug_id = atomic_inc_return(&netfs_region_debug_ids);

	_debug("split D=%x from D=%x", front->debug_id, region->debug_id);

	refcount_set(&front->ref, 1);
	netfs_get_flush_group(front->group);
	spin_lock_init(&front->lock);
	// TODO: grab cache resources

	// TODO: need to split the bounding box?
	if (ctx->ops->split_dirty_region)
		ctx->ops->split_dirty_region(front);
	list_add_tail(&front->dirty_link, &region->dirty_link);
	list_add(&front->flush_link, &region->flush_link);
	trace_netfs_dirty(ctx, front, region, netfs_dirty_trace_split);
	netfs_proc_add_region(front);
	return front;
}

/*
 * Flush some of the dirty queue, transforming a part of a sequence of dirty
 * regions into a block we can flush.
 *
 * A number of things constrain us:
 *  - The region we write out should not be undergoing modification
 *  - We may need to expand or split the region for a number of reasons:
 *    - Filesystem storage block/object size
 *    - Filesystem RPC size (wsize)
 *    - Cache block size
 *    - Cache DIO block size
 *    - Crypto/compression block size
 *
 * The caller must hold ctx->lock.
 */
static long netfs_flush_dirty(struct netfs_i_context *ctx,
			      struct netfs_dirty_region *head,
			      struct netfs_dirty_region *spares[2],
			      struct netfs_range *requested,
			      struct netfs_writeback *wback,
			      struct netfs_dirty_region **_wait_for,
			      loff_t *_wait_to)
{
	struct netfs_dirty_region *tail = NULL, *r, *q;
	struct netfs_range block;
	unsigned long long dirty_start, dirty_to, active_from, limit, i_size;
	unsigned int wsize = ctx->wsize;
	unsigned int min_bsize = 1U << ctx->min_bshift;
	long ret;

	_enter("%llx-%llx", requested->start, requested->end);
	*_wait_for = NULL;

	/* Determine where we're going to start and the limits on where we
	 * might end.
	 */
	dirty_start = round_down(head->dirty.start, min_bsize);
	_debug("dirty D=%x start %llx", head->debug_id, dirty_start);

	if (ctx->obj_bshift) {
		/* Handle object storage - we limit the write to one object,
		 * but we round down the start if there's more dirty data that
		 * way.
		 */
		unsigned long long obj_start;
		unsigned long long obj_size  = 1ULL << ctx->obj_bshift;
		unsigned long long obj_end;

		obj_start = max(requested->start, dirty_start);
		obj_start = round_down(obj_start, obj_size);
		obj_end   = obj_start + obj_size;
		_debug("object %llx-%llx", obj_start, obj_end);

		block.start = max(dirty_start, obj_start);
		limit = min(requested->end, obj_end);
		if (limit - block.start > wsize) {
			_debug("size %llx", limit - block.start);
			block.start = max(block.start, requested->start);
			limit = min(requested->end,
				    block.start + round_down(wsize, min_bsize));
		}
		_debug("object %llx-%llx", block.start, limit);
	} else if (min_bsize > 1) {
		/* There's a block size (cache DIO, crypto). */
		block.start = max(dirty_start, requested->start);
		if (wsize > min_bsize) {
			/* A single write can encompass several blocks. */
			limit = block.start + round_down(wsize, min_bsize);
			limit = min(limit, requested->end);
		} else {
			/* The block will need several writes to send it. */
			limit = block.start + min_bsize;
		}
		_debug("block %llx-%llx", block.start, limit);
	} else {
		/* No blocking factors and no object division. */
		block.start = max(dirty_start, requested->start);
		limit = min(block.start + wsize, requested->end);
		_debug("plain %llx-%llx", block.start, limit);
	}

	i_size = i_size_read(netfs_inode(ctx));
	limit = min_t(unsigned long long, limit, i_size);
	_debug("limit %llx %llx", limit, i_size);

	/* Determine the subset of dirty regions that are going to contribute. */
	r = head;
	list_for_each_entry_from(r, &ctx->dirty_regions, dirty_link) {
		_debug("- maybe D=%x s=%llx", r->debug_id, r->dirty.start);
		if (r->dirty.start >= limit)
			break;

		if (min_bsize <= 1 && tail) {
			/* If we don't need to use a whole block, break at any
			 * discontiguity so that we don't include bridging
			 * blocks in our writeback.
			 */
			if (r->dirty.start != tail->dirty.end) {
				kdebug(" - discontig");
				break;
			}
		}

		switch (READ_ONCE(r->state)) {
		case NETFS_REGION_IS_DIRTY:
			_debug("- dirty");
			tail = r;
			continue;
		case NETFS_REGION_IS_FLUSHING:
			kdebug("- flushing");
			limit = round_down(r->dirty.start, min_bsize);
			goto determined_tail;
		case NETFS_REGION_IS_ACTIVE:
			/* We can break off part of a region undergoing active
			 * modification, but assume, for now, that we don't
			 * want to include anything that will change under us
			 * or that's only partially uptodate - especially if
			 * we're going to be encrypting or compressing from it.
			 */
			dirty_to = READ_ONCE(r->dirty.end);
			active_from = round_down(dirty_to, min_bsize);
			kdebug("active D=%x from %llx", r->debug_id, active_from);
			if (active_from > limit) {
				kdebug(" - >limit");
				tail = r;
				goto determined_tail;
			}

			limit = active_from;
			if (r->dirty.start < limit) {
				kdebug(" - reduce limit");
				tail = r;
				goto determined_tail;
			}

			if (limit == block.start || r == head)
				goto wait_for_active_region;

			if (limit == r->dirty.start) {
				kdebug("- active contig");
				goto determined_tail;
			}

			/* We may need to rewind the subset we're collecting. */
			q = r;
			list_for_each_entry_continue_reverse(q, &ctx->dirty_regions,
							     dirty_link) {
				kdebug(" - rewind D=%x", q->debug_id);
				tail = q;
				if (q->dirty.start < limit)
					goto determined_tail;
				if (q == head) {
					kdebug("over rewound");
					return -EIO;
				}
			}

			*_wait_for = r;
			goto wait_for_active_region;
		}
	}

determined_tail:
	if (!tail) {
		kleave(" = -EAGAIN [no tail]");
		return -EAGAIN;
	}
	dirty_to = round_up(tail->dirty.end, min_bsize);
	_debug("dto %llx", dirty_to);
	block.end = min(dirty_to, limit);
	_debug("block %llx-%llx", block.start, block.end);

	/* If the leading and/or trailing edges of the selected regions overlap
	 * the ends of the block, we will need to split those blocks.
	 */
	if ((dirty_start < block.start && !spares[0]) ||
	    (tail->dirty.end > block.end && !spares[1])) {
		_leave(" = -ENOBUFS [need spares]");
		return -ENOBUFS;
	}

	if (dirty_start < block.start) {
		_debug("eject front");
		netfs_split_off_front(ctx, head, &spares[0], block.start);
	}

	if (tail->dirty.end > block.end) {
		_debug("eject back");
		r = netfs_split_off_front(ctx, tail, &spares[1], block.end);
		if (head == tail)
			head = r;
		tail = r;
	}

	/* Set up the write request */
	_debug("wback W=%x", wback->debug_id);
	wback->coverage = block;
	wback->first  =  block.start    / PAGE_SIZE;
	wback->last   = (block.end - 1) / PAGE_SIZE;

	/* Flip the state of all the regions and add them to the request */
	r = head;
	list_for_each_entry_from(r, &ctx->dirty_regions, dirty_link) {
		if (r->type != NETFS_REGION_CACHE_COPY)
			__set_bit(NETFS_WBACK_UPLOAD_TO_SERVER, &wback->flags);
		set_bit(NETFS_REGION_FLUSH_Q, &r->flags);
		smp_store_release(&r->state, NETFS_REGION_IS_FLUSHING);
		trace_netfs_dirty(ctx, r, NULL, netfs_dirty_trace_flushing);
		wake_up_var(&r->state);
		netfs_get_dirty_region(ctx, r, netfs_region_trace_get_wback);
		netfs_deduct_write_credit(r, r->dirty.end - r->dirty.start);
		list_move_tail(&r->flush_link, &wback->regions);
		if (r == tail)
			break;
	}

	netfs_proc_add_writeback(wback);

	requested->start = block.end;
	ret = wback->last - wback->first + 1;
	_leave(" = %ld", ret);
	return ret;

wait_for_active_region:
	/* We have to wait for an active region to progress */
	_debug("- wait for active %x", r->debug_id);
	set_bit(NETFS_REGION_FLUSH_Q, &r->flags);
	*_wait_for = r;
	*_wait_to = dirty_to;
	return -EAGAIN;
}

/*
 * Flush a range of addresses.
 */
static int netfs_flush_range(struct address_space *mapping,
			     struct writeback_control *wbc,
			     struct netfs_range *requested)
{
	struct netfs_writeback *wback = NULL;
	struct netfs_dirty_region *spares[2] = {}, *head, *r, *wait_for;
	struct netfs_i_context *ctx = netfs_i_context(mapping->host);
	unsigned int min_bsize = 1U << ctx->min_bshift;
	loff_t wait_to;
	int ret;

	_enter("%llx-%llx", requested->start, requested->end);

	ret = netfs_sanity_check_ictx(mapping);
	if (ret < 0)
		return ret;

	/* Round the requested region out to the minimum block size (eg. for
	 * crypto purposes).
	 */
	requested->start = round_down(requested->start, min_bsize);
	requested->end   = round_up  (requested->end,   min_bsize);

retry:
	ret = netfs_wait_for_credit(wbc);
	if (ret < 0)
		goto out_unlocked;

	if (!wback) {
		ret = -ENOMEM;
		wback = netfs_alloc_writeback(mapping, false);
		if (!wback)
			goto out_unlocked;
	}

	spin_lock(&ctx->lock);

	/* Find the first dirty region that overlaps the requested flush region */
	ret = 0;
	head = NULL;
	list_for_each_entry(r, &ctx->dirty_regions, dirty_link) {
		//kdebug("query D=%x", r->debug_id);
		if (r->dirty.end <= requested->start ||
		    r->dirty.end == r->dirty.start)
			continue;
		if (READ_ONCE(r->state) == NETFS_REGION_IS_FLUSHING)
			continue;
		if (r->dirty.start >= requested->end)
			goto out;
		head = r;
		break;
	}

	if (!head || head->dirty.start >= requested->end)
		goto out;

	ret = netfs_flush_dirty(ctx, head, spares, requested, wback, &wait_for, &wait_to);
	if (ret == -EAGAIN && wait_for)
		goto wait_for_active_region;
	spin_unlock(&ctx->lock);

	switch (ret) {
	case -ENOBUFS:
		goto need_spares;
	case -EAGAIN:
		//goto retry;
		goto out_unlocked;
	default:
		goto out_unlocked;
	case 1 ... INT_MAX:
		wbc->nr_to_write -= ret;
		ret = 0;
		break;
	}

	/* Finish preparing the write request. */
	//netfs_get_writeback(wback, netfs_wback_trace_get_debug);
	ret = netfs_begin_write(wback, wbc->sync_mode != WB_SYNC_NONE);

	wback = NULL;

	/* TODO: Flush more pieces */
	if (wbc->nr_to_write <= 0)
		goto out_unlocked;
	if (requested->start < requested->end)
		goto retry;
	goto out_unlocked;

out:
	spin_unlock(&ctx->lock);
out_unlocked:
	netfs_free_dirty_region(ctx, spares[0]);
	netfs_free_dirty_region(ctx, spares[1]);
	netfs_put_writeback(wback, false, netfs_wback_trace_put_discard);
	return ret;

wait_for_active_region:
	if (wbc->sync_mode == WB_SYNC_NONE) {
		spin_unlock(&ctx->lock);
		ret = -EBUSY;
		goto out_unlocked;
	}

	if (!spares[0] || !spares[1]) {
		spin_unlock(&ctx->lock);
		ret = -ENOBUFS;
		goto out_unlocked;
	}

	netfs_get_dirty_region(ctx, r, netfs_region_trace_get_wait_active);
	spin_unlock(&ctx->lock);

	wait_var_event(&r->state, (READ_ONCE(r->state) != NETFS_REGION_IS_ACTIVE ||
				   READ_ONCE(r->dirty.end) != wait_to));
	netfs_put_dirty_region(ctx, r, netfs_region_trace_put_wait_active);
need_spares:
	ret = -ENOMEM;
	if (!spares[0]) {
		spares[0] = netfs_alloc_dirty_region();
		if (!spares[0])
			goto out_unlocked;
	}
	if (!spares[1]) {
		spares[1] = netfs_alloc_dirty_region();
		if (!spares[1])
			goto out_unlocked;
	}
	goto retry;
}

/**
 * netfs_writepages - Initiate writeback to the server and cache
 * @mapping: The pagecache to write from
 * @wbc: Hints from the VM as to what to write
 *
 * This is a helper intended to be called directly from a network filesystem's
 * address space operations table to perform writeback to the server and the
 * cache.
 *
 * We have to be careful as we can end up racing with setattr() truncating the
 * pagecache since the caller doesn't take a lock here to prevent it.
 */
int netfs_writepages(struct address_space *mapping,
		     struct writeback_control *wbc)
{
	struct netfs_range range;
	unsigned long nr_to_write = wbc->nr_to_write;
	int ret;

	_enter("%lx,%llx-%llx,%u,%c%c%c%c,%u,%u",
	       wbc->nr_to_write,
	       wbc->range_start, wbc->range_end,
	       wbc->sync_mode,
	       wbc->for_kupdate		? 'k' : '-',
	       wbc->for_background	? 'b' : '-',
	       wbc->for_reclaim		? 'r' : '-',
	       wbc->for_sync		? 's' : '-',
	       wbc->tagged_writepages,
	       wbc->range_cyclic);

	//dump_stack();

	if (wbc->range_cyclic) {
		range.start = mapping->writeback_index * PAGE_SIZE;
		range.end   = (unsigned long long)LLONG_MAX + 1;
		ret = netfs_flush_range(mapping, wbc, &range);
		if (ret == 0 && range.start > 0 && wbc->nr_to_write > 0) {
			range.start = 0;
			range.end   = mapping->writeback_index * PAGE_SIZE;
			ret = netfs_flush_range(mapping, wbc, &range);
		}
		mapping->writeback_index = range.start / PAGE_SIZE;
	} else {
		range.start = wbc->range_start;
		range.end   = wbc->range_end + 1;
		ret = netfs_flush_range(mapping, wbc, &range);
	}

	_leave(" = %d [%lx/%lx]", ret, wbc->nr_to_write, nr_to_write);
	if (ret == -EBUSY)
		ret = 0;
	return ret;
}
EXPORT_SYMBOL(netfs_writepages);
