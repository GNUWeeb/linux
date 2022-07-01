// SPDX-License-Identifier: GPL-2.0-only
/* Network filesystem write flushing
 *
 * Copyright (C) 2022 Red Hat, Inc. All Rights Reserved.
 * Written by David Howells (dhowells@redhat.com)
 */

#include <linux/pagevec.h>
#include "internal.h"

/* Round up the last page of a region where the range is inclusive.  */
#define round_up_incl(x, to) (round_up((x) + 1, (to)) - 1)

/**
 * list_excise - Extract the specified sublist onto a new head
 * @first: The first element in the sublist
 * @last: The last element in the sublist
 * @onto: The head to attach the extracted sublist to.
 *
 * Move the specified sublist from its current list onto a new one.  The new
 * list is assumed to be empty.
 */
static inline void list_excise(struct list_head *first,
			       struct list_head *last,
			       struct list_head *onto)
{
	struct list_head *before = first->prev, *after = last->next;

	BUG_ON(!list_empty(onto));
	BUG_ON(list_empty(first));
	BUG_ON(list_empty(last));
	onto->next = first;
	onto->prev = last;
	before->next = after;
	after->prev = before;
	first->prev = onto;
	last->next = onto;
}

/*
 * Remove the writeback I/O request from the for conflict detection list.
 */
static void netfs_remove_wback_from_list(struct netfs_inode *ctx,
					 struct netfs_io_request *wreq)
{
	spin_lock(&ctx->dirty_lock);
	list_del_init(&wreq->wb_link);
	spin_unlock(&ctx->dirty_lock);
}

/*
 * Find the first region inside the range.
 */
static struct netfs_dirty_region *netfs_scan_for_region(struct netfs_inode *ctx,
							pgoff_t first, pgoff_t last)
{
	struct netfs_dirty_region *r;

	list_for_each_entry(r, &ctx->dirty_regions, dirty_link) {
		if (r->first > last)
			return NULL; /* Beyond */
		if (r->last >= first)
			return r; /* Overlaps */
	}
	return NULL;
}

/*
 * Unmark for writeback the pages attached to the writeback record.  Pages from
 * the pagecache containing the raw data are attached to wreq->buffer and
 * marked with NETFS_BUF_PAGECACHE_MARK.  There may be other pages interspersed
 * that we shouldn't change (for instance the ZERO_PAGE).
 */
static void netfs_writeback_end(struct netfs_io_request *wreq)
{
	struct folio *folio;
	unsigned long index;

	trace_netfs_rreq(wreq, netfs_rreq_trace_unmark);
	xa_for_each_range(&wreq->buffer, index, folio, wreq->first, wreq->last) {
		if (xa_get_mark(&wreq->buffer, index, NETFS_BUF_PAGECACHE_MARK))
			folio_end_writeback(folio);
	}
}

/*
 * Fix up the list of dirty regions upon completion of write.
 */
static void netfs_clean_dirty_range(struct netfs_io_request *wreq)
{
	struct netfs_inode *ctx = netfs_inode(wreq->inode);
	LIST_HEAD(discards);

	_enter("");

	netfs_writeback_end(wreq);

	//spin_lock(&ctx->dirty_lock);
	//spin_unlock(&ctx->dirty_lock);

	netfs_discard_regions(ctx, &discards, netfs_region_trace_put_written);
}

/*
 * Redirty the folios associated with a dirty range.
 */
static void netfs_redirty_folios(struct netfs_io_request *wreq,
				 pgoff_t first, pgoff_t last)
{
	struct folio *folio;
	unsigned long index;

	xa_for_each_range(&wreq->buffer, index, folio, first, last) {
		if (xa_get_mark(&wreq->buffer, index, NETFS_BUF_PAGECACHE_MARK)) {
			filemap_dirty_folio(folio->mapping, folio);
			folio_account_redirty(folio);
			folio_end_writeback(folio);
		}
	}
}

/*
 * The write failed to some extent.  We need to work out which bits we managed
 * to do - for instance, we might have managed to write stuff to the cache, but
 * not upload to the server.
 */
static void netfs_redirty_range(struct netfs_io_request *wreq)
{
	struct netfs_io_chain *chain;
	struct netfs_dirty_region *d, *d2, *w, *w2, *tmp;
	struct netfs_inode *ctx = netfs_inode(wreq->inode);
	unsigned int c;
	bool upload_failed = false;
	LIST_HEAD(discards);

	trace_netfs_rreq(wreq, netfs_rreq_trace_redirty);

	if (list_empty(&wreq->regions))
		return netfs_clean_dirty_range(wreq);

	/* If an upload failed, we need to ask the filesystem how it wants to
	 * handle things.  It has two choices: redirty everything or leave
	 * everything clean.
	 */
	for (c = 0; c < wreq->nr_chains; c++) {
		chain = &wreq->chains[c];
		if (chain->source != NETFS_WRITE_TO_CACHE && chain->error)
			upload_failed = true;
	}

	if (!upload_failed ||
	    !wreq->netfs_ops->redirty_on_failure ||
	    !wreq->netfs_ops->redirty_on_failure(wreq))
		return netfs_clean_dirty_range(wreq);

	/* First of all, we step through the list of regions that were to be
	 * written back and see if we can discard/shorten anything that got
	 * partially stored.
	 *
	 * Don't retry write failures to the cache.  If the cache got a fatal
	 * error, it will have gone offline and retrying is pointless; if it
	 * ran out of space, it probably won't be able to supply us with space
	 * on the second attempt.
	 */
	list_for_each_entry_safe(w, tmp, &wreq->regions, dirty_link) {
		if (w->type == NETFS_COPY_TO_CACHE) {
			list_del_init(&w->dirty_link);
			netfs_put_dirty_region(ctx, w, netfs_region_trace_put_clear);
		}
	}

	if (list_empty(&wreq->regions))
		return;

	/* Mark the pages dirty again. */
	list_for_each_entry(w, &wreq->regions, dirty_link) {
		netfs_redirty_folios(wreq, w->first, w->last);
	}

	/* Step through the the uncompleted regions and reintegrate them into
	 * the dirty list.
	 */
	spin_lock(&ctx->dirty_lock);

	w = list_first_entry(&wreq->regions, struct netfs_dirty_region, dirty_link);
	d = list_first_entry_or_null(&ctx->dirty_regions,
				     struct netfs_dirty_region, dirty_link);

	while (d && w) {
		w2 = netfs_rreq_next_region(wreq, w);

		/* Dirty region before writeback region and not touching. */
		if (d->last < w->first && d->last != w->first - 1) {
			d = netfs_next_region(ctx, d);
			if (!d)
				break;
			continue;
		}

		/* Dirty region overlaps with writeback region.  If two regions
		 * overlap, they *must* be compatible, otherwise the new
		 * changes would not get applied until this request completes.
		 */
		if (d->first <= w->last) {
			if (d->last == w->first - 1 &&
			    !netfs_are_regions_mergeable(ctx, d, d2)) {
				d = netfs_next_region(ctx, d);
				if (!d)
					break;
				continue;
			}

			d->first = min(d->first, w->first);
			d->last  = max(d->last, w->last);
			d->from  = min(d->from, w->from);
			d->to    = max(d->to, w->to);
			trace_netfs_dirty(ctx, d, w, netfs_dirty_trace_redirty_merge);

			while ((d2 = netfs_next_region(ctx, d)) &&
			       d->last >= d2->first - 1 &&
			       netfs_are_regions_mergeable(ctx, d, d2)
			       ) {
				d->last = d2->last;
				d->to   = d2->to;
				list_move(&d2->dirty_link, &discards);
				trace_netfs_dirty(ctx, d, d2, netfs_dirty_trace_bridged);
			}

			list_move_tail(&w->dirty_link, &discards);
			w = w2;
			continue;
		}

		/* Dirty region after writeback region and touching. */
		if (d->first == w->last + 1) {
			if (netfs_are_regions_mergeable(ctx, d, d2)) {
				d->first = min(d->first, w->first);
				d->from  = min(d->from, w->from);
				trace_netfs_dirty(ctx, d, w, netfs_dirty_trace_redirty_merge);
				list_move_tail(&w->dirty_link, &discards);
				w = w2;
				continue;
			}
		}

		/* Dirty region after writeback and not touching. */
		list_move_tail(&w->dirty_link, &d->dirty_link);
		trace_netfs_dirty(ctx, w, NULL, netfs_dirty_trace_redirty_insert);
		w = w2;
	}

	if (w && !d) {
		list_for_each_entry_from(w, &wreq->regions, dirty_link) {
			trace_netfs_dirty(ctx, w, NULL, netfs_dirty_trace_redirty_insert);
		}
		list_splice_tail_init(&wreq->regions, &ctx->dirty_regions);
	}

	spin_unlock(&ctx->dirty_lock);

	while ((d = list_first_entry_or_null(&discards,
					     struct netfs_dirty_region, dirty_link))) {
		list_del_init(&d->dirty_link);
		netfs_put_dirty_region(ctx, d, netfs_region_trace_put_merged);
	}
}

static void netfs_cleanup_buffered_write(struct netfs_io_request *wreq)
{
	struct netfs_inode *ctx = netfs_inode(wreq->inode);

	if (wreq->error)
		netfs_redirty_range(wreq);
	else
		netfs_clean_dirty_range(wreq);
	netfs_remove_wback_from_list(ctx, wreq);
}

/*
 * See if there are any conflicting dirty regions in the specified range.  The
 * caller must hold the dirty_regions lock or the RCU read lock.
 */
static bool netfs_check_for_conflicting_regions(struct netfs_inode *ctx,
						struct file *file,
						loff_t start, size_t len)
{
	struct netfs_dirty_region *r;
	unsigned long long from = start;
	unsigned long long to = from + len;
	size_t min_bsize = 1UL << ctx->min_bshift;
	pgoff_t first = round_down(from, min_bsize) / PAGE_SIZE;
	pgoff_t last  = round_up(from + len - 1, min_bsize) / PAGE_SIZE;

	_debug("check %lx-%lx", first, last);

	/* See if there are any dirty regions that need flushing first. */
	list_for_each_entry(r, &ctx->dirty_regions, dirty_link) {
		if (r->last < first)
			continue;
		if (r->first > last)
			break;
		_debug("confl? [D=%x] %lx-%lx", r->debug_id, r->first, r->last);

		if (r->group != list_first_entry_or_null(&ctx->flush_groups,
							 struct netfs_flush_group,
							 group_link))
			goto conflict;
		if (ctx->ops->is_write_compatible &&
		    !ctx->ops->is_write_compatible(ctx, file, r))
			goto conflict;
		if (from >= ctx->zero_point || r->from >= ctx->zero_point)
			continue;
		if (from > r->to || to < r->from)
			goto conflict;
	}

	return false;
conflict:
	trace_netfs_dirty(ctx, r, NULL, netfs_dirty_trace_flush_conflict);
	return true;
}

int netfs_flush_conflicting_writes(struct netfs_inode *ctx,
				   struct file *file,
				   loff_t start, size_t len,
				   struct folio *unlock_this)
{
	bool check;

	spin_lock(&ctx->dirty_lock);
	check = netfs_check_for_conflicting_regions(ctx, file, start, len);
	spin_unlock(&ctx->dirty_lock);

	if (check) {
		if (unlock_this)
			folio_unlock(unlock_this);
		pr_warn("NEED TO FLUSH CONFLICTING REGIONS\n");
		return -EAGAIN;
	}
	return 0;
}

/*
 * Split the front off of the dirty region at the specified point, where the
 * point indicates the last page in the front region.  A pointer to the new
 * front part is returned.
 */
static struct netfs_dirty_region *netfs_alloc_split_off_front(
	struct netfs_inode *ctx,
	struct netfs_dirty_region *back,
	pgoff_t front_last,
	enum netfs_dirty_trace why)
{
	struct netfs_dirty_region *front;

	front = netfs_alloc_dirty_region(GFP_ATOMIC);
	if (!front) {
		pr_err("OOM\n");
		BUG();
	}

	netfs_split_off_front(ctx, front, back, front_last, why);
	return front;
}

void netfs_check_dirty_list(char c, const struct list_head *list,
			    const struct netfs_dirty_region *star)
{
	const struct netfs_dirty_region *r, *q;
	const struct list_head *p;
	int i = 0;

	if (c == 'W')
		goto failed;
	return;

	if (list->next == list) {
		BUG_ON(list->prev != list);
		return;
	}
	BUG_ON(list->prev == list);

	list_for_each(p, list) {
		r = list_entry(p, struct netfs_dirty_region, dirty_link);
		if (p->prev->next != p ||
		    p->next->prev != p ||
		    r->last < r->first ||
		    r->from > r->to ||
		    r->from < r->first * PAGE_SIZE ||
		    r->to > (r->last + 1) * PAGE_SIZE)
			goto failed;
		if (!list_is_first(p, list)) {
			q = list_prev_entry(r, dirty_link);
			if (q->last >= r->first)
				goto failed;
		}
	}

	return;

failed:
	kdebug("");
	list_for_each(p, list) {
		r = list_entry(p, struct netfs_dirty_region, dirty_link);
		kdebug("CHECK-%c[%x]%c D=%03x %04lx-%04lx %06llx-%06llx",
		       c, i++, r == star ? '*' : ' ',
		       r->debug_id, r->first, r->last, r->from, r->to);
		BUG_ON(p->prev->next != p);
		BUG_ON(p->next->prev != p);
		BUG_ON(r->last < r->first);
		BUG_ON(r->from > r->to);
		BUG_ON(r->from < r->first * PAGE_SIZE);
		BUG_ON(r->to > (r->last + 1) * PAGE_SIZE);
		if (!list_is_first(p, list)) {
			q = list_prev_entry(r, dirty_link);
			BUG_ON(q->last >= r->first);
		}
	}
}

/*
 * Split the dirty regions covering a writeback request as necessary and attach
 * them to the request.
 */
static void netfs_split_out_regions(struct netfs_io_request *wreq,
				    struct netfs_inode *ctx,
				    struct netfs_dirty_region *region)
{
	struct netfs_dirty_region *front = region, *p;

	spin_lock(&ctx->dirty_lock);

	while (region->absorbed_by)
		region = region->absorbed_by;

	netfs_check_dirty_list('S', &ctx->dirty_regions, region);

	if (wreq->first != region->first) {
		BUG_ON(wreq->first < region->first);
		BUG_ON(wreq->first == 0);
		netfs_alloc_split_off_front(ctx, region, wreq->first - 1,
					    netfs_dirty_trace_split_off_front);
		netfs_check_dirty_list('F', &ctx->dirty_regions, region);
	}

	if (wreq->last != region->last) {
		list_for_each_entry_from(region, &ctx->dirty_regions, dirty_link) {
			if (wreq->last == region->last)
				goto excise;
			if (wreq->last < region->last) {
				region = netfs_alloc_split_off_front(
					ctx, region, wreq->last,
					netfs_dirty_trace_split_off_back);
				if (region->dirty_link.next == &front->dirty_link)
					front = region;
				netfs_check_dirty_list('T', &ctx->dirty_regions, region);
				goto excise;
			}
		}

		region = list_last_entry(&ctx->dirty_regions,
					 struct netfs_dirty_region, dirty_link);
	}

excise:
	list_excise(&front->dirty_link, &region->dirty_link, &wreq->regions);
	netfs_check_dirty_list('X', &ctx->dirty_regions, region);
	netfs_check_dirty_list('W', &wreq->regions, region);
	if (ctx->dirty_regions.next == &ctx->dirty_regions)
		BUG_ON(ctx->dirty_regions.prev != &ctx->dirty_regions);
	else
		BUG_ON(ctx->dirty_regions.prev == &ctx->dirty_regions);
	list_for_each_entry_from(region, &wreq->regions, dirty_link) {
		list_del_init(&region->flush_link);
	}
	spin_unlock(&ctx->dirty_lock);

	list_for_each_entry(p, &wreq->regions, dirty_link) {
		_debug("WRITE D=%x %lx-%lx t=%x",
		       p->debug_id, p->first, p->last, p->type);
		if (p->type == NETFS_MODIFIED_REGION)
			__set_bit(NETFS_RREQ_UPLOAD_TO_SERVER, &wreq->flags);
	}

	if (wreq->cache_resources.ops)
		__set_bit(NETFS_RREQ_WRITE_TO_CACHE, &wreq->flags);
}

/*
 * Stick the writeback I/O request on the list for conflict detection.
 */
static void netfs_add_wback_to_list(struct netfs_inode *ctx,
				    struct netfs_io_request *wreq)
{
	struct netfs_io_request *w;
	struct list_head *p;

	list_for_each(p, &ctx->writebacks) {
		w = list_entry(p, struct netfs_io_request, wb_link);
		if (w->last < wreq->first)
			continue;
		break;
	}

	list_add_tail(&wreq->wb_link, p);
}

/*
 * Find if there's a region undergoing writeback in the range of pages.
 */
static struct netfs_io_request *netfs_find_writeback(struct netfs_inode *ctx,
						     pgoff_t first, pgoff_t last)
{
	struct netfs_io_request *wreq;

	list_for_each_entry(wreq, &ctx->writebacks, wb_link) {
		kdebug("find? R=%08x", wreq->debug_id);
		if (wreq->last < first)
			continue;
		if (wreq->first > last)
			return NULL;
		return wreq;
	}
	return NULL;
}

static void netfs_wait_for_writeback(struct netfs_io_request *wreq,
				     struct netfs_io_request *conflict)
{
	kdebug("WAIT FOR WRITEBACK R=%08x for R=%08x",
	       wreq->debug_id, conflict->debug_id);
	trace_netfs_rreq(conflict, netfs_rreq_trace_wait_conflict);
	wait_on_bit(&conflict->flags, NETFS_RREQ_IN_PROGRESS, TASK_UNINTERRUPTIBLE);
}

/*
 * Advance to the next dirty region covering the writeback that we're
 * extending.
 */
static bool netfs_extend_to_next_region(struct netfs_inode *ctx,
					struct netfs_dirty_region *start_region,
					struct netfs_dirty_region **_region,
					pgoff_t index)
{
	struct netfs_dirty_region *region = *_region, *old = NULL;

	spin_lock(&ctx->dirty_lock);

	/* The dirty list may have been altered whilst we were working, so
	 * allow for the region we were focussing on to have been absorbed,
	 * split and/or superseded.
	 */
	while (region->absorbed_by)
		region = region->absorbed_by;

	if (index <= region->last)
		goto cont;

	while (index < region->first)
		region = netfs_next_region(ctx, region);
	if (index <= region->last)
		goto cont;

	region = netfs_next_region(ctx, region);
	if (!region)
		goto stop;

	if (region->group != (*_region)->group)
		goto stop;

	// TODO: Allow discontiguity
	if (region->first > index)
		goto stop;

cont:
	if (region != *_region) {
		netfs_get_dirty_region(ctx, region, netfs_region_trace_get_wback);
		old = *_region;
		*_region = region;
	}

	spin_unlock(&ctx->dirty_lock);
	if (old && old != start_region)
		netfs_put_dirty_region(ctx, old, netfs_region_trace_put_wback);
	return true;

stop:
	spin_unlock(&ctx->dirty_lock);
	return false;
}

/*
 * Extend the span to be written back to include subsequent contiguously dirty
 * pages if possible, but don't sleep while doing so.
 *
 * If this page holds new content, then we can include filler zeros in the
 * writeback.
 */
static void netfs_extend_writeback(struct netfs_io_request *wreq,
				   struct writeback_control *wbc,
				   struct netfs_inode *ctx,
				   struct netfs_dirty_region *start_region)
{
	struct netfs_dirty_region *region = start_region;
	struct folio_batch fbatch;
	struct folio *folio;
	unsigned int i;
	pgoff_t index = wreq->last + 1, stop_mask, stop_at, max_pages;
	ssize_t max_size;
	size_t align, hard_align;
	bool stop = true, dirty;
	int ret;

	XA_STATE(xas, &wreq->mapping->i_pages, index);

	_enter("%lx", index);

	/* We have a number of criteria by which we can decide where to stop
	 * extension of this writeback:
	 *
	 *  1) The maximum I/O size (but wbacks can be subdivided)
	 *  2) Boundaries within the filesystem (eg. ceph object size)
	 *  3) Local boundaries (cache granules, VM radix node sizes)
	 *  4) Content crypto/compression boundaries
	 */
	hard_align = PAGE_SIZE;
	if (ctx->min_bshift || ctx->crypto_bshift)
		hard_align = max(hard_align,
				 1UL << max(ctx->min_bshift, ctx->crypto_bshift));
	if (ctx->cache_order)
		hard_align = max(hard_align, PAGE_SIZE << ctx->cache_order);

	align = min(hard_align, XA_CHUNK_SIZE * PAGE_SIZE);
	if (wreq->alignment > align)
		align = wreq->alignment;

	stop_mask = (align - 1) / PAGE_SIZE;

	max_size = XA_CHUNK_SIZE * PAGE_SIZE;
	if (wreq->wsize > max_size)
		max_size = roundup_pow_of_two(wreq->wsize);

	_debug("LIMITS al=%zx ha=%zx mx=%zx", align, hard_align, max_size);

	max_pages = max_size / PAGE_SIZE;
	max_pages &= ~stop_mask;
	_debug("MAX_PAGES %lx %lx", max_pages, stop_mask);
	if (wreq->last - wreq->first + 1 >= max_pages) {
		_leave(" [already hit wsize %lx %lx]",
		       wreq->last - wreq->first + 1, max_pages);
		return;
	}

	stop_at = wreq->first + max_pages;
	if (stop_at < wreq->first)
		stop_at = ULONG_MAX;
	else
		stop_at = round_down(stop_at, align / PAGE_SIZE);
	_debug("STOP_AT %lx (%lx %lx %lx)", stop_at, wreq->first, max_pages, align / PAGE_SIZE);

	if (index >= stop_at || wbc->nr_to_write <= 0 || wreq->len > max_size) {
		_leave(" [prestop]");
		return;
	}

	do {
		/* Firstly, we gather up a batch of contiguous dirty folios
		 * under the RCU read lock - but we can't clear the dirty flags
		 * there if any of those folios are mapped.
		 */
		folio_batch_init(&fbatch);

		if (index > region->last &&
		    !netfs_extend_to_next_region(ctx, start_region, &region, index)) {
			kdebug("stop!");
			goto stop;
		}

		kdebug("extend D=%x %lx %lx", region->debug_id, index, xas.xa_index);
		rcu_read_lock();
		xas_for_each(&xas, folio, ULONG_MAX) {
			stop = true;
			if (xas_retry(&xas, folio))
				continue;
			if (xa_is_value(folio))
				break;
			if (folio_index(folio) != index)
				break;

			if (!folio_try_get_rcu(folio)) {
				xas_reset(&xas);
				continue;
			}

			/* Has the folio moved or been split? */
			if (unlikely(folio != xas_reload(&xas))) {
				folio_put(folio);
				break;
			}

			if (!folio_trylock(folio)) {
				folio_put(folio);
				break;
			}
			if (!folio_test_dirty(folio) ||
			    folio_test_writeback(folio)) {
				folio_unlock(folio);
				folio_put(folio);
				break;
			}

			wreq->len += folio_size(folio);
			index += folio_nr_pages(folio);
			stop = index >= stop_at || wbc->nr_to_write <= 0;

			if (!folio_batch_add(&fbatch, folio))
				break;
			if (stop)
				break;
			if (index > region->last)
				break;
		}

		if (!stop)
			xas_pause(&xas);
		rcu_read_unlock();

		/* Now, if we obtained any pages, we can shift them to being
		 * writable and mark them for caching.
		 */
		if (!folio_batch_count(&fbatch))
			break;

		for (i = 0; i < folio_batch_count(&fbatch); i++) {
			folio = fbatch.folios[i];
			//_debug("found [%x] %lx", i, folio->index);
			trace_netfs_folio_dirty(wreq->mapping, folio,
						netfs_folio_trace_store_ex);

			dirty = folio_clear_dirty_for_io(folio);
			if (folio_start_writeback(folio)) {
				_debug("! no wb");
				goto nomem_redirty;
			}

			ret = netfs_xa_store_and_mark(&wreq->buffer, folio->index, folio,
						      true, true, dirty, GFP_NOFS);
			if (ret < 0) {
				_debug("! no buffer");
				goto nomem_cancel_wb;
			}
			wbc->nr_to_write -= folio_nr_pages(folio);
			index = folio_next_index(folio);
			wreq->last = index - 1;
			folio_unlock(folio);
		}

		cond_resched();
	} while (!stop);

	_leave(" ok [%zx]", wreq->last);
stop:
	if (region != start_region)
		netfs_put_dirty_region(ctx, region, netfs_region_trace_put_wback);
	return;

nomem_cancel_wb:
	folio_end_writeback(folio);
nomem_redirty:
	if (dirty)
		folio_redirty_for_writepage(wbc, folio);
	for (; i < folio_batch_count(&fbatch); i++) {
		folio_unlock(folio);
		folio_put(folio);
	}
	_leave(" cancel [%zx]", wreq->last);
	goto stop;
}

/*
 * Pin the first folio of the region and lock it.  The folio is attached to the
 * buffer xarray with markings indicating what we need to do to clean it up
 * (redirty it, drop its refcount, etc.).
 */
static int netfs_find_writeback_start(struct netfs_io_request *wreq,
				      struct writeback_control *wbc,
				      struct netfs_dirty_region *region,
				      pgoff_t *_first, pgoff_t last)
{
	struct folio *folio;
	ssize_t ret;
	bool dirty;
	int skips = 0;

	_enter("%lx,%lx,", *_first, last);

retry:
	folio = __filemap_get_folio(wreq->mapping, *_first, 0, 0);
	if (!folio) {
		pr_warn("Folio %lx in dirty region D=%x not present\n",
			*_first, region->debug_id);
		return 0;
	}

	/* At this point we hold neither the i_pages lock nor the folio lock:
	 * the folio may be truncated or invalidated (changing folio->mapping to
	 * NULL), or even swizzled back from swapper_space to tmpfs file
	 * mapping
	 */
	if (wbc->sync_mode != WB_SYNC_NONE) {
		ret = folio_lock_killable(folio);
		if (ret < 0) {
			folio_put(folio);
			_leave(" = %zd [lock]", ret);
			return ret;
		}
	} else {
		if (!folio_trylock(folio)) {
			folio_put(folio);
			_leave(" = 0 [trylock]");
			return 0;
		}
	}

	/* A dirty region must fit exactly over a span of folios - there should
	 * be no partial folio coverage.
	 */
	if (*_first < folio->index) {
		pr_warn("Folio %lx extends before dirty region D=%x\n",
			*_first, region->debug_id);
		goto skip;
	}

	if (folio_mapping(folio) != wreq->mapping) {
		pr_warn("Folio %lx in dirty region D=%x has no mapping set\n",
			*_first, region->debug_id);
		goto skip;
	}

	/* Any folio we have to include must not already have writeback in
	 * progress otherwise we may get a race against old data being written.
	 */
	if (folio_test_writeback(folio)) {
		folio_unlock(folio);
		if (wbc->sync_mode != WB_SYNC_NONE)
			folio_wait_writeback(folio);
		else
			*_first = folio_next_index(folio);
		folio_put(folio);
		if (wbc->sync_mode == WB_SYNC_NONE) {
			if (skips >= 5 || need_resched())
				return 0;
			skips++;
		}
		goto retry;
	}

	/* A dirty region may include a number of folios that are clean in order
	 * to make up a minimum-sized unit for writing, e.g. if we need to
	 * compress a large block or write a bigger unit to the cache, so we
	 * need to keep track of that in case the write op fails.
	 */
	dirty = folio_clear_dirty_for_io(folio);
	trace_netfs_folio_dirty(wreq->mapping, folio, netfs_folio_trace_store);
	trace_netfs_wb_page(wreq, folio);
	if (folio_start_writeback(folio)) {
		kdebug ("start wb failed");
		goto out_unlock;
	}

	ret = netfs_xa_store_and_mark(&wreq->buffer, folio->index, folio,
				      true, true, dirty, GFP_NOFS);
	if (ret < 0) {
		kdebug("oom store");
		goto nomem;
	}

	wreq->first = folio->index;
	wreq->last  = folio_next_index(folio) - 1;
	wreq->len   = folio_size(folio);
	wreq->start = folio_pos(folio);
	if (wreq->start >= wreq->i_size) {
		pr_err("wreq->start >= wreq->i_size\n");
		wreq->len = 0;
		ret = -EIO;
		goto out_unlock;
	}
	_debug("START %zx @%llx [%llx]", wreq->len, wreq->start, wreq->i_size);
	if (wreq->len > wreq->i_size - wreq->start)
		wreq->len = wreq->i_size - wreq->start;
	*_first = wreq->last + 1;
	ret = 1;
out_unlock:
	folio_unlock(folio);
	_leave(" = %zd [%lx]", ret, *_first);
	return ret;

nomem:
	if (dirty)
		folio_redirty_for_writepage(wbc, folio);
	folio_end_writeback(folio);
	goto out_unlock;

skip:
	BUG();
}

/*
 * Make sure there's a flush group.
 */
int netfs_require_flush_group(struct inode *inode, bool force)
{
	struct netfs_flush_group *group;
	struct netfs_inode *ctx = netfs_inode(inode);

	if (list_empty(&ctx->flush_groups) || force) {
		kdebug("new flush group");
		group = netfs_new_flush_group(inode, NULL);
		if (!group)
			return -ENOMEM;
	}
	return 0;
}

/*
 * Select a region from an old flush group to write back instead of a region
 * from the currently live flush group.
 */
static struct netfs_dirty_region *netfs_select_from_flush_group(
	struct writeback_control *wbc,
	struct netfs_inode *ctx,
	struct netfs_flush_group *group)
{
	struct netfs_dirty_region *region;

	region = list_first_entry_or_null(&group->region_list,
					  struct netfs_dirty_region, flush_link);
	if (region) {
		kleave(" = D=%x", region->debug_id);
		return region;
	}

	if (atomic_read(&group->nr_regions) == 0) {
		list_del_init(&group->group_link);
		spin_unlock(&ctx->dirty_lock);
		goto again;
	}

	netfs_get_flush_group(group);
	spin_unlock(&ctx->dirty_lock);

	mutex_unlock(&ctx->wb_mutex);
	kdebug("wait for flush");
	wait_var_event(&group->nr_regions, atomic_read(&group->nr_regions) == 0);
	kdebug("waited for flush");
	mutex_lock(&ctx->wb_mutex);

again:
	netfs_put_flush_group(ctx, group);
	return ERR_PTR(-EAGAIN);
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
 * This may be entered multiple times simultaneously.  Automatic flushing by
 * the VM is serialised on I_SYNC, but things like fsync() may enter multiple
 * times simultaneously.
 */
static int netfs_select_dirty(struct netfs_io_request *wreq,
			      struct writeback_control *wbc,
			      struct netfs_inode *ctx,
			      pgoff_t *_first, pgoff_t last)
{
	struct netfs_dirty_region *region;
	struct netfs_flush_group *group;
	pgoff_t first = *_first;
	pgoff_t csize = 1UL << ctx->cache_order;
	bool advance = true;
	int ret;

	/* Round out the range we're looking through to accommodate whole cache
	 * blocks.  The cache may only be able to store blocks of that size, in
	 * which case we may need to add non-dirty pages to the buffer too.
	 */
	if (ctx->cache_order) {
		first = round_down(first, csize);
		last = round_up_incl(last, csize);
	}

	_enter("%lx-%lx", first, last);

	if (wbc->sync_mode == WB_SYNC_NONE) {
		if (!mutex_trylock(&ctx->wb_mutex))
			return 0;
	} else {
		mutex_lock(&ctx->wb_mutex);
	}

	/* Find the first dirty region that overlaps the requested range */
	spin_lock(&ctx->dirty_lock);

	region = netfs_scan_for_region(ctx, first, last);
	if (region)
		kdebug("scan got D=%08x", region->debug_id);

	/* If the region selected is not in the bottommost flush group, we need
	 * to flush prerequisites first.
	 */
	if (region && region->group) {
		group = list_first_entry(&ctx->flush_groups,
					 struct netfs_flush_group, group_link);
		if (region->group != group) {
			kdebug("flush prereq");
			region = netfs_select_from_flush_group(wbc, ctx, group);
			if (IS_ERR(region)) {
				ret = PTR_ERR(region);
				goto unlock;
			}
			advance = false;
		}
	}

	if (region)
		netfs_get_dirty_region(ctx, region, netfs_region_trace_get_wback);

	spin_unlock(&ctx->dirty_lock);
	if (!region) {
		_debug("scan failed");
		*_first = last;
		ret = 0;
		goto unlock;
	}

	/* Try to grab the first folio of the requested range within that
	 * region.
	 */
	if (*_first < region->first)
		*_first = region->first;

	ret = netfs_find_writeback_start(wreq, wbc, region, _first, last);
	if (ret <= 0)
		goto put_region;

	netfs_extend_writeback(wreq, wbc, ctx, region);
	if (advance)
		*_first = wreq->last + 1;

	netfs_split_out_regions(wreq, ctx, region);

	/* The assembled write request gets placed on the list to prevent
	 * conflicting write requests happening simultaneously.
	 */
	netfs_add_wback_to_list(ctx, wreq);
	ret = 1;

put_region:
	netfs_put_dirty_region(ctx, region, netfs_region_trace_put_wback);
unlock:
	mutex_unlock(&ctx->wb_mutex);
	_leave(" = %d [%lx]", ret, *_first);
	return ret;
}

/*
 * Flush a range of pages.
 */
static int netfs_flush_range(struct address_space *mapping,
			     struct writeback_control *wbc,
			     pgoff_t *_first, pgoff_t last)
{
	struct netfs_io_request *wreq = NULL;
	struct netfs_inode *ctx = netfs_inode(mapping->host);
	long ret;

	_enter("%lx-%lx", *_first, last);

retry:
	ret = netfs_wait_for_credit(wbc);
	if (ret < 0)
		goto out_unlocked;

	if (!wreq) {
		ret = -ENOMEM;
		wreq = netfs_alloc_request(mapping, NULL, 0, 0, NETFS_WRITEBACK);
		if (!wreq)
			goto out_unlocked;
		wreq->cleanup = netfs_cleanup_buffered_write;
		wreq->buffering = NETFS_BUFFER;
		if (test_bit(NETFS_RREQ_CONTENT_ENCRYPTION, &wreq->flags))
			wreq->buffering = NETFS_ENC_BUFFER_TO_BOUNCE;
	}

	/* We need to select the series of regions that we're going to write
	 * back and flip all the folios we need for it into the writeback
	 * state.  Some of those folios will be marked dirty - which we need to
	 * clear - but not necessarily all.
	 */
	ret = netfs_select_dirty(wreq, wbc, ctx, _first, last);
	switch (ret) {
	case -EAGAIN:
		kdebug("retry");
		goto retry;
	default:
		goto out_unlocked;
	case 1:
		break;
	}

	/* Now we can submit the write request for processing. */
	ret = netfs_begin_write(wreq, wbc->sync_mode != WB_SYNC_NONE);
	wreq = NULL;
	if (ret < 0)
		goto out_unlocked;

	/* Flush more. */
	if (wbc->nr_to_write <= 0)
		goto out_unlocked;
	if (*_first >= last)
		goto out_unlocked;
	if (list_empty(&ctx->dirty_regions))
		goto out_unlocked;
	_debug("go again %lx-%lx", *_first, last);
	goto retry;

out_unlocked:
	netfs_put_request(wreq, false, netfs_rreq_trace_put_discard);
	return ret;
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
	struct netfs_inode *ctx = netfs_inode(mapping->host);
	unsigned long nr_to_write = wbc->nr_to_write;
	pgoff_t min_bsize = min_t(pgoff_t, (1UL << ctx->min_bshift) / PAGE_SIZE, 1);
	pgoff_t first, last;
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

	trace_netfs_writepages(mapping, wbc);

	if (wbc->range_cyclic) {
		first = round_down(mapping->writeback_index, min_bsize);
		last  = ULONG_MAX;
		ret = netfs_flush_range(mapping, wbc, &first, last);
		if (ret == 0 && first > 0 && wbc->nr_to_write > 0) {
			last  = first - 1;
			first = 0;
			ret = netfs_flush_range(mapping, wbc, &first, last);
		}
		mapping->writeback_index = first;
	} else {
		first = wbc->range_start / PAGE_SIZE;
		last  = wbc->range_end / PAGE_SIZE;
		ret = netfs_flush_range(mapping, wbc, &first, last);
	}

	_leave(" = %d [%lx/%lx]", ret, wbc->nr_to_write, nr_to_write);
	if (ret == -EBUSY)
		ret = 0;
	return ret;
}
EXPORT_SYMBOL(netfs_writepages);
