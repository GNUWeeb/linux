// SPDX-License-Identifier: GPL-2.0
/*
 * Copyright (C) 2010 Red Hat, Inc.
 * Copyright (c) 2016-2018 Christoph Hellwig.
 */
#include <linux/module.h>
#include <linux/compiler.h>
#include <linux/fs.h>
#include <linux/iomap.h>
#include "trace.h"

/*
 * Execute a iomap write on a segment of the mapping that spans a
 * contiguous range of pages that have identical block mapping state.
 *
 * This avoids the need to map pages individually, do individual allocations
 * for each page and most importantly avoid the need for filesystem specific
 * locking per page. Instead, all the operations are amortised over the entire
 * range of pages. It is assumed that the filesystems will lock whatever
 * resources they require in the iomap_begin call, and release them in the
 * iomap_end call.
 */
loff_t
iomap_apply(struct iomap_data *data, const struct iomap_ops *ops,
	    iomap_actor_t actor)
{
	struct iomap iomap = {
		.type		= IOMAP_HOLE,
		.page_list	= LIST_HEAD_INIT(iomap.page_list)
	};
	struct iomap srcmap = { .type = IOMAP_HOLE };
	loff_t written = 0, ret;
	u64 end;

	trace_iomap_apply(data->inode, data->pos, data->len, data->flags, ops,
				actor, _RET_IP_);

	/*
	 * Need to map a range from start position for length bytes. This can
	 * span multiple pages - it is only guaranteed to return a range of a
	 * single type of pages (e.g. all into a hole, all mapped or all
	 * unwritten). Failure at this point has nothing to undo.
	 *
	 * If allocation is required for this range, reserve the space now so
	 * that the allocation is guaranteed to succeed later on. Once we copy
	 * the data into the page cache pages, then we cannot fail otherwise we
	 * expose transient stale data. If the reserve fails, we can safely
	 * back out at this point as there is nothing to undo.
	 */
	ret = ops->iomap_begin(data->inode, data->pos, data->len, data->flags,
				&iomap, &srcmap);
	if (ret)
		return ret;
	if (WARN_ON(iomap.offset > data->pos))
		return -EIO;
	if (WARN_ON(iomap.length == 0))
		return -EIO;

	trace_iomap_apply_dstmap(data->inode, &iomap);
	if (srcmap.type != IOMAP_HOLE)
		trace_iomap_apply_srcmap(data->inode, &srcmap);

	/*
	 * Cut down the length to the one actually provided by the filesystem,
	 * as it might not be able to give us the whole size that we requested.
	 */
	end = iomap.offset + iomap.length;
	if (srcmap.type != IOMAP_HOLE)
		end = min(end, srcmap.offset + srcmap.length);
	if (data->pos + data->len > end)
		data->len = end - data->pos;

	/*
	 * Now that we have guaranteed that the space allocation will succeed,
	 * we can do the copy-in page by page without having to worry about
	 * failures exposing transient data.
	 *
	 * To support COW operations, we read in data for partially blocks from
	 * the srcmap if the file system filled it in.  In that case we the
	 * length needs to be limited to the earlier of the ends of the iomaps.
	 * If the file system did not provide a srcmap we pass in the normal
	 * iomap into the actors so that they don't need to have special
	 * handling for the two cases.
	 */
	written = actor(data, &iomap,
			srcmap.type != IOMAP_HOLE ? &srcmap : &iomap);

	/*
	 * Now the data has been copied, commit the range we've copied.  This
	 * should not fail unless the filesystem has had a fatal error.
	 */
	if (ops->iomap_end) {
		ret = ops->iomap_end(data->inode, data->pos, data->len,
				     written > 0 ? written : 0,
				     data->flags, &iomap);
	}

	if (!list_empty(&iomap.page_list))
		uncached_write_pages(data->inode->i_mapping, &iomap.page_list);

	return written ? written : ret;
}
