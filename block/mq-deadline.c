/*
 *  MQ Deadline i/o scheduler - adaptation of the legacy deadline scheduler,
 *  for the blk-mq scheduling framework
 *
 *  Copyright (C) 2016 Jens Axboe <axboe@kernel.dk>
 */
#include <linux/kernel.h>
#include <linux/fs.h>
#include <linux/blkdev.h>
#include <linux/blk-mq.h>
#include <linux/elevator.h>
#include <linux/bio.h>
#include <linux/module.h>
#include <linux/slab.h>
#include <linux/init.h>
#include <linux/compiler.h>
#include <linux/rbtree.h>
#include <linux/sbitmap.h>

#include "blk.h"
#include "blk-mq.h"
#include "blk-mq-tag.h"
#include "blk-mq-sched.h"

/*
 * Work-around for the flush machinery, since it intercepts before
 * the request is properly added.
 */
static bool flush_fua_bypass(unsigned int op)
{
	return op & (REQ_PREFLUSH | REQ_FUA);
}

/*
 * See Documentation/block/deadline-iosched.txt
 */
static const int read_expire = HZ / 2;  /* max time before a read is submitted. */
static const int write_expire = 5 * HZ; /* ditto for writes, these limits are SOFT! */
static const int writes_starved = 2;    /* max times reads can starve a write */
static const int fifo_batch = 16;       /* # of sequential requests treated as one
				     by the above parameters. For throughput. */

struct deadline_data {
	/*
	 * run time data
	 */

	/*
	 * requests (deadline_rq s) are present on both sort_list and fifo_list
	 */
	struct rb_root sort_list[2];
	struct list_head fifo_list[2];

	/*
	 * next in sort order. read, write or both are NULL
	 */
	struct request *next_rq[2];
	unsigned int batching;		/* number of sequential requests made */
	unsigned int starved;		/* times reads have starved writes */

	/*
	 * settings that change how the i/o scheduler behaves
	 */
	int fifo_expire[2];
	int fifo_batch;
	int writes_starved;
	int front_merges;

	spinlock_t lock;
	struct list_head dispatch;
	struct blk_mq_tags *tags;
	atomic_t wait_index;
};

static inline struct rb_root *
deadline_rb_root(struct deadline_data *dd, struct request *rq)
{
	return &dd->sort_list[rq_data_dir(rq)];
}

/*
 * get the request after `rq' in sector-sorted order
 */
static inline struct request *
deadline_latter_request(struct request *rq)
{
	struct rb_node *node = rb_next(&rq->rb_node);

	if (node)
		return rb_entry_rq(node);

	return NULL;
}

static void
deadline_add_rq_rb(struct deadline_data *dd, struct request *rq)
{
	struct rb_root *root = deadline_rb_root(dd, rq);

	elv_rb_add(root, rq);
}

static inline void
deadline_del_rq_rb(struct deadline_data *dd, struct request *rq)
{
	const int data_dir = rq_data_dir(rq);

	if (dd->next_rq[data_dir] == rq)
		dd->next_rq[data_dir] = deadline_latter_request(rq);

	elv_rb_del(deadline_rb_root(dd, rq), rq);
}

/*
 * remove rq from rbtree and fifo.
 */
static void deadline_remove_request(struct request_queue *q, struct request *rq)
{
	struct deadline_data *dd = q->elevator->elevator_data;

	list_del_init(&rq->queuelist);
	deadline_del_rq_rb(dd, rq);

	elv_rqhash_del(q, rq);
	if (q->last_merge == rq)
		q->last_merge = NULL;
}

#if 0
static void
deadline_merged_requests(struct request_queue *q, struct request *req,
			 struct request *next)
{
	/*
	 * if next expires before rq, assign its expire time to rq
	 * and move into next position (next will be deleted) in fifo
	 */
	if (!list_empty(&req->queuelist) && !list_empty(&next->queuelist)) {
		if (time_before((unsigned long)next->fifo_time,
				(unsigned long)req->fifo_time)) {
			list_move(&req->queuelist, &next->queuelist);
			req->fifo_time = next->fifo_time;
		}
	}

	/*
	 * kill knowledge of next, this one is a goner
	 */
	deadline_remove_request(q, next);
}
#endif

/*
 * move an entry to dispatch queue
 */
static void
deadline_move_request(struct deadline_data *dd, struct request *rq)
{
	const int data_dir = rq_data_dir(rq);

	dd->next_rq[READ] = NULL;
	dd->next_rq[WRITE] = NULL;
	dd->next_rq[data_dir] = deadline_latter_request(rq);

	/*
	 * take it off the sort and fifo list
	 */
	deadline_remove_request(rq->q, rq);
}

/*
 * deadline_check_fifo returns 0 if there are no expired requests on the fifo,
 * 1 otherwise. Requires !list_empty(&dd->fifo_list[data_dir])
 */
static inline int deadline_check_fifo(struct deadline_data *dd, int ddir)
{
	struct request *rq = rq_entry_fifo(dd->fifo_list[ddir].next);

	/*
	 * rq is expired!
	 */
	if (time_after_eq(jiffies, (unsigned long)rq->fifo_time))
		return 1;

	return 0;
}

/*
 * deadline_dispatch_requests selects the best request according to
 * read/write expire, fifo_batch, etc
 */
static struct request *__dd_dispatch_request(struct blk_mq_hw_ctx *hctx)
{
	struct deadline_data *dd = hctx->queue->elevator->elevator_data;
	struct request *rq;
	bool reads, writes;
	int data_dir;

	spin_lock(&dd->lock);

	if (!list_empty(&dd->dispatch)) {
		rq = list_first_entry(&dd->dispatch, struct request, queuelist);
		list_del_init(&rq->queuelist);
		goto done;
	}

	reads = !list_empty(&dd->fifo_list[READ]);
	writes = !list_empty(&dd->fifo_list[WRITE]);

	/*
	 * batches are currently reads XOR writes
	 */
	if (dd->next_rq[WRITE])
		rq = dd->next_rq[WRITE];
	else
		rq = dd->next_rq[READ];

	if (rq && dd->batching < dd->fifo_batch)
		/* we have a next request are still entitled to batch */
		goto dispatch_request;

	/*
	 * at this point we are not running a batch. select the appropriate
	 * data direction (read / write)
	 */

	if (reads) {
		BUG_ON(RB_EMPTY_ROOT(&dd->sort_list[READ]));

		if (writes && (dd->starved++ >= dd->writes_starved))
			goto dispatch_writes;

		data_dir = READ;

		goto dispatch_find_request;
	}

	/*
	 * there are either no reads or writes have been starved
	 */

	if (writes) {
dispatch_writes:
		BUG_ON(RB_EMPTY_ROOT(&dd->sort_list[WRITE]));

		dd->starved = 0;

		data_dir = WRITE;

		goto dispatch_find_request;
	}

	spin_unlock(&dd->lock);
	return NULL;

dispatch_find_request:
	/*
	 * we are not running a batch, find best request for selected data_dir
	 */
	if (deadline_check_fifo(dd, data_dir) || !dd->next_rq[data_dir]) {
		/*
		 * A deadline has expired, the last request was in the other
		 * direction, or we have run out of higher-sectored requests.
		 * Start again from the request with the earliest expiry time.
		 */
		rq = rq_entry_fifo(dd->fifo_list[data_dir].next);
	} else {
		/*
		 * The last req was the same dir and we have a next request in
		 * sort order. No expired requests so continue on from here.
		 */
		rq = dd->next_rq[data_dir];
	}

	dd->batching = 0;

dispatch_request:
	/*
	 * rq is the selected appropriate request.
	 */
	dd->batching++;
	deadline_move_request(dd, rq);
done:
	spin_unlock(&dd->lock);
	return rq;
}

static struct request *dd_dispatch_request(struct blk_mq_hw_ctx *hctx)
{
	return blk_mq_sched_request_from_shadow(hctx, __dd_dispatch_request);
}

static void dd_exit_queue(struct elevator_queue *e)
{
	struct deadline_data *dd = e->elevator_data;

	BUG_ON(!list_empty(&dd->fifo_list[READ]));
	BUG_ON(!list_empty(&dd->fifo_list[WRITE]));

	blk_mq_sched_free_requests(dd->tags);
	kfree(dd);
}

/*
 * initialize elevator private data (deadline_data).
 */
static int dd_init_queue(struct request_queue *q, struct elevator_type *e)
{
	struct deadline_data *dd;
	struct elevator_queue *eq;

	eq = elevator_alloc(q, e);
	if (!eq)
		return -ENOMEM;

	dd = kzalloc_node(sizeof(*dd), GFP_KERNEL, q->node);
	if (!dd) {
		kobject_put(&eq->kobj);
		return -ENOMEM;
	}
	eq->elevator_data = dd;

	dd->tags = blk_mq_sched_alloc_requests(256, q->node);
	if (!dd->tags) {
		kfree(dd);
		kobject_put(&eq->kobj);
		return -ENOMEM;
	}

	INIT_LIST_HEAD(&dd->fifo_list[READ]);
	INIT_LIST_HEAD(&dd->fifo_list[WRITE]);
	dd->sort_list[READ] = RB_ROOT;
	dd->sort_list[WRITE] = RB_ROOT;
	dd->fifo_expire[READ] = read_expire;
	dd->fifo_expire[WRITE] = write_expire;
	dd->writes_starved = writes_starved;
	dd->front_merges = 1;
	dd->fifo_batch = fifo_batch;
	spin_lock_init(&dd->lock);
	INIT_LIST_HEAD(&dd->dispatch);
	atomic_set(&dd->wait_index, 0);

	q->elevator = eq;
	return 0;
}

static int __dd_bio_merge(struct blk_mq_hw_ctx *hctx, struct bio *bio,
			  struct request **req)
{
	struct request_queue *q = hctx->queue;
	struct deadline_data *dd = q->elevator->elevator_data;
	struct request *__rq;
	sector_t sector;
	int ret;

	/*
	 * First try one-hit cache.
	 */
	if (q->last_merge && elv_bio_merge_ok(q->last_merge, bio)) {
		ret = blk_try_merge(q->last_merge, bio);
		if (ret != ELEVATOR_NO_MERGE) {
			*req = q->last_merge;
			return ret;
		}
	}

	if (blk_queue_noxmerges(q))
		return ELEVATOR_NO_MERGE;

	/*
	 * See if our hash lookup can find a potential backmerge.
	 */
	__rq = elv_rqhash_find(q, bio->bi_iter.bi_sector);
	if (__rq && elv_bio_merge_ok(__rq, bio)) {
		*req = __rq;
		return ELEVATOR_BACK_MERGE;
	}

	if (!dd->front_merges)
		return ELEVATOR_NO_MERGE;

	sector = bio_end_sector(bio);

	__rq = elv_rb_find(&dd->sort_list[bio_data_dir(bio)], sector);
	if (__rq) {
		BUG_ON(sector != blk_rq_pos(__rq));

		if (elv_bio_merge_ok(__rq, bio)) {
			*req = __rq;
			return ELEVATOR_FRONT_MERGE;
		}
	}

	return ELEVATOR_NO_MERGE;
}

static bool dd_bio_merge(struct blk_mq_hw_ctx *hctx, struct bio *bio)
{
	struct request_queue *q = hctx->queue;
	struct deadline_data *dd = q->elevator->elevator_data;
	struct request *rq;
	int ret;

	spin_lock(&dd->lock);

	ret = __dd_bio_merge(hctx, bio, &rq);

	if (ret == ELEVATOR_BACK_MERGE) {
		if (bio_attempt_back_merge(q, rq, bio)) {
			if (!attempt_back_merge(q, rq)) {
				q->last_merge = rq;
				elv_rqhash_reposition(q, rq);
				goto done;
			}
		}
		ret = ELEVATOR_NO_MERGE;
	} else if (ret == ELEVATOR_FRONT_MERGE) {
		if (bio_attempt_front_merge(q, rq, bio)) {
			if (!attempt_front_merge(q, rq)) {
				q->last_merge = rq;
				elv_rb_del(deadline_rb_root(dd, rq), rq);
				deadline_add_rq_rb(dd, rq);
				goto done;
			}
		}
		ret = ELEVATOR_NO_MERGE;
	}

done:
	spin_unlock(&dd->lock);
	return ret != ELEVATOR_NO_MERGE;
}

/*
 * add rq to rbtree and fifo
 */
static void dd_insert_request(struct blk_mq_hw_ctx *hctx, struct request *rq,
			      bool at_head)
{
	struct request_queue *q = hctx->queue;
	struct deadline_data *dd = q->elevator->elevator_data;
	const int data_dir = rq_data_dir(rq);

	if (unlikely(flush_fua_bypass(rq->cmd_flags))) {
		spin_lock(&hctx->lock);
		list_add_tail(&rq->queuelist, &hctx->dispatch);
		spin_unlock(&hctx->lock);
		return;
	}

	spin_lock(&dd->lock);

	if (at_head || rq->cmd_type != REQ_TYPE_FS) {
		if (at_head)
			list_add(&rq->queuelist, &dd->dispatch);
		else
			list_add_tail(&rq->queuelist, &dd->dispatch);
	} else {
		deadline_add_rq_rb(dd, rq);

		if (rq_mergeable(rq)) {
			elv_rqhash_add(q, rq);
			if (!q->last_merge)
				q->last_merge = rq;
		}

		/*
		 * set expire time and add to fifo list
		 */
		rq->fifo_time = jiffies + dd->fifo_expire[data_dir];
		list_add_tail(&rq->queuelist, &dd->fifo_list[data_dir]);
	}

	spin_unlock(&dd->lock);
}

static struct request *dd_get_request(struct request_queue *q, struct bio *bio,
				      struct blk_mq_alloc_data *data)
{
	struct deadline_data *dd = q->elevator->elevator_data;
	struct request *rq;

	if (unlikely(flush_fua_bypass(bio->bi_opf)))
		rq = __blk_mq_alloc_request(data, bio->bi_opf);
	else {
		rq = blk_mq_sched_alloc_shadow_request(q, data, dd->tags, &dd->wait_index);
		if (rq)
			blk_mq_rq_ctx_init(q, data->ctx, rq, bio->bi_opf);
	}

	return rq;
}

static void dd_completed_request(struct blk_mq_hw_ctx *hctx, struct request *rq)
{
	struct request *sched_rq = rq->end_io_data;

	/*
	 * sched_rq can be NULL, if we haven't setup the shadow yet
	 * because we failed getting one.
	 */
	if (sched_rq) {
		struct deadline_data *dd = hctx->queue->elevator->elevator_data;

		blk_mq_sched_free_shadow_request(dd->tags, sched_rq);
		blk_mq_start_stopped_hw_queue(hctx, true);
	}
}

static bool dd_has_work(struct blk_mq_hw_ctx *hctx)
{
	struct deadline_data *dd = hctx->queue->elevator->elevator_data;

	return !list_empty_careful(&dd->dispatch) ||
		!list_empty_careful(&dd->fifo_list[0]) ||
		!list_empty_careful(&dd->fifo_list[1]);
}

/*
 * sysfs parts below
 */
static ssize_t
deadline_var_show(int var, char *page)
{
	return sprintf(page, "%d\n", var);
}

static ssize_t
deadline_var_store(int *var, const char *page, size_t count)
{
	char *p = (char *) page;

	*var = simple_strtol(p, &p, 10);
	return count;
}

#define SHOW_FUNCTION(__FUNC, __VAR, __CONV)				\
static ssize_t __FUNC(struct elevator_queue *e, char *page)		\
{									\
	struct deadline_data *dd = e->elevator_data;			\
	int __data = __VAR;						\
	if (__CONV)							\
		__data = jiffies_to_msecs(__data);			\
	return deadline_var_show(__data, (page));			\
}
SHOW_FUNCTION(deadline_read_expire_show, dd->fifo_expire[READ], 1);
SHOW_FUNCTION(deadline_write_expire_show, dd->fifo_expire[WRITE], 1);
SHOW_FUNCTION(deadline_writes_starved_show, dd->writes_starved, 0);
SHOW_FUNCTION(deadline_front_merges_show, dd->front_merges, 0);
SHOW_FUNCTION(deadline_fifo_batch_show, dd->fifo_batch, 0);
#undef SHOW_FUNCTION

#define STORE_FUNCTION(__FUNC, __PTR, MIN, MAX, __CONV)			\
static ssize_t __FUNC(struct elevator_queue *e, const char *page, size_t count)	\
{									\
	struct deadline_data *dd = e->elevator_data;			\
	int __data;							\
	int ret = deadline_var_store(&__data, (page), count);		\
	if (__data < (MIN))						\
		__data = (MIN);						\
	else if (__data > (MAX))					\
		__data = (MAX);						\
	if (__CONV)							\
		*(__PTR) = msecs_to_jiffies(__data);			\
	else								\
		*(__PTR) = __data;					\
	return ret;							\
}
STORE_FUNCTION(deadline_read_expire_store, &dd->fifo_expire[READ], 0, INT_MAX, 1);
STORE_FUNCTION(deadline_write_expire_store, &dd->fifo_expire[WRITE], 0, INT_MAX, 1);
STORE_FUNCTION(deadline_writes_starved_store, &dd->writes_starved, INT_MIN, INT_MAX, 0);
STORE_FUNCTION(deadline_front_merges_store, &dd->front_merges, 0, 1, 0);
STORE_FUNCTION(deadline_fifo_batch_store, &dd->fifo_batch, 0, INT_MAX, 0);
#undef STORE_FUNCTION

#define DD_ATTR(name) \
	__ATTR(name, S_IRUGO|S_IWUSR, deadline_##name##_show, \
				      deadline_##name##_store)

static struct elv_fs_entry deadline_attrs[] = {
	DD_ATTR(read_expire),
	DD_ATTR(write_expire),
	DD_ATTR(writes_starved),
	DD_ATTR(front_merges),
	DD_ATTR(fifo_batch),
	__ATTR_NULL
};

static struct elevator_type mq_deadline = {
	.mq_ops = {
		.get_request		= dd_get_request,
		.insert_request		= dd_insert_request,
		.dispatch_request	= dd_dispatch_request,
		.completed_request	= dd_completed_request,
		.bio_merge		= dd_bio_merge,
		.has_work		= dd_has_work,
		.init_sched		= dd_init_queue,
		.exit_sched		= dd_exit_queue,
	},

	.uses_mq	= true,
	.elevator_attrs = deadline_attrs,
	.elevator_name = "mq-deadline",
	.elevator_owner = THIS_MODULE,
};

static int __init deadline_init(void)
{
	return elv_register(&mq_deadline);
}

static void __exit deadline_exit(void)
{
	elv_unregister(&mq_deadline);
}

module_init(deadline_init);
module_exit(deadline_exit);

MODULE_AUTHOR("Jens Axboe");
MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("MQ deadline IO scheduler");
