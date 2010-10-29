/*
 * TODO
 *
 * - Proper ioctls
 * - Get rid of device list?
 */
#include <linux/kernel.h>
#include <linux/module.h>
#include <linux/init.h>
#include <linux/cdev.h>
#include <linux/poll.h>
#include <linux/slab.h>
#include <linux/idr.h>
#include <linux/file.h>
#include <linux/miscdevice.h>
#include <linux/bio.h>
#include <linux/blkdev.h>

#include "binject.h"

static LIST_HEAD(b_dev_list);
static DEFINE_SPINLOCK(b_dev_lock);
static DEFINE_IDR(b_minor_idr);
static struct kmem_cache *b_slab;
static struct class *b_class;
static int b_major;

#define B_MAX_DEVS	64

struct b_dev {
	struct list_head device_list;
	struct list_head done_list;
	atomic_t in_flight;
	unsigned int done_cmds;
	wait_queue_head_t wq_done;
	struct block_device *bdev;
	spinlock_t lock;
	atomic_t ref;
	struct file *file;
	struct device *dev;
	int minor;
	struct rcu_head rcu_free;
};

struct b_cmd {
	struct list_head list;
	struct b_dev *bd;
	struct bio *bio;
	struct b_user_cmd cmd;
	u64 issue_time;
};

static const unsigned long uc_flag_map[__B_FLAG_NR] = {
	REQ_SYNC,
	REQ_UNPLUG,
	REQ_NOIDLE,
	REQ_HARDBARRIER,
	REQ_META,
	REQ_RAHEAD,
	REQ_FAILFAST_DEV,
	REQ_FAILFAST_TRANSPORT,
	REQ_FAILFAST_DRIVER
};

struct uc_map {
	int type;
	unsigned int data_transfer : 1;
	unsigned int todevice : 1;
	unsigned int map_zero : 1;
};

static const struct uc_map uc_map[B_TYPE_NR] = {
	{
		.type		= B_TYPE_READ,
		.data_transfer	= 1,
		.todevice	= 0,
		.map_zero	= 0,
	},
	{
		.type		= B_TYPE_WRITE,
		.data_transfer	= 1,
		.todevice	= 1,
		.map_zero	= 0,
	},
	{
		.type		= B_TYPE_DISCARD,
		.data_transfer	= 0,
		.todevice	= 0,
		.map_zero	= 0,
	},
	{
		.type		= B_TYPE_READVOID,
		.data_transfer	= 1,
		.todevice	= 0,
		.map_zero	= 1,
	},
	{
		.type		= B_TYPE_WRITEZERO,
		.data_transfer	= 1,
		.todevice	= 1,
		.map_zero	= 1,
	}
};

static void b_dev_complete_commands(struct b_dev *bd);

static void b_dev_remove_lookup(struct b_dev *bd)
{
	if (!list_empty(&bd->device_list)) {
		list_del_init(&bd->device_list);
		idr_remove(&b_minor_idr, bd->minor);
	}
}

static void bd_rcu_free(struct rcu_head *head)
{
	kfree(container_of(head, struct b_dev, rcu_free));
}

static void b_dev_put(struct b_dev *bd)
{
	if (!atomic_dec_and_test(&bd->ref))
		return;

	spin_lock(&b_dev_lock);
	b_dev_remove_lookup(bd);
	spin_unlock(&b_dev_lock);

	b_dev_complete_commands(bd);

	device_destroy(b_class, MKDEV(b_major, bd->minor));
	fput(bd->file);
	module_put(THIS_MODULE);

	call_rcu(&bd->rcu_free, bd_rcu_free);
}

static struct b_cmd *get_free_command(struct b_dev *bd)
{
	struct b_cmd *bc;

	bc = kmem_cache_alloc(b_slab, GFP_KERNEL);
	if (bc) {
		memset(bc, 0, sizeof(*bc));
		INIT_LIST_HEAD(&bc->list);
		bc->bd = bd;
		return bc;
	}

	return ERR_PTR(-ENOMEM);
}

static struct b_cmd *get_completed_command(struct b_dev *bd)
{
	struct b_cmd *bc = NULL;

	spin_lock_irq(&bd->lock);
	if (!list_empty(&bd->done_list)) {
		bc = list_entry(bd->done_list.next, struct b_cmd, list);
		bd->done_cmds--;
		list_del(&bc->list);
	}
	spin_unlock_irq(&bd->lock);
	return bc;
}

static struct b_cmd *get_done_command(struct b_dev *bd, int block)
{
	struct b_cmd *bc;
	int ret;

	do {
		bc = get_completed_command(bd);
		if (bc)
			break;

		if (!block)
			break;

		ret = wait_event_interruptible(bd->wq_done, bd->done_cmds);
		if (ret) {
			bc = ERR_PTR(-ERESTARTSYS);
			break;
		}
	} while (1);

	return bc;
}

static void bc_put_bio_pages(struct bio *bio)
{
	struct bio_vec *bv;
	unsigned int i;

	__bio_for_each_segment(bv, bio, i, 0) {
		if (bv->bv_page != ZERO_PAGE(0))
			__free_page(bv->bv_page);
	}
}

static void complete_and_free_bio(struct b_cmd *bc)
{
	if (bc->bio) {
		const struct uc_map *ucm = &uc_map[bc->cmd.type];

		if (ucm->data_transfer) {
			if (!ucm->map_zero)
				bio_unmap_user(bc->bio);
			else
				bc_put_bio_pages(bc->bio);
		}
		bio_put(bc->bio);
		bc->bio = NULL;
	}
}

static void b_dev_complete_commands(struct b_dev *bd)
{
	struct b_cmd *bc;

	wait_event(bd->wq_done, !atomic_read(&bd->in_flight));

	while ((bc = get_completed_command(bd)) != NULL)
		complete_and_free_bio(bc);
}

static int b_dev_validate_command(struct b_user_cmd *buc)
{
	if (!binject_buc_check_magic(buc))
		return -EINVAL;

	switch (buc->type) {
	case B_TYPE_WRITE:
	case B_TYPE_READ:
	case B_TYPE_DISCARD:
	case B_TYPE_READVOID:
	case B_TYPE_WRITEZERO:
		if (buc->len)
			return 0;
		return -EINVAL;
	default:
		return -EINVAL;
	}
}

static void b_cmd_endio(struct bio *bio, int error)
{
	struct b_cmd *bc = bio->bi_private;
	struct b_dev *bd = bc->bd;
	unsigned long flags;
	unsigned long now;

	now = ktime_to_ns(ktime_get());
	bc->cmd.nsec = now - bc->issue_time;
	bc->cmd.error = error;

	spin_lock_irqsave(&bd->lock, flags);
	list_add_tail(&bc->list, &bd->done_list);
	bd->done_cmds++;
	spin_unlock_irqrestore(&bd->lock, flags);

	atomic_dec(&bd->in_flight);

	wake_up(&bd->wq_done);
}

static int zero_map_bio(struct request_queue *q, struct bio *bio,
			const struct uc_map *ucm, unsigned int len)
{
	unsigned int i, nr_pages, this_len, ret, err;
	struct page *page;

	nr_pages = len / PAGE_SIZE;
	for (i = 0; i < nr_pages; i++) {
		if (ucm->todevice)
			page = ZERO_PAGE(0);
		else {
			page = alloc_page(GFP_KERNEL);
			if (!page) {
				err = -ENOMEM;
				goto oom;
			}
		}

		this_len = PAGE_SIZE;
		if (this_len > len)
			this_len = len;

		ret = bio_add_pc_page(q, bio, page, len, 0);
		if (ret < len) {
			err = -E2BIG;
			goto oom;
		}
	}
	return 0;
oom:
	bc_put_bio_pages(bio);
	return err;
}

static void map_uc_to_bio_flags(struct bio *bio, struct b_user_cmd *uc)
{
	unsigned int i;

	for (i = 0; i < 8 * sizeof(uc->flags); i++) {
		unsigned long mask;

		if (uc->flags & (1UL << i))
			bio->bi_rw |= uc_flag_map[i];

		mask = ~((1UL << i) - 1);
		if (!(mask & uc->flags))
			break;
	}
}

static struct bio *map_uc_to_bio(struct b_dev *bd, struct b_user_cmd *uc)
{
	struct request_queue *q = bdev_get_queue(bd->bdev);
	const struct uc_map *ucm = &uc_map[uc->type];
	struct bio *bio;

	if (ucm->data_transfer && !ucm->map_zero) {
		bio = bio_map_user(q, bd->bdev, uc->buf, uc->len,
					!ucm->todevice, GFP_KERNEL);
	} else {
		bio = bio_alloc(GFP_KERNEL, uc->len / PAGE_SIZE);
		if (bio) {
			bio->bi_bdev = bd->bdev;
			if (ucm->todevice)
				bio->bi_rw |= REQ_WRITE;
			if (uc->type == B_TYPE_DISCARD)
				bio->bi_rw |= REQ_DISCARD;
			if (ucm->map_zero && uc->len) {
				int err;

				err = zero_map_bio(q, bio, ucm, uc->len);
				if (err) {
					bio_put(bio);
					bio = ERR_PTR(err);
				}
			} else
				bio->bi_size = uc->len;
		}
	}

	if (!bio)
		bio = ERR_PTR(-ENOMEM);
	else if (!IS_ERR(bio)) {
		map_uc_to_bio_flags(bio, uc);
		bio->bi_sector = uc->offset / queue_physical_block_size(q);
	}

	return bio;
}

static int b_dev_add_command(struct b_dev *bd, struct b_cmd *bc)
{
	struct b_user_cmd *uc = &bc->cmd;
	struct bio *bio;

	bio = map_uc_to_bio(bd, uc);
	if (IS_ERR(bio))
		return PTR_ERR(bio);

	bio_get(bio);
	bc->bio = bio;

	bio->bi_end_io = b_cmd_endio;
	bio->bi_private = bc;

	bc->issue_time = ktime_to_ns(ktime_get());

	atomic_inc(&bd->in_flight);
	submit_bio(bio->bi_rw, bio);
	return 0;
}

static void b_dev_free_command(struct b_dev *bd, struct b_cmd *bc)
{
	kmem_cache_free(b_slab, bc);
}

/*
 * We are always writable, as we have an infinite queue depth
 */
static unsigned int b_dev_poll(struct file *file, poll_table *wait)
{
	struct b_dev *bd = file->private_data;
	unsigned int mask = POLLOUT;

	poll_wait(file, &bd->wq_done, wait);

	spin_lock_irq(&bd->lock);
	if (!list_empty(&bd->done_list))
		mask |= POLLIN | POLLRDNORM;
	spin_unlock_irq(&bd->lock);

	return mask;
}

static int b_dev_release(struct inode *inode, struct file *file)
{
	struct b_dev *bd = file->private_data;

	b_dev_put(bd);
	return 0;
}

static struct b_dev *b_dev_lookup(int minor)
{
	struct b_dev *bd;

	rcu_read_lock();

	bd = idr_find(&b_minor_idr, minor);
	if (bd && !atomic_inc_not_zero(&bd->ref))
		bd = NULL;

	rcu_read_unlock();
	return bd;
}

static int b_dev_open(struct inode *inode, struct file *file)
{
	struct b_dev *bd;

	bd = b_dev_lookup(iminor(inode));
	if (!bd)
		return -ENODEV;

	file->private_data = bd;
	return 0;
}

static ssize_t b_dev_write(struct file *file, const char __user *buf,
			   size_t count, loff_t *ppos)
{
	struct b_dev *bd = file->private_data;
	struct b_cmd *bc = NULL;
	unsigned int total;
	ssize_t done = 0;
	int err = 0;

	if (count % sizeof(struct b_user_cmd))
		return -EINVAL;

	total = count / sizeof(struct b_user_cmd);
	while (total) {
		bc = get_free_command(bd);
		if (IS_ERR(bc)) {
			err = PTR_ERR(bc);
			bc = NULL;
			break;
		}

		if (copy_from_user(&bc->cmd, buf, sizeof(struct b_user_cmd))) {
			err = -EFAULT;
			break;
		}

		err = b_dev_validate_command(&bc->cmd);
		if (err)
			break;

		err = b_dev_add_command(bd, bc);
		if (err)
			break;

		done += sizeof(struct b_user_cmd);
		buf += sizeof(struct b_user_cmd);
		total--;
	}

	if (bc)
		b_dev_free_command(bd, bc);

	*ppos = done;
	if (!done)
		done = err;

	return done;
}

static ssize_t b_dev_read(struct file *file, char __user *buf, size_t count,
			  loff_t *ppos)
{
	struct b_dev *bd = file->private_data;
	unsigned int total;
	ssize_t done = 0;
	int err = 0;

	if (count % sizeof(struct b_user_cmd))
		return -EINVAL;

	total = count / sizeof(struct b_user_cmd);
	while (total) {
		struct b_cmd *bc;

		bc = get_done_command(bd, !(file->f_flags & O_NONBLOCK));
		if (IS_ERR(bc)) {
			err = PTR_ERR(bc);
			break;
		}

		complete_and_free_bio(bc);

		if (copy_to_user(buf, &bc->cmd, sizeof(bc->cmd)))
			err = -EFAULT;

		b_dev_free_command(bd, bc);

		if (err)
			break;

		done += sizeof(struct b_user_cmd);
		buf += sizeof(struct b_user_cmd);
		total--;
	}

	*ppos = done;
	if (!done)
		done = err;

	return done;
}

static const struct file_operations b_dev_fops = {
	.open		= b_dev_open,
	.release	= b_dev_release,
	.read		= b_dev_read,
	.write		= b_dev_write,
	.poll		= b_dev_poll,
	.owner		= THIS_MODULE,
};

static int b_del_dev(struct b_ioctl_cmd *bic)
{
	struct b_dev *bd;

	bd = b_dev_lookup(bic->minor);
	if (bd) {
		spin_lock(&b_dev_lock);
		b_dev_remove_lookup(bd);
		spin_unlock(&b_dev_lock);

		/*
		 * Our lookup grabbed a reference, drop two
		 */
		b_dev_put(bd);
		b_dev_put(bd);
		return 0;
	}

	return -ENODEV;
}

static int b_add_dev(struct b_ioctl_cmd *bic)
{
	struct inode *inode;
	struct file *file;
	struct b_dev *bd;
	int ret;

	file = fget(bic->fd);
	if (!file)
		return -EBADF;

	__module_get(THIS_MODULE);

	inode = file->f_mapping->host;
	if (!S_ISBLK(inode->i_mode)) {
		ret = -EINVAL;
		goto out_put;
	}

	ret = idr_pre_get(&b_minor_idr, GFP_KERNEL);
	if (!ret) {
		ret = -ENOMEM;
		goto out_put;
	}

	bd = kzalloc(sizeof(*bd), GFP_KERNEL);
	if (!bd) {
		ret = -ENOMEM;
		goto out_put;
	}

	atomic_set(&bd->ref, 1);
	spin_lock_init(&bd->lock);
	INIT_LIST_HEAD(&bd->done_list);
	init_waitqueue_head(&bd->wq_done);
	bd->file = file;
	bd->bdev = inode->i_bdev;;

	spin_lock(&b_dev_lock);

	ret = idr_get_new(&b_minor_idr, bd, &bd->minor);
	if (ret < 0)
		goto out_unlock;

	if (bd->minor >= B_MAX_DEVS)
		goto out_idr;

	spin_unlock(&b_dev_lock);

	INIT_LIST_HEAD(&bd->device_list);
	bd->dev = device_create(b_class, NULL, MKDEV(b_major, bd->minor), bd,
				"binject%d", bd->minor);

	spin_lock(&b_dev_lock);

	if (IS_ERR(bd->dev))
		goto out_idr;

	list_add_tail(&bd->device_list, &b_dev_list);
	spin_unlock(&b_dev_lock);
	return 0;
out_idr:
	idr_remove(&b_minor_idr, bd->minor);
out_unlock:
	spin_unlock(&b_dev_lock);
	kfree(bd);
out_put:
	fput(file);
	module_put(THIS_MODULE);
	return ret;
}

static long b_misc_ioctl(struct file *file, unsigned int cmd, unsigned long arg)
{
	int __user *uarg = (int __user *) arg;
	struct b_ioctl_cmd bic;

	if (copy_from_user(&bic, uarg, sizeof(bic)))
		return -EFAULT;

	switch (cmd) {
	case 0:
		return b_add_dev(&bic);
	case 1:
		return b_del_dev(&bic);
	default:
		break;
	}

	return -ENOTTY;
}

static const struct file_operations b_misc_fops = {
	.unlocked_ioctl	= b_misc_ioctl,
	.owner		= THIS_MODULE,
};

static struct miscdevice b_misc_dev = {
	.minor		= MISC_DYNAMIC_MINOR,
	.name		= "binject-ctl",
	.fops		= &b_misc_fops,
};

static void __exit b_exit(void)
{
	synchronize_rcu();
	kmem_cache_destroy(b_slab);
	class_destroy(b_class);
	misc_deregister(&b_misc_dev);
}

static int __init b_init(void)
{
	int ret;

	b_slab = kmem_cache_create("binject", sizeof(struct b_cmd), 0, 0, NULL);
	if (!b_slab) {
		printk(KERN_ERR "binject: failed to create cmd slab\n");
		return -ENOMEM;
	}

	ret = misc_register(&b_misc_dev);
	if (ret < 0)
		goto fail_misc;

	b_major = register_chrdev(0, "binject", &b_dev_fops);
	if (b_major < 0)
		goto fail_chr;

	b_class = class_create(THIS_MODULE, "binject");
	if (IS_ERR(b_class))
		goto fail_class;

	return 0;
fail_class:
	unregister_chrdev(b_major, "binject");
fail_chr:
	misc_deregister(&b_misc_dev);
fail_misc:
	kmem_cache_destroy(b_slab);
	return ret;
}

module_init(b_init);
module_exit(b_exit);

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Jens Axboe <jaxboe@fusionio.com>");
