// SPDX-License-Identifier: GPL-2.0-or-later
/* Test the fsinfo() system call
 *
 * Copyright (C) 2020 Red Hat, Inc. All Rights Reserved.
 * Written by David Howells (dhowells@redhat.com)
 */

#define _GNU_SOURCE
#define _ATFILE_SOURCE
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include <ctype.h>
#include <errno.h>
#include <time.h>
#include <math.h>
#include <fcntl.h>
#include <sys/syscall.h>
#include <linux/fsinfo.h>
#include <linux/socket.h>
#include <sys/stat.h>
#include <arpa/inet.h>
#include <linux/rxrpc.h>

#ifndef __NR_fsinfo
#define __NR_fsinfo -1
#endif

static bool debug = 0;
static bool list_last;

static __attribute__((unused))
ssize_t fsinfo(int dfd, const char *filename,
	       struct fsinfo_params *params, size_t params_size,
	       void *result_buffer, size_t result_buf_size)
{
	return syscall(__NR_fsinfo, dfd, filename,
		       params, params_size,
		       result_buffer, result_buf_size);
}

struct fsinfo_attribute {
	unsigned int		attr_id;
	enum fsinfo_value_type	type;
	unsigned int		size;
	const char		*name;
	void (*dump)(void *reply, unsigned int size);
};

static const struct fsinfo_attribute fsinfo_attributes[];

static ssize_t get_fsinfo(const char *, const char *, struct fsinfo_params *, void **);

static void dump_hex(unsigned int *data, int from, int to)
{
	unsigned offset, print_offset = 1, col = 0;

	from /= 4;
	to = (to + 3) / 4;

	for (offset = from; offset < to; offset++) {
		if (print_offset) {
			printf("%04x: ", offset * 8);
			print_offset = 0;
		}
		printf("%08x", data[offset]);
		col++;
		if ((col & 3) == 0) {
			printf("\n");
			print_offset = 1;
		} else {
			printf(" ");
		}
	}

	if (!print_offset)
		printf("\n");
}

static void dump_attribute_info(void *reply, unsigned int size)
{
	struct fsinfo_attribute_info *attr_info = reply;
	const struct fsinfo_attribute *attr;
	char type[32], val_size[32];

	switch (attr_info->type) {
	case FSINFO_TYPE_VSTRUCT:	strcpy(type, "V-STRUCT");	break;
	case FSINFO_TYPE_STRING:	strcpy(type, "STRING");		break;
	case FSINFO_TYPE_OPAQUE:	strcpy(type, "OPAQUE");		break;
	case FSINFO_TYPE_LIST:		strcpy(type, "LIST");		break;
	default:
		sprintf(type, "type-%x", attr_info->type);
		break;
	}

	if (attr_info->flags & FSINFO_FLAGS_N)
		strcat(type, " x N");
	else if (attr_info->flags & FSINFO_FLAGS_NM)
		strcat(type, " x NM");

	for (attr = fsinfo_attributes; attr->name; attr++)
		if (attr->attr_id == attr_info->attr_id)
			break;

	if (attr_info->size)
		sprintf(val_size, "%u", attr_info->size);
	else
		strcpy(val_size, "-");

	printf("%8x %-12s %08x %5s %s\n",
	       attr_info->attr_id,
	       type,
	       attr_info->flags,
	       val_size,
	       attr->name ? attr->name : "");
}

static void dump_fsinfo_generic_statfs(void *reply, unsigned int size)
{
	struct fsinfo_statfs *f = reply;

	printf("\n");
	printf("\tblocks       : n=%llu fr=%llu av=%llu\n",
	       (unsigned long long)f->f_blocks.lo,
	       (unsigned long long)f->f_bfree.lo,
	       (unsigned long long)f->f_bavail.lo);

	printf("\tfiles        : n=%llu fr=%llu av=%llu\n",
	       (unsigned long long)f->f_files.lo,
	       (unsigned long long)f->f_ffree.lo,
	       (unsigned long long)f->f_favail.lo);
	printf("\tbsize        : %llu\n", f->f_bsize);
	printf("\tfrsize       : %llu\n", f->f_frsize);
}

static void dump_fsinfo_generic_ids(void *reply, unsigned int size)
{
	struct fsinfo_ids *f = reply;

	printf("\n");
	printf("\tdev          : %02x:%02x\n", f->f_dev_major, f->f_dev_minor);
	printf("\tfs           : type=%x name=%s\n", f->f_fstype, f->f_fs_name);
	printf("\tfsid         : %llx\n", (unsigned long long)f->f_fsid);
	printf("\tsbid         : %llx\n", (unsigned long long)f->f_sb_id);
}

static void dump_fsinfo_generic_limits(void *reply, unsigned int size)
{
	struct fsinfo_limits *f = reply;

	printf("\n");
	printf("\tmax file size: %llx%016llx\n",
	       (unsigned long long)f->max_file_size.hi,
	       (unsigned long long)f->max_file_size.lo);
	printf("\tmax ino      : %llx%016llx\n",
	       (unsigned long long)f->max_ino.hi,
	       (unsigned long long)f->max_ino.lo);
	printf("\tmax ids      : u=%llx g=%llx p=%llx\n",
	       (unsigned long long)f->max_uid,
	       (unsigned long long)f->max_gid,
	       (unsigned long long)f->max_projid);
	printf("\tmax dev      : maj=%x min=%x\n",
	       f->max_dev_major, f->max_dev_minor);
	printf("\tmax links    : %llx\n",
	       (unsigned long long)f->max_hard_links);
	printf("\tmax xattr    : n=%x b=%llx\n",
	       f->max_xattr_name_len,
	       (unsigned long long)f->max_xattr_body_len);
	printf("\tmax len      : file=%x sym=%x\n",
	       f->max_filename_len, f->max_symlink_len);
}

static void dump_fsinfo_generic_supports(void *reply, unsigned int size)
{
	struct fsinfo_supports *f = reply;

	printf("\n");
	printf("\tstx_attr     : %llx\n", (unsigned long long)f->stx_attributes);
	printf("\tstx_mask     : %x\n", f->stx_mask);
	printf("\tfs_ioc_*flags: get=%x set=%x clr=%x\n",
	       f->fs_ioc_getflags, f->fs_ioc_setflags_set, f->fs_ioc_setflags_clear);
	printf("\twin_fattrs   : %x\n", f->win_file_attrs);
}

#define FSINFO_FEATURE_NAME(C) [FSINFO_FEAT_##C] = #C
static const char *fsinfo_feature_names[FSINFO_FEAT__NR] = {
	FSINFO_FEATURE_NAME(IS_KERNEL_FS),
	FSINFO_FEATURE_NAME(IS_BLOCK_FS),
	FSINFO_FEATURE_NAME(IS_FLASH_FS),
	FSINFO_FEATURE_NAME(IS_NETWORK_FS),
	FSINFO_FEATURE_NAME(IS_AUTOMOUNTER_FS),
	FSINFO_FEATURE_NAME(IS_MEMORY_FS),
	FSINFO_FEATURE_NAME(AUTOMOUNTS),
	FSINFO_FEATURE_NAME(ADV_LOCKS),
	FSINFO_FEATURE_NAME(MAND_LOCKS),
	FSINFO_FEATURE_NAME(LEASES),
	FSINFO_FEATURE_NAME(UIDS),
	FSINFO_FEATURE_NAME(GIDS),
	FSINFO_FEATURE_NAME(PROJIDS),
	FSINFO_FEATURE_NAME(STRING_USER_IDS),
	FSINFO_FEATURE_NAME(GUID_USER_IDS),
	FSINFO_FEATURE_NAME(WINDOWS_ATTRS),
	FSINFO_FEATURE_NAME(USER_QUOTAS),
	FSINFO_FEATURE_NAME(GROUP_QUOTAS),
	FSINFO_FEATURE_NAME(PROJECT_QUOTAS),
	FSINFO_FEATURE_NAME(XATTRS),
	FSINFO_FEATURE_NAME(JOURNAL),
	FSINFO_FEATURE_NAME(DATA_IS_JOURNALLED),
	FSINFO_FEATURE_NAME(O_SYNC),
	FSINFO_FEATURE_NAME(O_DIRECT),
	FSINFO_FEATURE_NAME(VOLUME_ID),
	FSINFO_FEATURE_NAME(VOLUME_UUID),
	FSINFO_FEATURE_NAME(VOLUME_NAME),
	FSINFO_FEATURE_NAME(VOLUME_FSID),
	FSINFO_FEATURE_NAME(IVER_ALL_CHANGE),
	FSINFO_FEATURE_NAME(IVER_DATA_CHANGE),
	FSINFO_FEATURE_NAME(IVER_MONO_INCR),
	FSINFO_FEATURE_NAME(DIRECTORIES),
	FSINFO_FEATURE_NAME(SYMLINKS),
	FSINFO_FEATURE_NAME(HARD_LINKS),
	FSINFO_FEATURE_NAME(HARD_LINKS_1DIR),
	FSINFO_FEATURE_NAME(DEVICE_FILES),
	FSINFO_FEATURE_NAME(UNIX_SPECIALS),
	FSINFO_FEATURE_NAME(RESOURCE_FORKS),
	FSINFO_FEATURE_NAME(NAME_CASE_INDEP),
	FSINFO_FEATURE_NAME(NAME_NON_UTF8),
	FSINFO_FEATURE_NAME(NAME_HAS_CODEPAGE),
	FSINFO_FEATURE_NAME(SPARSE),
	FSINFO_FEATURE_NAME(NOT_PERSISTENT),
	FSINFO_FEATURE_NAME(NO_UNIX_MODE),
	FSINFO_FEATURE_NAME(HAS_ATIME),
	FSINFO_FEATURE_NAME(HAS_BTIME),
	FSINFO_FEATURE_NAME(HAS_CTIME),
	FSINFO_FEATURE_NAME(HAS_MTIME),
	FSINFO_FEATURE_NAME(HAS_ACL),
	FSINFO_FEATURE_NAME(HAS_INODE_NUMBERS),
};

static void dump_fsinfo_generic_features(void *reply, unsigned int size)
{
	struct fsinfo_features *f = reply;
	int i;

	printf("\n\t");
	for (i = 0; i < sizeof(f->features); i++)
		printf("%02x", f->features[i]);
	printf(" (nr=%u)\n", f->nr_features);
	for (i = 0; i < FSINFO_FEAT__NR; i++)
		if (f->features[i / 8] & (1 << (i % 8)))
			printf("\t- %s\n", fsinfo_feature_names[i]);
}

static void print_time(struct fsinfo_timestamp_one *t, char stamp)
{
	printf("\t%ctime       : gran=%gs range=%llx-%llx\n",
	       stamp,
	       t->gran_mantissa * pow(10., t->gran_exponent),
	       (long long)t->minimum,
	       (long long)t->maximum);
}

static void dump_fsinfo_generic_timestamp_info(void *reply, unsigned int size)
{
	struct fsinfo_timestamp_info *f = reply;

	printf("\n");
	print_time(&f->atime, 'a');
	print_time(&f->mtime, 'm');
	print_time(&f->ctime, 'c');
	print_time(&f->btime, 'b');
}

static void dump_fsinfo_generic_volume_uuid(void *reply, unsigned int size)
{
	struct fsinfo_volume_uuid *f = reply;

	printf("%02x%02x%02x%02x-%02x%02x-%02x%02x-%02x%02x"
	       "-%02x%02x%02x%02x%02x%02x\n",
	       f->uuid[ 0], f->uuid[ 1],
	       f->uuid[ 2], f->uuid[ 3],
	       f->uuid[ 4], f->uuid[ 5],
	       f->uuid[ 6], f->uuid[ 7],
	       f->uuid[ 8], f->uuid[ 9],
	       f->uuid[10], f->uuid[11],
	       f->uuid[12], f->uuid[13],
	       f->uuid[14], f->uuid[15]);
}

static void dump_fsinfo_generic_mount_info(void *reply, unsigned int size)
{
	struct fsinfo_mount_info *r = reply;

	printf("\n");
	printf("\tsb_uniq : %llx\n", (unsigned long long)r->sb_unique_id);
	printf("\tmnt_uniq: %llx\n", (unsigned long long)r->mnt_unique_id);
	printf("\tmnt_id  : %x\n", r->mnt_id);
	printf("\tparent  : %x\n", r->parent_id);
	printf("\tgroup   : %x\n", r->group_id);
	printf("\tattr    : %x\n", r->attr);
	printf("\tpropag  : %x\n", r->propagation);
	printf("\tsb_nfy  : changes=%u other=%u\n", r->sb_changes, r->sb_notifications);
	printf("\tmnt_nfy : attr=%u topology=%u subtree=%u\n",
	       r->mnt_attr_changes, r->mnt_topology_changes, r->mnt_subtree_notifications);
}

static void dump_fsinfo_generic_mount_child(void *reply, unsigned int size)
{
	struct fsinfo_mount_child *r = reply;
	ssize_t mplen;
	char path[32], *mp;

	struct fsinfo_params params = {
		.flags		= FSINFO_FLAGS_QUERY_MOUNT,
		.request	= FSINFO_ATTR_MOUNT_POINT,
	};

	if (!list_last) {
		sprintf(path, "%u", r->mnt_id);
		mplen = get_fsinfo(path, "FSINFO_ATTR_MOUNT_POINT", &params, (void **)&mp);
		if (mplen < 0)
			mp = "-";
	} else {
		mp = "<this>";
	}

	printf("%8x %16llx %10u %s\n",
	       r->mnt_id, (unsigned long long)r->mnt_unique_id, r->notify_sum, mp);
}

static void dump_afs_fsinfo_server_address(void *reply, unsigned int size)
{
	struct fsinfo_afs_server_address *f = reply;
	struct sockaddr_storage *ss = (struct sockaddr_storage *)&f->address;
	struct sockaddr_rxrpc *srx;
	struct sockaddr_in6 *sin6;
	struct sockaddr_in *sin;
	char proto[32], buf[1024];

	if (ss->ss_family == AF_RXRPC) {
		srx = (struct sockaddr_rxrpc *)ss;
		printf("%5u ", srx->srx_service);
		switch (srx->transport_type) {
		case SOCK_DGRAM:
			sprintf(proto, "udp");
			break;
		case SOCK_STREAM:
			sprintf(proto, "tcp");
			break;
		default:
			sprintf(proto, "%3u", srx->transport_type);
			break;
		}
		ss = (struct sockaddr_storage *)&srx->transport;
	}

	switch (ss->ss_family) {
	case AF_INET:
		sin = (struct sockaddr_in *)ss;
		if (!inet_ntop(AF_INET, &sin->sin_addr, buf, sizeof(buf)))
			break;
		printf("%5u/%s %s\n", ntohs(sin->sin_port), proto, buf);
		return;
	case AF_INET6:
		sin6 = (struct sockaddr_in6 *)ss;
		if (!inet_ntop(AF_INET6, &sin6->sin6_addr, buf, sizeof(buf)))
			break;
		printf("%5u/%s %s\n", ntohs(sin6->sin6_port), proto, buf);
		return;
	}

	printf("family=%u\n", ss->ss_family);
}

static char *dump_ext4_time(char *buffer, time_t tim)
{
	struct tm tm;
	int len;

	if (tim == 0)
		return "-";

	if (!localtime_r(&tim, &tm)) {
		perror("localtime_r");
		exit(1);
	}
	len = strftime(buffer, 100, "%F %T", &tm);
	if (len == 0) {
		perror("strftime");
		exit(1);
	}
	return buffer;
}

static void dump_ext4_fsinfo_timestamps(void *reply, unsigned int size)
{
	struct fsinfo_ext4_timestamps *r = reply;
	char buffer[100];

	printf("\n");
	printf("\tmkfs    : %s\n", dump_ext4_time(buffer, r->mkfs_time));
	printf("\tmount   : %s\n", dump_ext4_time(buffer, r->mount_time));
	printf("\twrite   : %s\n", dump_ext4_time(buffer, r->write_time));
	printf("\tfsck    : %s\n", dump_ext4_time(buffer, r->last_check_time));
	printf("\t1st-err : %s\n", dump_ext4_time(buffer, r->first_error_time));
	printf("\tlast-err: %s\n", dump_ext4_time(buffer, r->last_error_time));
}

static void dump_string(void *reply, unsigned int size)
{
	char *s = reply, *p;
	bool nl = false, last_nl = false;

	p = s;
	if (size >= 4096) {
		size = 4096;
		p[4092] = '.';
		p[4093] = '.';
		p[4094] = '.';
		p[4095] = 0;
	} else {
		p[size] = 0;
	}

	for (p = s; *p; p++) {
		if (*p == '\n') {
			last_nl = nl = true;
			continue;
		}
		last_nl = false;
		if (!isprint(*p) && *p != '\t')
			*p = '?';
	}

	if (nl)
		putchar('\n');
	printf("%s", s);
	if (!last_nl)
		putchar('\n');
}

#define dump_fsinfo_meta_attribute_info		(void *)0x123
#define dump_fsinfo_meta_attributes		(void *)0x123

/*
 *
 */
#define __FSINFO(A, T, S, G, F, N)					\
	{ .attr_id = A, .type = T, .size = S, .name = N, .dump = dump_##G }

#define _FSINFO(A,T,S,G,N)	__FSINFO(A, T, S, G, 0, N)
#define _FSINFO_N(A,T,S,G,N)	__FSINFO(A, T, S, G, FSINFO_FLAGS_N, N)
#define _FSINFO_NM(A,T,S,G,N)	__FSINFO(A, T, S, G, FSINFO_FLAGS_NM, N)

#define _FSINFO_VSTRUCT(A,S,G,N)    _FSINFO   (A, FSINFO_TYPE_VSTRUCT, sizeof(S), G, N)
#define _FSINFO_VSTRUCT_N(A,S,G,N)  _FSINFO_N (A, FSINFO_TYPE_VSTRUCT, sizeof(S), G, N)
#define _FSINFO_VSTRUCT_NM(A,S,G,N) _FSINFO_NM(A, FSINFO_TYPE_VSTRUCT, sizeof(S), G, N)

#define FSINFO_VSTRUCT(A,G)	_FSINFO_VSTRUCT   (A, A##__STRUCT, G, #A)
#define FSINFO_VSTRUCT_N(A,G)	_FSINFO_VSTRUCT_N (A, A##__STRUCT, G, #A)
#define FSINFO_VSTRUCT_NM(A,G)	_FSINFO_VSTRUCT_NM(A, A##__STRUCT, G, #A)
#define FSINFO_STRING(A,G)	_FSINFO   (A, FSINFO_TYPE_STRING, 0, G, #A)
#define FSINFO_STRING_N(A,G)	_FSINFO_N (A, FSINFO_TYPE_STRING, 0, G, #A)
#define FSINFO_STRING_NM(A,G)	_FSINFO_NM(A, FSINFO_TYPE_STRING, 0, G, #A)
#define FSINFO_OPAQUE(A,G)	_FSINFO   (A, FSINFO_TYPE_OPAQUE, 0, G, #A)
#define FSINFO_LIST(A,G)	_FSINFO   (A, FSINFO_TYPE_LIST, sizeof(A##__STRUCT), G, #A)
#define FSINFO_LIST_N(A,G)	_FSINFO_N (A, FSINFO_TYPE_LIST, sizeof(A##__STRUCT), G, #A)

static const struct fsinfo_attribute fsinfo_attributes[] = {
	FSINFO_VSTRUCT	(FSINFO_ATTR_STATFS,		fsinfo_generic_statfs),
	FSINFO_VSTRUCT	(FSINFO_ATTR_IDS,		fsinfo_generic_ids),
	FSINFO_VSTRUCT	(FSINFO_ATTR_LIMITS,		fsinfo_generic_limits),
	FSINFO_VSTRUCT	(FSINFO_ATTR_SUPPORTS,		fsinfo_generic_supports),
	FSINFO_VSTRUCT	(FSINFO_ATTR_FEATURES,		fsinfo_generic_features),
	FSINFO_VSTRUCT	(FSINFO_ATTR_TIMESTAMP_INFO,	fsinfo_generic_timestamp_info),
	FSINFO_STRING	(FSINFO_ATTR_VOLUME_ID,		string),
	FSINFO_VSTRUCT	(FSINFO_ATTR_VOLUME_UUID,	fsinfo_generic_volume_uuid),
	FSINFO_STRING	(FSINFO_ATTR_VOLUME_NAME,	string),
	FSINFO_STRING	(FSINFO_ATTR_SOURCE,		string),
	FSINFO_STRING	(FSINFO_ATTR_CONFIGURATION,	string),
	FSINFO_STRING	(FSINFO_ATTR_FS_STATISTICS,	string),

	FSINFO_VSTRUCT_N(FSINFO_ATTR_FSINFO_ATTRIBUTE_INFO, fsinfo_meta_attribute_info),
	FSINFO_LIST	(FSINFO_ATTR_FSINFO_ATTRIBUTES,	fsinfo_meta_attributes),

	FSINFO_VSTRUCT	(FSINFO_ATTR_MOUNT_INFO,	fsinfo_generic_mount_info),
	FSINFO_STRING	(FSINFO_ATTR_MOUNT_PATH,	string),
	FSINFO_STRING_N	(FSINFO_ATTR_MOUNT_POINT,	string),
	FSINFO_STRING_N	(FSINFO_ATTR_MOUNT_POINT_FULL,	string),
	FSINFO_LIST	(FSINFO_ATTR_MOUNT_CHILDREN,	fsinfo_generic_mount_child),

	FSINFO_STRING	(FSINFO_ATTR_AFS_CELL_NAME,	string),
	FSINFO_STRING	(FSINFO_ATTR_AFS_SERVER_NAME,	string),
	FSINFO_LIST_N	(FSINFO_ATTR_AFS_SERVER_ADDRESSES, afs_fsinfo_server_address),
	FSINFO_VSTRUCT	(FSINFO_ATTR_EXT4_TIMESTAMPS,	ext4_fsinfo_timestamps),
	{}
};

static void dump_value(unsigned int attr_id,
		       const struct fsinfo_attribute *attr,
		       const struct fsinfo_attribute_info *attr_info,
		       void *reply, unsigned int size)
{
	if (!attr || !attr->dump) {
		printf("<no dumper>\n");
		return;
	}

	if (attr->type == FSINFO_TYPE_VSTRUCT && size < attr->size) {
		printf("<short data %u/%u>\n", size, attr->size);
		return;
	}

	attr->dump(reply, size);
}

static void dump_list(unsigned int attr_id,
		      const struct fsinfo_attribute *attr,
		      const struct fsinfo_attribute_info *attr_info,
		      void *reply, unsigned int size)
{
	size_t elem_size = attr_info->size;
	unsigned int ix = 0;

	printf("\n");
	if (!attr || !attr->dump) {
		printf("<no dumper>\n");
		return;
	}

	if (attr->type == FSINFO_TYPE_VSTRUCT && size < attr->size) {
		printf("<short data %u/%u>\n", size, attr->size);
		return;
	}

	list_last = false;
	while (size >= elem_size) {
		printf("\t[%02x] ", ix);
		if (size == elem_size)
			list_last = true;
		attr->dump(reply, size);
		reply += elem_size;
		size -= elem_size;
		ix++;
	}
}

/*
 * Call fsinfo, expanding the buffer as necessary.
 */
static ssize_t get_fsinfo(const char *file, const char *name,
			  struct fsinfo_params *params, void **_r)
{
	ssize_t ret;
	size_t buf_size = 4096;
	void *r;

	for (;;) {
		r = malloc(buf_size);
		if (!r) {
			perror("malloc");
			exit(1);
		}
		memset(r, 0xbd, buf_size);

		errno = 0;
		ret = fsinfo(AT_FDCWD, file, params, sizeof(*params), r, buf_size - 1);
		if (ret == -1)
			goto error;

		if (ret <= buf_size - 1)
			break;
		buf_size = (ret + 4096 - 1) & ~(4096 - 1);
	}

	if (debug)
		printf("fsinfo(%s,%s,%u,%u) = %zd\n",
		       file, name, params->Nth, params->Mth, ret);

	((char *)r)[ret] = 0;
	*_r = r;
	return ret;

error:
	*_r = NULL;
	free(r);
	if (debug)
		printf("fsinfo(%s,%s,%u,%u) = %m\n",
		       file, name, params->Nth, params->Mth);
	return ret;
}

/*
 * Try one subinstance of an attribute.
 */
static int try_one(const char *file, struct fsinfo_params *params,
		   const struct fsinfo_attribute_info *attr_info, bool raw)
{
	const struct fsinfo_attribute *attr;
	const char *name;
	size_t size = 4096;
	char namebuf[32];
	void *r;

	for (attr = fsinfo_attributes; attr->name; attr++) {
		if (attr->attr_id == params->request) {
			name = attr->name;
			if (strncmp(name, "fsinfo_generic_", 15) == 0)
				name += 15;
			goto found;
		}
	}

	sprintf(namebuf, "<unknown-%x>", params->request);
	name = namebuf;
	attr = NULL;

found:
	size = get_fsinfo(file, name, params, &r);

	if (size == -1) {
		if (errno == ENODATA) {
			if (!(attr_info->flags & (FSINFO_FLAGS_N | FSINFO_FLAGS_NM)) &&
			    params->Nth == 0 && params->Mth == 0) {
				fprintf(stderr,
					"Unexpected ENODATA (0x%x{%u}{%u})\n",
					params->request, params->Nth, params->Mth);
				exit(1);
			}
			free(r);
			return (params->Mth == 0) ? 2 : 1;
		}
		if (errno == EOPNOTSUPP) {
			if (params->Nth > 0 || params->Mth > 0) {
				fprintf(stderr,
					"Should return -ENODATA (0x%x{%u}{%u})\n",
					params->request, params->Nth, params->Mth);
				exit(1);
			}
			//printf("\e[33m%s\e[m: <not supported>\n",
			//       fsinfo_attr_names[attr]);
			free(r);
			return 2;
		}
		perror(file);
		exit(1);
	}

	if (raw) {
		if (size > 4096)
			size = 4096;
		dump_hex(r, 0, size);
		free(r);
		return 0;
	}

	switch (attr_info->flags & (FSINFO_FLAGS_N | FSINFO_FLAGS_NM)) {
	case 0:
		printf("\e[33m%s\e[m: ", name);
		break;
	case FSINFO_FLAGS_N:
		printf("\e[33m%s{%u}\e[m: ", name, params->Nth);
		break;
	case FSINFO_FLAGS_NM:
		printf("\e[33m%s{%u,%u}\e[m: ", name, params->Nth, params->Mth);
		break;
	}

	switch (attr_info->type) {
	case FSINFO_TYPE_VSTRUCT:
	case FSINFO_TYPE_STRING:
		dump_value(params->request, attr, attr_info, r, size);
		free(r);
		return 0;

	case FSINFO_TYPE_LIST:
		dump_list(params->request, attr, attr_info, r, size);
		free(r);
		return 0;

	case FSINFO_TYPE_OPAQUE:
		free(r);
		return 0;

	default:
		fprintf(stderr, "Fishy about %u 0x%x,%x,%x\n",
			params->request, attr_info->type, attr_info->flags, attr_info->size);
		exit(1);
	}
}

static int cmp_u32(const void *a, const void *b)
{
	return *(const int *)a - *(const int *)b;
}

/*
 *
 */
int main(int argc, char **argv)
{
	struct fsinfo_attribute_info attr_info;
	struct fsinfo_params params = {
		.resolve_flags	= RESOLVE_NO_TRAILING_SYMLINKS,
		.flags		= FSINFO_FLAGS_QUERY_PATH,
	};
	unsigned int *attrs, ret, nr, i;
	bool meta = false;
	int raw = 0, opt, Nth, Mth;

	while ((opt = getopt(argc, argv, "Madmlr"))) {
		switch (opt) {
		case 'M':
			meta = true;
			continue;
		case 'a':
			params.resolve_flags |= RESOLVE_NO_TRAILING_AUTOMOUNTS;
			params.flags = FSINFO_FLAGS_QUERY_PATH;
			continue;
		case 'd':
			debug = true;
			continue;
		case 'l':
			params.resolve_flags &= ~RESOLVE_NO_TRAILING_SYMLINKS;
			params.flags = FSINFO_FLAGS_QUERY_PATH;
			continue;
		case 'm':
			params.resolve_flags = 0;
			params.flags = FSINFO_FLAGS_QUERY_MOUNT;
			continue;
		case 'r':
			raw = 1;
			continue;
		}
		break;
	}

	argc -= optind;
	argv += optind;

	if (argc != 1) {
		printf("Format: test-fsinfo [-Madlr] <path>\n");
		printf("Format: test-fsinfo [-Mdr] -m <mnt_id>\n");
		exit(2);
	}

	/* Retrieve a list of supported attribute IDs */
	params.request = FSINFO_ATTR_FSINFO_ATTRIBUTES;
	params.Nth = 0;
	params.Mth = 0;
	ret = get_fsinfo(argv[0], "attributes", &params, (void **)&attrs);
	if (ret == -1) {
		fprintf(stderr, "Unable to get attribute list: %m\n");
		exit(1);
	}

	if (ret % sizeof(attrs[0])) {
		fprintf(stderr, "Bad length of attribute list (0x%x)\n", ret);
		exit(2);
	}

	nr = ret / sizeof(attrs[0]);
	qsort(attrs, nr, sizeof(attrs[0]), cmp_u32);

	if (meta) {
		printf("ATTR ID  TYPE         FLAGS    SIZE  NAME\n");
		printf("======== ============ ======== ===== =========\n");
		for (i = 0; i < nr; i++) {
			params.request = FSINFO_ATTR_FSINFO_ATTRIBUTE_INFO;
			params.Nth = attrs[i];
			params.Mth = 0;
			ret = fsinfo(AT_FDCWD, argv[0],
				     &params, sizeof(params),
				     &attr_info, sizeof(attr_info));
			if (ret == -1) {
				fprintf(stderr, "Can't get info for attribute %x: %m\n", attrs[i]);
				exit(1);
			}

			dump_attribute_info(&attr_info, ret);
		}
		exit(0);
	}

	for (i = 0; i < nr; i++) {
		params.request = FSINFO_ATTR_FSINFO_ATTRIBUTE_INFO;
		params.Nth = attrs[i];
		params.Mth = 0;
		ret = fsinfo(AT_FDCWD, argv[0],
			     &params, sizeof(params),
			     &attr_info, sizeof(attr_info));
		if (ret == -1) {
			fprintf(stderr, "Can't get info for attribute %x: %m\n", attrs[i]);
			exit(1);
		}

		if (attrs[i] == FSINFO_ATTR_FSINFO_ATTRIBUTE_INFO ||
		    attrs[i] == FSINFO_ATTR_FSINFO_ATTRIBUTES)
			continue;

		if (attrs[i] != attr_info.attr_id) {
			fprintf(stderr, "ID for %03x returned %03x\n",
				attrs[i], attr_info.attr_id);
			break;
		}
		Nth = 0;
		do {
			Mth = 0;
			do {
				params.request = attrs[i];
				params.Nth = Nth;
				params.Mth = Mth;

				switch (try_one(argv[0], &params, &attr_info, raw)) {
				case 0:
					continue;
				case 1:
					goto done_M;
				case 2:
					goto done_N;
				}
			} while (++Mth < 100);

		done_M:
			if (Mth >= 100) {
				fprintf(stderr, "Fishy: Mth %x[%u][%u]\n", attrs[i], Nth, Mth);
				break;
			}

		} while (++Nth < 100);

	done_N:
		if (Nth >= 100) {
			fprintf(stderr, "Fishy: Nth %x[%u]\n", attrs[i], Nth);
			break;
		}
	}

	return 0;
}
