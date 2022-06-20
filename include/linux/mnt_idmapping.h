/* SPDX-License-Identifier: GPL-2.0 */
#ifndef _LINUX_MNT_IDMAPPING_H
#define _LINUX_MNT_IDMAPPING_H

#include <linux/types.h>
#include <linux/uidgid.h>

struct user_namespace;
/*
 * Carries the initial idmapping of 0:0:4294967295 which is an identity
 * mapping. This means that {g,u}id 0 is mapped to {g,u}id 0, {g,u}id 1 is
 * mapped to {g,u}id 1, [...], {g,u}id 1000 to {g,u}id 1000, [...].
 */
extern struct user_namespace init_user_ns;

typedef struct {
	uid_t val;
} kmntuid_t;

typedef struct {
	gid_t val;
} kmntgid_t;

static_assert(sizeof(kmntuid_t) == sizeof(kuid_t));
static_assert(sizeof(kmntgid_t) == sizeof(kgid_t));
static_assert(offsetof(kmntuid_t, val) == offsetof(kuid_t, val));
static_assert(offsetof(kmntgid_t, val) == offsetof(kgid_t, val));

#ifdef CONFIG_MULTIUSER
static inline uid_t __kmntuid_val(kmntuid_t uid)
{
	return uid.val;
}

static inline gid_t __kmntgid_val(kmntgid_t gid)
{
	return gid.val;
}
#else
static inline uid_t __kmntuid_val(kmntuid_t uid)
{
	return 0;
}

static inline gid_t __kmntgid_val(kmntgid_t gid)
{
	return 0;
}
#endif

static inline bool kmntuid_valid(kmntuid_t uid)
{
	return __kmntuid_val(uid) != (uid_t) -1;
}

static inline bool kmntgid_valid(kmntgid_t gid)
{
	return __kmntgid_val(gid) != (gid_t) -1;
}

/**
 * kuid_eq_kmntuid - check whether kuid and kmntuid have the same value
 * @kuid: the kuid to compare
 * @kmntuid: the kmntuid to compare
 *
 * Check whether @kuid and @kmntuid have the same values.
 *
 * Return: true if @kuid and @kmntuid have the same value, false if not.
 */
static inline bool kuid_eq_kmntuid(kuid_t kuid, kmntuid_t kmntuid)
{
	return __kmntuid_val(kmntuid) == __kuid_val(kuid);
}

/**
 * kgid_eq_kmntgid - check whether kgid and kmntgid have the same value
 * @kgid: the kgid to compare
 * @kmntgid: the kmntgid to compare
 *
 * Check whether @kgid and @kmntgid have the same values.
 *
 * Return: true if @kgid and @kmntgid have the same value, false if not.
 */
static inline bool kgid_eq_kmntgid(kgid_t kgid, kmntgid_t kmntgid)
{
	return __kmntgid_val(kmntgid) == __kgid_val(kgid);
}

static inline bool kmntuid_eq(kmntuid_t left, kmntuid_t right)
{
	return __kmntuid_val(left) == __kmntuid_val(right);
}

static inline bool kmntgid_eq(kmntgid_t left, kmntgid_t right)
{
	return __kmntgid_val(left) == __kmntgid_val(right);
}

/*
 * kmnt{g,u}ids are created from k{g,u}ids.
 * We don't allow them to be created from regular {u,g}id.
 */
#define KMNTUIDT_INIT(val) (kmntuid_t){ __kuid_val(val) }
#define KMNTGIDT_INIT(val) (kmntgid_t){ __kgid_val(val) }

#define INVALID_KMNTUID KMNTUIDT_INIT(INVALID_UID)
#define INVALID_KMNTGID KMNTGIDT_INIT(INVALID_GID)

/*
 * Allow a kmnt{g,u}id to be used as a k{g,u}id where we want to compare
 * whether the mapped value is identical to value of a k{g,u}id.
 */
#define AS_KUIDT(val) (kuid_t){ __kmntuid_val(val) }
#define AS_KGIDT(val) (kgid_t){ __kmntgid_val(val) }

#ifdef CONFIG_MULTIUSER
/**
 * kmntgid_in_group_p() - check whether a kmntuid matches the caller's groups
 * @kmntgid: the mnt gid to match
 *
 * This function can be used to determine whether @kmntuid matches any of the
 * caller's groups.
 *
 * Return: 1 if kmntuid matches caller's groups, 0 if not.
 */
static inline int kmntgid_in_group_p(kmntgid_t kmntgid)
{
	return in_group_p(AS_KGIDT(kmntgid));
}
#else
static inline int kmntgid_in_group_p(kmntgid_t kmntgid)
{
	return 1;
}
#endif

/**
 * initial_idmapping - check whether this is the initial mapping
 * @ns: idmapping to check
 *
 * Check whether this is the initial mapping, mapping 0 to 0, 1 to 1,
 * [...], 1000 to 1000 [...].
 *
 * Return: true if this is the initial mapping, false if not.
 */
static inline bool initial_idmapping(const struct user_namespace *ns)
{
	return ns == &init_user_ns;
}

/**
 * no_idmapping - check whether we can skip remapping a kuid/gid
 * @mnt_userns: the mount's idmapping
 * @fs_userns: the filesystem's idmapping
 *
 * This function can be used to check whether a remapping between two
 * idmappings is required.
 * An idmapped mount is a mount that has an idmapping attached to it that
 * is different from the filsystem's idmapping and the initial idmapping.
 * If the initial mapping is used or the idmapping of the mount and the
 * filesystem are identical no remapping is required.
 *
 * Return: true if remapping can be skipped, false if not.
 */
static inline bool no_idmapping(const struct user_namespace *mnt_userns,
				const struct user_namespace *fs_userns)
{
	return initial_idmapping(mnt_userns) || mnt_userns == fs_userns;
}

/**
 * mapped_kuid_fs - map a filesystem kuid into a mnt_userns
 * @mnt_userns: the mount's idmapping
 * @fs_userns: the filesystem's idmapping
 * @kuid : kuid to be mapped
 *
 * Take a @kuid and remap it from @fs_userns into @mnt_userns. Use this
 * function when preparing a @kuid to be reported to userspace.
 *
 * If no_idmapping() determines that this is not an idmapped mount we can
 * simply return @kuid unchanged.
 * If initial_idmapping() tells us that the filesystem is not mounted with an
 * idmapping we know the value of @kuid won't change when calling
 * from_kuid() so we can simply retrieve the value via __kuid_val()
 * directly.
 *
 * Return: @kuid mapped according to @mnt_userns.
 * If @kuid has no mapping in either @mnt_userns or @fs_userns INVALID_UID is
 * returned.
 */
static inline kuid_t mapped_kuid_fs(struct user_namespace *mnt_userns,
				    struct user_namespace *fs_userns,
				    kuid_t kuid)
{
	uid_t uid;

	if (no_idmapping(mnt_userns, fs_userns))
		return kuid;
	if (initial_idmapping(fs_userns))
		uid = __kuid_val(kuid);
	else
		uid = from_kuid(fs_userns, kuid);
	if (uid == (uid_t)-1)
		return INVALID_UID;
	return make_kuid(mnt_userns, uid);
}

/**
 * mapped_kgid_fs - map a filesystem kgid into a mnt_userns
 * @mnt_userns: the mount's idmapping
 * @fs_userns: the filesystem's idmapping
 * @kgid : kgid to be mapped
 *
 * Take a @kgid and remap it from @fs_userns into @mnt_userns. Use this
 * function when preparing a @kgid to be reported to userspace.
 *
 * If no_idmapping() determines that this is not an idmapped mount we can
 * simply return @kgid unchanged.
 * If initial_idmapping() tells us that the filesystem is not mounted with an
 * idmapping we know the value of @kgid won't change when calling
 * from_kgid() so we can simply retrieve the value via __kgid_val()
 * directly.
 *
 * Return: @kgid mapped according to @mnt_userns.
 * If @kgid has no mapping in either @mnt_userns or @fs_userns INVALID_GID is
 * returned.
 */
static inline kgid_t mapped_kgid_fs(struct user_namespace *mnt_userns,
				    struct user_namespace *fs_userns,
				    kgid_t kgid)
{
	gid_t gid;

	if (no_idmapping(mnt_userns, fs_userns))
		return kgid;
	if (initial_idmapping(fs_userns))
		gid = __kgid_val(kgid);
	else
		gid = from_kgid(fs_userns, kgid);
	if (gid == (gid_t)-1)
		return INVALID_GID;
	return make_kgid(mnt_userns, gid);
}

/**
 * mapped_kuid_user - map a user kuid into a mnt_userns
 * @mnt_userns: the mount's idmapping
 * @fs_userns: the filesystem's idmapping
 * @kuid : kuid to be mapped
 *
 * Use the idmapping of @mnt_userns to remap a @kuid into @fs_userns. Use this
 * function when preparing a @kuid to be written to disk or inode.
 *
 * If no_idmapping() determines that this is not an idmapped mount we can
 * simply return @kuid unchanged.
 * If initial_idmapping() tells us that the filesystem is not mounted with an
 * idmapping we know the value of @kuid won't change when calling
 * make_kuid() so we can simply retrieve the value via KUIDT_INIT()
 * directly.
 *
 * Return: @kuid mapped according to @mnt_userns.
 * If @kuid has no mapping in either @mnt_userns or @fs_userns INVALID_UID is
 * returned.
 */
static inline kuid_t mapped_kuid_user(struct user_namespace *mnt_userns,
				      struct user_namespace *fs_userns,
				      kuid_t kuid)
{
	uid_t uid;

	if (no_idmapping(mnt_userns, fs_userns))
		return kuid;
	uid = from_kuid(mnt_userns, kuid);
	if (uid == (uid_t)-1)
		return INVALID_UID;
	if (initial_idmapping(fs_userns))
		return KUIDT_INIT(uid);
	return make_kuid(fs_userns, uid);
}

/**
 * kmntuid_to_kuid - map a kmntuid into the filesystem idmapping
 * @mnt_userns: the mount's idmapping
 * @fs_userns: the filesystem's idmapping
 * @kmntuid : kmntuid to be mapped
 *
 * Map @kmntuid into the filesystem idmapping. This function has to be used in
 * order to e.g. write @kmntuid to inode->i_uid.
 *
 * Return: @kmntuid mapped into the filesystem idmapping
 */
static inline kuid_t kmntuid_to_kuid(struct user_namespace *mnt_userns,
				     struct user_namespace *fs_userns,
				     kmntuid_t kmntuid)
{
	return mapped_kuid_user(mnt_userns, fs_userns, AS_KUIDT(kmntuid));
}

/**
 * kmntuid_has_mapping - check whether a kmntuid maps into the filesystem
 * @mnt_userns: the mount's idmapping
 * @fs_userns: the filesystem's idmapping
 * @kmntuid: kmntuid to be mapped
 *
 * Check whether @kmntuid has a mapping in the filesystem idmapping. Use this
 * function to check whether the filesystem idmapping has a mapping for
 * @kmntuid.
 *
 * Return: true if @kmntuid has a mapping in the filesystem, false if not.
 */
static inline bool kmntuid_has_mapping(struct user_namespace *mnt_userns,
				       struct user_namespace *fs_userns,
				       kmntuid_t kmntuid)
{
	return uid_valid(kmntuid_to_kuid(mnt_userns, fs_userns, kmntuid));
}

/**
 * mapped_kgid_user - map a user kgid into a mnt_userns
 * @mnt_userns: the mount's idmapping
 * @fs_userns: the filesystem's idmapping
 * @kgid : kgid to be mapped
 *
 * Use the idmapping of @mnt_userns to remap a @kgid into @fs_userns. Use this
 * function when preparing a @kgid to be written to disk or inode.
 *
 * If no_idmapping() determines that this is not an idmapped mount we can
 * simply return @kgid unchanged.
 * If initial_idmapping() tells us that the filesystem is not mounted with an
 * idmapping we know the value of @kgid won't change when calling
 * make_kgid() so we can simply retrieve the value via KGIDT_INIT()
 * directly.
 *
 * Return: @kgid mapped according to @mnt_userns.
 * If @kgid has no mapping in either @mnt_userns or @fs_userns INVALID_GID is
 * returned.
 */
static inline kgid_t mapped_kgid_user(struct user_namespace *mnt_userns,
				      struct user_namespace *fs_userns,
				      kgid_t kgid)
{
	gid_t gid;

	if (no_idmapping(mnt_userns, fs_userns))
		return kgid;
	gid = from_kgid(mnt_userns, kgid);
	if (gid == (gid_t)-1)
		return INVALID_GID;
	if (initial_idmapping(fs_userns))
		return KGIDT_INIT(gid);
	return make_kgid(fs_userns, gid);
}

/**
 * kmntgid_to_kgid - map a kmntgid into the filesystem idmapping
 * @mnt_userns: the mount's idmapping
 * @fs_userns: the filesystem's idmapping
 * @kmntgid : kmntgid to be mapped
 *
 * Map @kmntgid into the filesystem idmapping. This function has to be used in
 * order to e.g. write @kmntgid to inode->i_gid.
 *
 * Return: @kmntgid mapped into the filesystem idmapping
 */
static inline kgid_t kmntgid_to_kgid(struct user_namespace *mnt_userns,
				     struct user_namespace *fs_userns,
				     kmntgid_t kmntgid)
{
	return mapped_kgid_user(mnt_userns, fs_userns, AS_KGIDT(kmntgid));
}

/**
 * kmntgid_has_mapping - check whether a kmntgid maps into the filesystem
 * @mnt_userns: the mount's idmapping
 * @fs_userns: the filesystem's idmapping
 * @kmntgid: kmntgid to be mapped
 *
 * Check whether @kmntgid has a mapping in the filesystem idmapping. Use this
 * function to check whether the filesystem idmapping has a mapping for
 * @kmntgid.
 *
 * Return: true if @kmntgid has a mapping in the filesystem, false if not.
 */
static inline bool kmntgid_has_mapping(struct user_namespace *mnt_userns,
				       struct user_namespace *fs_userns,
				       kmntgid_t kmntgid)
{
	return gid_valid(kmntgid_to_kgid(mnt_userns, fs_userns, kmntgid));
}

/**
 * mapped_fsuid - return caller's fsuid mapped up into a mnt_userns
 * @mnt_userns: the mount's idmapping
 * @fs_userns: the filesystem's idmapping
 *
 * Use this helper to initialize a new vfs or filesystem object based on
 * the caller's fsuid. A common example is initializing the i_uid field of
 * a newly allocated inode triggered by a creation event such as mkdir or
 * O_CREAT. Other examples include the allocation of quotas for a specific
 * user.
 *
 * Return: the caller's current fsuid mapped up according to @mnt_userns.
 */
static inline kuid_t mapped_fsuid(struct user_namespace *mnt_userns,
				  struct user_namespace *fs_userns)
{
	return mapped_kuid_user(mnt_userns, fs_userns, current_fsuid());
}

/**
 * mapped_fsgid - return caller's fsgid mapped up into a mnt_userns
 * @mnt_userns: the mount's idmapping
 * @fs_userns: the filesystem's idmapping
 *
 * Use this helper to initialize a new vfs or filesystem object based on
 * the caller's fsgid. A common example is initializing the i_gid field of
 * a newly allocated inode triggered by a creation event such as mkdir or
 * O_CREAT. Other examples include the allocation of quotas for a specific
 * user.
 *
 * Return: the caller's current fsgid mapped up according to @mnt_userns.
 */
static inline kgid_t mapped_fsgid(struct user_namespace *mnt_userns,
				  struct user_namespace *fs_userns)
{
	return mapped_kgid_user(mnt_userns, fs_userns, current_fsgid());
}

#endif /* _LINUX_MNT_IDMAPPING_H */
