/*
 * Copyright (C) 2004,2007,2008 IBM Corporation
 *
 * Authors:
 * Leendert van Doorn <leendert@watson.ibm.com>
 * Dave Safford <safford@watson.ibm.com>
 * Reiner Sailer <sailer@watson.ibm.com>
 * Kylene Hall <kjhall@us.ibm.com>
 * Debora Velarde <dvelarde@us.ibm.com>
 *
 * Maintained by: <tpmdd_devel@lists.sourceforge.net>
 *
 * Device driver for TCG/TCPA TPM (trusted platform module).
 * Specifications at www.trustedcomputinggroup.org
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, version 2 of the
 * License.
 *
 */
#ifndef __LINUX_TPM_H__
#define __LINUX_TPM_H__

#define TPM_DIGEST_SIZE 20	/* Max TPM v1.2 PCR size */

/*
 * Chip num is this value or a valid tpm idx
 */
#define	TPM_ANY_NUM 0xFFFF

struct tpm_chip;

struct tpm_class_ops {
	const u8 req_complete_mask;
	const u8 req_complete_val;
	bool (*req_canceled)(struct tpm_chip *chip, u8 status);
	int (*recv) (struct tpm_chip *chip, u8 *buf, size_t len);
	int (*send) (struct tpm_chip *chip, u8 *buf, size_t len);
	void (*cancel) (struct tpm_chip *chip);
	u8 (*status) (struct tpm_chip *chip);
	bool (*update_timeouts)(struct tpm_chip *chip,
				unsigned long *timeout_cap);

};

#if defined(CONFIG_TCG_TPM) || defined(CONFIG_TCG_TPM_MODULE)

extern struct tpm_chip *tpm_chip_find_get(int chip_num);
extern void tpm_chip_put(struct tpm_chip *chip);

extern int tpm_pcr_read(struct tpm_chip *chip, int pcr_idx, u8 *res_buf);
extern int tpm_pcr_extend(struct tpm_chip *chip, int pcr_idx, const u8 *hash);
extern long tpm_send_command(struct tpm_chip *chip, void *buf, size_t buflen,
			     const char *desc);
extern int tpm_get_random(struct tpm_chip *chip, u8 *data, size_t max);
#else
static inline struct tpm_chip *tpm_chip_find_get(int chip_num)
{
	return NULL;
}
static inline void tpm_chip_put(struct tpm_chip *chip)
{
}
static inline int tpm_pcr_read(struct tpm_chip *chip, int pcr_idx, u8 *res_buf) {
	return -ENODEV;
}
static inline int tpm_pcr_extend(struct tpm_chip *chip, int pcr_idx, const u8 *hash) {
	return -ENODEV;
}
static inline long tpm_send_command(struct tpm_chip *chip, void *buf, size_t buflen,
				    const char *desc)
{
	return -ENODEV;
}
static inline int tpm_get_random(struct tpm_chip *chip, u8 *data, size_t max) {
	return -ENODEV;
}
#endif

/*
 * TPM call library.
 */
/* implementation specific TPM constants */
#define MAX_PCRINFO_SIZE		64
#define MAX_BUF_SIZE			(2048 - 4)
#define TPM_GETRANDOM_SIZE		14
#define TPM_OSAP_SIZE			36
#define TPM_OIAP_SIZE			10
#define TPM_SEAL_SIZE			87
#define TPM_UNSEAL_SIZE			104
#define TPM_SIZE_OFFSET			2
#define TPM_RETURN_OFFSET		6
#define TPM_DATA_OFFSET			10

enum tpm_entity_type {
	TPM_ET_KEYHANDLE		= 0x01,
	TPM_ET_OWNER			= 0x02,
	TPM_ET_DATA			= 0x03,
	TPM_ET_SRK			= 0x04,
	TPM_ET_KEY			= 0x05,
	TPM_ET_REVOKE			= 0x06,
	TPM_ET_DEL_OWNER_BLOB		= 0x07,
	TPM_ET_DEL_ROW			= 0x08,
	TPM_ET_DEL_KEY_BLOB		= 0x09,
	TPM_ET_COUNTER			= 0x0a,
	TPM_ET_NV			= 0x0b,
	TPM_ET_OPERATOR			= 0x0c,
	TPM_ET_RESERVED_HANDLE		= 0x40,
};

struct tpm_buf {
	unsigned short len;
	unsigned short offset;
	unsigned char data[MAX_BUF_SIZE];
};

#define INIT_BUF(tb) (tb->len = 0)

extern int tpm_library_use(void);
extern void tpm_library_unuse(void);

extern int tpm_seal(struct tpm_chip *chip,
		    struct tpm_buf *tb, enum tpm_entity_type keytype,
		    uint32_t keyhandle, const unsigned char *keyauth,
		    const unsigned char *data, uint32_t datalen,
		    unsigned char *blob, uint32_t *bloblen,
		    const unsigned char *blobauth,
		    const unsigned char *pcrinfo, uint32_t pcrinfosize);
extern int tpm_unseal(struct tpm_chip *chip, struct tpm_buf *tb,
		      uint32_t keyhandle, const unsigned char *keyauth,
		      const unsigned char *blob, int bloblen,
		      const unsigned char *blobauth,
		      unsigned char *data, unsigned int *datalen);

struct tpm_wrapped_key {
	unsigned short data_len;
	unsigned short pubkey_offset;
	unsigned short pubkey_len;
	u8 data[];
};

extern int tpm_create_wrap_key(struct tpm_chip *chip,
			       enum tpm_entity_type parent_type,
			       uint32_t parent_handle,
			       const unsigned char *parent_auth,
			       const unsigned char *usage_auth,
			       const unsigned char *migration_auth,
			       struct tpm_wrapped_key **_wrapped_key);
extern int tpm_load_key2(struct tpm_chip *chip,
			 enum tpm_entity_type parent_type,
			 uint32_t parent_handle,
			 const unsigned char *parent_auth,
			 const struct tpm_wrapped_key *wrapped_key,
			 uint32_t *_key_handle);

#endif
