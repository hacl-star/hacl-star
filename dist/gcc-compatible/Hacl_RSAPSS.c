/* MIT License
 *
 * Copyright (c) 2016-2022 INRIA, CMU and Microsoft Corporation
 * Copyright (c) 2022-2023 HACL* Contributors
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#include "Hacl_RSAPSS.h"

#include "internal/Hacl_RSA.h"
#include "internal/Hacl_Krmllib.h"
#include "internal/Hacl_Bignum_Base.h"
#include "internal/Hacl_Bignum.h"

static inline uint32_t hash_len(Spec_Hash_Definitions_hash_alg a)
{
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        return 16U;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        return 20U;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        return 28U;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        return 32U;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        return 48U;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        return 64U;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        return 32U;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        return 64U;
      }
    case Spec_Hash_Definitions_SHA3_224:
      {
        return 28U;
      }
    case Spec_Hash_Definitions_SHA3_256:
      {
        return 32U;
      }
    case Spec_Hash_Definitions_SHA3_384:
      {
        return 48U;
      }
    case Spec_Hash_Definitions_SHA3_512:
      {
        return 64U;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static inline void
hash(Spec_Hash_Definitions_hash_alg a, uint8_t *mHash, uint32_t msgLen, uint8_t *msg)
{
  switch (a)
  {
    case Spec_Hash_Definitions_SHA2_256:
      {
        Hacl_Hash_SHA2_hash_256(mHash, msg, msgLen);
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        Hacl_Hash_SHA2_hash_384(mHash, msg, msgLen);
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        Hacl_Hash_SHA2_hash_512(mHash, msg, msgLen);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static inline void
mgf_hash(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t len,
  uint8_t *mgfseed,
  uint32_t maskLen,
  uint8_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), len + 4U);
  uint8_t mgfseed_counter[len + 4U];
  memset(mgfseed_counter, 0U, (len + 4U) * sizeof (uint8_t));
  memcpy(mgfseed_counter, mgfseed, len * sizeof (uint8_t));
  uint32_t hLen = hash_len(a);
  uint32_t n = (maskLen - 1U) / hLen + 1U;
  uint32_t accLen = n * hLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), accLen);
  uint8_t acc[accLen];
  memset(acc, 0U, accLen * sizeof (uint8_t));
  for (uint32_t i = 0U; i < n; i++)
  {
    uint8_t *acc_i = acc + i * hLen;
    uint8_t *c = mgfseed_counter + len;
    c[0U] = (uint8_t)(i >> 24U);
    c[1U] = (uint8_t)(i >> 16U);
    c[2U] = (uint8_t)(i >> 8U);
    c[3U] = (uint8_t)i;
    hash(a, acc_i, len + 4U, mgfseed_counter);
  }
  memcpy(res, acc, maskLen * sizeof (uint8_t));
}

static inline void
pss_encode(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t saltLen,
  uint8_t *salt,
  uint32_t msgLen,
  uint8_t *msg,
  uint32_t emBits,
  uint8_t *em
)
{
  uint32_t hLen = hash_len(a);
  KRML_CHECK_SIZE(sizeof (uint8_t), hLen);
  uint8_t m1Hash[hLen];
  memset(m1Hash, 0U, hLen * sizeof (uint8_t));
  uint32_t m1Len = 8U + hLen + saltLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), m1Len);
  uint8_t m1[m1Len];
  memset(m1, 0U, m1Len * sizeof (uint8_t));
  hash(a, m1 + 8U, msgLen, msg);
  memcpy(m1 + 8U + hLen, salt, saltLen * sizeof (uint8_t));
  hash(a, m1Hash, m1Len, m1);
  uint32_t emLen = (emBits - 1U) / 8U + 1U;
  uint32_t dbLen = emLen - hLen - 1U;
  KRML_CHECK_SIZE(sizeof (uint8_t), dbLen);
  uint8_t db[dbLen];
  memset(db, 0U, dbLen * sizeof (uint8_t));
  uint32_t last_before_salt = dbLen - saltLen - 1U;
  db[last_before_salt] = 1U;
  memcpy(db + last_before_salt + 1U, salt, saltLen * sizeof (uint8_t));
  KRML_CHECK_SIZE(sizeof (uint8_t), dbLen);
  uint8_t dbMask[dbLen];
  memset(dbMask, 0U, dbLen * sizeof (uint8_t));
  mgf_hash(a, hLen, m1Hash, dbLen, dbMask);
  for (uint32_t i = 0U; i < dbLen; i++)
  {
    uint8_t *os = db;
    uint8_t x = (uint32_t)db[i] ^ (uint32_t)dbMask[i];
    os[i] = x;
  }
  uint32_t msBits = emBits % 8U;
  if (msBits > 0U)
  {
    db[0U] = (uint32_t)db[0U] & 0xffU >> (8U - msBits);
  }
  memcpy(em, db, dbLen * sizeof (uint8_t));
  memcpy(em + dbLen, m1Hash, hLen * sizeof (uint8_t));
  em[emLen - 1U] = 0xbcU;
}

static inline bool
pss_verify(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t saltLen,
  uint32_t msgLen,
  uint8_t *msg,
  uint32_t emBits,
  uint8_t *em
)
{
  uint32_t emLen = (emBits - 1U) / 8U + 1U;
  uint32_t msBits = emBits % 8U;
  uint8_t em_0;
  if (msBits > 0U)
  {
    em_0 = (uint32_t)em[0U] & 0xffU << msBits;
  }
  else
  {
    em_0 = 0U;
  }
  uint8_t em_last = em[emLen - 1U];
  if (emLen < saltLen + hash_len(a) + 2U)
  {
    return false;
  }
  if (!(em_last == 0xbcU && em_0 == 0U))
  {
    return false;
  }
  uint32_t emLen1 = (emBits - 1U) / 8U + 1U;
  uint32_t hLen = hash_len(a);
  KRML_CHECK_SIZE(sizeof (uint8_t), hLen);
  uint8_t m1Hash0[hLen];
  memset(m1Hash0, 0U, hLen * sizeof (uint8_t));
  uint32_t dbLen = emLen1 - hLen - 1U;
  uint8_t *maskedDB = em;
  uint8_t *m1Hash = em + dbLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), dbLen);
  uint8_t dbMask[dbLen];
  memset(dbMask, 0U, dbLen * sizeof (uint8_t));
  mgf_hash(a, hLen, m1Hash, dbLen, dbMask);
  for (uint32_t i = 0U; i < dbLen; i++)
  {
    uint8_t *os = dbMask;
    uint8_t x = (uint32_t)dbMask[i] ^ (uint32_t)maskedDB[i];
    os[i] = x;
  }
  uint32_t msBits1 = emBits % 8U;
  if (msBits1 > 0U)
  {
    dbMask[0U] = (uint32_t)dbMask[0U] & 0xffU >> (8U - msBits1);
  }
  uint32_t padLen = emLen1 - saltLen - hLen - 1U;
  KRML_CHECK_SIZE(sizeof (uint8_t), padLen);
  uint8_t pad2[padLen];
  memset(pad2, 0U, padLen * sizeof (uint8_t));
  pad2[padLen - 1U] = 0x01U;
  uint8_t *pad = dbMask;
  uint8_t *salt = dbMask + padLen;
  uint8_t res = 255U;
  for (uint32_t i = 0U; i < padLen; i++)
  {
    uint8_t uu____0 = FStar_UInt8_eq_mask(pad[i], pad2[i]);
    res = (uint32_t)uu____0 & (uint32_t)res;
  }
  uint8_t z = res;
  if (!(z == 255U))
  {
    return false;
  }
  uint32_t m1Len = 8U + hLen + saltLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), m1Len);
  uint8_t m1[m1Len];
  memset(m1, 0U, m1Len * sizeof (uint8_t));
  hash(a, m1 + 8U, msgLen, msg);
  memcpy(m1 + 8U + hLen, salt, saltLen * sizeof (uint8_t));
  hash(a, m1Hash0, m1Len, m1);
  uint8_t res0 = 255U;
  for (uint32_t i = 0U; i < hLen; i++)
  {
    uint8_t uu____1 = FStar_UInt8_eq_mask(m1Hash0[i], m1Hash[i]);
    res0 = (uint32_t)uu____1 & (uint32_t)res0;
  }
  uint8_t z0 = res0;
  return z0 == 255U;
}

static inline bool
load_pkey(uint32_t modBits, uint32_t eBits, uint8_t *nb, uint8_t *eb, uint64_t *pkey)
{
  uint32_t nbLen = (modBits - 1U) / 8U + 1U;
  uint32_t ebLen = (eBits - 1U) / 8U + 1U;
  uint32_t nLen = (modBits - 1U) / 64U + 1U;
  uint64_t *n = pkey;
  uint64_t *r2 = pkey + nLen;
  uint64_t *e = pkey + nLen + nLen;
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(nbLen, nb, n);
  Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64((modBits - 1U) / 64U + 1U, modBits - 1U, n, r2);
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(ebLen, eb, e);
  uint64_t m0 = Hacl_Impl_RSA_Keys_check_modulus_u64(modBits, n);
  uint64_t m1 = Hacl_Impl_RSA_Keys_check_exponent_u64(eBits, e);
  uint64_t m = m0 & m1;
  return m == 0xFFFFFFFFFFFFFFFFULL;
}

static inline bool
load_skey(
  uint32_t modBits,
  uint32_t eBits,
  uint32_t dBits,
  uint8_t *nb,
  uint8_t *eb,
  uint8_t *db,
  uint64_t *skey
)
{
  uint32_t dbLen = (dBits - 1U) / 8U + 1U;
  uint32_t nLen = (modBits - 1U) / 64U + 1U;
  uint32_t eLen = (eBits - 1U) / 64U + 1U;
  uint32_t pkeyLen = nLen + nLen + eLen;
  uint64_t *pkey = skey;
  uint64_t *d = skey + pkeyLen;
  bool b = load_pkey(modBits, eBits, nb, eb, pkey);
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(dbLen, db, d);
  uint64_t m1 = Hacl_Impl_RSA_Keys_check_exponent_u64(dBits, d);
  return b && m1 == 0xFFFFFFFFFFFFFFFFULL;
}

/**
Sign a message `msg` and write the signature to `sgnt`.

@param a Hash algorithm to use. Allowed values for `a` are ...
  - Spec_Hash_Definitions_SHA2_256,
  - Spec_Hash_Definitions_SHA2_384, and
  - Spec_Hash_Definitions_SHA2_512.
@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param dBits Count of bits in `d` value.
@param skey Pointer to secret key created by `Hacl_RSAPSS_new_rsapss_load_skey`.
@param saltLen Length of salt.
@param salt Pointer to `saltLen` bytes where the salt is read from.
@param msgLen Length of message.
@param msg Pointer to `msgLen` bytes where the message is read from.
@param sgnt Pointer to `ceil(modBits / 8)` bytes where the signature is written to.

@return Returns true if and only if signing was successful.
*/
bool
Hacl_RSAPSS_rsapss_sign(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t modBits,
  uint32_t eBits,
  uint32_t dBits,
  uint64_t *skey,
  uint32_t saltLen,
  uint8_t *salt,
  uint32_t msgLen,
  uint8_t *msg,
  uint8_t *sgnt
)
{
  uint32_t hLen = hash_len(a);
  bool
  b = saltLen <= 0xffffffffU - hLen - 8U && saltLen + hLen + 2U <= (modBits - 1U - 1U) / 8U + 1U;
  if (b)
  {
    uint32_t emLen = (modBits - 1U - 1U) / 8U + 1U;
    KRML_CHECK_SIZE(sizeof (uint8_t), emLen);
    uint8_t em[emLen];
    memset(em, 0U, emLen * sizeof (uint8_t));
    uint32_t emBits = modBits - 1U;
    pss_encode(a, saltLen, salt, msgLen, msg, emBits, em);
    bool eq_b = Hacl_RSA_rsa_dec(modBits, eBits, dBits, skey, em, sgnt);
    return eq_b;
  }
  return false;
}

/**
Verify the signature `sgnt` of a message `msg`.

@param a Hash algorithm to use. Allowed values for `a` are ...
  - Spec_Hash_Definitions_SHA2_256,
  - Spec_Hash_Definitions_SHA2_384, and
  - Spec_Hash_Definitions_SHA2_512.
@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param pkey Pointer to public key created by `Hacl_RSAPSS_new_rsapss_load_pkey`.
@param saltLen Length of salt.
@param sgntLen Length of signature.
@param sgnt Pointer to `sgntLen` bytes where the signature is read from.
@param msgLen Length of message.
@param msg Pointer to `msgLen` bytes where the message is read from.

@return Returns true if and only if the signature is valid.
*/
bool
Hacl_RSAPSS_rsapss_verify(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t modBits,
  uint32_t eBits,
  uint64_t *pkey,
  uint32_t saltLen,
  uint32_t sgntLen,
  uint8_t *sgnt,
  uint32_t msgLen,
  uint8_t *msg
)
{
  uint32_t hLen = hash_len(a);
  bool b = saltLen <= 0xffffffffU - hLen - 8U && sgntLen == (modBits - 1U) / 8U + 1U;
  if (b)
  {
    uint32_t emBits = modBits - 1U;
    uint32_t emLen = (emBits - 1U) / 8U + 1U;
    KRML_CHECK_SIZE(sizeof (uint8_t), emLen);
    uint8_t em[emLen];
    memset(em, 0U, emLen * sizeof (uint8_t));
    bool b1 = Hacl_RSA_rsa_enc(modBits, eBits, pkey, sgnt, em);
    if (b1)
    {
      uint32_t emBits1 = modBits - 1U;
      bool res = pss_verify(a, saltLen, msgLen, msg, emBits1, em);
      return res;
    }
    return false;
  }
  return false;
}

/**
Sign a message `msg` and write the signature to `sgnt`.

@param a Hash algorithm to use. Allowed values for `a` are ...
  - Spec_Hash_Definitions_SHA2_256,
  - Spec_Hash_Definitions_SHA2_384, and
  - Spec_Hash_Definitions_SHA2_512.
@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param dBits Count of bits in `d` value.
@param nb Pointer to `ceil(modBits / 8)` bytes where the modulus (`n`), in big-endian byte order, is read from.
@param eb Pointer to `ceil(modBits / 8)` bytes where the `e` value, in big-endian byte order, is read from.
@param db Pointer to `ceil(modBits / 8)` bytes where the `d` value, in big-endian byte order, is read from.
@param saltLen Length of salt.
@param salt Pointer to `saltLen` bytes where the salt is read from.
@param msgLen Length of message.
@param msg Pointer to `msgLen` bytes where the message is read from.
@param sgnt Pointer to `ceil(modBits / 8)` bytes where the signature is written to.

@return Returns true if and only if signing was successful.
*/
bool
Hacl_RSAPSS_rsapss_skey_sign(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t modBits,
  uint32_t eBits,
  uint32_t dBits,
  uint8_t *nb,
  uint8_t *eb,
  uint8_t *db,
  uint32_t saltLen,
  uint8_t *salt,
  uint32_t msgLen,
  uint8_t *msg,
  uint8_t *sgnt
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t),
    2U * ((modBits - 1U) / 64U + 1U) + (eBits - 1U) / 64U + 1U + (dBits - 1U) / 64U + 1U);
  uint64_t
  skey[2U * ((modBits - 1U) / 64U + 1U) + (eBits - 1U) / 64U + 1U + (dBits - 1U) / 64U + 1U];
  memset(skey,
    0U,
    (2U * ((modBits - 1U) / 64U + 1U) + (eBits - 1U) / 64U + 1U + (dBits - 1U) / 64U + 1U)
    * sizeof (uint64_t));
  bool b = load_skey(modBits, eBits, dBits, nb, eb, db, skey);
  if (b)
  {
    return
      Hacl_RSAPSS_rsapss_sign(a,
        modBits,
        eBits,
        dBits,
        skey,
        saltLen,
        salt,
        msgLen,
        msg,
        sgnt);
  }
  return false;
}

/**
Verify the signature `sgnt` of a message `msg`.

@param a Hash algorithm to use. Allowed values for `a` are ...
  - Spec_Hash_Definitions_SHA2_256,
  - Spec_Hash_Definitions_SHA2_384, and
  - Spec_Hash_Definitions_SHA2_512.
@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param nb Pointer to `ceil(modBits / 8)` bytes where the modulus (`n`), in big-endian byte order, is read from.
@param eb Pointer to `ceil(modBits / 8)` bytes where the `e` value, in big-endian byte order, is read from.
@param saltLen Length of salt.
@param sgntLen Length of signature.
@param sgnt Pointer to `sgntLen` bytes where the signature is read from.
@param msgLen Length of message.
@param msg Pointer to `msgLen` bytes where the message is read from.

@return Returns true if and only if the signature is valid.
*/
bool
Hacl_RSAPSS_rsapss_pkey_verify(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t modBits,
  uint32_t eBits,
  uint8_t *nb,
  uint8_t *eb,
  uint32_t saltLen,
  uint32_t sgntLen,
  uint8_t *sgnt,
  uint32_t msgLen,
  uint8_t *msg
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), 2U * ((modBits - 1U) / 64U + 1U) + (eBits - 1U) / 64U + 1U);
  uint64_t pkey[2U * ((modBits - 1U) / 64U + 1U) + (eBits - 1U) / 64U + 1U];
  memset(pkey,
    0U,
    (2U * ((modBits - 1U) / 64U + 1U) + (eBits - 1U) / 64U + 1U) * sizeof (uint64_t));
  bool b = load_pkey(modBits, eBits, nb, eb, pkey);
  if (b)
  {
    return Hacl_RSAPSS_rsapss_verify(a, modBits, eBits, pkey, saltLen, sgntLen, sgnt, msgLen, msg);
  }
  return false;
}

/**
  The mask generation function defined in the Public Key Cryptography Standard #1
  (https://www.ietf.org/rfc/rfc2437.txt Section 10.2.1) 
*/
void
Hacl_RSAPSS_mgf_hash(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t len,
  uint8_t *mgfseed,
  uint32_t maskLen,
  uint8_t *res
)
{
  mgf_hash(a, len, mgfseed, maskLen, res);
}

