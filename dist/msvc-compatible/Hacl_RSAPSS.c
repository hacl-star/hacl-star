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
  uint8_t *mgfseed_counter = (uint8_t *)alloca((len + 4U) * sizeof (uint8_t));
  memset(mgfseed_counter, 0U, (len + 4U) * sizeof (uint8_t));
  memcpy(mgfseed_counter, mgfseed, len * sizeof (uint8_t));
  uint32_t hLen = hash_len(a);
  uint32_t n = (maskLen - 1U) / hLen + 1U;
  uint32_t accLen = n * hLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), accLen);
  uint8_t *acc = (uint8_t *)alloca(accLen * sizeof (uint8_t));
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

static inline uint64_t check_num_bits_u64(uint32_t bs, uint64_t *b)
{
  uint32_t bLen = (bs - 1U) / 64U + 1U;
  if (bs == 64U * bLen)
  {
    return 0xFFFFFFFFFFFFFFFFULL;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), bLen);
  uint64_t *b2 = (uint64_t *)alloca(bLen * sizeof (uint64_t));
  memset(b2, 0U, bLen * sizeof (uint64_t));
  uint32_t i0 = bs / 64U;
  uint32_t j = bs % 64U;
  b2[i0] = b2[i0] | 1ULL << j;
  uint64_t acc = 0ULL;
  for (uint32_t i = 0U; i < bLen; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(b[i], b2[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(b[i], b2[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
  }
  uint64_t res = acc;
  return res;
}

static inline uint64_t check_modulus_u64(uint32_t modBits, uint64_t *n)
{
  uint32_t nLen = (modBits - 1U) / 64U + 1U;
  uint64_t bits0 = n[0U] & 1ULL;
  uint64_t m0 = 0ULL - bits0;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t *b2 = (uint64_t *)alloca(nLen * sizeof (uint64_t));
  memset(b2, 0U, nLen * sizeof (uint64_t));
  uint32_t i0 = (modBits - 1U) / 64U;
  uint32_t j = (modBits - 1U) % 64U;
  b2[i0] = b2[i0] | 1ULL << j;
  uint64_t acc = 0ULL;
  for (uint32_t i = 0U; i < nLen; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(b2[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(b2[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
  }
  uint64_t res = acc;
  uint64_t m1 = res;
  uint64_t m2 = check_num_bits_u64(modBits, n);
  return m0 & (m1 & m2);
}

static inline uint64_t check_exponent_u64(uint32_t eBits, uint64_t *e)
{
  uint32_t eLen = (eBits - 1U) / 64U + 1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), eLen);
  uint64_t *bn_zero = (uint64_t *)alloca(eLen * sizeof (uint64_t));
  memset(bn_zero, 0U, eLen * sizeof (uint64_t));
  uint64_t mask = 0xFFFFFFFFFFFFFFFFULL;
  for (uint32_t i = 0U; i < eLen; i++)
  {
    uint64_t uu____0 = FStar_UInt64_eq_mask(e[i], bn_zero[i]);
    mask = uu____0 & mask;
  }
  uint64_t mask1 = mask;
  uint64_t res = mask1;
  uint64_t m0 = res;
  uint64_t m1 = check_num_bits_u64(eBits, e);
  return ~m0 & m1;
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
  uint8_t *m1Hash = (uint8_t *)alloca(hLen * sizeof (uint8_t));
  memset(m1Hash, 0U, hLen * sizeof (uint8_t));
  uint32_t m1Len = 8U + hLen + saltLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), m1Len);
  uint8_t *m1 = (uint8_t *)alloca(m1Len * sizeof (uint8_t));
  memset(m1, 0U, m1Len * sizeof (uint8_t));
  hash(a, m1 + 8U, msgLen, msg);
  memcpy(m1 + 8U + hLen, salt, saltLen * sizeof (uint8_t));
  hash(a, m1Hash, m1Len, m1);
  uint32_t emLen = (emBits - 1U) / 8U + 1U;
  uint32_t dbLen = emLen - hLen - 1U;
  KRML_CHECK_SIZE(sizeof (uint8_t), dbLen);
  uint8_t *db = (uint8_t *)alloca(dbLen * sizeof (uint8_t));
  memset(db, 0U, dbLen * sizeof (uint8_t));
  uint32_t last_before_salt = dbLen - saltLen - 1U;
  db[last_before_salt] = 1U;
  memcpy(db + last_before_salt + 1U, salt, saltLen * sizeof (uint8_t));
  KRML_CHECK_SIZE(sizeof (uint8_t), dbLen);
  uint8_t *dbMask = (uint8_t *)alloca(dbLen * sizeof (uint8_t));
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
  uint8_t *m1Hash0 = (uint8_t *)alloca(hLen * sizeof (uint8_t));
  memset(m1Hash0, 0U, hLen * sizeof (uint8_t));
  uint32_t dbLen = emLen1 - hLen - 1U;
  uint8_t *maskedDB = em;
  uint8_t *m1Hash = em + dbLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), dbLen);
  uint8_t *dbMask = (uint8_t *)alloca(dbLen * sizeof (uint8_t));
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
  uint8_t *pad2 = (uint8_t *)alloca(padLen * sizeof (uint8_t));
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
  uint8_t *m1 = (uint8_t *)alloca(m1Len * sizeof (uint8_t));
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
  uint64_t m0 = check_modulus_u64(modBits, n);
  uint64_t m1 = check_exponent_u64(eBits, e);
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
  uint64_t m1 = check_exponent_u64(dBits, d);
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
    uint32_t nLen = (modBits - 1U) / 64U + 1U;
    KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
    uint64_t *m = (uint64_t *)alloca(nLen * sizeof (uint64_t));
    memset(m, 0U, nLen * sizeof (uint64_t));
    uint32_t emBits = modBits - 1U;
    uint32_t emLen = (emBits - 1U) / 8U + 1U;
    KRML_CHECK_SIZE(sizeof (uint8_t), emLen);
    uint8_t *em = (uint8_t *)alloca(emLen * sizeof (uint8_t));
    memset(em, 0U, emLen * sizeof (uint8_t));
    pss_encode(a, saltLen, salt, msgLen, msg, emBits, em);
    Hacl_Bignum_Convert_bn_from_bytes_be_uint64(emLen, em, m);
    uint32_t nLen1 = (modBits - 1U) / 64U + 1U;
    uint32_t k = (modBits - 1U) / 8U + 1U;
    KRML_CHECK_SIZE(sizeof (uint64_t), nLen1);
    uint64_t *s = (uint64_t *)alloca(nLen1 * sizeof (uint64_t));
    memset(s, 0U, nLen1 * sizeof (uint64_t));
    KRML_CHECK_SIZE(sizeof (uint64_t), nLen1);
    uint64_t *m_ = (uint64_t *)alloca(nLen1 * sizeof (uint64_t));
    memset(m_, 0U, nLen1 * sizeof (uint64_t));
    uint32_t nLen2 = (modBits - 1U) / 64U + 1U;
    uint32_t eLen = (eBits - 1U) / 64U + 1U;
    uint64_t *n = skey;
    uint64_t *r2 = skey + nLen2;
    uint64_t *e = skey + nLen2 + nLen2;
    uint64_t *d = skey + nLen2 + nLen2 + eLen;
    uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
    Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64((modBits - 1U) / 64U + 1U,
      n,
      mu,
      r2,
      m,
      dBits,
      d,
      s);
    uint64_t mu0 = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
    Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64((modBits - 1U) / 64U + 1U,
      n,
      mu0,
      r2,
      s,
      eBits,
      e,
      m_);
    uint64_t mask = 0xFFFFFFFFFFFFFFFFULL;
    for (uint32_t i = 0U; i < nLen2; i++)
    {
      uint64_t uu____0 = FStar_UInt64_eq_mask(m[i], m_[i]);
      mask = uu____0 & mask;
    }
    uint64_t mask1 = mask;
    uint64_t eq_m = mask1;
    for (uint32_t i = 0U; i < nLen2; i++)
    {
      uint64_t *os = s;
      uint64_t x = s[i];
      uint64_t x0 = eq_m & x;
      os[i] = x0;
    }
    bool eq_b = eq_m == 0xFFFFFFFFFFFFFFFFULL;
    Hacl_Bignum_Convert_bn_to_bytes_be_uint64(k, s, sgnt);
    bool eq_b0 = eq_b;
    return eq_b0;
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
    uint32_t nLen = (modBits - 1U) / 64U + 1U;
    KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
    uint64_t *m = (uint64_t *)alloca(nLen * sizeof (uint64_t));
    memset(m, 0U, nLen * sizeof (uint64_t));
    uint32_t nLen1 = (modBits - 1U) / 64U + 1U;
    uint32_t k = (modBits - 1U) / 8U + 1U;
    KRML_CHECK_SIZE(sizeof (uint64_t), nLen1);
    uint64_t *s = (uint64_t *)alloca(nLen1 * sizeof (uint64_t));
    memset(s, 0U, nLen1 * sizeof (uint64_t));
    Hacl_Bignum_Convert_bn_from_bytes_be_uint64(k, sgnt, s);
    uint32_t nLen2 = (modBits - 1U) / 64U + 1U;
    uint64_t *n = pkey;
    uint64_t *r2 = pkey + nLen2;
    uint64_t *e = pkey + nLen2 + nLen2;
    uint64_t acc = 0ULL;
    for (uint32_t i = 0U; i < nLen2; i++)
    {
      uint64_t beq = FStar_UInt64_eq_mask(s[i], n[i]);
      uint64_t blt = ~FStar_UInt64_gte_mask(s[i], n[i]);
      acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
    }
    uint64_t mask = acc;
    bool res;
    if (mask == 0xFFFFFFFFFFFFFFFFULL)
    {
      uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
      Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64((modBits - 1U) / 64U + 1U,
        n,
        mu,
        r2,
        s,
        eBits,
        e,
        m);
      bool ite;
      if (!((modBits - 1U) % 8U == 0U))
      {
        ite = true;
      }
      else
      {
        uint32_t i = (modBits - 1U) / 64U;
        uint32_t j = (modBits - 1U) % 64U;
        uint64_t tmp = m[i];
        uint64_t get_bit = tmp >> j & 1ULL;
        ite = get_bit == 0ULL;
      }
      if (ite)
      {
        res = true;
      }
      else
      {
        res = false;
      }
    }
    else
    {
      res = false;
    }
    bool b1 = res;
    bool b10 = b1;
    if (b10)
    {
      uint32_t emBits = modBits - 1U;
      uint32_t emLen = (emBits - 1U) / 8U + 1U;
      KRML_CHECK_SIZE(sizeof (uint8_t), emLen);
      uint8_t *em = (uint8_t *)alloca(emLen * sizeof (uint8_t));
      memset(em, 0U, emLen * sizeof (uint8_t));
      uint64_t *m1 = m;
      Hacl_Bignum_Convert_bn_to_bytes_be_uint64(emLen, m1, em);
      bool res0 = pss_verify(a, saltLen, msgLen, msg, emBits, em);
      return res0;
    }
    return false;
  }
  return false;
}

/**
Load a public key from key parts.

@param modBits Count of bits in modulus (`n`).
@param eBits Count of bits in `e` value.
@param nb Pointer to `ceil(modBits / 8)` bytes where the modulus (`n`), in big-endian byte order, is read from.
@param eb Pointer to `ceil(modBits / 8)` bytes where the `e` value, in big-endian byte order, is read from.

@return Returns an allocated public key upon success, otherwise, `NULL` if key part arguments are invalid or memory allocation fails. Note: caller must take care to `free()` the created key.
*/
uint64_t
*Hacl_RSAPSS_new_rsapss_load_pkey(uint32_t modBits, uint32_t eBits, uint8_t *nb, uint8_t *eb)
{
  bool ite;
  if (1U < modBits && 0U < eBits)
  {
    uint32_t nLen = (modBits - 1U) / 64U + 1U;
    uint32_t eLen = (eBits - 1U) / 64U + 1U;
    ite = nLen <= 33554431U && eLen <= 67108863U && nLen + nLen <= 0xffffffffU - eLen;
  }
  else
  {
    ite = false;
  }
  if (!ite)
  {
    return NULL;
  }
  uint32_t nLen = (modBits - 1U) / 64U + 1U;
  uint32_t eLen = (eBits - 1U) / 64U + 1U;
  uint32_t pkeyLen = nLen + nLen + eLen;
  KRML_CHECK_SIZE(sizeof (uint64_t), pkeyLen);
  uint64_t *pkey = (uint64_t *)KRML_HOST_CALLOC(pkeyLen, sizeof (uint64_t));
  if (pkey == NULL)
  {
    return pkey;
  }
  uint64_t *pkey1 = pkey;
  uint64_t *pkey2 = pkey1;
  uint32_t nbLen = (modBits - 1U) / 8U + 1U;
  uint32_t ebLen = (eBits - 1U) / 8U + 1U;
  uint32_t nLen1 = (modBits - 1U) / 64U + 1U;
  uint64_t *n = pkey2;
  uint64_t *r2 = pkey2 + nLen1;
  uint64_t *e = pkey2 + nLen1 + nLen1;
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(nbLen, nb, n);
  Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64((modBits - 1U) / 64U + 1U, modBits - 1U, n, r2);
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(ebLen, eb, e);
  uint64_t m0 = check_modulus_u64(modBits, n);
  uint64_t m1 = check_exponent_u64(eBits, e);
  uint64_t m = m0 & m1;
  bool b = m == 0xFFFFFFFFFFFFFFFFULL;
  if (b)
  {
    return pkey2;
  }
  KRML_HOST_FREE(pkey2);
  return NULL;
}

/**
Load a secret key from key parts.

@param modBits Count of bits in modulus (`n`).
@param eBits Count of bits in `e` value.
@param dBits Count of bits in `d` value.
@param nb Pointer to `ceil(modBits / 8)` bytes where the modulus (`n`), in big-endian byte order, is read from.
@param eb Pointer to `ceil(modBits / 8)` bytes where the `e` value, in big-endian byte order, is read from.
@param db Pointer to `ceil(modBits / 8)` bytes where the `d` value, in big-endian byte order, is read from.

@return Returns an allocated secret key upon success, otherwise, `NULL` if key part arguments are invalid or memory allocation fails. Note: caller must take care to `free()` the created key.
*/
uint64_t
*Hacl_RSAPSS_new_rsapss_load_skey(
  uint32_t modBits,
  uint32_t eBits,
  uint32_t dBits,
  uint8_t *nb,
  uint8_t *eb,
  uint8_t *db
)
{
  bool ite0;
  if (1U < modBits && 0U < eBits)
  {
    uint32_t nLen = (modBits - 1U) / 64U + 1U;
    uint32_t eLen = (eBits - 1U) / 64U + 1U;
    ite0 = nLen <= 33554431U && eLen <= 67108863U && nLen + nLen <= 0xffffffffU - eLen;
  }
  else
  {
    ite0 = false;
  }
  bool ite;
  if (ite0 && 0U < dBits)
  {
    uint32_t nLen = (modBits - 1U) / 64U + 1U;
    uint32_t eLen = (eBits - 1U) / 64U + 1U;
    uint32_t dLen = (dBits - 1U) / 64U + 1U;
    ite = dLen <= 67108863U && 2U * nLen <= 0xffffffffU - eLen - dLen;
  }
  else
  {
    ite = false;
  }
  if (!ite)
  {
    return NULL;
  }
  uint32_t nLen = (modBits - 1U) / 64U + 1U;
  uint32_t eLen = (eBits - 1U) / 64U + 1U;
  uint32_t dLen = (dBits - 1U) / 64U + 1U;
  uint32_t skeyLen = nLen + nLen + eLen + dLen;
  KRML_CHECK_SIZE(sizeof (uint64_t), skeyLen);
  uint64_t *skey = (uint64_t *)KRML_HOST_CALLOC(skeyLen, sizeof (uint64_t));
  if (skey == NULL)
  {
    return skey;
  }
  uint64_t *skey1 = skey;
  uint64_t *skey2 = skey1;
  uint32_t dbLen = (dBits - 1U) / 8U + 1U;
  uint32_t nLen1 = (modBits - 1U) / 64U + 1U;
  uint32_t eLen1 = (eBits - 1U) / 64U + 1U;
  uint32_t pkeyLen = nLen1 + nLen1 + eLen1;
  uint64_t *pkey = skey2;
  uint64_t *d = skey2 + pkeyLen;
  uint32_t nbLen1 = (modBits - 1U) / 8U + 1U;
  uint32_t ebLen1 = (eBits - 1U) / 8U + 1U;
  uint32_t nLen2 = (modBits - 1U) / 64U + 1U;
  uint64_t *n = pkey;
  uint64_t *r2 = pkey + nLen2;
  uint64_t *e = pkey + nLen2 + nLen2;
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(nbLen1, nb, n);
  Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64((modBits - 1U) / 64U + 1U, modBits - 1U, n, r2);
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(ebLen1, eb, e);
  uint64_t m0 = check_modulus_u64(modBits, n);
  uint64_t m10 = check_exponent_u64(eBits, e);
  uint64_t m = m0 & m10;
  bool b = m == 0xFFFFFFFFFFFFFFFFULL;
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(dbLen, db, d);
  uint64_t m1 = check_exponent_u64(dBits, d);
  bool b0 = b && m1 == 0xFFFFFFFFFFFFFFFFULL;
  if (b0)
  {
    return skey2;
  }
  KRML_HOST_FREE(skey2);
  return NULL;
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
  *skey =
    (uint64_t *)alloca((2U
      * ((modBits - 1U) / 64U + 1U)
      + (eBits - 1U) / 64U + 1U
      + (dBits - 1U) / 64U + 1U)
      * sizeof (uint64_t));
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
  uint64_t
  *pkey =
    (uint64_t *)alloca((2U * ((modBits - 1U) / 64U + 1U) + (eBits - 1U) / 64U + 1U)
      * sizeof (uint64_t));
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

