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


#include "Hacl_RSA.h"

#include "internal/Hacl_Bignum_Base.h"
#include "internal/Hacl_Bignum.h"

static inline uint64_t check_num_bits_u64(uint32_t bs, uint64_t *b)
{
  uint32_t bLen = (bs - 1U) / 64U + 1U;
  if (bs == 64U * bLen)
  {
    return 0xFFFFFFFFFFFFFFFFULL;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), bLen);
  uint64_t b2[bLen];
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
  uint64_t b2[nLen];
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
  uint64_t bn_zero[eLen];
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

/**
Decrypt a message `cipher` and write the plaintext to `plain`.

@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param dBits Count of bits in `d` value.
@param skey Pointer to secret key created by `Hacl_RSA_new_rsa_load_skey`.
@param cipher Pointer to `ceil(modBits - 1 / 8)` bytes where the ciphertext is read from.
@param plain Pointer to `ceil(modBits / 8)` bytes where the plaintext is written to.

@return Returns true if and only if decryption was successful.
*/
bool
Hacl_RSA_rsa_dec(
  uint32_t modBits,
  uint32_t eBits,
  uint32_t dBits,
  uint64_t *skey,
  uint8_t *cipher,
  uint8_t *plain
)
{
  uint32_t nLen = (modBits - 1U) / 64U + 1U;
  uint32_t k = (modBits - 1U) / 8U + 1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t m[nLen];
  memset(m, 0U, nLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t s[nLen];
  memset(s, 0U, nLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t m_[nLen];
  memset(m_, 0U, nLen * sizeof (uint64_t));
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(k, cipher, m);
  uint32_t nLen1 = (modBits - 1U) / 64U + 1U;
  uint32_t eLen = (eBits - 1U) / 64U + 1U;
  uint64_t *n = skey;
  uint64_t *r2 = skey + nLen1;
  uint64_t *e = skey + nLen1 + nLen1;
  uint64_t *d = skey + nLen1 + nLen1 + eLen;
  uint64_t acc = 0ULL;
  for (uint32_t i = 0U; i < nLen1; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(m[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(m[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
  }
  uint64_t lt_c = acc;
  bool eq_b;
  if (lt_c == 0xFFFFFFFFFFFFFFFFULL)
  {
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
    for (uint32_t i = 0U; i < nLen1; i++)
    {
      uint64_t uu____0 = FStar_UInt64_eq_mask(m[i], m_[i]);
      mask = uu____0 & mask;
    }
    uint64_t mask1 = mask;
    uint64_t eq_m = mask1;
    for (uint32_t i = 0U; i < nLen1; i++)
    {
      uint64_t *os = s;
      uint64_t x = s[i];
      uint64_t x0 = eq_m & x;
      os[i] = x0;
    }
    eq_b = eq_m == 0xFFFFFFFFFFFFFFFFULL;
  }
  else
  {
    memset(s, 0U, nLen1 * sizeof (uint64_t));
    eq_b = false;
  }
  Hacl_Bignum_Convert_bn_to_bytes_be_uint64(k, s, plain);
  return eq_b;
}

/**
Encrypt a message `plain` and write the ciphertext to `cipher`.

@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param dBits Count of bits in `d` value.
@param skey Pointer to secret key created by `Hacl_RSA_new_rsa_load_skey`.
@param plain Pointer to `ceil(modBits / 8)` bytes where the plaintext is written to.
@param cipher Pointer to `ceil(modBits - 1 / 8)` bytes where the ciphertext is read from.

@return Returns true if and only if decryption was successful.
*/
bool
Hacl_RSA_rsa_enc(
  uint32_t modBits,
  uint32_t eBits,
  uint64_t *pkey,
  uint8_t *plain,
  uint8_t *cipher
)
{
  uint32_t nLen = (modBits - 1U) / 64U + 1U;
  uint32_t k = (modBits - 1U) / 8U + 1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t s[nLen];
  memset(s, 0U, nLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (modBits - 1U) / 64U + 1U);
  uint64_t c[(modBits - 1U) / 64U + 1U];
  memset(c, 0U, ((modBits - 1U) / 64U + 1U) * sizeof (uint64_t));
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64(k, plain, s);
  uint32_t nLen1 = (modBits - 1U) / 64U + 1U;
  uint64_t *n = pkey;
  uint64_t *r2 = pkey + nLen1;
  uint64_t *e = pkey + nLen1 + nLen1;
  uint64_t acc = 0ULL;
  for (uint32_t i = 0U; i < nLen1; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(s[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(s[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
  }
  uint64_t mask = acc;
  bool b;
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
      c);
    b = true;
  }
  else
  {
    memset(c, 0U, nLen1 * sizeof (uint64_t));
    c[0U] = 0ULL;
    b = false;
  }
  Hacl_Bignum_Convert_bn_to_bytes_be_uint64(k, c, cipher);
  return b;
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
*Hacl_RSA_new_rsa_load_pkey(uint32_t modBits, uint32_t eBits, uint8_t *nb, uint8_t *eb)
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
*Hacl_RSA_new_rsa_load_skey(
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

