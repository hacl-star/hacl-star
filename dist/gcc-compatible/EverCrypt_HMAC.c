/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
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


#include "EverCrypt_HMAC.h"

#include "internal/Hacl_Hash_SHA2.h"
#include "internal/Hacl_Hash_SHA1.h"
#include "internal/Hacl_Hash_Blake2.h"
#include "internal/Hacl_HMAC.h"

void
EverCrypt_HMAC_compute_sha1(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
)
{
  uint32_t l = (uint32_t)64U;
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t key_block[l];
  memset(key_block, 0U, l * sizeof (uint8_t));
  uint32_t i0;
  if (key_len <= (uint32_t)64U)
  {
    i0 = key_len;
  }
  else
  {
    i0 = (uint32_t)20U;
  }
  uint8_t *nkey = key_block;
  if (key_len <= (uint32_t)64U)
  {
    memcpy(nkey, key, key_len * sizeof (uint8_t));
  }
  else
  {
    Hacl_Hash_SHA1_legacy_hash(key, key_len, nkey);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t ipad[l];
  memset(ipad, (uint8_t)0x36U, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = ipad[i];
    uint8_t yi = key_block[i];
    ipad[i] = xi ^ yi;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t opad[l];
  memset(opad, (uint8_t)0x5cU, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = opad[i];
    uint8_t yi = key_block[i];
    opad[i] = xi ^ yi;
  }
  uint32_t
  scrut[5U] =
    {
      (uint32_t)0x67452301U, (uint32_t)0xefcdab89U, (uint32_t)0x98badcfeU, (uint32_t)0x10325476U,
      (uint32_t)0xc3d2e1f0U
    };
  uint32_t *s = scrut;
  uint8_t *dst1 = ipad;
  Hacl_Hash_Core_SHA1_legacy_init(s);
  if (data_len == (uint32_t)0U)
  {
    Hacl_Hash_SHA1_legacy_update_last(s, (uint64_t)0U, ipad, (uint32_t)64U);
  }
  else
  {
    Hacl_Hash_SHA1_legacy_update_multi(s, ipad, (uint32_t)1U);
    Hacl_Hash_SHA1_legacy_update_last(s, (uint64_t)(uint32_t)64U, data, data_len);
  }
  Hacl_Hash_Core_SHA1_legacy_finish(s, dst1);
  uint8_t *hash1 = ipad;
  Hacl_Hash_Core_SHA1_legacy_init(s);
  if ((uint32_t)20U == (uint32_t)0U)
  {
    Hacl_Hash_SHA1_legacy_update_last(s, (uint64_t)0U, opad, (uint32_t)64U);
  }
  else
  {
    Hacl_Hash_SHA1_legacy_update_multi(s, opad, (uint32_t)1U);
    Hacl_Hash_SHA1_legacy_update_last(s, (uint64_t)(uint32_t)64U, hash1, (uint32_t)20U);
  }
  Hacl_Hash_Core_SHA1_legacy_finish(s, dst);
}

void
EverCrypt_HMAC_compute_sha2_256(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
)
{
  uint32_t l = (uint32_t)64U;
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t key_block[l];
  memset(key_block, 0U, l * sizeof (uint8_t));
  uint32_t i0;
  if (key_len <= (uint32_t)64U)
  {
    i0 = key_len;
  }
  else
  {
    i0 = (uint32_t)32U;
  }
  uint8_t *nkey = key_block;
  if (key_len <= (uint32_t)64U)
  {
    memcpy(nkey, key, key_len * sizeof (uint8_t));
  }
  else
  {
    EverCrypt_Hash_hash_256(key, key_len, nkey);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t ipad[l];
  memset(ipad, (uint8_t)0x36U, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = ipad[i];
    uint8_t yi = key_block[i];
    ipad[i] = xi ^ yi;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t opad[l];
  memset(opad, (uint8_t)0x5cU, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = opad[i];
    uint8_t yi = key_block[i];
    opad[i] = xi ^ yi;
  }
  uint32_t
  scrut[8U] =
    {
      (uint32_t)0x6a09e667U, (uint32_t)0xbb67ae85U, (uint32_t)0x3c6ef372U, (uint32_t)0xa54ff53aU,
      (uint32_t)0x510e527fU, (uint32_t)0x9b05688cU, (uint32_t)0x1f83d9abU, (uint32_t)0x5be0cd19U
    };
  uint32_t *s = scrut;
  uint8_t *dst1 = ipad;
  Hacl_Hash_Core_SHA2_init_256(s);
  if (data_len == (uint32_t)0U)
  {
    EverCrypt_Hash_update_last_256(s, (uint64_t)0U, ipad, (uint32_t)64U);
  }
  else
  {
    EverCrypt_Hash_update_multi_256(s, ipad, (uint32_t)1U);
    EverCrypt_Hash_update_last_256(s, (uint64_t)(uint32_t)64U, data, data_len);
  }
  Hacl_Hash_Core_SHA2_finish_256(s, dst1);
  uint8_t *hash1 = ipad;
  Hacl_Hash_Core_SHA2_init_256(s);
  if ((uint32_t)32U == (uint32_t)0U)
  {
    EverCrypt_Hash_update_last_256(s, (uint64_t)0U, opad, (uint32_t)64U);
  }
  else
  {
    EverCrypt_Hash_update_multi_256(s, opad, (uint32_t)1U);
    EverCrypt_Hash_update_last_256(s, (uint64_t)(uint32_t)64U, hash1, (uint32_t)32U);
  }
  Hacl_Hash_Core_SHA2_finish_256(s, dst);
}

void
EverCrypt_HMAC_compute_sha2_384(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
)
{
  uint32_t l = (uint32_t)128U;
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t key_block[l];
  memset(key_block, 0U, l * sizeof (uint8_t));
  uint32_t i0;
  if (key_len <= (uint32_t)128U)
  {
    i0 = key_len;
  }
  else
  {
    i0 = (uint32_t)48U;
  }
  uint8_t *nkey = key_block;
  if (key_len <= (uint32_t)128U)
  {
    memcpy(nkey, key, key_len * sizeof (uint8_t));
  }
  else
  {
    Hacl_Hash_SHA2_hash_384(key, key_len, nkey);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t ipad[l];
  memset(ipad, (uint8_t)0x36U, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = ipad[i];
    uint8_t yi = key_block[i];
    ipad[i] = xi ^ yi;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t opad[l];
  memset(opad, (uint8_t)0x5cU, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = opad[i];
    uint8_t yi = key_block[i];
    opad[i] = xi ^ yi;
  }
  uint64_t
  scrut[8U] =
    {
      (uint64_t)0xcbbb9d5dc1059ed8U, (uint64_t)0x629a292a367cd507U, (uint64_t)0x9159015a3070dd17U,
      (uint64_t)0x152fecd8f70e5939U, (uint64_t)0x67332667ffc00b31U, (uint64_t)0x8eb44a8768581511U,
      (uint64_t)0xdb0c2e0d64f98fa7U, (uint64_t)0x47b5481dbefa4fa4U
    };
  uint64_t *s = scrut;
  uint8_t *dst1 = ipad;
  Hacl_Hash_Core_SHA2_init_384(s);
  if (data_len == (uint32_t)0U)
  {
    Hacl_Hash_SHA2_update_last_384(s,
      FStar_UInt128_uint64_to_uint128((uint64_t)0U),
      ipad,
      (uint32_t)128U);
  }
  else
  {
    Hacl_Hash_SHA2_update_multi_384(s, ipad, (uint32_t)1U);
    Hacl_Hash_SHA2_update_last_384(s,
      FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
      data,
      data_len);
  }
  Hacl_Hash_Core_SHA2_finish_384(s, dst1);
  uint8_t *hash1 = ipad;
  Hacl_Hash_Core_SHA2_init_384(s);
  if ((uint32_t)48U == (uint32_t)0U)
  {
    Hacl_Hash_SHA2_update_last_384(s,
      FStar_UInt128_uint64_to_uint128((uint64_t)0U),
      opad,
      (uint32_t)128U);
  }
  else
  {
    Hacl_Hash_SHA2_update_multi_384(s, opad, (uint32_t)1U);
    Hacl_Hash_SHA2_update_last_384(s,
      FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
      hash1,
      (uint32_t)48U);
  }
  Hacl_Hash_Core_SHA2_finish_384(s, dst);
}

void
EverCrypt_HMAC_compute_sha2_512(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
)
{
  uint32_t l = (uint32_t)128U;
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t key_block[l];
  memset(key_block, 0U, l * sizeof (uint8_t));
  uint32_t i0;
  if (key_len <= (uint32_t)128U)
  {
    i0 = key_len;
  }
  else
  {
    i0 = (uint32_t)64U;
  }
  uint8_t *nkey = key_block;
  if (key_len <= (uint32_t)128U)
  {
    memcpy(nkey, key, key_len * sizeof (uint8_t));
  }
  else
  {
    Hacl_Hash_SHA2_hash_512(key, key_len, nkey);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t ipad[l];
  memset(ipad, (uint8_t)0x36U, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = ipad[i];
    uint8_t yi = key_block[i];
    ipad[i] = xi ^ yi;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t opad[l];
  memset(opad, (uint8_t)0x5cU, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = opad[i];
    uint8_t yi = key_block[i];
    opad[i] = xi ^ yi;
  }
  uint64_t
  scrut[8U] =
    {
      (uint64_t)0x6a09e667f3bcc908U, (uint64_t)0xbb67ae8584caa73bU, (uint64_t)0x3c6ef372fe94f82bU,
      (uint64_t)0xa54ff53a5f1d36f1U, (uint64_t)0x510e527fade682d1U, (uint64_t)0x9b05688c2b3e6c1fU,
      (uint64_t)0x1f83d9abfb41bd6bU, (uint64_t)0x5be0cd19137e2179U
    };
  uint64_t *s = scrut;
  uint8_t *dst1 = ipad;
  Hacl_Hash_Core_SHA2_init_512(s);
  if (data_len == (uint32_t)0U)
  {
    Hacl_Hash_SHA2_update_last_512(s,
      FStar_UInt128_uint64_to_uint128((uint64_t)0U),
      ipad,
      (uint32_t)128U);
  }
  else
  {
    Hacl_Hash_SHA2_update_multi_512(s, ipad, (uint32_t)1U);
    Hacl_Hash_SHA2_update_last_512(s,
      FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
      data,
      data_len);
  }
  Hacl_Hash_Core_SHA2_finish_512(s, dst1);
  uint8_t *hash1 = ipad;
  Hacl_Hash_Core_SHA2_init_512(s);
  if ((uint32_t)64U == (uint32_t)0U)
  {
    Hacl_Hash_SHA2_update_last_512(s,
      FStar_UInt128_uint64_to_uint128((uint64_t)0U),
      opad,
      (uint32_t)128U);
  }
  else
  {
    Hacl_Hash_SHA2_update_multi_512(s, opad, (uint32_t)1U);
    Hacl_Hash_SHA2_update_last_512(s,
      FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
      hash1,
      (uint32_t)64U);
  }
  Hacl_Hash_Core_SHA2_finish_512(s, dst);
}

void
EverCrypt_HMAC_compute_blake2s(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
)
{
  uint32_t l = (uint32_t)64U;
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t key_block[l];
  memset(key_block, 0U, l * sizeof (uint8_t));
  uint32_t i0;
  if (key_len <= (uint32_t)64U)
  {
    i0 = key_len;
  }
  else
  {
    i0 = (uint32_t)32U;
  }
  uint8_t *nkey = key_block;
  if (key_len <= (uint32_t)64U)
  {
    memcpy(nkey, key, key_len * sizeof (uint8_t));
  }
  else
  {
    Hacl_Hash_Blake2_hash_blake2s_32(key, key_len, nkey);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t ipad[l];
  memset(ipad, (uint8_t)0x36U, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = ipad[i];
    uint8_t yi = key_block[i];
    ipad[i] = xi ^ yi;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t opad[l];
  memset(opad, (uint8_t)0x5cU, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = opad[i];
    uint8_t yi = key_block[i];
    opad[i] = xi ^ yi;
  }
  uint32_t s[16U] = { 0U };
  uint32_t *r00 = s + (uint32_t)0U * (uint32_t)4U;
  uint32_t *r10 = s + (uint32_t)1U * (uint32_t)4U;
  uint32_t *r20 = s + (uint32_t)2U * (uint32_t)4U;
  uint32_t *r30 = s + (uint32_t)3U * (uint32_t)4U;
  uint32_t iv00 = Hacl_Impl_Blake2_Constants_ivTable_S[0U];
  uint32_t iv10 = Hacl_Impl_Blake2_Constants_ivTable_S[1U];
  uint32_t iv20 = Hacl_Impl_Blake2_Constants_ivTable_S[2U];
  uint32_t iv30 = Hacl_Impl_Blake2_Constants_ivTable_S[3U];
  uint32_t iv40 = Hacl_Impl_Blake2_Constants_ivTable_S[4U];
  uint32_t iv50 = Hacl_Impl_Blake2_Constants_ivTable_S[5U];
  uint32_t iv60 = Hacl_Impl_Blake2_Constants_ivTable_S[6U];
  uint32_t iv70 = Hacl_Impl_Blake2_Constants_ivTable_S[7U];
  r20[0U] = iv00;
  r20[1U] = iv10;
  r20[2U] = iv20;
  r20[3U] = iv30;
  r30[0U] = iv40;
  r30[1U] = iv50;
  r30[2U] = iv60;
  r30[3U] = iv70;
  uint32_t kk_shift_80 = (uint32_t)0U;
  uint32_t iv0_ = iv00 ^ ((uint32_t)0x01010000U ^ (kk_shift_80 ^ (uint32_t)32U));
  r00[0U] = iv0_;
  r00[1U] = iv10;
  r00[2U] = iv20;
  r00[3U] = iv30;
  r10[0U] = iv40;
  r10[1U] = iv50;
  r10[2U] = iv60;
  r10[3U] = iv70;
  uint64_t es = (uint64_t)0U;
  K____uint32_t__uint64_t scrut = { .fst = s, .snd = es };
  uint32_t *s0 = scrut.fst;
  uint8_t *dst1 = ipad;
  uint32_t *r01 = s0 + (uint32_t)0U * (uint32_t)4U;
  uint32_t *r11 = s0 + (uint32_t)1U * (uint32_t)4U;
  uint32_t *r21 = s0 + (uint32_t)2U * (uint32_t)4U;
  uint32_t *r31 = s0 + (uint32_t)3U * (uint32_t)4U;
  uint32_t iv01 = Hacl_Impl_Blake2_Constants_ivTable_S[0U];
  uint32_t iv11 = Hacl_Impl_Blake2_Constants_ivTable_S[1U];
  uint32_t iv21 = Hacl_Impl_Blake2_Constants_ivTable_S[2U];
  uint32_t iv31 = Hacl_Impl_Blake2_Constants_ivTable_S[3U];
  uint32_t iv41 = Hacl_Impl_Blake2_Constants_ivTable_S[4U];
  uint32_t iv51 = Hacl_Impl_Blake2_Constants_ivTable_S[5U];
  uint32_t iv61 = Hacl_Impl_Blake2_Constants_ivTable_S[6U];
  uint32_t iv71 = Hacl_Impl_Blake2_Constants_ivTable_S[7U];
  r21[0U] = iv01;
  r21[1U] = iv11;
  r21[2U] = iv21;
  r21[3U] = iv31;
  r31[0U] = iv41;
  r31[1U] = iv51;
  r31[2U] = iv61;
  r31[3U] = iv71;
  uint32_t kk_shift_81 = (uint32_t)0U;
  uint32_t iv0_0 = iv01 ^ ((uint32_t)0x01010000U ^ (kk_shift_81 ^ (uint32_t)32U));
  r01[0U] = iv0_0;
  r01[1U] = iv11;
  r01[2U] = iv21;
  r01[3U] = iv31;
  r11[0U] = iv41;
  r11[1U] = iv51;
  r11[2U] = iv61;
  r11[3U] = iv71;
  uint64_t ev = (uint64_t)0U;
  uint64_t ev10;
  if (data_len == (uint32_t)0U)
  {
    uint64_t
    ev1 = Hacl_Hash_Blake2_update_last_blake2s_32(s0, ev, (uint64_t)0U, ipad, (uint32_t)64U);
    ev10 = ev1;
  }
  else
  {
    uint64_t ev1 = Hacl_Hash_Blake2_update_multi_blake2s_32(s0, ev, ipad, (uint32_t)1U);
    uint64_t
    ev2 = Hacl_Hash_Blake2_update_last_blake2s_32(s0, ev1, (uint64_t)(uint32_t)64U, data, data_len);
    ev10 = ev2;
  }
  Hacl_Hash_Core_Blake2_finish_blake2s_32(s0, ev10, dst1);
  uint8_t *hash1 = ipad;
  uint32_t *r0 = s0 + (uint32_t)0U * (uint32_t)4U;
  uint32_t *r1 = s0 + (uint32_t)1U * (uint32_t)4U;
  uint32_t *r2 = s0 + (uint32_t)2U * (uint32_t)4U;
  uint32_t *r3 = s0 + (uint32_t)3U * (uint32_t)4U;
  uint32_t iv0 = Hacl_Impl_Blake2_Constants_ivTable_S[0U];
  uint32_t iv1 = Hacl_Impl_Blake2_Constants_ivTable_S[1U];
  uint32_t iv2 = Hacl_Impl_Blake2_Constants_ivTable_S[2U];
  uint32_t iv3 = Hacl_Impl_Blake2_Constants_ivTable_S[3U];
  uint32_t iv4 = Hacl_Impl_Blake2_Constants_ivTable_S[4U];
  uint32_t iv5 = Hacl_Impl_Blake2_Constants_ivTable_S[5U];
  uint32_t iv6 = Hacl_Impl_Blake2_Constants_ivTable_S[6U];
  uint32_t iv7 = Hacl_Impl_Blake2_Constants_ivTable_S[7U];
  r2[0U] = iv0;
  r2[1U] = iv1;
  r2[2U] = iv2;
  r2[3U] = iv3;
  r3[0U] = iv4;
  r3[1U] = iv5;
  r3[2U] = iv6;
  r3[3U] = iv7;
  uint32_t kk_shift_8 = (uint32_t)0U;
  uint32_t iv0_1 = iv0 ^ ((uint32_t)0x01010000U ^ (kk_shift_8 ^ (uint32_t)32U));
  r0[0U] = iv0_1;
  r0[1U] = iv1;
  r0[2U] = iv2;
  r0[3U] = iv3;
  r1[0U] = iv4;
  r1[1U] = iv5;
  r1[2U] = iv6;
  r1[3U] = iv7;
  uint64_t ev0 = (uint64_t)0U;
  uint64_t ev11;
  if ((uint32_t)32U == (uint32_t)0U)
  {
    uint64_t
    ev1 = Hacl_Hash_Blake2_update_last_blake2s_32(s0, ev0, (uint64_t)0U, opad, (uint32_t)64U);
    ev11 = ev1;
  }
  else
  {
    uint64_t ev1 = Hacl_Hash_Blake2_update_multi_blake2s_32(s0, ev0, opad, (uint32_t)1U);
    uint64_t
    ev2 =
      Hacl_Hash_Blake2_update_last_blake2s_32(s0,
        ev1,
        (uint64_t)(uint32_t)64U,
        hash1,
        (uint32_t)32U);
    ev11 = ev2;
  }
  Hacl_Hash_Core_Blake2_finish_blake2s_32(s0, ev11, dst);
}

void
EverCrypt_HMAC_compute_blake2b(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
)
{
  uint32_t l = (uint32_t)128U;
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t key_block[l];
  memset(key_block, 0U, l * sizeof (uint8_t));
  uint32_t i0;
  if (key_len <= (uint32_t)128U)
  {
    i0 = key_len;
  }
  else
  {
    i0 = (uint32_t)64U;
  }
  uint8_t *nkey = key_block;
  if (key_len <= (uint32_t)128U)
  {
    memcpy(nkey, key, key_len * sizeof (uint8_t));
  }
  else
  {
    Hacl_Hash_Blake2_hash_blake2b_32(key, key_len, nkey);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t ipad[l];
  memset(ipad, (uint8_t)0x36U, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = ipad[i];
    uint8_t yi = key_block[i];
    ipad[i] = xi ^ yi;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t opad[l];
  memset(opad, (uint8_t)0x5cU, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = opad[i];
    uint8_t yi = key_block[i];
    opad[i] = xi ^ yi;
  }
  uint64_t s[16U] = { 0U };
  uint64_t *r00 = s + (uint32_t)0U * (uint32_t)4U;
  uint64_t *r10 = s + (uint32_t)1U * (uint32_t)4U;
  uint64_t *r20 = s + (uint32_t)2U * (uint32_t)4U;
  uint64_t *r30 = s + (uint32_t)3U * (uint32_t)4U;
  uint64_t iv00 = Hacl_Impl_Blake2_Constants_ivTable_B[0U];
  uint64_t iv10 = Hacl_Impl_Blake2_Constants_ivTable_B[1U];
  uint64_t iv20 = Hacl_Impl_Blake2_Constants_ivTable_B[2U];
  uint64_t iv30 = Hacl_Impl_Blake2_Constants_ivTable_B[3U];
  uint64_t iv40 = Hacl_Impl_Blake2_Constants_ivTable_B[4U];
  uint64_t iv50 = Hacl_Impl_Blake2_Constants_ivTable_B[5U];
  uint64_t iv60 = Hacl_Impl_Blake2_Constants_ivTable_B[6U];
  uint64_t iv70 = Hacl_Impl_Blake2_Constants_ivTable_B[7U];
  r20[0U] = iv00;
  r20[1U] = iv10;
  r20[2U] = iv20;
  r20[3U] = iv30;
  r30[0U] = iv40;
  r30[1U] = iv50;
  r30[2U] = iv60;
  r30[3U] = iv70;
  uint64_t kk_shift_80 = (uint64_t)(uint32_t)0U << (uint32_t)8U;
  uint64_t iv0_ = iv00 ^ ((uint64_t)0x01010000U ^ (kk_shift_80 ^ (uint64_t)(uint32_t)64U));
  r00[0U] = iv0_;
  r00[1U] = iv10;
  r00[2U] = iv20;
  r00[3U] = iv30;
  r10[0U] = iv40;
  r10[1U] = iv50;
  r10[2U] = iv60;
  r10[3U] = iv70;
  FStar_UInt128_uint128 es = FStar_UInt128_uint64_to_uint128((uint64_t)0U);
  K____uint64_t__FStar_UInt128_uint128 scrut = { .fst = s, .snd = es };
  uint64_t *s0 = scrut.fst;
  uint8_t *dst1 = ipad;
  uint64_t *r01 = s0 + (uint32_t)0U * (uint32_t)4U;
  uint64_t *r11 = s0 + (uint32_t)1U * (uint32_t)4U;
  uint64_t *r21 = s0 + (uint32_t)2U * (uint32_t)4U;
  uint64_t *r31 = s0 + (uint32_t)3U * (uint32_t)4U;
  uint64_t iv01 = Hacl_Impl_Blake2_Constants_ivTable_B[0U];
  uint64_t iv11 = Hacl_Impl_Blake2_Constants_ivTable_B[1U];
  uint64_t iv21 = Hacl_Impl_Blake2_Constants_ivTable_B[2U];
  uint64_t iv31 = Hacl_Impl_Blake2_Constants_ivTable_B[3U];
  uint64_t iv41 = Hacl_Impl_Blake2_Constants_ivTable_B[4U];
  uint64_t iv51 = Hacl_Impl_Blake2_Constants_ivTable_B[5U];
  uint64_t iv61 = Hacl_Impl_Blake2_Constants_ivTable_B[6U];
  uint64_t iv71 = Hacl_Impl_Blake2_Constants_ivTable_B[7U];
  r21[0U] = iv01;
  r21[1U] = iv11;
  r21[2U] = iv21;
  r21[3U] = iv31;
  r31[0U] = iv41;
  r31[1U] = iv51;
  r31[2U] = iv61;
  r31[3U] = iv71;
  uint64_t kk_shift_81 = (uint64_t)(uint32_t)0U << (uint32_t)8U;
  uint64_t iv0_0 = iv01 ^ ((uint64_t)0x01010000U ^ (kk_shift_81 ^ (uint64_t)(uint32_t)64U));
  r01[0U] = iv0_0;
  r01[1U] = iv11;
  r01[2U] = iv21;
  r01[3U] = iv31;
  r11[0U] = iv41;
  r11[1U] = iv51;
  r11[2U] = iv61;
  r11[3U] = iv71;
  FStar_UInt128_uint128 ev = FStar_UInt128_uint64_to_uint128((uint64_t)0U);
  FStar_UInt128_uint128 ev10;
  if (data_len == (uint32_t)0U)
  {
    FStar_UInt128_uint128
    ev1 =
      Hacl_Hash_Blake2_update_last_blake2b_32(s0,
        ev,
        FStar_UInt128_uint64_to_uint128((uint64_t)0U),
        ipad,
        (uint32_t)128U);
    ev10 = ev1;
  }
  else
  {
    FStar_UInt128_uint128
    ev1 = Hacl_Hash_Blake2_update_multi_blake2b_32(s0, ev, ipad, (uint32_t)1U);
    FStar_UInt128_uint128
    ev2 =
      Hacl_Hash_Blake2_update_last_blake2b_32(s0,
        ev1,
        FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
        data,
        data_len);
    ev10 = ev2;
  }
  Hacl_Hash_Core_Blake2_finish_blake2b_32(s0, ev10, dst1);
  uint8_t *hash1 = ipad;
  uint64_t *r0 = s0 + (uint32_t)0U * (uint32_t)4U;
  uint64_t *r1 = s0 + (uint32_t)1U * (uint32_t)4U;
  uint64_t *r2 = s0 + (uint32_t)2U * (uint32_t)4U;
  uint64_t *r3 = s0 + (uint32_t)3U * (uint32_t)4U;
  uint64_t iv0 = Hacl_Impl_Blake2_Constants_ivTable_B[0U];
  uint64_t iv1 = Hacl_Impl_Blake2_Constants_ivTable_B[1U];
  uint64_t iv2 = Hacl_Impl_Blake2_Constants_ivTable_B[2U];
  uint64_t iv3 = Hacl_Impl_Blake2_Constants_ivTable_B[3U];
  uint64_t iv4 = Hacl_Impl_Blake2_Constants_ivTable_B[4U];
  uint64_t iv5 = Hacl_Impl_Blake2_Constants_ivTable_B[5U];
  uint64_t iv6 = Hacl_Impl_Blake2_Constants_ivTable_B[6U];
  uint64_t iv7 = Hacl_Impl_Blake2_Constants_ivTable_B[7U];
  r2[0U] = iv0;
  r2[1U] = iv1;
  r2[2U] = iv2;
  r2[3U] = iv3;
  r3[0U] = iv4;
  r3[1U] = iv5;
  r3[2U] = iv6;
  r3[3U] = iv7;
  uint64_t kk_shift_8 = (uint64_t)(uint32_t)0U << (uint32_t)8U;
  uint64_t iv0_1 = iv0 ^ ((uint64_t)0x01010000U ^ (kk_shift_8 ^ (uint64_t)(uint32_t)64U));
  r0[0U] = iv0_1;
  r0[1U] = iv1;
  r0[2U] = iv2;
  r0[3U] = iv3;
  r1[0U] = iv4;
  r1[1U] = iv5;
  r1[2U] = iv6;
  r1[3U] = iv7;
  FStar_UInt128_uint128 ev0 = FStar_UInt128_uint64_to_uint128((uint64_t)0U);
  FStar_UInt128_uint128 ev11;
  if ((uint32_t)64U == (uint32_t)0U)
  {
    FStar_UInt128_uint128
    ev1 =
      Hacl_Hash_Blake2_update_last_blake2b_32(s0,
        ev0,
        FStar_UInt128_uint64_to_uint128((uint64_t)0U),
        opad,
        (uint32_t)128U);
    ev11 = ev1;
  }
  else
  {
    FStar_UInt128_uint128
    ev1 = Hacl_Hash_Blake2_update_multi_blake2b_32(s0, ev0, opad, (uint32_t)1U);
    FStar_UInt128_uint128
    ev2 =
      Hacl_Hash_Blake2_update_last_blake2b_32(s0,
        ev1,
        FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
        hash1,
        (uint32_t)64U);
    ev11 = ev2;
  }
  Hacl_Hash_Core_Blake2_finish_blake2b_32(s0, ev11, dst);
}

bool EverCrypt_HMAC_is_supported_alg(Spec_Hash_Definitions_hash_alg uu___)
{
  switch (uu___)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        return true;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        return true;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        return true;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        return true;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        return true;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

void
EverCrypt_HMAC_compute(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *mac,
  uint8_t *key,
  uint32_t keylen,
  uint8_t *data,
  uint32_t datalen
)
{
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        EverCrypt_HMAC_compute_sha1(mac, key, keylen, data, datalen);
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        EverCrypt_HMAC_compute_sha2_256(mac, key, keylen, data, datalen);
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        EverCrypt_HMAC_compute_sha2_384(mac, key, keylen, data, datalen);
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        EverCrypt_HMAC_compute_sha2_512(mac, key, keylen, data, datalen);
        break;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        EverCrypt_HMAC_compute_blake2s(mac, key, keylen, data, datalen);
        break;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        EverCrypt_HMAC_compute_blake2b(mac, key, keylen, data, datalen);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

