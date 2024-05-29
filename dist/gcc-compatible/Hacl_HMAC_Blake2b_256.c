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


#include "Hacl_HMAC_Blake2b_256.h"

#include "internal/Hacl_Krmllib.h"
#include "internal/Hacl_Hash_Blake2b_Simd256.h"
#include "internal/Hacl_HMAC.h"

/**
Write the HMAC-BLAKE2b MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 128 bytes.
`dst` must point to 64 bytes of memory.
*/
void
Hacl_HMAC_Blake2b_256_compute_blake2b_256(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
)
{
  uint32_t l = 128U;
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t key_block[l];
  memset(key_block, 0U, l * sizeof (uint8_t));
  uint8_t *nkey = key_block;
  uint32_t ite;
  if (key_len <= 128U)
  {
    ite = key_len;
  }
  else
  {
    ite = 64U;
  }
  uint8_t *zeroes = key_block + ite;
  KRML_MAYBE_UNUSED_VAR(zeroes);
  if (key_len <= 128U)
  {
    memcpy(nkey, key, key_len * sizeof (uint8_t));
  }
  else
  {
    Hacl_Hash_Blake2b_Simd256_hash_with_key(nkey, 64U, key, key_len, NULL, 0U);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t ipad[l];
  memset(ipad, 0x36U, l * sizeof (uint8_t));
  for (uint32_t i = 0U; i < l; i++)
  {
    uint8_t xi = ipad[i];
    uint8_t yi = key_block[i];
    ipad[i] = (uint32_t)xi ^ (uint32_t)yi;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t opad[l];
  memset(opad, 0x5cU, l * sizeof (uint8_t));
  for (uint32_t i = 0U; i < l; i++)
  {
    uint8_t xi = opad[i];
    uint8_t yi = key_block[i];
    opad[i] = (uint32_t)xi ^ (uint32_t)yi;
  }
  KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 s[4U] KRML_POST_ALIGN(32) = { 0U };
  Hacl_Hash_Blake2b_Simd256_init(s, 0U, 64U);
  Lib_IntVector_Intrinsics_vec256 *s0 = s;
  uint8_t *dst1 = ipad;
  if (data_len == 0U)
  {
    KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 wv[4U] KRML_POST_ALIGN(32) = { 0U };
    Hacl_Hash_Blake2b_Simd256_update_last(128U,
      wv,
      s0,
      false,
      FStar_UInt128_uint64_to_uint128(0ULL),
      128U,
      ipad);
  }
  else
  {
    uint32_t block_len = 128U;
    uint32_t n_blocks0 = data_len / block_len;
    uint32_t rem0 = data_len % block_len;
    K___uint32_t_uint32_t scrut;
    if (n_blocks0 > 0U && rem0 == 0U)
    {
      uint32_t n_blocks_ = n_blocks0 - 1U;
      scrut = ((K___uint32_t_uint32_t){ .fst = n_blocks_, .snd = data_len - n_blocks_ * block_len });
    }
    else
    {
      scrut = ((K___uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem0 });
    }
    uint32_t n_blocks = scrut.fst;
    uint32_t rem_len = scrut.snd;
    uint32_t full_blocks_len = n_blocks * block_len;
    uint8_t *full_blocks = data;
    uint8_t *rem = data + full_blocks_len;
    KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 wv[4U] KRML_POST_ALIGN(32) = { 0U };
    Hacl_Hash_Blake2b_Simd256_update_multi(128U,
      wv,
      s0,
      FStar_UInt128_uint64_to_uint128(0ULL),
      ipad,
      1U);
    KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 wv0[4U] KRML_POST_ALIGN(32) = { 0U };
    Hacl_Hash_Blake2b_Simd256_update_multi(n_blocks * 128U,
      wv0,
      s0,
      FStar_UInt128_uint64_to_uint128((uint64_t)block_len),
      full_blocks,
      n_blocks);
    KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 wv1[4U] KRML_POST_ALIGN(32) = { 0U };
    Hacl_Hash_Blake2b_Simd256_update_last(rem_len,
      wv1,
      s0,
      false,
      FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)128U),
        FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
      rem_len,
      rem);
  }
  Hacl_Hash_Blake2b_Simd256_finish(64U, dst1, s0);
  uint8_t *hash1 = ipad;
  Hacl_Hash_Blake2b_Simd256_init(s0, 0U, 64U);
  uint32_t block_len = 128U;
  uint32_t n_blocks0 = 64U / block_len;
  uint32_t rem0 = 64U % block_len;
  K___uint32_t_uint32_t scrut;
  if (n_blocks0 > 0U && rem0 == 0U)
  {
    uint32_t n_blocks_ = n_blocks0 - 1U;
    scrut = ((K___uint32_t_uint32_t){ .fst = n_blocks_, .snd = 64U - n_blocks_ * block_len });
  }
  else
  {
    scrut = ((K___uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem0 });
  }
  uint32_t n_blocks = scrut.fst;
  uint32_t rem_len = scrut.snd;
  uint32_t full_blocks_len = n_blocks * block_len;
  uint8_t *full_blocks = hash1;
  uint8_t *rem = hash1 + full_blocks_len;
  KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 wv[4U] KRML_POST_ALIGN(32) = { 0U };
  Hacl_Hash_Blake2b_Simd256_update_multi(128U,
    wv,
    s0,
    FStar_UInt128_uint64_to_uint128(0ULL),
    opad,
    1U);
  KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 wv0[4U] KRML_POST_ALIGN(32) = { 0U };
  Hacl_Hash_Blake2b_Simd256_update_multi(n_blocks * 128U,
    wv0,
    s0,
    FStar_UInt128_uint64_to_uint128((uint64_t)block_len),
    full_blocks,
    n_blocks);
  KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 wv1[4U] KRML_POST_ALIGN(32) = { 0U };
  Hacl_Hash_Blake2b_Simd256_update_last(rem_len,
    wv1,
    s0,
    false,
    FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)128U),
      FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
    rem_len,
    rem);
  Hacl_Hash_Blake2b_Simd256_finish(64U, dst, s0);
}

