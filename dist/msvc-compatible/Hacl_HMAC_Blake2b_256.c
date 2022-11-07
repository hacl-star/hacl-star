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


#include "Hacl_HMAC_Blake2b_256.h"

#include "internal/Hacl_Hash_Blake2b_256.h"
#include "internal/Hacl_Hash_Blake2.h"

typedef struct ___Lib_IntVector_Intrinsics_vec256__FStar_UInt128_uint128_s
{
  Lib_IntVector_Intrinsics_vec256 *fst;
  FStar_UInt128_uint128 snd;
}
___Lib_IntVector_Intrinsics_vec256__FStar_UInt128_uint128;

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
  uint32_t l = (uint32_t)128U;
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t *key_block = (uint8_t *)alloca(l * sizeof (uint8_t));
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
    Hacl_Hash_Blake2b_256_hash_blake2b_256(key, key_len, nkey);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t *ipad = (uint8_t *)alloca(l * sizeof (uint8_t));
  memset(ipad, (uint8_t)0x36U, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = ipad[i];
    uint8_t yi = key_block[i];
    ipad[i] = xi ^ yi;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t *opad = (uint8_t *)alloca(l * sizeof (uint8_t));
  memset(opad, (uint8_t)0x5cU, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = opad[i];
    uint8_t yi = key_block[i];
    opad[i] = xi ^ yi;
  }
  KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 s[4U] KRML_POST_ALIGN(32) = { 0U };
  Lib_IntVector_Intrinsics_vec256 *r0 = s;
  Lib_IntVector_Intrinsics_vec256 *r1 = s + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *r2 = s + (uint32_t)2U;
  Lib_IntVector_Intrinsics_vec256 *r3 = s + (uint32_t)3U;
  uint64_t iv0 = Hacl_Impl_Blake2_Constants_ivTable_B[0U];
  uint64_t iv1 = Hacl_Impl_Blake2_Constants_ivTable_B[1U];
  uint64_t iv2 = Hacl_Impl_Blake2_Constants_ivTable_B[2U];
  uint64_t iv3 = Hacl_Impl_Blake2_Constants_ivTable_B[3U];
  uint64_t iv4 = Hacl_Impl_Blake2_Constants_ivTable_B[4U];
  uint64_t iv5 = Hacl_Impl_Blake2_Constants_ivTable_B[5U];
  uint64_t iv6 = Hacl_Impl_Blake2_Constants_ivTable_B[6U];
  uint64_t iv7 = Hacl_Impl_Blake2_Constants_ivTable_B[7U];
  r2[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0, iv1, iv2, iv3);
  r3[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4, iv5, iv6, iv7);
  uint64_t kk_shift_8 = (uint64_t)(uint32_t)0U << (uint32_t)8U;
  uint64_t iv0_ = iv0 ^ ((uint64_t)0x01010000U ^ (kk_shift_8 ^ (uint64_t)(uint32_t)64U));
  r0[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0_, iv1, iv2, iv3);
  r1[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4, iv5, iv6, iv7);
  FStar_UInt128_uint128 es = FStar_UInt128_uint64_to_uint128((uint64_t)0U);
  ___Lib_IntVector_Intrinsics_vec256__FStar_UInt128_uint128 scrut0 = { .fst = s, .snd = es };
  Lib_IntVector_Intrinsics_vec256 *s0 = scrut0.fst;
  uint8_t *dst1 = ipad;
  FStar_UInt128_uint128 ev0 = Hacl_Hash_Blake2b_256_init_blake2b_256(s0);
  FStar_UInt128_uint128 ev10;
  if (data_len == (uint32_t)0U)
  {
    FStar_UInt128_uint128
    ev1 =
      Hacl_Hash_Blake2b_256_update_last_blake2b_256(s0,
        ev0,
        FStar_UInt128_uint64_to_uint128((uint64_t)0U),
        ipad,
        (uint32_t)128U);
    ev10 = ev1;
  }
  else
  {
    FStar_UInt128_uint128
    ev1 = Hacl_Hash_Blake2b_256_update_multi_blake2b_256(s0, ev0, ipad, (uint32_t)1U);
    uint32_t block_len = (uint32_t)128U;
    uint32_t n_blocks0 = data_len / block_len;
    uint32_t rem0 = data_len % block_len;
    K___uint32_t_uint32_t scrut;
    if (n_blocks0 > (uint32_t)0U && rem0 == (uint32_t)0U)
    {
      uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
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
    FStar_UInt128_uint128
    ev2 = Hacl_Hash_Blake2b_256_update_multi_blake2b_256(s0, ev1, full_blocks, n_blocks);
    uint8_t *rem = data + full_blocks_len;
    FStar_UInt128_uint128
    ev3 =
      Hacl_Hash_Blake2b_256_update_last_blake2b_256(s0,
        ev2,
        FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
          FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
        rem,
        rem_len);
    ev10 = ev3;
  }
  Hacl_Hash_Blake2b_256_finish_blake2b_256(s0, ev10, dst1);
  uint8_t *hash1 = ipad;
  FStar_UInt128_uint128 ev = Hacl_Hash_Blake2b_256_init_blake2b_256(s0);
  FStar_UInt128_uint128
  ev1 = Hacl_Hash_Blake2b_256_update_multi_blake2b_256(s0, ev, opad, (uint32_t)1U);
  uint32_t block_len = (uint32_t)128U;
  uint32_t n_blocks0 = (uint32_t)64U / block_len;
  uint32_t rem0 = (uint32_t)64U % block_len;
  K___uint32_t_uint32_t scrut;
  if (n_blocks0 > (uint32_t)0U && rem0 == (uint32_t)0U)
  {
    uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
    scrut =
      ((K___uint32_t_uint32_t){ .fst = n_blocks_, .snd = (uint32_t)64U - n_blocks_ * block_len });
  }
  else
  {
    scrut = ((K___uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem0 });
  }
  uint32_t n_blocks = scrut.fst;
  uint32_t rem_len = scrut.snd;
  uint32_t full_blocks_len = n_blocks * block_len;
  uint8_t *full_blocks = hash1;
  FStar_UInt128_uint128
  ev2 = Hacl_Hash_Blake2b_256_update_multi_blake2b_256(s0, ev1, full_blocks, n_blocks);
  uint8_t *rem = hash1 + full_blocks_len;
  FStar_UInt128_uint128
  ev3 =
    Hacl_Hash_Blake2b_256_update_last_blake2b_256(s0,
      ev2,
      FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
        FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
      rem,
      rem_len);
  FStar_UInt128_uint128 ev11 = ev3;
  Hacl_Hash_Blake2b_256_finish_blake2b_256(s0, ev11, dst);
}

