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


#include "internal/Hacl_HMAC.h"

#include "internal/Hacl_Hash_SHA2.h"
#include "internal/Hacl_Hash_SHA1.h"
#include "internal/Hacl_Hash_Blake2.h"

/* SNIPPET_START: Hacl_HMAC_legacy_compute_sha1 */

/**
Write the HMAC-SHA-1 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 64 byte.
`dst` must point to 20 bytes of memory.
*/
void
Hacl_HMAC_legacy_compute_sha1(
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
  scrut0[5U] =
    {
      (uint32_t)0x67452301U, (uint32_t)0xefcdab89U, (uint32_t)0x98badcfeU, (uint32_t)0x10325476U,
      (uint32_t)0xc3d2e1f0U
    };
  uint32_t *s = scrut0;
  uint8_t *dst1 = ipad;
  Hacl_Hash_Core_SHA1_legacy_init(s);
  if (data_len == (uint32_t)0U)
  {
    Hacl_Hash_SHA1_legacy_update_last(s, (uint64_t)0U, ipad, (uint32_t)64U);
  }
  else
  {
    Hacl_Hash_SHA1_legacy_update_multi(s, ipad, (uint32_t)1U);
    uint32_t block_len = (uint32_t)64U;
    uint32_t n_blocks0 = data_len / block_len;
    uint32_t rem = data_len % block_len;
    K___uint32_t_uint32_t scrut;
    if (n_blocks0 > (uint32_t)0U && rem == (uint32_t)0U)
    {
      uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
      scrut = ((K___uint32_t_uint32_t){ .fst = n_blocks_, .snd = data_len - n_blocks_ * block_len });
    }
    else
    {
      scrut = ((K___uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem });
    }
    uint32_t n_blocks = scrut.fst;
    uint32_t rem_len = scrut.snd;
    uint32_t full_blocks_len = n_blocks * block_len;
    uint8_t *full_blocks = data;
    Hacl_Hash_SHA1_legacy_update_multi(s, full_blocks, n_blocks);
    uint8_t *rem0 = data + full_blocks_len;
    Hacl_Hash_SHA1_legacy_update_last(s,
      (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len,
      rem0,
      rem_len);
  }
  Hacl_Hash_Core_SHA1_legacy_finish(s, dst1);
  uint8_t *hash1 = ipad;
  Hacl_Hash_Core_SHA1_legacy_init(s);
  Hacl_Hash_SHA1_legacy_update_multi(s, opad, (uint32_t)1U);
  uint32_t block_len = (uint32_t)64U;
  uint32_t n_blocks0 = (uint32_t)20U / block_len;
  uint32_t rem = (uint32_t)20U % block_len;
  K___uint32_t_uint32_t scrut;
  if (n_blocks0 > (uint32_t)0U && rem == (uint32_t)0U)
  {
    uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
    scrut =
      ((K___uint32_t_uint32_t){ .fst = n_blocks_, .snd = (uint32_t)20U - n_blocks_ * block_len });
  }
  else
  {
    scrut = ((K___uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem });
  }
  uint32_t n_blocks = scrut.fst;
  uint32_t rem_len = scrut.snd;
  uint32_t full_blocks_len = n_blocks * block_len;
  uint8_t *full_blocks = hash1;
  Hacl_Hash_SHA1_legacy_update_multi(s, full_blocks, n_blocks);
  uint8_t *rem0 = hash1 + full_blocks_len;
  Hacl_Hash_SHA1_legacy_update_last(s,
    (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len,
    rem0,
    rem_len);
  Hacl_Hash_Core_SHA1_legacy_finish(s, dst);
}

/* SNIPPET_END: Hacl_HMAC_legacy_compute_sha1 */

/* SNIPPET_START: Hacl_HMAC_compute_sha2_256 */

/**
Write the HMAC-SHA-2-256 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 64 bytes.
`dst` must point to 32 bytes of memory.
*/
void
Hacl_HMAC_compute_sha2_256(
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
    Hacl_Hash_SHA2_hash_256(key, key_len, nkey);
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
  scrut0[8U] =
    {
      (uint32_t)0x6a09e667U, (uint32_t)0xbb67ae85U, (uint32_t)0x3c6ef372U, (uint32_t)0xa54ff53aU,
      (uint32_t)0x510e527fU, (uint32_t)0x9b05688cU, (uint32_t)0x1f83d9abU, (uint32_t)0x5be0cd19U
    };
  uint32_t *s = scrut0;
  uint8_t *dst1 = ipad;
  Hacl_Hash_Core_SHA2_init_256(s);
  if (data_len == (uint32_t)0U)
  {
    Hacl_Hash_SHA2_update_last_256(s, (uint64_t)0U, ipad, (uint32_t)64U);
  }
  else
  {
    Hacl_Hash_SHA2_update_multi_256(s, ipad, (uint32_t)1U);
    uint32_t block_len = (uint32_t)64U;
    uint32_t n_blocks0 = data_len / block_len;
    uint32_t rem = data_len % block_len;
    K___uint32_t_uint32_t scrut;
    if (n_blocks0 > (uint32_t)0U && rem == (uint32_t)0U)
    {
      uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
      scrut = ((K___uint32_t_uint32_t){ .fst = n_blocks_, .snd = data_len - n_blocks_ * block_len });
    }
    else
    {
      scrut = ((K___uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem });
    }
    uint32_t n_blocks = scrut.fst;
    uint32_t rem_len = scrut.snd;
    uint32_t full_blocks_len = n_blocks * block_len;
    uint8_t *full_blocks = data;
    Hacl_Hash_SHA2_update_multi_256(s, full_blocks, n_blocks);
    uint8_t *rem0 = data + full_blocks_len;
    Hacl_Hash_SHA2_update_last_256(s,
      (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len,
      rem0,
      rem_len);
  }
  Hacl_Hash_Core_SHA2_finish_256(s, dst1);
  uint8_t *hash1 = ipad;
  Hacl_Hash_Core_SHA2_init_256(s);
  Hacl_Hash_SHA2_update_multi_256(s, opad, (uint32_t)1U);
  uint32_t block_len = (uint32_t)64U;
  uint32_t n_blocks0 = (uint32_t)32U / block_len;
  uint32_t rem = (uint32_t)32U % block_len;
  K___uint32_t_uint32_t scrut;
  if (n_blocks0 > (uint32_t)0U && rem == (uint32_t)0U)
  {
    uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
    scrut =
      ((K___uint32_t_uint32_t){ .fst = n_blocks_, .snd = (uint32_t)32U - n_blocks_ * block_len });
  }
  else
  {
    scrut = ((K___uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem });
  }
  uint32_t n_blocks = scrut.fst;
  uint32_t rem_len = scrut.snd;
  uint32_t full_blocks_len = n_blocks * block_len;
  uint8_t *full_blocks = hash1;
  Hacl_Hash_SHA2_update_multi_256(s, full_blocks, n_blocks);
  uint8_t *rem0 = hash1 + full_blocks_len;
  Hacl_Hash_SHA2_update_last_256(s,
    (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len,
    rem0,
    rem_len);
  Hacl_Hash_Core_SHA2_finish_256(s, dst);
}

/* SNIPPET_END: Hacl_HMAC_compute_sha2_256 */

/* SNIPPET_START: Hacl_HMAC_compute_sha2_384 */

/**
Write the HMAC-SHA-2-384 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 128 bytes.
`dst` must point to 48 bytes of memory.
*/
void
Hacl_HMAC_compute_sha2_384(
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
  scrut0[8U] =
    {
      (uint64_t)0xcbbb9d5dc1059ed8U, (uint64_t)0x629a292a367cd507U, (uint64_t)0x9159015a3070dd17U,
      (uint64_t)0x152fecd8f70e5939U, (uint64_t)0x67332667ffc00b31U, (uint64_t)0x8eb44a8768581511U,
      (uint64_t)0xdb0c2e0d64f98fa7U, (uint64_t)0x47b5481dbefa4fa4U
    };
  uint64_t *s = scrut0;
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
    uint32_t block_len = (uint32_t)128U;
    uint32_t n_blocks0 = data_len / block_len;
    uint32_t rem = data_len % block_len;
    K___uint32_t_uint32_t scrut;
    if (n_blocks0 > (uint32_t)0U && rem == (uint32_t)0U)
    {
      uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
      scrut = ((K___uint32_t_uint32_t){ .fst = n_blocks_, .snd = data_len - n_blocks_ * block_len });
    }
    else
    {
      scrut = ((K___uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem });
    }
    uint32_t n_blocks = scrut.fst;
    uint32_t rem_len = scrut.snd;
    uint32_t full_blocks_len = n_blocks * block_len;
    uint8_t *full_blocks = data;
    Hacl_Hash_SHA2_update_multi_384(s, full_blocks, n_blocks);
    uint8_t *rem0 = data + full_blocks_len;
    Hacl_Hash_SHA2_update_last_384(s,
      FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
        FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
      rem0,
      rem_len);
  }
  Hacl_Hash_Core_SHA2_finish_384(s, dst1);
  uint8_t *hash1 = ipad;
  Hacl_Hash_Core_SHA2_init_384(s);
  Hacl_Hash_SHA2_update_multi_384(s, opad, (uint32_t)1U);
  uint32_t block_len = (uint32_t)128U;
  uint32_t n_blocks0 = (uint32_t)48U / block_len;
  uint32_t rem = (uint32_t)48U % block_len;
  K___uint32_t_uint32_t scrut;
  if (n_blocks0 > (uint32_t)0U && rem == (uint32_t)0U)
  {
    uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
    scrut =
      ((K___uint32_t_uint32_t){ .fst = n_blocks_, .snd = (uint32_t)48U - n_blocks_ * block_len });
  }
  else
  {
    scrut = ((K___uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem });
  }
  uint32_t n_blocks = scrut.fst;
  uint32_t rem_len = scrut.snd;
  uint32_t full_blocks_len = n_blocks * block_len;
  uint8_t *full_blocks = hash1;
  Hacl_Hash_SHA2_update_multi_384(s, full_blocks, n_blocks);
  uint8_t *rem0 = hash1 + full_blocks_len;
  Hacl_Hash_SHA2_update_last_384(s,
    FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
      FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
    rem0,
    rem_len);
  Hacl_Hash_Core_SHA2_finish_384(s, dst);
}

/* SNIPPET_END: Hacl_HMAC_compute_sha2_384 */

/* SNIPPET_START: Hacl_HMAC_compute_sha2_512 */

/**
Write the HMAC-SHA-2-512 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 128 bytes.
`dst` must point to 64 bytes of memory.
*/
void
Hacl_HMAC_compute_sha2_512(
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
  scrut0[8U] =
    {
      (uint64_t)0x6a09e667f3bcc908U, (uint64_t)0xbb67ae8584caa73bU, (uint64_t)0x3c6ef372fe94f82bU,
      (uint64_t)0xa54ff53a5f1d36f1U, (uint64_t)0x510e527fade682d1U, (uint64_t)0x9b05688c2b3e6c1fU,
      (uint64_t)0x1f83d9abfb41bd6bU, (uint64_t)0x5be0cd19137e2179U
    };
  uint64_t *s = scrut0;
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
    uint32_t block_len = (uint32_t)128U;
    uint32_t n_blocks0 = data_len / block_len;
    uint32_t rem = data_len % block_len;
    K___uint32_t_uint32_t scrut;
    if (n_blocks0 > (uint32_t)0U && rem == (uint32_t)0U)
    {
      uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
      scrut = ((K___uint32_t_uint32_t){ .fst = n_blocks_, .snd = data_len - n_blocks_ * block_len });
    }
    else
    {
      scrut = ((K___uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem });
    }
    uint32_t n_blocks = scrut.fst;
    uint32_t rem_len = scrut.snd;
    uint32_t full_blocks_len = n_blocks * block_len;
    uint8_t *full_blocks = data;
    Hacl_Hash_SHA2_update_multi_512(s, full_blocks, n_blocks);
    uint8_t *rem0 = data + full_blocks_len;
    Hacl_Hash_SHA2_update_last_512(s,
      FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
        FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
      rem0,
      rem_len);
  }
  Hacl_Hash_Core_SHA2_finish_512(s, dst1);
  uint8_t *hash1 = ipad;
  Hacl_Hash_Core_SHA2_init_512(s);
  Hacl_Hash_SHA2_update_multi_512(s, opad, (uint32_t)1U);
  uint32_t block_len = (uint32_t)128U;
  uint32_t n_blocks0 = (uint32_t)64U / block_len;
  uint32_t rem = (uint32_t)64U % block_len;
  K___uint32_t_uint32_t scrut;
  if (n_blocks0 > (uint32_t)0U && rem == (uint32_t)0U)
  {
    uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
    scrut =
      ((K___uint32_t_uint32_t){ .fst = n_blocks_, .snd = (uint32_t)64U - n_blocks_ * block_len });
  }
  else
  {
    scrut = ((K___uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem });
  }
  uint32_t n_blocks = scrut.fst;
  uint32_t rem_len = scrut.snd;
  uint32_t full_blocks_len = n_blocks * block_len;
  uint8_t *full_blocks = hash1;
  Hacl_Hash_SHA2_update_multi_512(s, full_blocks, n_blocks);
  uint8_t *rem0 = hash1 + full_blocks_len;
  Hacl_Hash_SHA2_update_last_512(s,
    FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
      FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
    rem0,
    rem_len);
  Hacl_Hash_Core_SHA2_finish_512(s, dst);
}

/* SNIPPET_END: Hacl_HMAC_compute_sha2_512 */

/* SNIPPET_START: Hacl_HMAC_compute_blake2s_32 */

/**
Write the HMAC-BLAKE2s MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 64 bytes.
`dst` must point to 32 bytes of memory.
*/
void
Hacl_HMAC_compute_blake2s_32(
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
  uint32_t *r0 = s;
  uint32_t *r1 = s + (uint32_t)4U;
  uint32_t *r2 = s + (uint32_t)8U;
  uint32_t *r3 = s + (uint32_t)12U;
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
  uint32_t iv0_ = iv0 ^ ((uint32_t)0x01010000U ^ (kk_shift_8 ^ (uint32_t)32U));
  r0[0U] = iv0_;
  r0[1U] = iv1;
  r0[2U] = iv2;
  r0[3U] = iv3;
  r1[0U] = iv4;
  r1[1U] = iv5;
  r1[2U] = iv6;
  r1[3U] = iv7;
  uint64_t es = (uint64_t)0U;
  K____uint32_t__uint64_t scrut0 = { .fst = s, .snd = es };
  uint32_t *s0 = scrut0.fst;
  uint8_t *dst1 = ipad;
  uint64_t ev0 = Hacl_Hash_Core_Blake2_init_blake2s_32(s0);
  uint64_t ev10;
  if (data_len == (uint32_t)0U)
  {
    uint64_t
    ev1 = Hacl_Hash_Blake2_update_last_blake2s_32(s0, ev0, (uint64_t)0U, ipad, (uint32_t)64U);
    ev10 = ev1;
  }
  else
  {
    uint64_t ev1 = Hacl_Hash_Blake2_update_multi_blake2s_32(s0, ev0, ipad, (uint32_t)1U);
    uint32_t block_len = (uint32_t)64U;
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
    uint64_t ev2 = Hacl_Hash_Blake2_update_multi_blake2s_32(s0, ev1, full_blocks, n_blocks);
    uint8_t *rem = data + full_blocks_len;
    uint64_t
    ev3 =
      Hacl_Hash_Blake2_update_last_blake2s_32(s0,
        ev2,
        (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len,
        rem,
        rem_len);
    ev10 = ev3;
  }
  Hacl_Hash_Core_Blake2_finish_blake2s_32(s0, ev10, dst1);
  uint8_t *hash1 = ipad;
  uint64_t ev = Hacl_Hash_Core_Blake2_init_blake2s_32(s0);
  uint64_t ev1 = Hacl_Hash_Blake2_update_multi_blake2s_32(s0, ev, opad, (uint32_t)1U);
  uint32_t block_len = (uint32_t)64U;
  uint32_t n_blocks0 = (uint32_t)32U / block_len;
  uint32_t rem0 = (uint32_t)32U % block_len;
  K___uint32_t_uint32_t scrut;
  if (n_blocks0 > (uint32_t)0U && rem0 == (uint32_t)0U)
  {
    uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
    scrut =
      ((K___uint32_t_uint32_t){ .fst = n_blocks_, .snd = (uint32_t)32U - n_blocks_ * block_len });
  }
  else
  {
    scrut = ((K___uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem0 });
  }
  uint32_t n_blocks = scrut.fst;
  uint32_t rem_len = scrut.snd;
  uint32_t full_blocks_len = n_blocks * block_len;
  uint8_t *full_blocks = hash1;
  uint64_t ev2 = Hacl_Hash_Blake2_update_multi_blake2s_32(s0, ev1, full_blocks, n_blocks);
  uint8_t *rem = hash1 + full_blocks_len;
  uint64_t
  ev3 =
    Hacl_Hash_Blake2_update_last_blake2s_32(s0,
      ev2,
      (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len,
      rem,
      rem_len);
  uint64_t ev11 = ev3;
  Hacl_Hash_Core_Blake2_finish_blake2s_32(s0, ev11, dst);
}

/* SNIPPET_END: Hacl_HMAC_compute_blake2s_32 */

/* SNIPPET_START: Hacl_HMAC_compute_blake2b_32 */

/**
Write the HMAC-BLAKE2b MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 128 bytes.
`dst` must point to 64 bytes of memory.
*/
void
Hacl_HMAC_compute_blake2b_32(
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
  uint64_t *r0 = s;
  uint64_t *r1 = s + (uint32_t)4U;
  uint64_t *r2 = s + (uint32_t)8U;
  uint64_t *r3 = s + (uint32_t)12U;
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
  uint64_t iv0_ = iv0 ^ ((uint64_t)0x01010000U ^ (kk_shift_8 ^ (uint64_t)(uint32_t)64U));
  r0[0U] = iv0_;
  r0[1U] = iv1;
  r0[2U] = iv2;
  r0[3U] = iv3;
  r1[0U] = iv4;
  r1[1U] = iv5;
  r1[2U] = iv6;
  r1[3U] = iv7;
  FStar_UInt128_uint128 es = FStar_UInt128_uint64_to_uint128((uint64_t)0U);
  K____uint64_t__FStar_UInt128_uint128 scrut0 = { .fst = s, .snd = es };
  uint64_t *s0 = scrut0.fst;
  uint8_t *dst1 = ipad;
  FStar_UInt128_uint128 ev0 = Hacl_Hash_Core_Blake2_init_blake2b_32(s0);
  FStar_UInt128_uint128 ev10;
  if (data_len == (uint32_t)0U)
  {
    FStar_UInt128_uint128
    ev1 =
      Hacl_Hash_Blake2_update_last_blake2b_32(s0,
        ev0,
        FStar_UInt128_uint64_to_uint128((uint64_t)0U),
        ipad,
        (uint32_t)128U);
    ev10 = ev1;
  }
  else
  {
    FStar_UInt128_uint128
    ev1 = Hacl_Hash_Blake2_update_multi_blake2b_32(s0, ev0, ipad, (uint32_t)1U);
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
    ev2 = Hacl_Hash_Blake2_update_multi_blake2b_32(s0, ev1, full_blocks, n_blocks);
    uint8_t *rem = data + full_blocks_len;
    FStar_UInt128_uint128
    ev3 =
      Hacl_Hash_Blake2_update_last_blake2b_32(s0,
        ev2,
        FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
          FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
        rem,
        rem_len);
    ev10 = ev3;
  }
  Hacl_Hash_Core_Blake2_finish_blake2b_32(s0, ev10, dst1);
  uint8_t *hash1 = ipad;
  FStar_UInt128_uint128 ev = Hacl_Hash_Core_Blake2_init_blake2b_32(s0);
  FStar_UInt128_uint128
  ev1 = Hacl_Hash_Blake2_update_multi_blake2b_32(s0, ev, opad, (uint32_t)1U);
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
  ev2 = Hacl_Hash_Blake2_update_multi_blake2b_32(s0, ev1, full_blocks, n_blocks);
  uint8_t *rem = hash1 + full_blocks_len;
  FStar_UInt128_uint128
  ev3 =
    Hacl_Hash_Blake2_update_last_blake2b_32(s0,
      ev2,
      FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
        FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
      rem,
      rem_len);
  FStar_UInt128_uint128 ev11 = ev3;
  Hacl_Hash_Core_Blake2_finish_blake2b_32(s0, ev11, dst);
}

/* SNIPPET_END: Hacl_HMAC_compute_blake2b_32 */

