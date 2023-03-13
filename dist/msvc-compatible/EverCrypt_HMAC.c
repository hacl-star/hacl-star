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


#include "internal/EverCrypt_HMAC.h"

#include "internal/Hacl_Krmllib.h"
#include "internal/Hacl_Hash_SHA2.h"
#include "internal/Hacl_Hash_SHA1.h"
#include "internal/Hacl_HMAC.h"
#include "internal/EverCrypt_Hash.h"

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
(*EverCrypt_HMAC_hash_256)(uint8_t *x0, uint8_t *x1, uint32_t x2) =
  EverCrypt_Hash_Incremental_hash_256;

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
  uint8_t *key_block = (uint8_t *)alloca(l * sizeof (uint8_t));
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
    Hacl_Hash_SHA1_legacy_hash(nkey, key, key_len);
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
  uint32_t
  s[5U] =
    {
      (uint32_t)0x67452301U, (uint32_t)0xefcdab89U, (uint32_t)0x98badcfeU, (uint32_t)0x10325476U,
      (uint32_t)0xc3d2e1f0U
    };
  uint8_t *dst1 = ipad;
  if (data_len == (uint32_t)0U)
  {
    Hacl_Hash_SHA1_legacy_update_last(s, (uint64_t)0U, ipad, (uint32_t)64U);
  }
  else
  {
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
    uint8_t *rem = data + full_blocks_len;
    Hacl_Hash_SHA1_legacy_update_multi(s, ipad, (uint32_t)1U);
    Hacl_Hash_SHA1_legacy_update_multi(s, full_blocks, n_blocks);
    Hacl_Hash_SHA1_legacy_update_last(s,
      (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len,
      rem,
      rem_len);
  }
  Hacl_Hash_SHA1_legacy_finish(s, dst1);
  uint8_t *hash1 = ipad;
  Hacl_Hash_SHA1_legacy_init(s);
  uint32_t block_len = (uint32_t)64U;
  uint32_t n_blocks0 = (uint32_t)20U / block_len;
  uint32_t rem0 = (uint32_t)20U % block_len;
  K___uint32_t_uint32_t scrut;
  if (n_blocks0 > (uint32_t)0U && rem0 == (uint32_t)0U)
  {
    uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
    scrut =
      ((K___uint32_t_uint32_t){ .fst = n_blocks_, .snd = (uint32_t)20U - n_blocks_ * block_len });
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
  Hacl_Hash_SHA1_legacy_update_multi(s, opad, (uint32_t)1U);
  Hacl_Hash_SHA1_legacy_update_multi(s, full_blocks, n_blocks);
  Hacl_Hash_SHA1_legacy_update_last(s,
    (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len,
    rem,
    rem_len);
  Hacl_Hash_SHA1_legacy_finish(s, dst);
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
  uint8_t *key_block = (uint8_t *)alloca(l * sizeof (uint8_t));
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
    Hacl_Hash_SHA2_hash_256(nkey, key, key_len);
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
  uint32_t
  s[8U] =
    {
      (uint32_t)0x6a09e667U, (uint32_t)0xbb67ae85U, (uint32_t)0x3c6ef372U, (uint32_t)0xa54ff53aU,
      (uint32_t)0x510e527fU, (uint32_t)0x9b05688cU, (uint32_t)0x1f83d9abU, (uint32_t)0x5be0cd19U
    };
  uint8_t *dst1 = ipad;
  if (data_len == (uint32_t)0U)
  {
    EverCrypt_Hash_update_last_256(s, (uint64_t)0U, ipad, (uint32_t)64U);
  }
  else
  {
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
    uint8_t *rem = data + full_blocks_len;
    EverCrypt_Hash_update_multi_256(s, ipad, (uint32_t)1U);
    EverCrypt_Hash_update_multi_256(s, full_blocks, n_blocks);
    EverCrypt_Hash_update_last_256(s,
      (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len,
      rem,
      rem_len);
  }
  Hacl_Hash_Core_SHA2_finish_256(s, dst1);
  uint8_t *hash1 = ipad;
  Hacl_Hash_Core_SHA2_init_256(s);
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
  uint8_t *rem = hash1 + full_blocks_len;
  EverCrypt_Hash_update_multi_256(s, opad, (uint32_t)1U);
  EverCrypt_Hash_update_multi_256(s, full_blocks, n_blocks);
  EverCrypt_Hash_update_last_256(s,
    (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len,
    rem,
    rem_len);
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
  uint8_t *key_block = (uint8_t *)alloca(l * sizeof (uint8_t));
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
    Hacl_Hash_SHA2_hash_384(nkey, key, key_len);
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
  uint64_t
  s[8U] =
    {
      (uint64_t)0xcbbb9d5dc1059ed8U, (uint64_t)0x629a292a367cd507U, (uint64_t)0x9159015a3070dd17U,
      (uint64_t)0x152fecd8f70e5939U, (uint64_t)0x67332667ffc00b31U, (uint64_t)0x8eb44a8768581511U,
      (uint64_t)0xdb0c2e0d64f98fa7U, (uint64_t)0x47b5481dbefa4fa4U
    };
  uint8_t *dst1 = ipad;
  if (data_len == (uint32_t)0U)
  {
    Hacl_Hash_SHA2_update_last_384(s,
      FStar_UInt128_uint64_to_uint128((uint64_t)0U),
      ipad,
      (uint32_t)128U);
  }
  else
  {
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
    uint8_t *rem = data + full_blocks_len;
    Hacl_Hash_SHA2_update_multi_384(s, ipad, (uint32_t)1U);
    Hacl_Hash_SHA2_update_multi_384(s, full_blocks, n_blocks);
    Hacl_Hash_SHA2_update_last_384(s,
      FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
        FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
      rem,
      rem_len);
  }
  Hacl_Hash_Core_SHA2_finish_384(s, dst1);
  uint8_t *hash1 = ipad;
  Hacl_Hash_Core_SHA2_init_384(s);
  uint32_t block_len = (uint32_t)128U;
  uint32_t n_blocks0 = (uint32_t)48U / block_len;
  uint32_t rem0 = (uint32_t)48U % block_len;
  K___uint32_t_uint32_t scrut;
  if (n_blocks0 > (uint32_t)0U && rem0 == (uint32_t)0U)
  {
    uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
    scrut =
      ((K___uint32_t_uint32_t){ .fst = n_blocks_, .snd = (uint32_t)48U - n_blocks_ * block_len });
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
  Hacl_Hash_SHA2_update_multi_384(s, opad, (uint32_t)1U);
  Hacl_Hash_SHA2_update_multi_384(s, full_blocks, n_blocks);
  Hacl_Hash_SHA2_update_last_384(s,
    FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
      FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
    rem,
    rem_len);
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
    Hacl_Hash_SHA2_hash_512(nkey, key, key_len);
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
  uint64_t
  s[8U] =
    {
      (uint64_t)0x6a09e667f3bcc908U, (uint64_t)0xbb67ae8584caa73bU, (uint64_t)0x3c6ef372fe94f82bU,
      (uint64_t)0xa54ff53a5f1d36f1U, (uint64_t)0x510e527fade682d1U, (uint64_t)0x9b05688c2b3e6c1fU,
      (uint64_t)0x1f83d9abfb41bd6bU, (uint64_t)0x5be0cd19137e2179U
    };
  uint8_t *dst1 = ipad;
  if (data_len == (uint32_t)0U)
  {
    Hacl_Hash_SHA2_update_last_512(s,
      FStar_UInt128_uint64_to_uint128((uint64_t)0U),
      ipad,
      (uint32_t)128U);
  }
  else
  {
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
    uint8_t *rem = data + full_blocks_len;
    Hacl_Hash_SHA2_update_multi_512(s, ipad, (uint32_t)1U);
    Hacl_Hash_SHA2_update_multi_512(s, full_blocks, n_blocks);
    Hacl_Hash_SHA2_update_last_512(s,
      FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
        FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
      rem,
      rem_len);
  }
  Hacl_Hash_Core_SHA2_finish_512(s, dst1);
  uint8_t *hash1 = ipad;
  Hacl_Hash_Core_SHA2_init_512(s);
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
  uint8_t *rem = hash1 + full_blocks_len;
  Hacl_Hash_SHA2_update_multi_512(s, opad, (uint32_t)1U);
  Hacl_Hash_SHA2_update_multi_512(s, full_blocks, n_blocks);
  Hacl_Hash_SHA2_update_last_512(s,
    FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
      FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
    rem,
    rem_len);
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
  uint8_t *key_block = (uint8_t *)alloca(l * sizeof (uint8_t));
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
    Hacl_Hash_Blake2s_32_hash_with_key(nkey, (uint32_t)32U, key, key_len, NULL, (uint32_t)0U);
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
  uint32_t s[16U] = { 0U };
  Hacl_Hash_Blake2s_32_init(s, (uint32_t)0U, (uint32_t)32U);
  uint32_t *s0 = s;
  uint8_t *dst1 = ipad;
  if (data_len == (uint32_t)0U)
  {
    uint32_t wv[16U] = { 0U };
    Hacl_Hash_Blake2s_32_update_last((uint32_t)64U, wv, s0, (uint64_t)0U, (uint32_t)64U, ipad);
  }
  else
  {
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
    uint8_t *rem = data + full_blocks_len;
    uint32_t wv[16U] = { 0U };
    Hacl_Hash_Blake2s_32_update_multi((uint32_t)64U, wv, s0, (uint64_t)0U, ipad, (uint32_t)1U);
    uint32_t wv0[16U] = { 0U };
    Hacl_Hash_Blake2s_32_update_multi(n_blocks * (uint32_t)64U,
      wv0,
      s0,
      (uint64_t)block_len,
      full_blocks,
      n_blocks);
    uint32_t wv1[16U] = { 0U };
    Hacl_Hash_Blake2s_32_update_last(rem_len,
      wv1,
      s0,
      (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len,
      rem_len,
      rem);
  }
  Hacl_Hash_Blake2s_32_finish((uint32_t)32U, dst1, s0);
  uint8_t *hash1 = ipad;
  Hacl_Hash_Blake2s_32_init(s0, (uint32_t)0U, (uint32_t)32U);
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
  uint8_t *rem = hash1 + full_blocks_len;
  uint32_t wv[16U] = { 0U };
  Hacl_Hash_Blake2s_32_update_multi((uint32_t)64U, wv, s0, (uint64_t)0U, opad, (uint32_t)1U);
  uint32_t wv0[16U] = { 0U };
  Hacl_Hash_Blake2s_32_update_multi(n_blocks * (uint32_t)64U,
    wv0,
    s0,
    (uint64_t)block_len,
    full_blocks,
    n_blocks);
  uint32_t wv1[16U] = { 0U };
  Hacl_Hash_Blake2s_32_update_last(rem_len,
    wv1,
    s0,
    (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len,
    rem_len,
    rem);
  Hacl_Hash_Blake2s_32_finish((uint32_t)32U, dst, s0);
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
    Hacl_Hash_Blake2b_32_hash_with_key(nkey, (uint32_t)64U, key, key_len, NULL, (uint32_t)0U);
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
  uint64_t s[16U] = { 0U };
  Hacl_Hash_Blake2b_32_init(s, (uint32_t)0U, (uint32_t)64U);
  uint64_t *s0 = s;
  uint8_t *dst1 = ipad;
  if (data_len == (uint32_t)0U)
  {
    uint64_t wv[16U] = { 0U };
    Hacl_Hash_Blake2b_32_update_last((uint32_t)128U,
      wv,
      s0,
      FStar_UInt128_uint64_to_uint128((uint64_t)0U),
      (uint32_t)128U,
      ipad);
  }
  else
  {
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
    uint8_t *rem = data + full_blocks_len;
    uint64_t wv[16U] = { 0U };
    Hacl_Hash_Blake2b_32_update_multi((uint32_t)128U,
      wv,
      s0,
      FStar_UInt128_uint64_to_uint128((uint64_t)0U),
      ipad,
      (uint32_t)1U);
    uint64_t wv0[16U] = { 0U };
    Hacl_Hash_Blake2b_32_update_multi(n_blocks * (uint32_t)128U,
      wv0,
      s0,
      FStar_UInt128_uint64_to_uint128((uint64_t)block_len),
      full_blocks,
      n_blocks);
    uint64_t wv1[16U] = { 0U };
    Hacl_Hash_Blake2b_32_update_last(rem_len,
      wv1,
      s0,
      FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
        FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
      rem_len,
      rem);
  }
  Hacl_Hash_Blake2b_32_finish((uint32_t)64U, dst1, s0);
  uint8_t *hash1 = ipad;
  Hacl_Hash_Blake2b_32_init(s0, (uint32_t)0U, (uint32_t)64U);
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
  uint8_t *rem = hash1 + full_blocks_len;
  uint64_t wv[16U] = { 0U };
  Hacl_Hash_Blake2b_32_update_multi((uint32_t)128U,
    wv,
    s0,
    FStar_UInt128_uint64_to_uint128((uint64_t)0U),
    opad,
    (uint32_t)1U);
  uint64_t wv0[16U] = { 0U };
  Hacl_Hash_Blake2b_32_update_multi(n_blocks * (uint32_t)128U,
    wv0,
    s0,
    FStar_UInt128_uint64_to_uint128((uint64_t)block_len),
    full_blocks,
    n_blocks);
  uint64_t wv1[16U] = { 0U };
  Hacl_Hash_Blake2b_32_update_last(rem_len,
    wv1,
    s0,
    FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
      FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
    rem_len,
    rem);
  Hacl_Hash_Blake2b_32_finish((uint32_t)64U, dst, s0);
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
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

