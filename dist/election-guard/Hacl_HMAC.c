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

#include "internal/Hacl_Hash.h"

typedef struct __uint32_t_uint32_t_s
{
  uint32_t fst;
  uint32_t snd;
}
__uint32_t_uint32_t;

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
  {
    uint8_t *key_block = (uint8_t *)alloca(l * sizeof (uint8_t));
    memset(key_block, 0U, l * sizeof (uint8_t));
    {
      uint32_t i0;
      if (key_len <= (uint32_t)64U)
      {
        i0 = key_len;
      }
      else
      {
        i0 = (uint32_t)20U;
      }
      {
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
        {
          uint8_t *ipad = (uint8_t *)alloca(l * sizeof (uint8_t));
          memset(ipad, (uint8_t)0x36U, l * sizeof (uint8_t));
          {
            uint32_t i;
            for (i = (uint32_t)0U; i < l; i++)
            {
              uint8_t xi = ipad[i];
              uint8_t yi = key_block[i];
              ipad[i] = xi ^ yi;
            }
          }
          KRML_CHECK_SIZE(sizeof (uint8_t), l);
          {
            uint8_t *opad = (uint8_t *)alloca(l * sizeof (uint8_t));
            memset(opad, (uint8_t)0x5cU, l * sizeof (uint8_t));
            {
              uint32_t scrut0[5];
              uint32_t *s;
              uint8_t *dst1;
              uint8_t *hash1;
              uint32_t block_len;
              uint32_t n_blocks0;
              uint32_t rem0;
              __uint32_t_uint32_t scrut1;
              uint32_t n_blocks1;
              uint32_t rem_len0;
              uint32_t full_blocks_len0;
              uint8_t *full_blocks0;
              uint8_t *rem1;
              {
                uint32_t i;
                for (i = (uint32_t)0U; i < l; i++)
                {
                  uint8_t xi = opad[i];
                  uint8_t yi = key_block[i];
                  opad[i] = xi ^ yi;
                }
              }
              scrut0[0U] = (uint32_t)0x67452301U;
              scrut0[1U] = (uint32_t)0xefcdab89U;
              scrut0[2U] = (uint32_t)0x98badcfeU;
              scrut0[3U] = (uint32_t)0x10325476U;
              scrut0[4U] = (uint32_t)0xc3d2e1f0U;
              s = scrut0;
              dst1 = ipad;
              Hacl_Hash_Core_SHA1_legacy_init(s);
              if (data_len == (uint32_t)0U)
              {
                Hacl_Hash_SHA1_legacy_update_last(s, (uint64_t)0U, ipad, (uint32_t)64U);
              }
              else
              {
                Hacl_Hash_SHA1_legacy_update_multi(s, ipad, (uint32_t)1U);
                {
                  uint32_t block_len0 = (uint32_t)64U;
                  uint32_t n_blocks2 = data_len / block_len0;
                  uint32_t rem = data_len % block_len0;
                  __uint32_t_uint32_t scrut;
                  if (n_blocks2 > (uint32_t)0U && rem == (uint32_t)0U)
                  {
                    uint32_t n_blocks_ = n_blocks2 - (uint32_t)1U;
                    __uint32_t_uint32_t lit;
                    lit.fst = n_blocks_;
                    lit.snd = data_len - n_blocks_ * block_len0;
                    scrut = lit;
                  }
                  else
                  {
                    __uint32_t_uint32_t lit;
                    lit.fst = n_blocks2;
                    lit.snd = rem;
                    scrut = lit;
                  }
                  {
                    uint32_t n_blocks = scrut.fst;
                    uint32_t rem_len = scrut.snd;
                    uint32_t full_blocks_len = n_blocks * block_len0;
                    uint8_t *full_blocks = data;
                    Hacl_Hash_SHA1_legacy_update_multi(s, full_blocks, n_blocks);
                    {
                      uint8_t *rem2 = data + full_blocks_len;
                      Hacl_Hash_SHA1_legacy_update_last(s,
                        (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len,
                        rem2,
                        rem_len);
                    }
                  }
                }
              }
              Hacl_Hash_Core_SHA1_legacy_finish(s, dst1);
              hash1 = ipad;
              Hacl_Hash_Core_SHA1_legacy_init(s);
              Hacl_Hash_SHA1_legacy_update_multi(s, opad, (uint32_t)1U);
              block_len = (uint32_t)64U;
              n_blocks0 = (uint32_t)20U / block_len;
              rem0 = (uint32_t)20U % block_len;
              if (n_blocks0 > (uint32_t)0U && rem0 == (uint32_t)0U)
              {
                uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
                __uint32_t_uint32_t lit;
                lit.fst = n_blocks_;
                lit.snd = (uint32_t)20U - n_blocks_ * block_len;
                scrut1 = lit;
              }
              else
              {
                __uint32_t_uint32_t lit;
                lit.fst = n_blocks0;
                lit.snd = rem0;
                scrut1 = lit;
              }
              n_blocks1 = scrut1.fst;
              rem_len0 = scrut1.snd;
              full_blocks_len0 = n_blocks1 * block_len;
              full_blocks0 = hash1;
              Hacl_Hash_SHA1_legacy_update_multi(s, full_blocks0, n_blocks1);
              rem1 = hash1 + full_blocks_len0;
              Hacl_Hash_SHA1_legacy_update_last(s,
                (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len0,
                rem1,
                rem_len0);
              Hacl_Hash_Core_SHA1_legacy_finish(s, dst);
            }
          }
        }
      }
    }
  }
}

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
  {
    uint8_t *key_block = (uint8_t *)alloca(l * sizeof (uint8_t));
    memset(key_block, 0U, l * sizeof (uint8_t));
    {
      uint32_t i0;
      if (key_len <= (uint32_t)64U)
      {
        i0 = key_len;
      }
      else
      {
        i0 = (uint32_t)32U;
      }
      {
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
        {
          uint8_t *ipad = (uint8_t *)alloca(l * sizeof (uint8_t));
          memset(ipad, (uint8_t)0x36U, l * sizeof (uint8_t));
          {
            uint32_t i;
            for (i = (uint32_t)0U; i < l; i++)
            {
              uint8_t xi = ipad[i];
              uint8_t yi = key_block[i];
              ipad[i] = xi ^ yi;
            }
          }
          KRML_CHECK_SIZE(sizeof (uint8_t), l);
          {
            uint8_t *opad = (uint8_t *)alloca(l * sizeof (uint8_t));
            memset(opad, (uint8_t)0x5cU, l * sizeof (uint8_t));
            {
              uint32_t scrut0[8];
              uint32_t *s;
              uint8_t *dst1;
              uint8_t *hash1;
              uint32_t block_len;
              uint32_t n_blocks0;
              uint32_t rem0;
              __uint32_t_uint32_t scrut1;
              uint32_t n_blocks1;
              uint32_t rem_len0;
              uint32_t full_blocks_len0;
              uint8_t *full_blocks0;
              uint8_t *rem1;
              {
                uint32_t i;
                for (i = (uint32_t)0U; i < l; i++)
                {
                  uint8_t xi = opad[i];
                  uint8_t yi = key_block[i];
                  opad[i] = xi ^ yi;
                }
              }
              scrut0[0U] = (uint32_t)0x6a09e667U;
              scrut0[1U] = (uint32_t)0xbb67ae85U;
              scrut0[2U] = (uint32_t)0x3c6ef372U;
              scrut0[3U] = (uint32_t)0xa54ff53aU;
              scrut0[4U] = (uint32_t)0x510e527fU;
              scrut0[5U] = (uint32_t)0x9b05688cU;
              scrut0[6U] = (uint32_t)0x1f83d9abU;
              scrut0[7U] = (uint32_t)0x5be0cd19U;
              s = scrut0;
              dst1 = ipad;
              Hacl_Hash_Core_SHA2_init_256(s);
              if (data_len == (uint32_t)0U)
              {
                Hacl_Hash_SHA2_update_last_256(s, (uint64_t)0U, ipad, (uint32_t)64U);
              }
              else
              {
                Hacl_Hash_SHA2_update_multi_256(s, ipad, (uint32_t)1U);
                {
                  uint32_t block_len0 = (uint32_t)64U;
                  uint32_t n_blocks2 = data_len / block_len0;
                  uint32_t rem = data_len % block_len0;
                  __uint32_t_uint32_t scrut;
                  if (n_blocks2 > (uint32_t)0U && rem == (uint32_t)0U)
                  {
                    uint32_t n_blocks_ = n_blocks2 - (uint32_t)1U;
                    __uint32_t_uint32_t lit;
                    lit.fst = n_blocks_;
                    lit.snd = data_len - n_blocks_ * block_len0;
                    scrut = lit;
                  }
                  else
                  {
                    __uint32_t_uint32_t lit;
                    lit.fst = n_blocks2;
                    lit.snd = rem;
                    scrut = lit;
                  }
                  {
                    uint32_t n_blocks = scrut.fst;
                    uint32_t rem_len = scrut.snd;
                    uint32_t full_blocks_len = n_blocks * block_len0;
                    uint8_t *full_blocks = data;
                    Hacl_Hash_SHA2_update_multi_256(s, full_blocks, n_blocks);
                    {
                      uint8_t *rem2 = data + full_blocks_len;
                      Hacl_Hash_SHA2_update_last_256(s,
                        (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len,
                        rem2,
                        rem_len);
                    }
                  }
                }
              }
              Hacl_Hash_Core_SHA2_finish_256(s, dst1);
              hash1 = ipad;
              Hacl_Hash_Core_SHA2_init_256(s);
              Hacl_Hash_SHA2_update_multi_256(s, opad, (uint32_t)1U);
              block_len = (uint32_t)64U;
              n_blocks0 = (uint32_t)32U / block_len;
              rem0 = (uint32_t)32U % block_len;
              if (n_blocks0 > (uint32_t)0U && rem0 == (uint32_t)0U)
              {
                uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
                __uint32_t_uint32_t lit;
                lit.fst = n_blocks_;
                lit.snd = (uint32_t)32U - n_blocks_ * block_len;
                scrut1 = lit;
              }
              else
              {
                __uint32_t_uint32_t lit;
                lit.fst = n_blocks0;
                lit.snd = rem0;
                scrut1 = lit;
              }
              n_blocks1 = scrut1.fst;
              rem_len0 = scrut1.snd;
              full_blocks_len0 = n_blocks1 * block_len;
              full_blocks0 = hash1;
              Hacl_Hash_SHA2_update_multi_256(s, full_blocks0, n_blocks1);
              rem1 = hash1 + full_blocks_len0;
              Hacl_Hash_SHA2_update_last_256(s,
                (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len0,
                rem1,
                rem_len0);
              Hacl_Hash_Core_SHA2_finish_256(s, dst);
            }
          }
        }
      }
    }
  }
}

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
  {
    uint8_t *key_block = (uint8_t *)alloca(l * sizeof (uint8_t));
    memset(key_block, 0U, l * sizeof (uint8_t));
    {
      uint32_t i0;
      if (key_len <= (uint32_t)128U)
      {
        i0 = key_len;
      }
      else
      {
        i0 = (uint32_t)48U;
      }
      {
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
        {
          uint8_t *ipad = (uint8_t *)alloca(l * sizeof (uint8_t));
          memset(ipad, (uint8_t)0x36U, l * sizeof (uint8_t));
          {
            uint32_t i;
            for (i = (uint32_t)0U; i < l; i++)
            {
              uint8_t xi = ipad[i];
              uint8_t yi = key_block[i];
              ipad[i] = xi ^ yi;
            }
          }
          KRML_CHECK_SIZE(sizeof (uint8_t), l);
          {
            uint8_t *opad = (uint8_t *)alloca(l * sizeof (uint8_t));
            memset(opad, (uint8_t)0x5cU, l * sizeof (uint8_t));
            {
              uint64_t scrut0[8];
              uint64_t *s;
              uint8_t *dst1;
              uint8_t *hash1;
              uint32_t block_len;
              uint32_t n_blocks0;
              uint32_t rem0;
              __uint32_t_uint32_t scrut1;
              uint32_t n_blocks1;
              uint32_t rem_len0;
              uint32_t full_blocks_len0;
              uint8_t *full_blocks0;
              uint8_t *rem1;
              {
                uint32_t i;
                for (i = (uint32_t)0U; i < l; i++)
                {
                  uint8_t xi = opad[i];
                  uint8_t yi = key_block[i];
                  opad[i] = xi ^ yi;
                }
              }
              scrut0[0U] = (uint64_t)0xcbbb9d5dc1059ed8U;
              scrut0[1U] = (uint64_t)0x629a292a367cd507U;
              scrut0[2U] = (uint64_t)0x9159015a3070dd17U;
              scrut0[3U] = (uint64_t)0x152fecd8f70e5939U;
              scrut0[4U] = (uint64_t)0x67332667ffc00b31U;
              scrut0[5U] = (uint64_t)0x8eb44a8768581511U;
              scrut0[6U] = (uint64_t)0xdb0c2e0d64f98fa7U;
              scrut0[7U] = (uint64_t)0x47b5481dbefa4fa4U;
              s = scrut0;
              dst1 = ipad;
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
                {
                  uint32_t block_len0 = (uint32_t)128U;
                  uint32_t n_blocks2 = data_len / block_len0;
                  uint32_t rem = data_len % block_len0;
                  __uint32_t_uint32_t scrut;
                  if (n_blocks2 > (uint32_t)0U && rem == (uint32_t)0U)
                  {
                    uint32_t n_blocks_ = n_blocks2 - (uint32_t)1U;
                    __uint32_t_uint32_t lit;
                    lit.fst = n_blocks_;
                    lit.snd = data_len - n_blocks_ * block_len0;
                    scrut = lit;
                  }
                  else
                  {
                    __uint32_t_uint32_t lit;
                    lit.fst = n_blocks2;
                    lit.snd = rem;
                    scrut = lit;
                  }
                  {
                    uint32_t n_blocks = scrut.fst;
                    uint32_t rem_len = scrut.snd;
                    uint32_t full_blocks_len = n_blocks * block_len0;
                    uint8_t *full_blocks = data;
                    Hacl_Hash_SHA2_update_multi_384(s, full_blocks, n_blocks);
                    {
                      uint8_t *rem2 = data + full_blocks_len;
                      Hacl_Hash_SHA2_update_last_384(s,
                        FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
                          FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
                        rem2,
                        rem_len);
                    }
                  }
                }
              }
              Hacl_Hash_Core_SHA2_finish_384(s, dst1);
              hash1 = ipad;
              Hacl_Hash_Core_SHA2_init_384(s);
              Hacl_Hash_SHA2_update_multi_384(s, opad, (uint32_t)1U);
              block_len = (uint32_t)128U;
              n_blocks0 = (uint32_t)48U / block_len;
              rem0 = (uint32_t)48U % block_len;
              if (n_blocks0 > (uint32_t)0U && rem0 == (uint32_t)0U)
              {
                uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
                __uint32_t_uint32_t lit;
                lit.fst = n_blocks_;
                lit.snd = (uint32_t)48U - n_blocks_ * block_len;
                scrut1 = lit;
              }
              else
              {
                __uint32_t_uint32_t lit;
                lit.fst = n_blocks0;
                lit.snd = rem0;
                scrut1 = lit;
              }
              n_blocks1 = scrut1.fst;
              rem_len0 = scrut1.snd;
              full_blocks_len0 = n_blocks1 * block_len;
              full_blocks0 = hash1;
              Hacl_Hash_SHA2_update_multi_384(s, full_blocks0, n_blocks1);
              rem1 = hash1 + full_blocks_len0;
              Hacl_Hash_SHA2_update_last_384(s,
                FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
                  FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len0)),
                rem1,
                rem_len0);
              Hacl_Hash_Core_SHA2_finish_384(s, dst);
            }
          }
        }
      }
    }
  }
}

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
  {
    uint8_t *key_block = (uint8_t *)alloca(l * sizeof (uint8_t));
    memset(key_block, 0U, l * sizeof (uint8_t));
    {
      uint32_t i0;
      if (key_len <= (uint32_t)128U)
      {
        i0 = key_len;
      }
      else
      {
        i0 = (uint32_t)64U;
      }
      {
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
        {
          uint8_t *ipad = (uint8_t *)alloca(l * sizeof (uint8_t));
          memset(ipad, (uint8_t)0x36U, l * sizeof (uint8_t));
          {
            uint32_t i;
            for (i = (uint32_t)0U; i < l; i++)
            {
              uint8_t xi = ipad[i];
              uint8_t yi = key_block[i];
              ipad[i] = xi ^ yi;
            }
          }
          KRML_CHECK_SIZE(sizeof (uint8_t), l);
          {
            uint8_t *opad = (uint8_t *)alloca(l * sizeof (uint8_t));
            memset(opad, (uint8_t)0x5cU, l * sizeof (uint8_t));
            {
              uint64_t scrut0[8];
              uint64_t *s;
              uint8_t *dst1;
              uint8_t *hash1;
              uint32_t block_len;
              uint32_t n_blocks0;
              uint32_t rem0;
              __uint32_t_uint32_t scrut1;
              uint32_t n_blocks1;
              uint32_t rem_len0;
              uint32_t full_blocks_len0;
              uint8_t *full_blocks0;
              uint8_t *rem1;
              {
                uint32_t i;
                for (i = (uint32_t)0U; i < l; i++)
                {
                  uint8_t xi = opad[i];
                  uint8_t yi = key_block[i];
                  opad[i] = xi ^ yi;
                }
              }
              scrut0[0U] = (uint64_t)0x6a09e667f3bcc908U;
              scrut0[1U] = (uint64_t)0xbb67ae8584caa73bU;
              scrut0[2U] = (uint64_t)0x3c6ef372fe94f82bU;
              scrut0[3U] = (uint64_t)0xa54ff53a5f1d36f1U;
              scrut0[4U] = (uint64_t)0x510e527fade682d1U;
              scrut0[5U] = (uint64_t)0x9b05688c2b3e6c1fU;
              scrut0[6U] = (uint64_t)0x1f83d9abfb41bd6bU;
              scrut0[7U] = (uint64_t)0x5be0cd19137e2179U;
              s = scrut0;
              dst1 = ipad;
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
                {
                  uint32_t block_len0 = (uint32_t)128U;
                  uint32_t n_blocks2 = data_len / block_len0;
                  uint32_t rem = data_len % block_len0;
                  __uint32_t_uint32_t scrut;
                  if (n_blocks2 > (uint32_t)0U && rem == (uint32_t)0U)
                  {
                    uint32_t n_blocks_ = n_blocks2 - (uint32_t)1U;
                    __uint32_t_uint32_t lit;
                    lit.fst = n_blocks_;
                    lit.snd = data_len - n_blocks_ * block_len0;
                    scrut = lit;
                  }
                  else
                  {
                    __uint32_t_uint32_t lit;
                    lit.fst = n_blocks2;
                    lit.snd = rem;
                    scrut = lit;
                  }
                  {
                    uint32_t n_blocks = scrut.fst;
                    uint32_t rem_len = scrut.snd;
                    uint32_t full_blocks_len = n_blocks * block_len0;
                    uint8_t *full_blocks = data;
                    Hacl_Hash_SHA2_update_multi_512(s, full_blocks, n_blocks);
                    {
                      uint8_t *rem2 = data + full_blocks_len;
                      Hacl_Hash_SHA2_update_last_512(s,
                        FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
                          FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
                        rem2,
                        rem_len);
                    }
                  }
                }
              }
              Hacl_Hash_Core_SHA2_finish_512(s, dst1);
              hash1 = ipad;
              Hacl_Hash_Core_SHA2_init_512(s);
              Hacl_Hash_SHA2_update_multi_512(s, opad, (uint32_t)1U);
              block_len = (uint32_t)128U;
              n_blocks0 = (uint32_t)64U / block_len;
              rem0 = (uint32_t)64U % block_len;
              if (n_blocks0 > (uint32_t)0U && rem0 == (uint32_t)0U)
              {
                uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
                __uint32_t_uint32_t lit;
                lit.fst = n_blocks_;
                lit.snd = (uint32_t)64U - n_blocks_ * block_len;
                scrut1 = lit;
              }
              else
              {
                __uint32_t_uint32_t lit;
                lit.fst = n_blocks0;
                lit.snd = rem0;
                scrut1 = lit;
              }
              n_blocks1 = scrut1.fst;
              rem_len0 = scrut1.snd;
              full_blocks_len0 = n_blocks1 * block_len;
              full_blocks0 = hash1;
              Hacl_Hash_SHA2_update_multi_512(s, full_blocks0, n_blocks1);
              rem1 = hash1 + full_blocks_len0;
              Hacl_Hash_SHA2_update_last_512(s,
                FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
                  FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len0)),
                rem1,
                rem_len0);
              Hacl_Hash_Core_SHA2_finish_512(s, dst);
            }
          }
        }
      }
    }
  }
}

