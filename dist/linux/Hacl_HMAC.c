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


#include "Hacl_HMAC.h"

void Hacl_HMAC_legacy_compute_sha1(u8 *dst, u8 *key, u32 key_len, u8 *data, u32 data_len)
{
  u32 l = (u32)64U;
  KRML_CHECK_SIZE(sizeof (u8), l);
  {
    u8 key_block[l];
    memset(key_block, 0U, l * sizeof (key_block[0U]));
    {
      u32 i1;
      if (key_len <= (u32)64U)
        i1 = key_len;
      else
        i1 = (u32)20U;
      {
        u8 *nkey = key_block;
        if (key_len <= (u32)64U)
          memcpy(nkey, key, key_len * sizeof (key[0U]));
        else
          Hacl_Hash_SHA1_legacy_hash(key, key_len, nkey);
        KRML_CHECK_SIZE(sizeof (u8), l);
        {
          u8 ipad[l];
          memset(ipad, (u8)0x36U, l * sizeof (ipad[0U]));
          {
            u32 i;
            for (i = (u32)0U; i < l; i++)
            {
              u8 xi = ipad[i];
              u8 yi = key_block[i];
              ipad[i] = xi ^ yi;
            }
          }
          KRML_CHECK_SIZE(sizeof (u8), l);
          {
            u8 opad[l];
            memset(opad, (u8)0x5cU, l * sizeof (opad[0U]));
            {
              u32 s[5];
              u8 *dst1;
              u8 *hash1;
              {
                u32 i;
                for (i = (u32)0U; i < l; i++)
                {
                  u8 xi = opad[i];
                  u8 yi = key_block[i];
                  opad[i] = xi ^ yi;
                }
              }
              s[0U] = (u32)0x67452301U;
              s[1U] = (u32)0xefcdab89U;
              s[2U] = (u32)0x98badcfeU;
              s[3U] = (u32)0x10325476U;
              s[4U] = (u32)0xc3d2e1f0U;
              Hacl_Hash_Core_SHA1_legacy_init(s);
              Hacl_Hash_SHA1_legacy_update_multi(s, ipad, (u32)1U);
              Hacl_Hash_SHA1_legacy_update_last(s, (u64)(u32)64U, data, data_len);
              dst1 = ipad;
              Hacl_Hash_Core_SHA1_legacy_finish(s, dst1);
              hash1 = ipad;
              Hacl_Hash_Core_SHA1_legacy_init(s);
              Hacl_Hash_SHA1_legacy_update_multi(s, opad, (u32)1U);
              Hacl_Hash_SHA1_legacy_update_last(s, (u64)(u32)64U, hash1, (u32)20U);
              Hacl_Hash_Core_SHA1_legacy_finish(s, dst);
            }
          }
        }
      }
    }
  }
}

void Hacl_HMAC_compute_sha2_256(u8 *dst, u8 *key, u32 key_len, u8 *data, u32 data_len)
{
  u32 l = (u32)64U;
  KRML_CHECK_SIZE(sizeof (u8), l);
  {
    u8 key_block[l];
    memset(key_block, 0U, l * sizeof (key_block[0U]));
    {
      u32 i1;
      if (key_len <= (u32)64U)
        i1 = key_len;
      else
        i1 = (u32)32U;
      {
        u8 *nkey = key_block;
        if (key_len <= (u32)64U)
          memcpy(nkey, key, key_len * sizeof (key[0U]));
        else
          Hacl_Hash_SHA2_hash_256(key, key_len, nkey);
        KRML_CHECK_SIZE(sizeof (u8), l);
        {
          u8 ipad[l];
          memset(ipad, (u8)0x36U, l * sizeof (ipad[0U]));
          {
            u32 i;
            for (i = (u32)0U; i < l; i++)
            {
              u8 xi = ipad[i];
              u8 yi = key_block[i];
              ipad[i] = xi ^ yi;
            }
          }
          KRML_CHECK_SIZE(sizeof (u8), l);
          {
            u8 opad[l];
            memset(opad, (u8)0x5cU, l * sizeof (opad[0U]));
            {
              u32 s[8];
              u8 *dst1;
              u8 *hash1;
              {
                u32 i;
                for (i = (u32)0U; i < l; i++)
                {
                  u8 xi = opad[i];
                  u8 yi = key_block[i];
                  opad[i] = xi ^ yi;
                }
              }
              s[0U] = (u32)0x6a09e667U;
              s[1U] = (u32)0xbb67ae85U;
              s[2U] = (u32)0x3c6ef372U;
              s[3U] = (u32)0xa54ff53aU;
              s[4U] = (u32)0x510e527fU;
              s[5U] = (u32)0x9b05688cU;
              s[6U] = (u32)0x1f83d9abU;
              s[7U] = (u32)0x5be0cd19U;
              Hacl_Hash_Core_SHA2_init_256(s);
              Hacl_Hash_SHA2_update_multi_256(s, ipad, (u32)1U);
              Hacl_Hash_SHA2_update_last_256(s, (u64)(u32)64U, data, data_len);
              dst1 = ipad;
              Hacl_Hash_Core_SHA2_finish_256(s, dst1);
              hash1 = ipad;
              Hacl_Hash_Core_SHA2_init_256(s);
              Hacl_Hash_SHA2_update_multi_256(s, opad, (u32)1U);
              Hacl_Hash_SHA2_update_last_256(s, (u64)(u32)64U, hash1, (u32)32U);
              Hacl_Hash_Core_SHA2_finish_256(s, dst);
            }
          }
        }
      }
    }
  }
}

void Hacl_HMAC_compute_sha2_384(u8 *dst, u8 *key, u32 key_len, u8 *data, u32 data_len)
{
  u32 l = (u32)128U;
  KRML_CHECK_SIZE(sizeof (u8), l);
  {
    u8 key_block[l];
    memset(key_block, 0U, l * sizeof (key_block[0U]));
    {
      u32 i1;
      if (key_len <= (u32)128U)
        i1 = key_len;
      else
        i1 = (u32)48U;
      {
        u8 *nkey = key_block;
        if (key_len <= (u32)128U)
          memcpy(nkey, key, key_len * sizeof (key[0U]));
        else
          Hacl_Hash_SHA2_hash_384(key, key_len, nkey);
        KRML_CHECK_SIZE(sizeof (u8), l);
        {
          u8 ipad[l];
          memset(ipad, (u8)0x36U, l * sizeof (ipad[0U]));
          {
            u32 i;
            for (i = (u32)0U; i < l; i++)
            {
              u8 xi = ipad[i];
              u8 yi = key_block[i];
              ipad[i] = xi ^ yi;
            }
          }
          KRML_CHECK_SIZE(sizeof (u8), l);
          {
            u8 opad[l];
            memset(opad, (u8)0x5cU, l * sizeof (opad[0U]));
            {
              u64 s[8];
              u8 *dst1;
              u8 *hash1;
              {
                u32 i;
                for (i = (u32)0U; i < l; i++)
                {
                  u8 xi = opad[i];
                  u8 yi = key_block[i];
                  opad[i] = xi ^ yi;
                }
              }
              s[0U] = (u64)0xcbbb9d5dc1059ed8U;
              s[1U] = (u64)0x629a292a367cd507U;
              s[2U] = (u64)0x9159015a3070dd17U;
              s[3U] = (u64)0x152fecd8f70e5939U;
              s[4U] = (u64)0x67332667ffc00b31U;
              s[5U] = (u64)0x8eb44a8768581511U;
              s[6U] = (u64)0xdb0c2e0d64f98fa7U;
              s[7U] = (u64)0x47b5481dbefa4fa4U;
              Hacl_Hash_Core_SHA2_init_384(s);
              Hacl_Hash_SHA2_update_multi_384(s, ipad, (u32)1U);
              Hacl_Hash_SHA2_update_last_384(s, (uint128_t)(u64)(u32)128U, data, data_len);
              dst1 = ipad;
              Hacl_Hash_Core_SHA2_finish_384(s, dst1);
              hash1 = ipad;
              Hacl_Hash_Core_SHA2_init_384(s);
              Hacl_Hash_SHA2_update_multi_384(s, opad, (u32)1U);
              Hacl_Hash_SHA2_update_last_384(s, (uint128_t)(u64)(u32)128U, hash1, (u32)48U);
              Hacl_Hash_Core_SHA2_finish_384(s, dst);
            }
          }
        }
      }
    }
  }
}

void Hacl_HMAC_compute_sha2_512(u8 *dst, u8 *key, u32 key_len, u8 *data, u32 data_len)
{
  u32 l = (u32)128U;
  KRML_CHECK_SIZE(sizeof (u8), l);
  {
    u8 key_block[l];
    memset(key_block, 0U, l * sizeof (key_block[0U]));
    {
      u32 i1;
      if (key_len <= (u32)128U)
        i1 = key_len;
      else
        i1 = (u32)64U;
      {
        u8 *nkey = key_block;
        if (key_len <= (u32)128U)
          memcpy(nkey, key, key_len * sizeof (key[0U]));
        else
          Hacl_Hash_SHA2_hash_512(key, key_len, nkey);
        KRML_CHECK_SIZE(sizeof (u8), l);
        {
          u8 ipad[l];
          memset(ipad, (u8)0x36U, l * sizeof (ipad[0U]));
          {
            u32 i;
            for (i = (u32)0U; i < l; i++)
            {
              u8 xi = ipad[i];
              u8 yi = key_block[i];
              ipad[i] = xi ^ yi;
            }
          }
          KRML_CHECK_SIZE(sizeof (u8), l);
          {
            u8 opad[l];
            memset(opad, (u8)0x5cU, l * sizeof (opad[0U]));
            {
              u64 s[8];
              u8 *dst1;
              u8 *hash1;
              {
                u32 i;
                for (i = (u32)0U; i < l; i++)
                {
                  u8 xi = opad[i];
                  u8 yi = key_block[i];
                  opad[i] = xi ^ yi;
                }
              }
              s[0U] = (u64)0x6a09e667f3bcc908U;
              s[1U] = (u64)0xbb67ae8584caa73bU;
              s[2U] = (u64)0x3c6ef372fe94f82bU;
              s[3U] = (u64)0xa54ff53a5f1d36f1U;
              s[4U] = (u64)0x510e527fade682d1U;
              s[5U] = (u64)0x9b05688c2b3e6c1fU;
              s[6U] = (u64)0x1f83d9abfb41bd6bU;
              s[7U] = (u64)0x5be0cd19137e2179U;
              Hacl_Hash_Core_SHA2_init_512(s);
              Hacl_Hash_SHA2_update_multi_512(s, ipad, (u32)1U);
              Hacl_Hash_SHA2_update_last_512(s, (uint128_t)(u64)(u32)128U, data, data_len);
              dst1 = ipad;
              Hacl_Hash_Core_SHA2_finish_512(s, dst1);
              hash1 = ipad;
              Hacl_Hash_Core_SHA2_init_512(s);
              Hacl_Hash_SHA2_update_multi_512(s, opad, (u32)1U);
              Hacl_Hash_SHA2_update_last_512(s, (uint128_t)(u64)(u32)128U, hash1, (u32)64U);
              Hacl_Hash_Core_SHA2_finish_512(s, dst);
            }
          }
        }
      }
    }
  }
}

