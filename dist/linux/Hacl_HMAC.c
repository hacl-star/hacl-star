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
    memset(key_block, 0U, l * sizeof (u8));
    {
      u32 i0;
      if (key_len <= (u32)64U)
        i0 = key_len;
      else
        i0 = (u32)20U;
      {
        u8 *nkey = key_block;
        if (key_len <= (u32)64U)
          memcpy(nkey, key, key_len * sizeof (u8));
        else
          Hacl_Hash_SHA1_legacy_hash(key, key_len, nkey);
        KRML_CHECK_SIZE(sizeof (u8), l);
        {
          u8 ipad[l];
          memset(ipad, (u8)0x36U, l * sizeof (u8));
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
            memset(opad, (u8)0x5cU, l * sizeof (u8));
            {
              u32 scrut[5];
              u32 *s;
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
              scrut[0U] = (u32)0x67452301U;
              scrut[1U] = (u32)0xefcdab89U;
              scrut[2U] = (u32)0x98badcfeU;
              scrut[3U] = (u32)0x10325476U;
              scrut[4U] = (u32)0xc3d2e1f0U;
              s = scrut;
              dst1 = ipad;
              Hacl_Hash_Core_SHA1_legacy_init(s);
              if (data_len == (u32)0U)
                Hacl_Hash_SHA1_legacy_update_last(s, (u64)0U, ipad, (u32)64U);
              else
              {
                Hacl_Hash_SHA1_legacy_update_multi(s, ipad, (u32)1U);
                Hacl_Hash_SHA1_legacy_update_last(s, (u64)(u32)64U, data, data_len);
              }
              Hacl_Hash_Core_SHA1_legacy_finish(s, dst1);
              hash1 = ipad;
              Hacl_Hash_Core_SHA1_legacy_init(s);
              if ((u32)20U == (u32)0U)
                Hacl_Hash_SHA1_legacy_update_last(s, (u64)0U, opad, (u32)64U);
              else
              {
                Hacl_Hash_SHA1_legacy_update_multi(s, opad, (u32)1U);
                Hacl_Hash_SHA1_legacy_update_last(s, (u64)(u32)64U, hash1, (u32)20U);
              }
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
    memset(key_block, 0U, l * sizeof (u8));
    {
      u32 i0;
      if (key_len <= (u32)64U)
        i0 = key_len;
      else
        i0 = (u32)32U;
      {
        u8 *nkey = key_block;
        if (key_len <= (u32)64U)
          memcpy(nkey, key, key_len * sizeof (u8));
        else
          Hacl_Hash_SHA2_hash_256(key, key_len, nkey);
        KRML_CHECK_SIZE(sizeof (u8), l);
        {
          u8 ipad[l];
          memset(ipad, (u8)0x36U, l * sizeof (u8));
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
            memset(opad, (u8)0x5cU, l * sizeof (u8));
            {
              u32 scrut[8];
              u32 *s;
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
              scrut[0U] = (u32)0x6a09e667U;
              scrut[1U] = (u32)0xbb67ae85U;
              scrut[2U] = (u32)0x3c6ef372U;
              scrut[3U] = (u32)0xa54ff53aU;
              scrut[4U] = (u32)0x510e527fU;
              scrut[5U] = (u32)0x9b05688cU;
              scrut[6U] = (u32)0x1f83d9abU;
              scrut[7U] = (u32)0x5be0cd19U;
              s = scrut;
              dst1 = ipad;
              Hacl_Hash_Core_SHA2_init_256(s);
              if (data_len == (u32)0U)
                Hacl_Hash_SHA2_update_last_256(s, (u64)0U, ipad, (u32)64U);
              else
              {
                Hacl_Hash_SHA2_update_multi_256(s, ipad, (u32)1U);
                Hacl_Hash_SHA2_update_last_256(s, (u64)(u32)64U, data, data_len);
              }
              Hacl_Hash_Core_SHA2_finish_256(s, dst1);
              hash1 = ipad;
              Hacl_Hash_Core_SHA2_init_256(s);
              if ((u32)32U == (u32)0U)
                Hacl_Hash_SHA2_update_last_256(s, (u64)0U, opad, (u32)64U);
              else
              {
                Hacl_Hash_SHA2_update_multi_256(s, opad, (u32)1U);
                Hacl_Hash_SHA2_update_last_256(s, (u64)(u32)64U, hash1, (u32)32U);
              }
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
    memset(key_block, 0U, l * sizeof (u8));
    {
      u32 i0;
      if (key_len <= (u32)128U)
        i0 = key_len;
      else
        i0 = (u32)48U;
      {
        u8 *nkey = key_block;
        if (key_len <= (u32)128U)
          memcpy(nkey, key, key_len * sizeof (u8));
        else
          Hacl_Hash_SHA2_hash_384(key, key_len, nkey);
        KRML_CHECK_SIZE(sizeof (u8), l);
        {
          u8 ipad[l];
          memset(ipad, (u8)0x36U, l * sizeof (u8));
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
            memset(opad, (u8)0x5cU, l * sizeof (u8));
            {
              u64 scrut[8];
              u64 *s;
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
              scrut[0U] = (u64)0xcbbb9d5dc1059ed8U;
              scrut[1U] = (u64)0x629a292a367cd507U;
              scrut[2U] = (u64)0x9159015a3070dd17U;
              scrut[3U] = (u64)0x152fecd8f70e5939U;
              scrut[4U] = (u64)0x67332667ffc00b31U;
              scrut[5U] = (u64)0x8eb44a8768581511U;
              scrut[6U] = (u64)0xdb0c2e0d64f98fa7U;
              scrut[7U] = (u64)0x47b5481dbefa4fa4U;
              s = scrut;
              dst1 = ipad;
              Hacl_Hash_Core_SHA2_init_384(s);
              if (data_len == (u32)0U)
                Hacl_Hash_SHA2_update_last_384(s, (uint128_t)(u64)0U, ipad, (u32)128U);
              else
              {
                Hacl_Hash_SHA2_update_multi_384(s, ipad, (u32)1U);
                Hacl_Hash_SHA2_update_last_384(s, (uint128_t)(u64)(u32)128U, data, data_len);
              }
              Hacl_Hash_Core_SHA2_finish_384(s, dst1);
              hash1 = ipad;
              Hacl_Hash_Core_SHA2_init_384(s);
              if ((u32)48U == (u32)0U)
                Hacl_Hash_SHA2_update_last_384(s, (uint128_t)(u64)0U, opad, (u32)128U);
              else
              {
                Hacl_Hash_SHA2_update_multi_384(s, opad, (u32)1U);
                Hacl_Hash_SHA2_update_last_384(s, (uint128_t)(u64)(u32)128U, hash1, (u32)48U);
              }
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
    memset(key_block, 0U, l * sizeof (u8));
    {
      u32 i0;
      if (key_len <= (u32)128U)
        i0 = key_len;
      else
        i0 = (u32)64U;
      {
        u8 *nkey = key_block;
        if (key_len <= (u32)128U)
          memcpy(nkey, key, key_len * sizeof (u8));
        else
          Hacl_Hash_SHA2_hash_512(key, key_len, nkey);
        KRML_CHECK_SIZE(sizeof (u8), l);
        {
          u8 ipad[l];
          memset(ipad, (u8)0x36U, l * sizeof (u8));
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
            memset(opad, (u8)0x5cU, l * sizeof (u8));
            {
              u64 scrut[8];
              u64 *s;
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
              scrut[0U] = (u64)0x6a09e667f3bcc908U;
              scrut[1U] = (u64)0xbb67ae8584caa73bU;
              scrut[2U] = (u64)0x3c6ef372fe94f82bU;
              scrut[3U] = (u64)0xa54ff53a5f1d36f1U;
              scrut[4U] = (u64)0x510e527fade682d1U;
              scrut[5U] = (u64)0x9b05688c2b3e6c1fU;
              scrut[6U] = (u64)0x1f83d9abfb41bd6bU;
              scrut[7U] = (u64)0x5be0cd19137e2179U;
              s = scrut;
              dst1 = ipad;
              Hacl_Hash_Core_SHA2_init_512(s);
              if (data_len == (u32)0U)
                Hacl_Hash_SHA2_update_last_512(s, (uint128_t)(u64)0U, ipad, (u32)128U);
              else
              {
                Hacl_Hash_SHA2_update_multi_512(s, ipad, (u32)1U);
                Hacl_Hash_SHA2_update_last_512(s, (uint128_t)(u64)(u32)128U, data, data_len);
              }
              Hacl_Hash_Core_SHA2_finish_512(s, dst1);
              hash1 = ipad;
              Hacl_Hash_Core_SHA2_init_512(s);
              if ((u32)64U == (u32)0U)
                Hacl_Hash_SHA2_update_last_512(s, (uint128_t)(u64)0U, opad, (u32)128U);
              else
              {
                Hacl_Hash_SHA2_update_multi_512(s, opad, (u32)1U);
                Hacl_Hash_SHA2_update_last_512(s, (uint128_t)(u64)(u32)128U, hash1, (u32)64U);
              }
              Hacl_Hash_Core_SHA2_finish_512(s, dst);
            }
          }
        }
      }
    }
  }
}

typedef struct ___u32__u64_s
{
  u32 *fst;
  u64 snd;
}
___u32__u64;

void Hacl_HMAC_compute_blake2s_32(u8 *dst, u8 *key, u32 key_len, u8 *data, u32 data_len)
{
  u32 l = (u32)64U;
  KRML_CHECK_SIZE(sizeof (u8), l);
  {
    u8 key_block[l];
    memset(key_block, 0U, l * sizeof (u8));
    {
      u32 i0;
      if (key_len <= (u32)64U)
        i0 = key_len;
      else
        i0 = (u32)32U;
      {
        u8 *nkey = key_block;
        if (key_len <= (u32)64U)
          memcpy(nkey, key, key_len * sizeof (u8));
        else
          Hacl_Hash_Blake2_hash_blake2s_32(key, key_len, nkey);
        KRML_CHECK_SIZE(sizeof (u8), l);
        {
          u8 ipad[l];
          memset(ipad, (u8)0x36U, l * sizeof (u8));
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
            memset(opad, (u8)0x5cU, l * sizeof (u8));
            {
              u32 i;
              for (i = (u32)0U; i < l; i++)
              {
                u8 xi = opad[i];
                u8 yi = key_block[i];
                opad[i] = xi ^ yi;
              }
            }
            {
              u32 s0[16U] = { 0U };
              u32 *r00 = s0 + (u32)0U * (u32)4U;
              u32 *r10 = s0 + (u32)1U * (u32)4U;
              u32 *r20 = s0 + (u32)2U * (u32)4U;
              u32 *r30 = s0 + (u32)3U * (u32)4U;
              u32 iv00 = Hacl_Impl_Blake2_Constants_ivTable_S[0U];
              u32 iv10 = Hacl_Impl_Blake2_Constants_ivTable_S[1U];
              u32 iv20 = Hacl_Impl_Blake2_Constants_ivTable_S[2U];
              u32 iv30 = Hacl_Impl_Blake2_Constants_ivTable_S[3U];
              u32 iv40 = Hacl_Impl_Blake2_Constants_ivTable_S[4U];
              u32 iv50 = Hacl_Impl_Blake2_Constants_ivTable_S[5U];
              u32 iv60 = Hacl_Impl_Blake2_Constants_ivTable_S[6U];
              u32 iv70 = Hacl_Impl_Blake2_Constants_ivTable_S[7U];
              u32 kk_shift_80;
              u32 iv0_;
              u64 es;
              ___u32__u64 scrut;
              u32 *s;
              u8 *dst1;
              u32 *r01;
              u32 *r11;
              u32 *r21;
              u32 *r31;
              u32 iv01;
              u32 iv11;
              u32 iv21;
              u32 iv31;
              u32 iv41;
              u32 iv51;
              u32 iv61;
              u32 iv71;
              u32 kk_shift_81;
              u32 iv0_0;
              u64 ev0;
              u64 ev10;
              u8 *hash1;
              u32 *r0;
              u32 *r1;
              u32 *r2;
              u32 *r3;
              u32 iv0;
              u32 iv1;
              u32 iv2;
              u32 iv3;
              u32 iv4;
              u32 iv5;
              u32 iv6;
              u32 iv7;
              u32 kk_shift_8;
              u32 iv0_1;
              u64 ev;
              u64 ev11;
              r20[0U] = iv00;
              r20[1U] = iv10;
              r20[2U] = iv20;
              r20[3U] = iv30;
              r30[0U] = iv40;
              r30[1U] = iv50;
              r30[2U] = iv60;
              r30[3U] = iv70;
              kk_shift_80 = (u32)0U;
              iv0_ = iv00 ^ ((u32)0x01010000U ^ (kk_shift_80 ^ (u32)32U));
              r00[0U] = iv0_;
              r00[1U] = iv10;
              r00[2U] = iv20;
              r00[3U] = iv30;
              r10[0U] = iv40;
              r10[1U] = iv50;
              r10[2U] = iv60;
              r10[3U] = iv70;
              es = (u64)0U;
              scrut = ((___u32__u64){ .fst = s0, .snd = es });
              s = scrut.fst;
              dst1 = ipad;
              r01 = s + (u32)0U * (u32)4U;
              r11 = s + (u32)1U * (u32)4U;
              r21 = s + (u32)2U * (u32)4U;
              r31 = s + (u32)3U * (u32)4U;
              iv01 = Hacl_Impl_Blake2_Constants_ivTable_S[0U];
              iv11 = Hacl_Impl_Blake2_Constants_ivTable_S[1U];
              iv21 = Hacl_Impl_Blake2_Constants_ivTable_S[2U];
              iv31 = Hacl_Impl_Blake2_Constants_ivTable_S[3U];
              iv41 = Hacl_Impl_Blake2_Constants_ivTable_S[4U];
              iv51 = Hacl_Impl_Blake2_Constants_ivTable_S[5U];
              iv61 = Hacl_Impl_Blake2_Constants_ivTable_S[6U];
              iv71 = Hacl_Impl_Blake2_Constants_ivTable_S[7U];
              r21[0U] = iv01;
              r21[1U] = iv11;
              r21[2U] = iv21;
              r21[3U] = iv31;
              r31[0U] = iv41;
              r31[1U] = iv51;
              r31[2U] = iv61;
              r31[3U] = iv71;
              kk_shift_81 = (u32)0U;
              iv0_0 = iv01 ^ ((u32)0x01010000U ^ (kk_shift_81 ^ (u32)32U));
              r01[0U] = iv0_0;
              r01[1U] = iv11;
              r01[2U] = iv21;
              r01[3U] = iv31;
              r11[0U] = iv41;
              r11[1U] = iv51;
              r11[2U] = iv61;
              r11[3U] = iv71;
              ev0 = (u64)0U;
              if (data_len == (u32)0U)
              {
                u64 ev1 = Hacl_Hash_Blake2_update_last_blake2s_32(s, ev0, (u64)0U, ipad, (u32)64U);
                ev10 = ev1;
              }
              else
              {
                u64 ev1 = Hacl_Hash_Blake2_update_multi_blake2s_32(s, ev0, ipad, (u32)1U);
                u64
                ev2 = Hacl_Hash_Blake2_update_last_blake2s_32(s, ev1, (u64)(u32)64U, data, data_len);
                ev10 = ev2;
              }
              Hacl_Hash_Core_Blake2_finish_blake2s_32(s, ev10, dst1);
              hash1 = ipad;
              r0 = s + (u32)0U * (u32)4U;
              r1 = s + (u32)1U * (u32)4U;
              r2 = s + (u32)2U * (u32)4U;
              r3 = s + (u32)3U * (u32)4U;
              iv0 = Hacl_Impl_Blake2_Constants_ivTable_S[0U];
              iv1 = Hacl_Impl_Blake2_Constants_ivTable_S[1U];
              iv2 = Hacl_Impl_Blake2_Constants_ivTable_S[2U];
              iv3 = Hacl_Impl_Blake2_Constants_ivTable_S[3U];
              iv4 = Hacl_Impl_Blake2_Constants_ivTable_S[4U];
              iv5 = Hacl_Impl_Blake2_Constants_ivTable_S[5U];
              iv6 = Hacl_Impl_Blake2_Constants_ivTable_S[6U];
              iv7 = Hacl_Impl_Blake2_Constants_ivTable_S[7U];
              r2[0U] = iv0;
              r2[1U] = iv1;
              r2[2U] = iv2;
              r2[3U] = iv3;
              r3[0U] = iv4;
              r3[1U] = iv5;
              r3[2U] = iv6;
              r3[3U] = iv7;
              kk_shift_8 = (u32)0U;
              iv0_1 = iv0 ^ ((u32)0x01010000U ^ (kk_shift_8 ^ (u32)32U));
              r0[0U] = iv0_1;
              r0[1U] = iv1;
              r0[2U] = iv2;
              r0[3U] = iv3;
              r1[0U] = iv4;
              r1[1U] = iv5;
              r1[2U] = iv6;
              r1[3U] = iv7;
              ev = (u64)0U;
              if ((u32)32U == (u32)0U)
              {
                u64 ev1 = Hacl_Hash_Blake2_update_last_blake2s_32(s, ev, (u64)0U, opad, (u32)64U);
                ev11 = ev1;
              }
              else
              {
                u64 ev1 = Hacl_Hash_Blake2_update_multi_blake2s_32(s, ev, opad, (u32)1U);
                u64
                ev2 =
                  Hacl_Hash_Blake2_update_last_blake2s_32(s,
                    ev1,
                    (u64)(u32)64U,
                    hash1,
                    (u32)32U);
                ev11 = ev2;
              }
              Hacl_Hash_Core_Blake2_finish_blake2s_32(s, ev11, dst);
            }
          }
        }
      }
    }
  }
}

typedef struct ___u64__FStar_UInt128_uint128_s
{
  u64 *fst;
  uint128_t snd;
}
___u64__FStar_UInt128_uint128;

void Hacl_HMAC_compute_blake2b_32(u8 *dst, u8 *key, u32 key_len, u8 *data, u32 data_len)
{
  u32 l = (u32)128U;
  KRML_CHECK_SIZE(sizeof (u8), l);
  {
    u8 key_block[l];
    memset(key_block, 0U, l * sizeof (u8));
    {
      u32 i0;
      if (key_len <= (u32)128U)
        i0 = key_len;
      else
        i0 = (u32)64U;
      {
        u8 *nkey = key_block;
        if (key_len <= (u32)128U)
          memcpy(nkey, key, key_len * sizeof (u8));
        else
          Hacl_Hash_Blake2_hash_blake2b_32(key, key_len, nkey);
        KRML_CHECK_SIZE(sizeof (u8), l);
        {
          u8 ipad[l];
          memset(ipad, (u8)0x36U, l * sizeof (u8));
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
            memset(opad, (u8)0x5cU, l * sizeof (u8));
            {
              u32 i;
              for (i = (u32)0U; i < l; i++)
              {
                u8 xi = opad[i];
                u8 yi = key_block[i];
                opad[i] = xi ^ yi;
              }
            }
            {
              u64 s0[16U] = { 0U };
              u64 *r00 = s0 + (u32)0U * (u32)4U;
              u64 *r10 = s0 + (u32)1U * (u32)4U;
              u64 *r20 = s0 + (u32)2U * (u32)4U;
              u64 *r30 = s0 + (u32)3U * (u32)4U;
              u64 iv00 = Hacl_Impl_Blake2_Constants_ivTable_B[0U];
              u64 iv10 = Hacl_Impl_Blake2_Constants_ivTable_B[1U];
              u64 iv20 = Hacl_Impl_Blake2_Constants_ivTable_B[2U];
              u64 iv30 = Hacl_Impl_Blake2_Constants_ivTable_B[3U];
              u64 iv40 = Hacl_Impl_Blake2_Constants_ivTable_B[4U];
              u64 iv50 = Hacl_Impl_Blake2_Constants_ivTable_B[5U];
              u64 iv60 = Hacl_Impl_Blake2_Constants_ivTable_B[6U];
              u64 iv70 = Hacl_Impl_Blake2_Constants_ivTable_B[7U];
              u64 kk_shift_80;
              u64 iv0_;
              uint128_t es;
              ___u64__FStar_UInt128_uint128 scrut;
              u64 *s;
              u8 *dst1;
              u64 *r01;
              u64 *r11;
              u64 *r21;
              u64 *r31;
              u64 iv01;
              u64 iv11;
              u64 iv21;
              u64 iv31;
              u64 iv41;
              u64 iv51;
              u64 iv61;
              u64 iv71;
              u64 kk_shift_81;
              u64 iv0_0;
              uint128_t ev0;
              uint128_t ev10;
              u8 *hash1;
              u64 *r0;
              u64 *r1;
              u64 *r2;
              u64 *r3;
              u64 iv0;
              u64 iv1;
              u64 iv2;
              u64 iv3;
              u64 iv4;
              u64 iv5;
              u64 iv6;
              u64 iv7;
              u64 kk_shift_8;
              u64 iv0_1;
              uint128_t ev;
              uint128_t ev11;
              r20[0U] = iv00;
              r20[1U] = iv10;
              r20[2U] = iv20;
              r20[3U] = iv30;
              r30[0U] = iv40;
              r30[1U] = iv50;
              r30[2U] = iv60;
              r30[3U] = iv70;
              kk_shift_80 = (u64)(u32)0U << (u32)8U;
              iv0_ = iv00 ^ ((u64)0x01010000U ^ (kk_shift_80 ^ (u64)(u32)64U));
              r00[0U] = iv0_;
              r00[1U] = iv10;
              r00[2U] = iv20;
              r00[3U] = iv30;
              r10[0U] = iv40;
              r10[1U] = iv50;
              r10[2U] = iv60;
              r10[3U] = iv70;
              es = (uint128_t)(u64)0U;
              scrut = ((___u64__FStar_UInt128_uint128){ .fst = s0, .snd = es });
              s = scrut.fst;
              dst1 = ipad;
              r01 = s + (u32)0U * (u32)4U;
              r11 = s + (u32)1U * (u32)4U;
              r21 = s + (u32)2U * (u32)4U;
              r31 = s + (u32)3U * (u32)4U;
              iv01 = Hacl_Impl_Blake2_Constants_ivTable_B[0U];
              iv11 = Hacl_Impl_Blake2_Constants_ivTable_B[1U];
              iv21 = Hacl_Impl_Blake2_Constants_ivTable_B[2U];
              iv31 = Hacl_Impl_Blake2_Constants_ivTable_B[3U];
              iv41 = Hacl_Impl_Blake2_Constants_ivTable_B[4U];
              iv51 = Hacl_Impl_Blake2_Constants_ivTable_B[5U];
              iv61 = Hacl_Impl_Blake2_Constants_ivTable_B[6U];
              iv71 = Hacl_Impl_Blake2_Constants_ivTable_B[7U];
              r21[0U] = iv01;
              r21[1U] = iv11;
              r21[2U] = iv21;
              r21[3U] = iv31;
              r31[0U] = iv41;
              r31[1U] = iv51;
              r31[2U] = iv61;
              r31[3U] = iv71;
              kk_shift_81 = (u64)(u32)0U << (u32)8U;
              iv0_0 = iv01 ^ ((u64)0x01010000U ^ (kk_shift_81 ^ (u64)(u32)64U));
              r01[0U] = iv0_0;
              r01[1U] = iv11;
              r01[2U] = iv21;
              r01[3U] = iv31;
              r11[0U] = iv41;
              r11[1U] = iv51;
              r11[2U] = iv61;
              r11[3U] = iv71;
              ev0 = (uint128_t)(u64)0U;
              if (data_len == (u32)0U)
              {
                uint128_t
                ev1 =
                  Hacl_Hash_Blake2_update_last_blake2b_32(s,
                    ev0,
                    (uint128_t)(u64)0U,
                    ipad,
                    (u32)128U);
                ev10 = ev1;
              }
              else
              {
                uint128_t ev1 = Hacl_Hash_Blake2_update_multi_blake2b_32(s, ev0, ipad, (u32)1U);
                uint128_t
                ev2 =
                  Hacl_Hash_Blake2_update_last_blake2b_32(s,
                    ev1,
                    (uint128_t)(u64)(u32)128U,
                    data,
                    data_len);
                ev10 = ev2;
              }
              Hacl_Hash_Core_Blake2_finish_blake2b_32(s, ev10, dst1);
              hash1 = ipad;
              r0 = s + (u32)0U * (u32)4U;
              r1 = s + (u32)1U * (u32)4U;
              r2 = s + (u32)2U * (u32)4U;
              r3 = s + (u32)3U * (u32)4U;
              iv0 = Hacl_Impl_Blake2_Constants_ivTable_B[0U];
              iv1 = Hacl_Impl_Blake2_Constants_ivTable_B[1U];
              iv2 = Hacl_Impl_Blake2_Constants_ivTable_B[2U];
              iv3 = Hacl_Impl_Blake2_Constants_ivTable_B[3U];
              iv4 = Hacl_Impl_Blake2_Constants_ivTable_B[4U];
              iv5 = Hacl_Impl_Blake2_Constants_ivTable_B[5U];
              iv6 = Hacl_Impl_Blake2_Constants_ivTable_B[6U];
              iv7 = Hacl_Impl_Blake2_Constants_ivTable_B[7U];
              r2[0U] = iv0;
              r2[1U] = iv1;
              r2[2U] = iv2;
              r2[3U] = iv3;
              r3[0U] = iv4;
              r3[1U] = iv5;
              r3[2U] = iv6;
              r3[3U] = iv7;
              kk_shift_8 = (u64)(u32)0U << (u32)8U;
              iv0_1 = iv0 ^ ((u64)0x01010000U ^ (kk_shift_8 ^ (u64)(u32)64U));
              r0[0U] = iv0_1;
              r0[1U] = iv1;
              r0[2U] = iv2;
              r0[3U] = iv3;
              r1[0U] = iv4;
              r1[1U] = iv5;
              r1[2U] = iv6;
              r1[3U] = iv7;
              ev = (uint128_t)(u64)0U;
              if ((u32)64U == (u32)0U)
              {
                uint128_t
                ev1 =
                  Hacl_Hash_Blake2_update_last_blake2b_32(s,
                    ev,
                    (uint128_t)(u64)0U,
                    opad,
                    (u32)128U);
                ev11 = ev1;
              }
              else
              {
                uint128_t ev1 = Hacl_Hash_Blake2_update_multi_blake2b_32(s, ev, opad, (u32)1U);
                uint128_t
                ev2 =
                  Hacl_Hash_Blake2_update_last_blake2b_32(s,
                    ev1,
                    (uint128_t)(u64)(u32)128U,
                    hash1,
                    (u32)64U);
                ev11 = ev2;
              }
              Hacl_Hash_Core_Blake2_finish_blake2b_32(s, ev11, dst);
            }
          }
        }
      }
    }
  }
}

