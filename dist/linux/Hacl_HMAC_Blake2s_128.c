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


#include "Hacl_HMAC_Blake2s_128.h"

typedef struct ___Lib_IntVector_Intrinsics_vec128__u64_s
{
  Lib_IntVector_Intrinsics_vec128 *fst;
  u64 snd;
}
___Lib_IntVector_Intrinsics_vec128__u64;

void
Hacl_HMAC_Blake2s_128_compute_blake2s_128(
  u8 *dst,
  u8 *key,
  u32 key_len,
  u8 *data,
  u32 data_len
)
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
          Hacl_Hash_Blake2s_128_hash_blake2s_128(key, key_len, nkey);
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
              Lib_IntVector_Intrinsics_vec128 s0[4U];
              {
                u32 _i;
                for (_i = 0U; _i < (u32)4U; ++_i)
                  s0[_i] = Lib_IntVector_Intrinsics_vec128_zero;
              }
              {
                Lib_IntVector_Intrinsics_vec128 *r00 = s0 + (u32)0U * (u32)1U;
                Lib_IntVector_Intrinsics_vec128 *r10 = s0 + (u32)1U * (u32)1U;
                Lib_IntVector_Intrinsics_vec128 *r20 = s0 + (u32)2U * (u32)1U;
                Lib_IntVector_Intrinsics_vec128 *r30 = s0 + (u32)3U * (u32)1U;
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
                ___Lib_IntVector_Intrinsics_vec128__u64 scrut;
                Lib_IntVector_Intrinsics_vec128 *s;
                u8 *dst1;
                Lib_IntVector_Intrinsics_vec128 *r01;
                Lib_IntVector_Intrinsics_vec128 *r11;
                Lib_IntVector_Intrinsics_vec128 *r21;
                Lib_IntVector_Intrinsics_vec128 *r31;
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
                Lib_IntVector_Intrinsics_vec128 *r0;
                Lib_IntVector_Intrinsics_vec128 *r1;
                Lib_IntVector_Intrinsics_vec128 *r2;
                Lib_IntVector_Intrinsics_vec128 *r3;
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
                r20[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv00, iv10, iv20, iv30);
                r30[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv40, iv50, iv60, iv70);
                kk_shift_80 = (u32)0U;
                iv0_ = iv00 ^ ((u32)0x01010000U ^ (kk_shift_80 ^ (u32)32U));
                r00[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv0_, iv10, iv20, iv30);
                r10[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv40, iv50, iv60, iv70);
                es = (u64)0U;
                scrut = ((___Lib_IntVector_Intrinsics_vec128__u64){ .fst = s0, .snd = es });
                s = scrut.fst;
                dst1 = ipad;
                r01 = s + (u32)0U * (u32)1U;
                r11 = s + (u32)1U * (u32)1U;
                r21 = s + (u32)2U * (u32)1U;
                r31 = s + (u32)3U * (u32)1U;
                iv01 = Hacl_Impl_Blake2_Constants_ivTable_S[0U];
                iv11 = Hacl_Impl_Blake2_Constants_ivTable_S[1U];
                iv21 = Hacl_Impl_Blake2_Constants_ivTable_S[2U];
                iv31 = Hacl_Impl_Blake2_Constants_ivTable_S[3U];
                iv41 = Hacl_Impl_Blake2_Constants_ivTable_S[4U];
                iv51 = Hacl_Impl_Blake2_Constants_ivTable_S[5U];
                iv61 = Hacl_Impl_Blake2_Constants_ivTable_S[6U];
                iv71 = Hacl_Impl_Blake2_Constants_ivTable_S[7U];
                r21[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv01, iv11, iv21, iv31);
                r31[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv41, iv51, iv61, iv71);
                kk_shift_81 = (u32)0U;
                iv0_0 = iv01 ^ ((u32)0x01010000U ^ (kk_shift_81 ^ (u32)32U));
                r01[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv0_0, iv11, iv21, iv31);
                r11[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv41, iv51, iv61, iv71);
                ev0 = (u64)0U;
                if (data_len == (u32)0U)
                {
                  u64
                  ev1 =
                    Hacl_Hash_Blake2s_128_update_last_blake2s_128(s,
                      ev0,
                      (u64)0U,
                      ipad,
                      (u32)64U);
                  ev10 = ev1;
                }
                else
                {
                  u64 ev1 = Hacl_Hash_Blake2s_128_update_multi_blake2s_128(s, ev0, ipad, (u32)1U);
                  u64
                  ev2 =
                    Hacl_Hash_Blake2s_128_update_last_blake2s_128(s,
                      ev1,
                      (u64)(u32)64U,
                      data,
                      data_len);
                  ev10 = ev2;
                }
                Hacl_Hash_Blake2s_128_finish_blake2s_128(s, ev10, dst1);
                hash1 = ipad;
                r0 = s + (u32)0U * (u32)1U;
                r1 = s + (u32)1U * (u32)1U;
                r2 = s + (u32)2U * (u32)1U;
                r3 = s + (u32)3U * (u32)1U;
                iv0 = Hacl_Impl_Blake2_Constants_ivTable_S[0U];
                iv1 = Hacl_Impl_Blake2_Constants_ivTable_S[1U];
                iv2 = Hacl_Impl_Blake2_Constants_ivTable_S[2U];
                iv3 = Hacl_Impl_Blake2_Constants_ivTable_S[3U];
                iv4 = Hacl_Impl_Blake2_Constants_ivTable_S[4U];
                iv5 = Hacl_Impl_Blake2_Constants_ivTable_S[5U];
                iv6 = Hacl_Impl_Blake2_Constants_ivTable_S[6U];
                iv7 = Hacl_Impl_Blake2_Constants_ivTable_S[7U];
                r2[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv0, iv1, iv2, iv3);
                r3[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv4, iv5, iv6, iv7);
                kk_shift_8 = (u32)0U;
                iv0_1 = iv0 ^ ((u32)0x01010000U ^ (kk_shift_8 ^ (u32)32U));
                r0[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv0_1, iv1, iv2, iv3);
                r1[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv4, iv5, iv6, iv7);
                ev = (u64)0U;
                if ((u32)32U == (u32)0U)
                {
                  u64
                  ev1 =
                    Hacl_Hash_Blake2s_128_update_last_blake2s_128(s,
                      ev,
                      (u64)0U,
                      opad,
                      (u32)64U);
                  ev11 = ev1;
                }
                else
                {
                  u64 ev1 = Hacl_Hash_Blake2s_128_update_multi_blake2s_128(s, ev, opad, (u32)1U);
                  u64
                  ev2 =
                    Hacl_Hash_Blake2s_128_update_last_blake2s_128(s,
                      ev1,
                      (u64)(u32)64U,
                      hash1,
                      (u32)32U);
                  ev11 = ev2;
                }
                Hacl_Hash_Blake2s_128_finish_blake2s_128(s, ev11, dst);
              }
            }
          }
        }
      }
    }
  }
}

