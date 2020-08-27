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

typedef struct ___Lib_IntVector_Intrinsics_vec256__FStar_UInt128_uint128_s
{
  Lib_IntVector_Intrinsics_vec256 *fst;
  uint128_t snd;
}
___Lib_IntVector_Intrinsics_vec256__FStar_UInt128_uint128;

void
Hacl_HMAC_Blake2b_256_compute_blake2b_256(
  u8 *dst,
  u8 *key,
  u32 key_len,
  u8 *data,
  u32 data_len
)
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
          Hacl_Hash_Blake2b_256_hash_blake2b_256(key, key_len, nkey);
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
              Lib_IntVector_Intrinsics_vec256 s0[4U];
              {
                u32 _i;
                for (_i = 0U; _i < (u32)4U; ++_i)
                  s0[_i] = Lib_IntVector_Intrinsics_vec256_zero;
              }
              {
                Lib_IntVector_Intrinsics_vec256 *r00 = s0 + (u32)0U * (u32)1U;
                Lib_IntVector_Intrinsics_vec256 *r10 = s0 + (u32)1U * (u32)1U;
                Lib_IntVector_Intrinsics_vec256 *r20 = s0 + (u32)2U * (u32)1U;
                Lib_IntVector_Intrinsics_vec256 *r30 = s0 + (u32)3U * (u32)1U;
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
                ___Lib_IntVector_Intrinsics_vec256__FStar_UInt128_uint128 scrut;
                Lib_IntVector_Intrinsics_vec256 *s;
                u8 *dst1;
                Lib_IntVector_Intrinsics_vec256 *r01;
                Lib_IntVector_Intrinsics_vec256 *r11;
                Lib_IntVector_Intrinsics_vec256 *r21;
                Lib_IntVector_Intrinsics_vec256 *r31;
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
                Lib_IntVector_Intrinsics_vec256 *r0;
                Lib_IntVector_Intrinsics_vec256 *r1;
                Lib_IntVector_Intrinsics_vec256 *r2;
                Lib_IntVector_Intrinsics_vec256 *r3;
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
                r20[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv00, iv10, iv20, iv30);
                r30[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv40, iv50, iv60, iv70);
                kk_shift_80 = (u64)(u32)0U << (u32)8U;
                iv0_ = iv00 ^ ((u64)0x01010000U ^ (kk_shift_80 ^ (u64)(u32)64U));
                r00[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0_, iv10, iv20, iv30);
                r10[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv40, iv50, iv60, iv70);
                es = (uint128_t)(u64)0U;
                scrut =
                  (
                    (___Lib_IntVector_Intrinsics_vec256__FStar_UInt128_uint128){
                      .fst = s0,
                      .snd = es
                    }
                  );
                s = scrut.fst;
                dst1 = ipad;
                r01 = s + (u32)0U * (u32)1U;
                r11 = s + (u32)1U * (u32)1U;
                r21 = s + (u32)2U * (u32)1U;
                r31 = s + (u32)3U * (u32)1U;
                iv01 = Hacl_Impl_Blake2_Constants_ivTable_B[0U];
                iv11 = Hacl_Impl_Blake2_Constants_ivTable_B[1U];
                iv21 = Hacl_Impl_Blake2_Constants_ivTable_B[2U];
                iv31 = Hacl_Impl_Blake2_Constants_ivTable_B[3U];
                iv41 = Hacl_Impl_Blake2_Constants_ivTable_B[4U];
                iv51 = Hacl_Impl_Blake2_Constants_ivTable_B[5U];
                iv61 = Hacl_Impl_Blake2_Constants_ivTable_B[6U];
                iv71 = Hacl_Impl_Blake2_Constants_ivTable_B[7U];
                r21[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv01, iv11, iv21, iv31);
                r31[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv41, iv51, iv61, iv71);
                kk_shift_81 = (u64)(u32)0U << (u32)8U;
                iv0_0 = iv01 ^ ((u64)0x01010000U ^ (kk_shift_81 ^ (u64)(u32)64U));
                r01[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0_0, iv11, iv21, iv31);
                r11[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv41, iv51, iv61, iv71);
                ev0 = (uint128_t)(u64)0U;
                if (data_len == (u32)0U)
                {
                  uint128_t
                  ev1 =
                    Hacl_Hash_Blake2b_256_update_last_blake2b_256(s,
                      ev0,
                      (uint128_t)(u64)0U,
                      ipad,
                      (u32)128U);
                  ev10 = ev1;
                }
                else
                {
                  uint128_t
                  ev1 = Hacl_Hash_Blake2b_256_update_multi_blake2b_256(s, ev0, ipad, (u32)1U);
                  uint128_t
                  ev2 =
                    Hacl_Hash_Blake2b_256_update_last_blake2b_256(s,
                      ev1,
                      (uint128_t)(u64)(u32)128U,
                      data,
                      data_len);
                  ev10 = ev2;
                }
                Hacl_Hash_Blake2b_256_finish_blake2b_256(s, ev10, dst1);
                hash1 = ipad;
                r0 = s + (u32)0U * (u32)1U;
                r1 = s + (u32)1U * (u32)1U;
                r2 = s + (u32)2U * (u32)1U;
                r3 = s + (u32)3U * (u32)1U;
                iv0 = Hacl_Impl_Blake2_Constants_ivTable_B[0U];
                iv1 = Hacl_Impl_Blake2_Constants_ivTable_B[1U];
                iv2 = Hacl_Impl_Blake2_Constants_ivTable_B[2U];
                iv3 = Hacl_Impl_Blake2_Constants_ivTable_B[3U];
                iv4 = Hacl_Impl_Blake2_Constants_ivTable_B[4U];
                iv5 = Hacl_Impl_Blake2_Constants_ivTable_B[5U];
                iv6 = Hacl_Impl_Blake2_Constants_ivTable_B[6U];
                iv7 = Hacl_Impl_Blake2_Constants_ivTable_B[7U];
                r2[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0, iv1, iv2, iv3);
                r3[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4, iv5, iv6, iv7);
                kk_shift_8 = (u64)(u32)0U << (u32)8U;
                iv0_1 = iv0 ^ ((u64)0x01010000U ^ (kk_shift_8 ^ (u64)(u32)64U));
                r0[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0_1, iv1, iv2, iv3);
                r1[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4, iv5, iv6, iv7);
                ev = (uint128_t)(u64)0U;
                if ((u32)64U == (u32)0U)
                {
                  uint128_t
                  ev1 =
                    Hacl_Hash_Blake2b_256_update_last_blake2b_256(s,
                      ev,
                      (uint128_t)(u64)0U,
                      opad,
                      (u32)128U);
                  ev11 = ev1;
                }
                else
                {
                  uint128_t
                  ev1 = Hacl_Hash_Blake2b_256_update_multi_blake2b_256(s, ev, opad, (u32)1U);
                  uint128_t
                  ev2 =
                    Hacl_Hash_Blake2b_256_update_last_blake2b_256(s,
                      ev1,
                      (uint128_t)(u64)(u32)128U,
                      hash1,
                      (u32)64U);
                  ev11 = ev2;
                }
                Hacl_Hash_Blake2b_256_finish_blake2b_256(s, ev11, dst);
              }
            }
          }
        }
      }
    }
  }
}

