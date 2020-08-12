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

typedef struct ___Lib_IntVector_Intrinsics_vec128__uint64_t_s
{
  Lib_IntVector_Intrinsics_vec128 *fst;
  uint64_t snd;
}
___Lib_IntVector_Intrinsics_vec128__uint64_t;

void
Hacl_HMAC_Blake2s_128_compute_blake2s_128(
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
    uint8_t key_block[l];
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
          Hacl_Hash_Blake2s_128_hash_blake2s_128(key, key_len, nkey);
        }
        KRML_CHECK_SIZE(sizeof (uint8_t), l);
        {
          uint8_t ipad[l];
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
            uint8_t opad[l];
            memset(opad, (uint8_t)0x5cU, l * sizeof (uint8_t));
            {
              uint32_t i;
              for (i = (uint32_t)0U; i < l; i++)
              {
                uint8_t xi = opad[i];
                uint8_t yi = key_block[i];
                opad[i] = xi ^ yi;
              }
            }
            {
              Lib_IntVector_Intrinsics_vec128 s0[4U];
              {
                uint32_t _i;
                for (_i = 0U; _i < (uint32_t)4U; ++_i)
                  s0[_i] = Lib_IntVector_Intrinsics_vec128_zero;
              }
              {
                Lib_IntVector_Intrinsics_vec128 *r00 = s0 + (uint32_t)0U * (uint32_t)1U;
                Lib_IntVector_Intrinsics_vec128 *r10 = s0 + (uint32_t)1U * (uint32_t)1U;
                Lib_IntVector_Intrinsics_vec128 *r20 = s0 + (uint32_t)2U * (uint32_t)1U;
                Lib_IntVector_Intrinsics_vec128 *r30 = s0 + (uint32_t)3U * (uint32_t)1U;
                uint32_t iv00 = Hacl_Impl_Blake2_Constants_ivTable_S[0U];
                uint32_t iv10 = Hacl_Impl_Blake2_Constants_ivTable_S[1U];
                uint32_t iv20 = Hacl_Impl_Blake2_Constants_ivTable_S[2U];
                uint32_t iv30 = Hacl_Impl_Blake2_Constants_ivTable_S[3U];
                uint32_t iv40 = Hacl_Impl_Blake2_Constants_ivTable_S[4U];
                uint32_t iv50 = Hacl_Impl_Blake2_Constants_ivTable_S[5U];
                uint32_t iv60 = Hacl_Impl_Blake2_Constants_ivTable_S[6U];
                uint32_t iv70 = Hacl_Impl_Blake2_Constants_ivTable_S[7U];
                uint32_t kk_shift_80;
                uint32_t iv0_;
                uint64_t es;
                r20[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv00, iv10, iv20, iv30);
                r30[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv40, iv50, iv60, iv70);
                kk_shift_80 = (uint32_t)0U;
                iv0_ = iv00 ^ ((uint32_t)0x01010000U ^ (kk_shift_80 ^ (uint32_t)32U));
                r00[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv0_, iv10, iv20, iv30);
                r10[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv40, iv50, iv60, iv70);
                es = (uint64_t)0U;
                {
                  ___Lib_IntVector_Intrinsics_vec128__uint64_t scrut;
                  Lib_IntVector_Intrinsics_vec128 *s;
                  uint8_t *dst1;
                  Lib_IntVector_Intrinsics_vec128 *r01;
                  Lib_IntVector_Intrinsics_vec128 *r11;
                  Lib_IntVector_Intrinsics_vec128 *r21;
                  Lib_IntVector_Intrinsics_vec128 *r31;
                  uint32_t iv01;
                  uint32_t iv11;
                  uint32_t iv21;
                  uint32_t iv31;
                  uint32_t iv41;
                  uint32_t iv51;
                  uint32_t iv61;
                  uint32_t iv71;
                  uint32_t kk_shift_81;
                  uint32_t iv0_0;
                  uint64_t ev0;
                  uint64_t ev10;
                  uint8_t *hash1;
                  Lib_IntVector_Intrinsics_vec128 *r0;
                  Lib_IntVector_Intrinsics_vec128 *r1;
                  Lib_IntVector_Intrinsics_vec128 *r2;
                  Lib_IntVector_Intrinsics_vec128 *r3;
                  uint32_t iv0;
                  uint32_t iv1;
                  uint32_t iv2;
                  uint32_t iv3;
                  uint32_t iv4;
                  uint32_t iv5;
                  uint32_t iv6;
                  uint32_t iv7;
                  uint32_t kk_shift_8;
                  uint32_t iv0_1;
                  uint64_t ev;
                  uint64_t ev11;
                  scrut.fst = s0;
                  scrut.snd = es;
                  s = scrut.fst;
                  dst1 = ipad;
                  r01 = s + (uint32_t)0U * (uint32_t)1U;
                  r11 = s + (uint32_t)1U * (uint32_t)1U;
                  r21 = s + (uint32_t)2U * (uint32_t)1U;
                  r31 = s + (uint32_t)3U * (uint32_t)1U;
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
                  kk_shift_81 = (uint32_t)0U;
                  iv0_0 = iv01 ^ ((uint32_t)0x01010000U ^ (kk_shift_81 ^ (uint32_t)32U));
                  r01[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv0_0, iv11, iv21, iv31);
                  r11[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv41, iv51, iv61, iv71);
                  ev0 = (uint64_t)0U;
                  if (data_len == (uint32_t)0U)
                  {
                    uint64_t
                    ev1 =
                      Hacl_Hash_Blake2s_128_update_last_blake2s_128(s,
                        ev0,
                        (uint64_t)0U,
                        ipad,
                        (uint32_t)64U);
                    ev10 = ev1;
                  }
                  else
                  {
                    uint64_t
                    ev1 = Hacl_Hash_Blake2s_128_update_multi_blake2s_128(s, ev0, ipad, (uint32_t)1U);
                    uint64_t
                    ev2 =
                      Hacl_Hash_Blake2s_128_update_last_blake2s_128(s,
                        ev1,
                        (uint64_t)(uint32_t)64U,
                        data,
                        data_len);
                    ev10 = ev2;
                  }
                  Hacl_Hash_Blake2s_128_finish_blake2s_128(s, ev10, dst1);
                  hash1 = ipad;
                  r0 = s + (uint32_t)0U * (uint32_t)1U;
                  r1 = s + (uint32_t)1U * (uint32_t)1U;
                  r2 = s + (uint32_t)2U * (uint32_t)1U;
                  r3 = s + (uint32_t)3U * (uint32_t)1U;
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
                  kk_shift_8 = (uint32_t)0U;
                  iv0_1 = iv0 ^ ((uint32_t)0x01010000U ^ (kk_shift_8 ^ (uint32_t)32U));
                  r0[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv0_1, iv1, iv2, iv3);
                  r1[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv4, iv5, iv6, iv7);
                  ev = (uint64_t)0U;
                  if ((uint32_t)32U == (uint32_t)0U)
                  {
                    uint64_t
                    ev1 =
                      Hacl_Hash_Blake2s_128_update_last_blake2s_128(s,
                        ev,
                        (uint64_t)0U,
                        opad,
                        (uint32_t)64U);
                    ev11 = ev1;
                  }
                  else
                  {
                    uint64_t
                    ev1 = Hacl_Hash_Blake2s_128_update_multi_blake2s_128(s, ev, opad, (uint32_t)1U);
                    uint64_t
                    ev2 =
                      Hacl_Hash_Blake2s_128_update_last_blake2s_128(s,
                        ev1,
                        (uint64_t)(uint32_t)64U,
                        hash1,
                        (uint32_t)32U);
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
}

