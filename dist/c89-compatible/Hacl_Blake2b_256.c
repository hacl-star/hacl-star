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


#include "Hacl_Blake2b_256.h"

static inline void
blake2b_update_block(
  Lib_IntVector_Intrinsics_vec256 *wv,
  Lib_IntVector_Intrinsics_vec256 *hash,
  bool flag,
  FStar_UInt128_uint128 totlen,
  uint8_t *d
)
{
  Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_zero;
  uint64_t wv_14;
  if (flag)
  {
    wv_14 = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  }
  else
  {
    wv_14 = (uint64_t)0U;
  }
  {
    uint64_t wv_15 = (uint64_t)0U;
    Lib_IntVector_Intrinsics_vec256 *wv3;
    Lib_IntVector_Intrinsics_vec256 *s00;
    Lib_IntVector_Intrinsics_vec256 *s16;
    Lib_IntVector_Intrinsics_vec256 *r00;
    Lib_IntVector_Intrinsics_vec256 *r10;
    Lib_IntVector_Intrinsics_vec256 *r20;
    Lib_IntVector_Intrinsics_vec256 *r30;
    mask =
      Lib_IntVector_Intrinsics_vec256_load64s(FStar_UInt128_uint128_to_uint64(totlen),
        FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(totlen, (uint32_t)64U)),
        wv_14,
        wv_15);
    memcpy(wv, hash, (uint32_t)4U * (uint32_t)1U * sizeof (hash[0U]));
    wv3 = wv + (uint32_t)3U * (uint32_t)1U;
    wv3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv3[0U], mask);
    {
      uint32_t i;
      for (i = (uint32_t)0U; i < (uint32_t)12U; i++)
      {
        uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
        KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
        {
          Lib_IntVector_Intrinsics_vec256 m_st[(uint32_t)4U * (uint32_t)1U];
          {
            uint32_t _i;
            for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
              m_st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
          }
          {
            Lib_IntVector_Intrinsics_vec256 *r01 = m_st + (uint32_t)0U * (uint32_t)1U;
            Lib_IntVector_Intrinsics_vec256 *r11 = m_st + (uint32_t)1U * (uint32_t)1U;
            Lib_IntVector_Intrinsics_vec256 *r21 = m_st + (uint32_t)2U * (uint32_t)1U;
            Lib_IntVector_Intrinsics_vec256 *r31 = m_st + (uint32_t)3U * (uint32_t)1U;
            uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
            uint32_t s1 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
            uint32_t s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
            uint32_t s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
            uint32_t s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
            uint32_t s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
            uint32_t s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
            uint32_t s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
            uint32_t s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
            uint32_t s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
            uint32_t s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
            uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
            uint32_t s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
            uint32_t s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
            uint32_t s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
            uint32_t s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
            uint32_t nb = (uint32_t)8U;
            uint8_t *b00 = d + s0 * nb;
            uint8_t *b10 = d + s2 * nb;
            uint8_t *b20 = d + s4 * nb;
            uint8_t *b30 = d + s6 * nb;
            uint64_t u0 = load64_le(b00);
            uint64_t u00 = u0;
            uint64_t u1 = load64_le(b10);
            uint64_t u11 = u1;
            uint64_t u2 = load64_le(b20);
            uint64_t u20 = u2;
            uint64_t u3 = load64_le(b30);
            uint64_t u30 = u3;
            r01[0U] = Lib_IntVector_Intrinsics_vec256_load64s(u00, u11, u20, u30);
            {
              uint32_t nb0 = (uint32_t)8U;
              uint8_t *b01 = d + s1 * nb0;
              uint8_t *b11 = d + s3 * nb0;
              uint8_t *b21 = d + s5 * nb0;
              uint8_t *b31 = d + s7 * nb0;
              uint64_t u4 = load64_le(b01);
              uint64_t u01 = u4;
              uint64_t u5 = load64_le(b11);
              uint64_t u110 = u5;
              uint64_t u6 = load64_le(b21);
              uint64_t u21 = u6;
              uint64_t u7 = load64_le(b31);
              uint64_t u31 = u7;
              r11[0U] = Lib_IntVector_Intrinsics_vec256_load64s(u01, u110, u21, u31);
              {
                uint32_t nb1 = (uint32_t)8U;
                uint8_t *b02 = d + s8 * nb1;
                uint8_t *b12 = d + s10 * nb1;
                uint8_t *b22 = d + s12 * nb1;
                uint8_t *b32 = d + s14 * nb1;
                uint64_t u8 = load64_le(b02);
                uint64_t u02 = u8;
                uint64_t u9 = load64_le(b12);
                uint64_t u111 = u9;
                uint64_t u10 = load64_le(b22);
                uint64_t u22 = u10;
                uint64_t u12 = load64_le(b32);
                uint64_t u32 = u12;
                r21[0U] = Lib_IntVector_Intrinsics_vec256_load64s(u02, u111, u22, u32);
                {
                  uint32_t nb2 = (uint32_t)8U;
                  uint8_t *b0 = d + s9 * nb2;
                  uint8_t *b1 = d + s11 * nb2;
                  uint8_t *b2 = d + s13 * nb2;
                  uint8_t *b3 = d + s15 * nb2;
                  uint64_t u13 = load64_le(b0);
                  uint64_t u03 = u13;
                  uint64_t u14 = load64_le(b1);
                  uint64_t u112 = u14;
                  uint64_t u15 = load64_le(b2);
                  uint64_t u23 = u15;
                  uint64_t u = load64_le(b3);
                  uint64_t u33 = u;
                  r31[0U] = Lib_IntVector_Intrinsics_vec256_load64s(u03, u112, u23, u33);
                  {
                    Lib_IntVector_Intrinsics_vec256 *x = m_st + (uint32_t)0U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec256 *y = m_st + (uint32_t)1U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec256 *z = m_st + (uint32_t)2U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec256 *w = m_st + (uint32_t)3U * (uint32_t)1U;
                    uint32_t a = (uint32_t)0U;
                    uint32_t b4 = (uint32_t)1U;
                    uint32_t c0 = (uint32_t)2U;
                    uint32_t d10 = (uint32_t)3U;
                    uint32_t r02 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
                    uint32_t r12 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
                    uint32_t r22 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
                    uint32_t r32 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
                    Lib_IntVector_Intrinsics_vec256 zz0 = Lib_IntVector_Intrinsics_vec256_zero;
                    Lib_IntVector_Intrinsics_vec256 *wv_a0 = wv + a * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec256 *wv_b0 = wv + b4 * (uint32_t)1U;
                    wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], wv_b0[0U]);
                    wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], x[0U]);
                    {
                      Lib_IntVector_Intrinsics_vec256 *wv_a1 = wv + d10 * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec256 *wv_b1 = wv + a * (uint32_t)1U;
                      wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a1[0U], wv_b1[0U]);
                      wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a1[0U], r02);
                      {
                        Lib_IntVector_Intrinsics_vec256 *wv_a2 = wv + c0 * (uint32_t)1U;
                        Lib_IntVector_Intrinsics_vec256 *wv_b2 = wv + d10 * (uint32_t)1U;
                        wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], wv_b2[0U]);
                        wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], zz0);
                        {
                          Lib_IntVector_Intrinsics_vec256 *wv_a3 = wv + b4 * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec256 *wv_b3 = wv + c0 * (uint32_t)1U;
                          wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a3[0U], wv_b3[0U]);
                          wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a3[0U], r12);
                          {
                            Lib_IntVector_Intrinsics_vec256 *wv_a4 = wv + a * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec256 *wv_b4 = wv + b4 * (uint32_t)1U;
                            wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], wv_b4[0U]);
                            wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], y[0U]);
                            {
                              Lib_IntVector_Intrinsics_vec256 *wv_a5 = wv + d10 * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec256 *wv_b5 = wv + a * (uint32_t)1U;
                              wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a5[0U], wv_b5[0U]);
                              wv_a5[0U] =
                                Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a5[0U],
                                  r22);
                              {
                                Lib_IntVector_Intrinsics_vec256 *wv_a6 = wv + c0 * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec256 *wv_b6 = wv + d10 * (uint32_t)1U;
                                wv_a6[0U] =
                                  Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U],
                                    wv_b6[0U]);
                                wv_a6[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U], zz0);
                                {
                                  Lib_IntVector_Intrinsics_vec256 *wv_a7 = wv + b4 * (uint32_t)1U;
                                  Lib_IntVector_Intrinsics_vec256 *wv_b7 = wv + c0 * (uint32_t)1U;
                                  wv_a7[0U] =
                                    Lib_IntVector_Intrinsics_vec256_xor(wv_a7[0U],
                                      wv_b7[0U]);
                                  wv_a7[0U] =
                                    Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a7[0U],
                                      r32);
                                  {
                                    Lib_IntVector_Intrinsics_vec256
                                    *r13 = wv + (uint32_t)1U * (uint32_t)1U;
                                    Lib_IntVector_Intrinsics_vec256
                                    *r23 = wv + (uint32_t)2U * (uint32_t)1U;
                                    Lib_IntVector_Intrinsics_vec256
                                    *r33 = wv + (uint32_t)3U * (uint32_t)1U;
                                    Lib_IntVector_Intrinsics_vec256 v00 = r13[0U];
                                    Lib_IntVector_Intrinsics_vec256
                                    v1 =
                                      Lib_IntVector_Intrinsics_vec256_shuffle64(v00,
                                        (uint32_t)1U,
                                        ((uint32_t)1U + (uint32_t)1U) % (uint32_t)4U,
                                        ((uint32_t)1U + (uint32_t)2U) % (uint32_t)4U,
                                        ((uint32_t)1U + (uint32_t)3U) % (uint32_t)4U);
                                    r13[0U] = v1;
                                    {
                                      Lib_IntVector_Intrinsics_vec256 v01 = r23[0U];
                                      Lib_IntVector_Intrinsics_vec256
                                      v10 =
                                        Lib_IntVector_Intrinsics_vec256_shuffle64(v01,
                                          (uint32_t)2U,
                                          ((uint32_t)2U + (uint32_t)1U) % (uint32_t)4U,
                                          ((uint32_t)2U + (uint32_t)2U) % (uint32_t)4U,
                                          ((uint32_t)2U + (uint32_t)3U) % (uint32_t)4U);
                                      r23[0U] = v10;
                                      {
                                        Lib_IntVector_Intrinsics_vec256 v02 = r33[0U];
                                        Lib_IntVector_Intrinsics_vec256
                                        v11 =
                                          Lib_IntVector_Intrinsics_vec256_shuffle64(v02,
                                            (uint32_t)3U,
                                            ((uint32_t)3U + (uint32_t)1U) % (uint32_t)4U,
                                            ((uint32_t)3U + (uint32_t)2U) % (uint32_t)4U,
                                            ((uint32_t)3U + (uint32_t)3U) % (uint32_t)4U);
                                        r33[0U] = v11;
                                        {
                                          uint32_t a0 = (uint32_t)0U;
                                          uint32_t b = (uint32_t)1U;
                                          uint32_t c = (uint32_t)2U;
                                          uint32_t d1 = (uint32_t)3U;
                                          uint32_t r0 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
                                          uint32_t r1 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
                                          uint32_t r24 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
                                          uint32_t r34 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
                                          Lib_IntVector_Intrinsics_vec256
                                          zz = Lib_IntVector_Intrinsics_vec256_zero;
                                          Lib_IntVector_Intrinsics_vec256
                                          *wv_a = wv + a0 * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec256
                                          *wv_b8 = wv + b * (uint32_t)1U;
                                          wv_a[0U] =
                                            Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U],
                                              wv_b8[0U]);
                                          wv_a[0U] =
                                            Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U],
                                              z[0U]);
                                          {
                                            Lib_IntVector_Intrinsics_vec256
                                            *wv_a8 = wv + d1 * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec256
                                            *wv_b9 = wv + a0 * (uint32_t)1U;
                                            wv_a8[0U] =
                                              Lib_IntVector_Intrinsics_vec256_xor(wv_a8[0U],
                                                wv_b9[0U]);
                                            wv_a8[0U] =
                                              Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a8[0U],
                                                r0);
                                            {
                                              Lib_IntVector_Intrinsics_vec256
                                              *wv_a9 = wv + c * (uint32_t)1U;
                                              Lib_IntVector_Intrinsics_vec256
                                              *wv_b10 = wv + d1 * (uint32_t)1U;
                                              wv_a9[0U] =
                                                Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U],
                                                  wv_b10[0U]);
                                              wv_a9[0U] =
                                                Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U],
                                                  zz);
                                              {
                                                Lib_IntVector_Intrinsics_vec256
                                                *wv_a10 = wv + b * (uint32_t)1U;
                                                Lib_IntVector_Intrinsics_vec256
                                                *wv_b11 = wv + c * (uint32_t)1U;
                                                wv_a10[0U] =
                                                  Lib_IntVector_Intrinsics_vec256_xor(wv_a10[0U],
                                                    wv_b11[0U]);
                                                wv_a10[0U] =
                                                  Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a10[0U],
                                                    r1);
                                                {
                                                  Lib_IntVector_Intrinsics_vec256
                                                  *wv_a11 = wv + a0 * (uint32_t)1U;
                                                  Lib_IntVector_Intrinsics_vec256
                                                  *wv_b12 = wv + b * (uint32_t)1U;
                                                  wv_a11[0U] =
                                                    Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U],
                                                      wv_b12[0U]);
                                                  wv_a11[0U] =
                                                    Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U],
                                                      w[0U]);
                                                  {
                                                    Lib_IntVector_Intrinsics_vec256
                                                    *wv_a12 = wv + d1 * (uint32_t)1U;
                                                    Lib_IntVector_Intrinsics_vec256
                                                    *wv_b13 = wv + a0 * (uint32_t)1U;
                                                    wv_a12[0U] =
                                                      Lib_IntVector_Intrinsics_vec256_xor(wv_a12[0U],
                                                        wv_b13[0U]);
                                                    wv_a12[0U] =
                                                      Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a12[0U],
                                                        r24);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec256
                                                      *wv_a13 = wv + c * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec256
                                                      *wv_b14 = wv + d1 * (uint32_t)1U;
                                                      wv_a13[0U] =
                                                        Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U],
                                                          wv_b14[0U]);
                                                      wv_a13[0U] =
                                                        Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U],
                                                          zz);
                                                      {
                                                        Lib_IntVector_Intrinsics_vec256
                                                        *wv_a14 = wv + b * (uint32_t)1U;
                                                        Lib_IntVector_Intrinsics_vec256
                                                        *wv_b = wv + c * (uint32_t)1U;
                                                        wv_a14[0U] =
                                                          Lib_IntVector_Intrinsics_vec256_xor(wv_a14[0U],
                                                            wv_b[0U]);
                                                        wv_a14[0U] =
                                                          Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a14[0U],
                                                            r34);
                                                        {
                                                          Lib_IntVector_Intrinsics_vec256
                                                          *r14 = wv + (uint32_t)1U * (uint32_t)1U;
                                                          Lib_IntVector_Intrinsics_vec256
                                                          *r2 = wv + (uint32_t)2U * (uint32_t)1U;
                                                          Lib_IntVector_Intrinsics_vec256
                                                          *r3 = wv + (uint32_t)3U * (uint32_t)1U;
                                                          Lib_IntVector_Intrinsics_vec256
                                                          v0 = r14[0U];
                                                          Lib_IntVector_Intrinsics_vec256
                                                          v12 =
                                                            Lib_IntVector_Intrinsics_vec256_shuffle64(v0,
                                                              (uint32_t)3U,
                                                              ((uint32_t)3U + (uint32_t)1U)
                                                              % (uint32_t)4U,
                                                              ((uint32_t)3U + (uint32_t)2U)
                                                              % (uint32_t)4U,
                                                              ((uint32_t)3U + (uint32_t)3U)
                                                              % (uint32_t)4U);
                                                          r14[0U] = v12;
                                                          {
                                                            Lib_IntVector_Intrinsics_vec256
                                                            v03 = r2[0U];
                                                            Lib_IntVector_Intrinsics_vec256
                                                            v13 =
                                                              Lib_IntVector_Intrinsics_vec256_shuffle64(v03,
                                                                (uint32_t)2U,
                                                                ((uint32_t)2U + (uint32_t)1U)
                                                                % (uint32_t)4U,
                                                                ((uint32_t)2U + (uint32_t)2U)
                                                                % (uint32_t)4U,
                                                                ((uint32_t)2U + (uint32_t)3U)
                                                                % (uint32_t)4U);
                                                            r2[0U] = v13;
                                                            {
                                                              Lib_IntVector_Intrinsics_vec256
                                                              v04 = r3[0U];
                                                              Lib_IntVector_Intrinsics_vec256
                                                              v14 =
                                                                Lib_IntVector_Intrinsics_vec256_shuffle64(v04,
                                                                  (uint32_t)1U,
                                                                  ((uint32_t)1U + (uint32_t)1U)
                                                                  % (uint32_t)4U,
                                                                  ((uint32_t)1U + (uint32_t)2U)
                                                                  % (uint32_t)4U,
                                                                  ((uint32_t)1U + (uint32_t)3U)
                                                                  % (uint32_t)4U);
                                                              r3[0U] = v14;
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    s00 = hash + (uint32_t)0U * (uint32_t)1U;
    s16 = hash + (uint32_t)1U * (uint32_t)1U;
    r00 = wv + (uint32_t)0U * (uint32_t)1U;
    r10 = wv + (uint32_t)1U * (uint32_t)1U;
    r20 = wv + (uint32_t)2U * (uint32_t)1U;
    r30 = wv + (uint32_t)3U * (uint32_t)1U;
    s00[0U] = Lib_IntVector_Intrinsics_vec256_xor(s00[0U], r00[0U]);
    s00[0U] = Lib_IntVector_Intrinsics_vec256_xor(s00[0U], r20[0U]);
    s16[0U] = Lib_IntVector_Intrinsics_vec256_xor(s16[0U], r10[0U]);
    s16[0U] = Lib_IntVector_Intrinsics_vec256_xor(s16[0U], r30[0U]);
  }
}

void
Hacl_Blake2b_256_blake2b(
  uint32_t nn,
  uint8_t *output,
  uint32_t ll,
  uint8_t *d,
  uint32_t kk,
  uint8_t *k
)
{
  uint32_t stlen = (uint32_t)4U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 stzero = Lib_IntVector_Intrinsics_vec256_zero;
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), stlen);
  {
    Lib_IntVector_Intrinsics_vec256 b[stlen];
    {
      uint32_t _i;
      for (_i = 0U; _i < stlen; ++_i)
        b[_i] = stzero;
    }
    {
      FStar_UInt128_uint128 prev0;
      if (kk == (uint32_t)0U)
      {
        prev0 = FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)0U);
      }
      else
      {
        prev0 = FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U);
      }
      KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), stlen);
      {
        Lib_IntVector_Intrinsics_vec256 b1[stlen];
        {
          uint32_t _i;
          for (_i = 0U; _i < stlen; ++_i)
            b1[_i] = stzero;
        }
        {
          uint8_t b20[128U] = { 0U };
          Lib_IntVector_Intrinsics_vec256 *r0 = b + (uint32_t)0U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *r1 = b + (uint32_t)1U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *r2 = b + (uint32_t)2U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *r3 = b + (uint32_t)3U * (uint32_t)1U;
          uint64_t iv0 = Hacl_Impl_Blake2_Constants_ivTable_B[0U];
          uint64_t iv1 = Hacl_Impl_Blake2_Constants_ivTable_B[1U];
          uint64_t iv2 = Hacl_Impl_Blake2_Constants_ivTable_B[2U];
          uint64_t iv3 = Hacl_Impl_Blake2_Constants_ivTable_B[3U];
          uint64_t iv4 = Hacl_Impl_Blake2_Constants_ivTable_B[4U];
          uint64_t iv5 = Hacl_Impl_Blake2_Constants_ivTable_B[5U];
          uint64_t iv6 = Hacl_Impl_Blake2_Constants_ivTable_B[6U];
          uint64_t iv7 = Hacl_Impl_Blake2_Constants_ivTable_B[7U];
          uint64_t kk_shift_8;
          uint64_t iv0_;
          uint32_t nb0;
          uint32_t rem10;
          K___uint32_t_uint32_t scrut;
          uint32_t nb;
          uint32_t rem1;
          r2[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0, iv1, iv2, iv3);
          r3[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4, iv5, iv6, iv7);
          kk_shift_8 = (uint64_t)kk << (uint32_t)8U;
          iv0_ = iv0 ^ ((uint64_t)0x01010000U ^ (kk_shift_8 ^ (uint64_t)nn));
          r0[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0_, iv1, iv2, iv3);
          r1[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4, iv5, iv6, iv7);
          if (!(kk == (uint32_t)0U))
          {
            memcpy(b20, k, kk * sizeof (k[0U]));
            {
              FStar_UInt128_uint128
              totlen =
                FStar_UInt128_add_mod(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)0U),
                  FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U));
              uint8_t *b3 = b20 + (uint32_t)0U * (uint32_t)128U;
              blake2b_update_block(b1, b, false, totlen, b3);
            }
          }
          memset(b20, 0U, (uint32_t)128U * sizeof (b20[0U]));
          nb0 = ll / (uint32_t)128U;
          rem10 = ll % (uint32_t)128U;
          if (rem10 == (uint32_t)0U && nb0 > (uint32_t)0U)
          {
            uint32_t nb_ = nb0 - (uint32_t)1U;
            uint32_t rem_ = (uint32_t)128U;
            K___uint32_t_uint32_t lit;
            lit.fst = nb_;
            lit.snd = rem_;
            scrut = lit;
          }
          else
          {
            K___uint32_t_uint32_t lit;
            lit.fst = nb0;
            lit.snd = rem10;
            scrut = lit;
          }
          nb = scrut.fst;
          rem1 = scrut.snd;
          {
            uint32_t i;
            for (i = (uint32_t)0U; i < nb; i++)
            {
              FStar_UInt128_uint128
              totlen =
                FStar_UInt128_add_mod(prev0,
                  FStar_UInt128_uint64_to_uint128((uint64_t)((i + (uint32_t)1U) * (uint32_t)128U)));
              uint8_t *b2 = d + i * (uint32_t)128U;
              blake2b_update_block(b1, b, false, totlen, b2);
            }
          }
          {
            uint8_t b21[128U] = { 0U };
            uint8_t *last1 = d + ll - rem1;
            FStar_UInt128_uint128 totlen;
            uint32_t double_row;
            memcpy(b21, last1, rem1 * sizeof (last1[0U]));
            totlen = FStar_UInt128_add_mod(prev0, FStar_UInt128_uint64_to_uint128((uint64_t)ll));
            blake2b_update_block(b1, b, true, totlen, b21);
            memset(b21, 0U, (uint32_t)128U * sizeof (b21[0U]));
            double_row = (uint32_t)2U * (uint32_t)4U * (uint32_t)8U;
            KRML_CHECK_SIZE(sizeof (uint8_t), double_row);
            {
              uint8_t b2[double_row];
              memset(b2, 0U, double_row * sizeof (b2[0U]));
              {
                uint8_t *first = b2;
                uint8_t *second = b2 + (uint32_t)4U * (uint32_t)8U;
                Lib_IntVector_Intrinsics_vec256 *row0 = b + (uint32_t)0U * (uint32_t)1U;
                Lib_IntVector_Intrinsics_vec256 *row1 = b + (uint32_t)1U * (uint32_t)1U;
                uint8_t *final;
                Lib_IntVector_Intrinsics_vec256_store_le(first, row0[0U]);
                Lib_IntVector_Intrinsics_vec256_store_le(second, row1[0U]);
                final = b2;
                memcpy(output, final, nn * sizeof (final[0U]));
                memset(b2, 0U, double_row * sizeof (b2[0U]));
                {
                  uint32_t _i;
                  for (_i = 0U; _i < stlen; ++_i)
                    b1[_i] = stzero;
                }
                {
                  uint32_t _i;
                  for (_i = 0U; _i < stlen; ++_i)
                    b[_i] = stzero;
                }
              }
            }
          }
        }
      }
    }
  }
}

