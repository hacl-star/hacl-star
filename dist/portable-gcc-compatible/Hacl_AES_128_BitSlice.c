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


#include "internal/Hacl_AES_128_BitSlice.h"

#include "internal/Hacl_Lib.h"

/* SNIPPET_START: __uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t */

typedef struct __uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_s
{
  uint64_t fst;
  uint64_t snd;
  uint64_t thd;
  uint64_t f3;
  uint64_t f4;
  uint64_t f5;
  uint64_t f6;
  uint64_t f7;
}
__uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t;

/* SNIPPET_END: __uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t */

/* SNIPPET_START: sub_bytes64x8 */

static __uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t
sub_bytes64x8(
  uint64_t st0,
  uint64_t st1,
  uint64_t st2,
  uint64_t st3,
  uint64_t st4,
  uint64_t st5,
  uint64_t st6,
  uint64_t st7
)
{
  uint64_t input[8U] = { 0U };
  input[0U] = st0;
  input[1U] = st1;
  input[2U] = st2;
  input[3U] = st3;
  input[4U] = st4;
  input[5U] = st5;
  input[6U] = st6;
  input[7U] = st7;
  uint64_t output[8U] = { 0U };
  uint64_t tmp[121U] = { 0U };
  tmp[0U] = input[0U];
  tmp[1U] = input[1U];
  tmp[2U] = input[2U];
  tmp[3U] = input[3U];
  tmp[4U] = input[4U];
  tmp[5U] = input[5U];
  tmp[6U] = input[6U];
  tmp[7U] = input[7U];
  tmp[8U] = tmp[3U] ^ tmp[5U];
  tmp[9U] = tmp[0U] ^ tmp[6U];
  tmp[10U] = tmp[0U] ^ tmp[3U];
  tmp[11U] = tmp[0U] ^ tmp[5U];
  tmp[12U] = tmp[1U] ^ tmp[2U];
  tmp[13U] = tmp[12U] ^ tmp[7U];
  tmp[14U] = tmp[13U] ^ tmp[3U];
  tmp[15U] = tmp[9U] ^ tmp[8U];
  tmp[16U] = tmp[13U] ^ tmp[0U];
  tmp[17U] = tmp[13U] ^ tmp[6U];
  tmp[18U] = tmp[17U] ^ tmp[11U];
  tmp[19U] = tmp[4U] ^ tmp[15U];
  tmp[20U] = tmp[19U] ^ tmp[5U];
  tmp[21U] = tmp[19U] ^ tmp[1U];
  tmp[22U] = tmp[20U] ^ tmp[7U];
  tmp[23U] = tmp[20U] ^ tmp[12U];
  tmp[24U] = tmp[21U] ^ tmp[10U];
  tmp[25U] = tmp[7U] ^ tmp[24U];
  tmp[26U] = tmp[23U] ^ tmp[24U];
  tmp[27U] = tmp[23U] ^ tmp[11U];
  tmp[28U] = tmp[12U] ^ tmp[24U];
  tmp[29U] = tmp[9U] ^ tmp[28U];
  tmp[30U] = tmp[0U] ^ tmp[28U];
  tmp[31U] = tmp[15U] & tmp[20U];
  tmp[32U] = tmp[18U] & tmp[22U];
  tmp[33U] = tmp[32U] ^ tmp[31U];
  tmp[34U] = tmp[14U] & tmp[7U];
  tmp[35U] = tmp[34U] ^ tmp[31U];
  tmp[36U] = tmp[9U] & tmp[28U];
  tmp[37U] = tmp[17U] & tmp[13U];
  tmp[38U] = tmp[37U] ^ tmp[36U];
  tmp[39U] = tmp[16U] & tmp[25U];
  tmp[40U] = tmp[39U] ^ tmp[36U];
  tmp[41U] = tmp[10U] & tmp[24U];
  tmp[42U] = tmp[8U] & tmp[26U];
  tmp[43U] = tmp[42U] ^ tmp[41U];
  tmp[44U] = tmp[11U] & tmp[23U];
  tmp[45U] = tmp[44U] ^ tmp[41U];
  tmp[46U] = tmp[33U] ^ tmp[21U];
  tmp[47U] = tmp[35U] ^ tmp[45U];
  tmp[48U] = tmp[38U] ^ tmp[43U];
  tmp[49U] = tmp[40U] ^ tmp[45U];
  tmp[50U] = tmp[46U] ^ tmp[43U];
  tmp[51U] = tmp[47U] ^ tmp[27U];
  tmp[52U] = tmp[48U] ^ tmp[29U];
  tmp[53U] = tmp[49U] ^ tmp[30U];
  tmp[54U] = tmp[50U] ^ tmp[51U];
  tmp[55U] = tmp[50U] & tmp[52U];
  tmp[56U] = tmp[53U] ^ tmp[55U];
  tmp[57U] = tmp[54U] & tmp[56U];
  tmp[58U] = tmp[57U] ^ tmp[51U];
  tmp[59U] = tmp[52U] ^ tmp[53U];
  tmp[60U] = tmp[51U] ^ tmp[55U];
  tmp[61U] = tmp[60U] & tmp[59U];
  tmp[62U] = tmp[61U] ^ tmp[53U];
  tmp[63U] = tmp[52U] ^ tmp[62U];
  tmp[64U] = tmp[56U] ^ tmp[62U];
  tmp[65U] = tmp[53U] & tmp[64U];
  tmp[66U] = tmp[65U] ^ tmp[63U];
  tmp[67U] = tmp[56U] ^ tmp[65U];
  tmp[68U] = tmp[58U] & tmp[67U];
  tmp[69U] = tmp[54U] ^ tmp[68U];
  tmp[70U] = tmp[69U] ^ tmp[66U];
  tmp[71U] = tmp[58U] ^ tmp[62U];
  tmp[72U] = tmp[58U] ^ tmp[69U];
  tmp[73U] = tmp[62U] ^ tmp[66U];
  tmp[74U] = tmp[71U] ^ tmp[70U];
  tmp[75U] = tmp[73U] & tmp[20U];
  tmp[76U] = tmp[66U] & tmp[22U];
  tmp[77U] = tmp[62U] & tmp[7U];
  tmp[78U] = tmp[72U] & tmp[28U];
  tmp[79U] = tmp[69U] & tmp[13U];
  tmp[80U] = tmp[58U] & tmp[25U];
  tmp[81U] = tmp[71U] & tmp[24U];
  tmp[82U] = tmp[74U] & tmp[26U];
  tmp[83U] = tmp[70U] & tmp[23U];
  tmp[84U] = tmp[73U] & tmp[15U];
  tmp[85U] = tmp[66U] & tmp[18U];
  tmp[86U] = tmp[62U] & tmp[14U];
  tmp[87U] = tmp[72U] & tmp[9U];
  tmp[88U] = tmp[69U] & tmp[17U];
  tmp[89U] = tmp[58U] & tmp[16U];
  tmp[90U] = tmp[71U] & tmp[10U];
  tmp[91U] = tmp[74U] & tmp[8U];
  tmp[92U] = tmp[70U] & tmp[11U];
  tmp[93U] = tmp[90U] ^ tmp[91U];
  tmp[94U] = tmp[85U] ^ tmp[93U];
  tmp[95U] = tmp[84U] ^ tmp[94U];
  tmp[96U] = tmp[75U] ^ tmp[77U];
  tmp[97U] = tmp[76U] ^ tmp[75U];
  tmp[98U] = tmp[78U] ^ tmp[79U];
  tmp[99U] = tmp[87U] ^ tmp[96U];
  tmp[100U] = tmp[82U] ^ tmp[98U];
  tmp[101U] = tmp[83U] ^ tmp[99U];
  tmp[102U] = tmp[100U] ^ tmp[101U];
  tmp[103U] = tmp[98U] ^ tmp[97U];
  tmp[104U] = tmp[78U] ^ tmp[80U];
  tmp[105U] = tmp[88U] ^ tmp[93U];
  tmp[106U] = tmp[96U] ^ tmp[104U];
  tmp[107U] = tmp[95U] ^ tmp[103U];
  tmp[108U] = tmp[81U] ^ tmp[100U];
  tmp[109U] = tmp[89U] ^ tmp[102U];
  tmp[110U] = tmp[105U] ^ tmp[106U];
  uint64_t uu____0 = tmp[87U];
  uint64_t uu____1 = tmp[110U];
  tmp[111U] = (~uu____0 & ~uu____1) | (uu____0 & uu____1);
  tmp[112U] = tmp[90U] ^ tmp[108U];
  tmp[113U] = tmp[94U] ^ tmp[86U];
  tmp[114U] = tmp[95U] ^ tmp[108U];
  uint64_t uu____2 = tmp[102U];
  uint64_t uu____3 = tmp[110U];
  tmp[115U] = (~uu____2 & ~uu____3) | (uu____2 & uu____3);
  tmp[116U] = tmp[106U] ^ tmp[107U];
  uint64_t uu____4 = tmp[107U];
  uint64_t uu____5 = tmp[108U];
  tmp[117U] = (~uu____4 & ~uu____5) | (uu____4 & uu____5);
  tmp[118U] = tmp[109U] ^ tmp[112U];
  uint64_t uu____6 = tmp[118U];
  uint64_t uu____7 = tmp[92U];
  tmp[119U] = (~uu____6 & ~uu____7) | (uu____6 & uu____7);
  tmp[120U] = tmp[113U] ^ tmp[109U];
  uint64_t o = tmp[114U];
  output[0U] = o;
  uint64_t o0 = tmp[117U];
  output[1U] = o0;
  uint64_t o8 = tmp[119U];
  output[2U] = o8;
  uint64_t o9 = tmp[107U];
  output[3U] = o9;
  uint64_t o10 = tmp[116U];
  output[4U] = o10;
  uint64_t o11 = tmp[120U];
  output[5U] = o11;
  uint64_t o12 = tmp[115U];
  output[6U] = o12;
  uint64_t o13 = tmp[111U];
  output[7U] = o13;
  uint64_t o00 = output[0U];
  uint64_t o1 = output[1U];
  uint64_t o2 = output[2U];
  uint64_t o3 = output[3U];
  uint64_t o4 = output[4U];
  uint64_t o5 = output[5U];
  uint64_t o6 = output[6U];
  uint64_t o7 = output[7U];
  return
    (
      (__uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t){
        .fst = o00,
        .snd = o1,
        .thd = o2,
        .f3 = o3,
        .f4 = o4,
        .f5 = o5,
        .f6 = o6,
        .f7 = o7
      }
    );
}

/* SNIPPET_END: sub_bytes64x8 */

/* SNIPPET_START: load_block0 */

static void load_block0(uint64_t *out, uint8_t *inp)
{
  uint8_t *b1 = inp;
  uint8_t *b2 = inp + (uint32_t)8U;
  uint64_t u0 = load64_le(b1);
  uint64_t fst = u0;
  uint64_t u1 = load64_le(b2);
  uint64_t snd = u1;
  uint64_t fst1 = Lib_Transposition64x8_transpose_bits64(fst);
  uint64_t snd1 = Lib_Transposition64x8_transpose_bits64(snd);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t sh = i * (uint32_t)8U;
    uint64_t u = fst1 >> sh & (uint64_t)0xffU;
    uint64_t u10 = u ^ (snd1 >> sh & (uint64_t)0xffU) << (uint32_t)8U;
    out[i] = u10;);
}

/* SNIPPET_END: load_block0 */

/* SNIPPET_START: transpose_state */

static void transpose_state(uint64_t *st)
{
  uint64_t i0 = st[0U];
  uint64_t i1 = st[1U];
  uint64_t i2 = st[2U];
  uint64_t i3 = st[3U];
  uint64_t i4 = st[4U];
  uint64_t i5 = st[5U];
  uint64_t i6 = st[6U];
  uint64_t i7 = st[7U];
  Lib_Transposition64x8_uint64x8
  scrut =
    Lib_Transposition64x8_transpose_bits64x8((
        (Lib_Transposition64x8_uint64x8){
          .fst = { .fst = { .fst = i0, .snd = i1 }, .snd = { .fst = i2, .snd = i3 } },
          .snd = { .fst = { .fst = i4, .snd = i5 }, .snd = { .fst = i6, .snd = i7 } }
        }
      ));
  uint64_t t7 = scrut.snd.snd.snd;
  uint64_t t6 = scrut.snd.snd.fst;
  uint64_t t5 = scrut.snd.fst.snd;
  uint64_t t4 = scrut.snd.fst.fst;
  uint64_t t3 = scrut.fst.snd.snd;
  uint64_t t2 = scrut.fst.snd.fst;
  uint64_t t1 = scrut.fst.fst.snd;
  uint64_t t0 = scrut.fst.fst.fst;
  st[0U] = t0;
  st[1U] = t1;
  st[2U] = t2;
  st[3U] = t3;
  st[4U] = t4;
  st[5U] = t5;
  st[6U] = t6;
  st[7U] = t7;
}

/* SNIPPET_END: transpose_state */

/* SNIPPET_START: Hacl_Impl_AES_CoreBitSlice_store_block0 */

void Hacl_Impl_AES_CoreBitSlice_store_block0(uint8_t *out, uint64_t *inp)
{
  uint64_t i0 = inp[0U];
  uint64_t i1 = inp[1U];
  uint64_t i2 = inp[2U];
  uint64_t i3 = inp[3U];
  uint64_t i4 = inp[4U];
  uint64_t i5 = inp[5U];
  uint64_t i6 = inp[6U];
  uint64_t i7 = inp[7U];
  Lib_Transposition64x8_uint64x8
  scrut =
    Lib_Transposition64x8_transpose_bits64x8_inv((
        (Lib_Transposition64x8_uint64x8){
          .fst = { .fst = { .fst = i0, .snd = i1 }, .snd = { .fst = i2, .snd = i3 } },
          .snd = { .fst = { .fst = i4, .snd = i5 }, .snd = { .fst = i6, .snd = i7 } }
        }
      ));
  uint64_t t1 = scrut.fst.fst.snd;
  uint64_t t0 = scrut.fst.fst.fst;
  store64_le(out, t0);
  store64_le(out + (uint32_t)8U, t1);
}

/* SNIPPET_END: Hacl_Impl_AES_CoreBitSlice_store_block0 */

/* SNIPPET_START: Hacl_Impl_AES_CoreBitSlice_load_key1 */

void Hacl_Impl_AES_CoreBitSlice_load_key1(uint64_t *out, uint8_t *k)
{
  load_block0(out, k);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t u = out[i];
    uint64_t u1 = u ^ u << (uint32_t)16U;
    uint64_t u2 = u1 ^ u1 << (uint32_t)32U;
    out[i] = u2;);
}

/* SNIPPET_END: Hacl_Impl_AES_CoreBitSlice_load_key1 */

/* SNIPPET_START: Hacl_Impl_AES_CoreBitSlice_load_nonce */

void Hacl_Impl_AES_CoreBitSlice_load_nonce(uint64_t *out, uint8_t *nonce1)
{
  uint8_t nb[16U] = { 0U };
  memcpy(nb, nonce1, (uint32_t)12U * sizeof (uint8_t));
  Hacl_Impl_AES_CoreBitSlice_load_key1(out, nb);
}

/* SNIPPET_END: Hacl_Impl_AES_CoreBitSlice_load_nonce */

/* SNIPPET_START: Hacl_Impl_AES_CoreBitSlice_load_state */

void Hacl_Impl_AES_CoreBitSlice_load_state(uint64_t *out, uint64_t *nonce1, uint32_t counter)
{
  uint8_t ctr[16U] = { 0U };
  store32_be(ctr, counter);
  store32_be(ctr + (uint32_t)4U, counter + (uint32_t)1U);
  store32_be(ctr + (uint32_t)8U, counter + (uint32_t)2U);
  store32_be(ctr + (uint32_t)12U, counter + (uint32_t)3U);
  load_block0(out, ctr);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t u = out[i];
    uint64_t
    u1 = ((u << (uint32_t)12U | u << (uint32_t)24U) | u << (uint32_t)36U) | u << (uint32_t)48U;
    uint64_t u2 = u1 & (uint64_t)0xf000f000f000f000U;
    out[i] = u2 ^ nonce1[i];);
}

/* SNIPPET_END: Hacl_Impl_AES_CoreBitSlice_load_state */

/* SNIPPET_START: Hacl_Impl_AES_CoreBitSlice_xor_state_key1 */

void Hacl_Impl_AES_CoreBitSlice_xor_state_key1(uint64_t *st, uint64_t *ost)
{
  KRML_MAYBE_FOR8(i, (uint32_t)0U, (uint32_t)8U, (uint32_t)1U, st[i] = st[i] ^ ost[i];);
}

/* SNIPPET_END: Hacl_Impl_AES_CoreBitSlice_xor_state_key1 */

/* SNIPPET_START: xor_block */

static void xor_block(uint8_t *out, uint64_t *st, uint8_t *inp)
{
  transpose_state(st);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint8_t *ob = out + i * (uint32_t)8U;
    uint8_t *ib = inp + i * (uint32_t)8U;
    uint64_t u = load64_le(ib);
    uint64_t u0 = u;
    store64_le(ob, u0 ^ st[i]););
}

/* SNIPPET_END: xor_block */

/* SNIPPET_START: sub_bytes_state */

static void sub_bytes_state(uint64_t *st)
{
  uint64_t st0 = st[0U];
  uint64_t st1 = st[1U];
  uint64_t st2 = st[2U];
  uint64_t st3 = st[3U];
  uint64_t st4 = st[4U];
  uint64_t st5 = st[5U];
  uint64_t st6 = st[6U];
  uint64_t st7 = st[7U];
  Lib_Transposition64x8_uint64x8
  scrut =
    Lib_Transposition64x8_transpose_bits64x8((
        (Lib_Transposition64x8_uint64x8){
          .fst = { .fst = { .fst = st0, .snd = st1 }, .snd = { .fst = st2, .snd = st3 } },
          .snd = { .fst = { .fst = st4, .snd = st5 }, .snd = { .fst = st6, .snd = st7 } }
        }
      ));
  uint64_t st71 = scrut.snd.snd.snd;
  uint64_t st61 = scrut.snd.snd.fst;
  uint64_t st51 = scrut.snd.fst.snd;
  uint64_t st41 = scrut.snd.fst.fst;
  uint64_t st31 = scrut.fst.snd.snd;
  uint64_t st21 = scrut.fst.snd.fst;
  uint64_t st11 = scrut.fst.fst.snd;
  uint64_t st01 = scrut.fst.fst.fst;
  __uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t_uint64_t
  scrut0 = sub_bytes64x8(st01, st11, st21, st31, st41, st51, st61, st71);
  uint64_t st02 = scrut0.fst;
  uint64_t st12 = scrut0.snd;
  uint64_t st22 = scrut0.thd;
  uint64_t st32 = scrut0.f3;
  uint64_t st42 = scrut0.f4;
  uint64_t st52 = scrut0.f5;
  uint64_t st62 = scrut0.f6;
  uint64_t st72 = scrut0.f7;
  Lib_Transposition64x8_uint64x8
  scrut1 =
    Lib_Transposition64x8_transpose_bits64x8_inv((
        (Lib_Transposition64x8_uint64x8){
          .fst = { .fst = { .fst = st02, .snd = st12 }, .snd = { .fst = st22, .snd = st32 } },
          .snd = { .fst = { .fst = st42, .snd = st52 }, .snd = { .fst = st62, .snd = st72 } }
        }
      ));
  uint64_t st73 = scrut1.snd.snd.snd;
  uint64_t st63 = scrut1.snd.snd.fst;
  uint64_t st53 = scrut1.snd.fst.snd;
  uint64_t st43 = scrut1.snd.fst.fst;
  uint64_t st33 = scrut1.fst.snd.snd;
  uint64_t st23 = scrut1.fst.snd.fst;
  uint64_t st13 = scrut1.fst.fst.snd;
  uint64_t st03 = scrut1.fst.fst.fst;
  st[0U] = st03;
  st[1U] = st13;
  st[2U] = st23;
  st[3U] = st33;
  st[4U] = st43;
  st[5U] = st53;
  st[6U] = st63;
  st[7U] = st73;
}

/* SNIPPET_END: sub_bytes_state */

/* SNIPPET_START: shift_rows_state */

static void shift_rows_state(uint64_t *st)
{
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t rowi = st[i];
    st[i] =
      ((((((rowi & (uint64_t)0x1111111111111111U)
      | (rowi & (uint64_t)0x2220222022202220U) >> (uint32_t)4U)
      | (rowi & (uint64_t)0x0002000200020002U) << (uint32_t)12U)
      | (rowi & (uint64_t)0x4400440044004400U) >> (uint32_t)8U)
      | (rowi & (uint64_t)0x0044004400440044U) << (uint32_t)8U)
      | (rowi & (uint64_t)0x8000800080008000U) >> (uint32_t)12U)
      | (rowi & (uint64_t)0x0888088808880888U) << (uint32_t)4U;);
}

/* SNIPPET_END: shift_rows_state */

/* SNIPPET_START: mix_columns_state */

static void mix_columns_state(uint64_t *st)
{
  uint64_t col[8U] = { 0U };
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t coli = st[i];
    col[i] =
      coli
      ^
        ((coli & (uint64_t)0xeeeeeeeeeeeeeeeeU)
        >> (uint32_t)1U
        | (coli & (uint64_t)0x1111111111111111U) << (uint32_t)3U););
  uint64_t col0 = col[0U];
  uint64_t
  ncol0 =
    col0
    ^
      ((col0 & (uint64_t)0xccccccccccccccccU)
      >> (uint32_t)2U
      | (col0 & (uint64_t)0x3333333333333333U) << (uint32_t)2U);
  st[0U] = st[0U] ^ ncol0;
  KRML_MAYBE_FOR7(i,
    (uint32_t)0U,
    (uint32_t)7U,
    (uint32_t)1U,
    uint64_t prev = col[i];
    uint64_t next = col[i + (uint32_t)1U];
    uint64_t
    ncoli =
      next
      ^
        ((next & (uint64_t)0xccccccccccccccccU)
        >> (uint32_t)2U
        | (next & (uint64_t)0x3333333333333333U) << (uint32_t)2U);
    st[i + (uint32_t)1U] = st[i + (uint32_t)1U] ^ (ncoli ^ prev););
  st[0U] = st[0U] ^ col[7U];
  st[1U] = st[1U] ^ col[7U];
  st[3U] = st[3U] ^ col[7U];
  st[4U] = st[4U] ^ col[7U];
}

/* SNIPPET_END: mix_columns_state */

/* SNIPPET_START: Hacl_Impl_AES_CoreBitSlice_aes_enc */

void Hacl_Impl_AES_CoreBitSlice_aes_enc(uint64_t *st, uint64_t *key)
{
  sub_bytes_state(st);
  shift_rows_state(st);
  mix_columns_state(st);
  Hacl_Impl_AES_CoreBitSlice_xor_state_key1(st, key);
}

/* SNIPPET_END: Hacl_Impl_AES_CoreBitSlice_aes_enc */

/* SNIPPET_START: Hacl_Impl_AES_CoreBitSlice_aes_enc_last */

void Hacl_Impl_AES_CoreBitSlice_aes_enc_last(uint64_t *st, uint64_t *key)
{
  sub_bytes_state(st);
  shift_rows_state(st);
  Hacl_Impl_AES_CoreBitSlice_xor_state_key1(st, key);
}

/* SNIPPET_END: Hacl_Impl_AES_CoreBitSlice_aes_enc_last */

/* SNIPPET_START: Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist */

void
Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(uint64_t *next, uint64_t *prev, uint8_t rcon1)
{
  memcpy(next, prev, (uint32_t)8U * sizeof (uint64_t));
  sub_bytes_state(next);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t u3 = next[i] & (uint64_t)0xf000f000f000f000U;
    uint64_t n = u3 >> (uint32_t)12U;
    uint64_t n1 = (n >> (uint32_t)1U | n << (uint32_t)3U) & (uint64_t)0x000f000f000f000fU;
    uint64_t ri = (uint64_t)(rcon1 >> i & (uint8_t)1U);
    uint64_t ri1 = ri ^ ri << (uint32_t)16U;
    uint64_t ri2 = ri1 ^ ri1 << (uint32_t)32U;
    uint64_t n2 = n1 ^ ri2;
    uint64_t n3 = n2 << (uint32_t)12U;
    next[i] = n3 ^ u3 >> (uint32_t)4U;);
}

/* SNIPPET_END: Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist */

/* SNIPPET_START: Hacl_Impl_AES_CoreBitSlice_key_expansion_step */

void Hacl_Impl_AES_CoreBitSlice_key_expansion_step(uint64_t *next, uint64_t *prev)
{
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t p = prev[i];
    uint64_t n = next[i];
    uint64_t
    p1 =
      p
      ^
        ((p & (uint64_t)0x0fff0fff0fff0fffU)
        << (uint32_t)4U
        ^
          ((p & (uint64_t)0x00ff00ff00ff00ffU)
          << (uint32_t)8U
          ^ (p & (uint64_t)0x000f000f000f000fU) << (uint32_t)12U));
    next[i] = n ^ p1;);
}

/* SNIPPET_END: Hacl_Impl_AES_CoreBitSlice_key_expansion_step */

/* SNIPPET_START: Hacl_Impl_AES_Generic_aes128_ctr_bitslice */

void
Hacl_Impl_AES_Generic_aes128_ctr_bitslice(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint64_t *ctx,
  uint32_t counter
)
{
  uint32_t blocks64 = len / (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < blocks64; i++)
  {
    uint32_t ctr = counter + i * (uint32_t)4U;
    uint8_t *ib = inp + i * (uint32_t)64U;
    uint8_t *ob = out + i * (uint32_t)64U;
    uint64_t st[8U] = { 0U };
    uint64_t *kex = ctx + (uint32_t)8U;
    uint64_t *n = ctx;
    Hacl_Impl_AES_CoreBitSlice_load_state(st, n, ctr);
    uint32_t klen = (uint32_t)8U;
    uint64_t *k0 = kex;
    uint64_t *kr = kex + klen;
    uint64_t *kn = kex + (uint32_t)10U * klen;
    Hacl_Impl_AES_CoreBitSlice_xor_state_key1(st, k0);
    KRML_MAYBE_FOR9(i0,
      (uint32_t)0U,
      (uint32_t)9U,
      (uint32_t)1U,
      uint64_t *sub_key = kr + i0 * (uint32_t)8U;
      Hacl_Impl_AES_CoreBitSlice_aes_enc(st, sub_key););
    Hacl_Impl_AES_CoreBitSlice_aes_enc_last(st, kn);
    xor_block(ob, st, ib);
  }
  uint32_t rem = len % (uint32_t)64U;
  uint8_t last[64U] = { 0U };
  if (rem > (uint32_t)0U)
  {
    uint32_t ctr = counter + blocks64 * (uint32_t)4U;
    uint8_t *ib = inp + blocks64 * (uint32_t)64U;
    uint8_t *ob = out + blocks64 * (uint32_t)64U;
    memcpy(last, ib, rem * sizeof (uint8_t));
    uint64_t st[8U] = { 0U };
    uint64_t *kex = ctx + (uint32_t)8U;
    uint64_t *n = ctx;
    Hacl_Impl_AES_CoreBitSlice_load_state(st, n, ctr);
    uint32_t klen = (uint32_t)8U;
    uint64_t *k0 = kex;
    uint64_t *kr = kex + klen;
    uint64_t *kn = kex + (uint32_t)10U * klen;
    Hacl_Impl_AES_CoreBitSlice_xor_state_key1(st, k0);
    KRML_MAYBE_FOR9(i,
      (uint32_t)0U,
      (uint32_t)9U,
      (uint32_t)1U,
      uint64_t *sub_key = kr + i * (uint32_t)8U;
      Hacl_Impl_AES_CoreBitSlice_aes_enc(st, sub_key););
    Hacl_Impl_AES_CoreBitSlice_aes_enc_last(st, kn);
    xor_block(last, st, last);
    memcpy(ob, last, rem * sizeof (uint8_t));
  }
}

/* SNIPPET_END: Hacl_Impl_AES_Generic_aes128_ctr_bitslice */

/* SNIPPET_START: Hacl_Impl_AES_Generic_aes256_ctr_bitslice */

void
Hacl_Impl_AES_Generic_aes256_ctr_bitslice(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint64_t *ctx,
  uint32_t counter
)
{
  uint32_t blocks64 = len / (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < blocks64; i++)
  {
    uint32_t ctr = counter + i * (uint32_t)4U;
    uint8_t *ib = inp + i * (uint32_t)64U;
    uint8_t *ob = out + i * (uint32_t)64U;
    uint64_t st[8U] = { 0U };
    uint64_t *kex = ctx + (uint32_t)8U;
    uint64_t *n = ctx;
    Hacl_Impl_AES_CoreBitSlice_load_state(st, n, ctr);
    uint32_t klen = (uint32_t)8U;
    uint64_t *k0 = kex;
    uint64_t *kr = kex + klen;
    uint64_t *kn = kex + (uint32_t)14U * klen;
    Hacl_Impl_AES_CoreBitSlice_xor_state_key1(st, k0);
    KRML_MAYBE_FOR13(i0,
      (uint32_t)0U,
      (uint32_t)13U,
      (uint32_t)1U,
      uint64_t *sub_key = kr + i0 * (uint32_t)8U;
      Hacl_Impl_AES_CoreBitSlice_aes_enc(st, sub_key););
    Hacl_Impl_AES_CoreBitSlice_aes_enc_last(st, kn);
    xor_block(ob, st, ib);
  }
  uint32_t rem = len % (uint32_t)64U;
  uint8_t last[64U] = { 0U };
  if (rem > (uint32_t)0U)
  {
    uint32_t ctr = counter + blocks64 * (uint32_t)4U;
    uint8_t *ib = inp + blocks64 * (uint32_t)64U;
    uint8_t *ob = out + blocks64 * (uint32_t)64U;
    memcpy(last, ib, rem * sizeof (uint8_t));
    uint64_t st[8U] = { 0U };
    uint64_t *kex = ctx + (uint32_t)8U;
    uint64_t *n = ctx;
    Hacl_Impl_AES_CoreBitSlice_load_state(st, n, ctr);
    uint32_t klen = (uint32_t)8U;
    uint64_t *k0 = kex;
    uint64_t *kr = kex + klen;
    uint64_t *kn = kex + (uint32_t)14U * klen;
    Hacl_Impl_AES_CoreBitSlice_xor_state_key1(st, k0);
    KRML_MAYBE_FOR13(i,
      (uint32_t)0U,
      (uint32_t)13U,
      (uint32_t)1U,
      uint64_t *sub_key = kr + i * (uint32_t)8U;
      Hacl_Impl_AES_CoreBitSlice_aes_enc(st, sub_key););
    Hacl_Impl_AES_CoreBitSlice_aes_enc_last(st, kn);
    xor_block(last, st, last);
    memcpy(ob, last, rem * sizeof (uint8_t));
  }
}

/* SNIPPET_END: Hacl_Impl_AES_Generic_aes256_ctr_bitslice */

/* SNIPPET_START: Hacl_AES_128_BitSlice_aes128_init */

void Hacl_AES_128_BitSlice_aes128_init(uint64_t *ctx, uint8_t *key, uint8_t *nonce)
{
  uint64_t *kex = ctx + (uint32_t)8U;
  uint64_t *n = ctx;
  uint32_t klen = (uint32_t)8U;
  Hacl_Impl_AES_CoreBitSlice_load_key1(kex, key);
  uint64_t *prev = kex;
  uint64_t *next = kex + klen;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next, prev, (uint8_t)0x01U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next, prev);
  uint64_t *prev1 = kex + klen;
  uint64_t *next1 = kex + (uint32_t)2U * klen;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next1, prev1, (uint8_t)0x02U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next1[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next1[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next1, prev1);
  uint64_t *prev2 = kex + klen * (uint32_t)2U;
  uint64_t *next2 = kex + klen * (uint32_t)3U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next2, prev2, (uint8_t)0x04U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next2[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next2[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next2, prev2);
  uint64_t *prev3 = kex + klen * (uint32_t)3U;
  uint64_t *next3 = kex + klen * (uint32_t)4U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next3, prev3, (uint8_t)0x08U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next3[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next3[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next3, prev3);
  uint64_t *prev4 = kex + klen * (uint32_t)4U;
  uint64_t *next4 = kex + klen * (uint32_t)5U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next4, prev4, (uint8_t)0x10U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next4[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next4[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next4, prev4);
  uint64_t *prev5 = kex + klen * (uint32_t)5U;
  uint64_t *next5 = kex + klen * (uint32_t)6U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next5, prev5, (uint8_t)0x20U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next5[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next5[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next5, prev5);
  uint64_t *prev6 = kex + klen * (uint32_t)6U;
  uint64_t *next6 = kex + klen * (uint32_t)7U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next6, prev6, (uint8_t)0x40U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next6[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next6[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next6, prev6);
  uint64_t *prev7 = kex + klen * (uint32_t)7U;
  uint64_t *next7 = kex + klen * (uint32_t)8U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next7, prev7, (uint8_t)0x80U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next7[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next7[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next7, prev7);
  uint64_t *prev8 = kex + klen * (uint32_t)8U;
  uint64_t *next8 = kex + klen * (uint32_t)9U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next8, prev8, (uint8_t)0x1bU);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next8[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next8[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next8, prev8);
  uint64_t *prev9 = kex + klen * (uint32_t)9U;
  uint64_t *next9 = kex + klen * (uint32_t)10U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next9, prev9, (uint8_t)0x36U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n1 = next9[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next9[i] = n4;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next9, prev9);
  Hacl_Impl_AES_CoreBitSlice_load_nonce(n, nonce);
}

/* SNIPPET_END: Hacl_AES_128_BitSlice_aes128_init */

/* SNIPPET_START: Hacl_AES_128_BitSlice_aes128_set_nonce */

void Hacl_AES_128_BitSlice_aes128_set_nonce(uint64_t *ctx, uint8_t *nonce)
{
  uint64_t *n = ctx;
  Hacl_Impl_AES_CoreBitSlice_load_nonce(n, nonce);
}

/* SNIPPET_END: Hacl_AES_128_BitSlice_aes128_set_nonce */

/* SNIPPET_START: Hacl_AES_128_BitSlice_aes128_key_block */

void Hacl_AES_128_BitSlice_aes128_key_block(uint8_t *kb, uint64_t *ctx, uint32_t counter)
{
  uint64_t *kex = ctx + (uint32_t)8U;
  uint64_t *n = ctx;
  uint64_t st[8U] = { 0U };
  Hacl_Impl_AES_CoreBitSlice_load_state(st, n, counter);
  uint32_t klen = (uint32_t)8U;
  uint64_t *k0 = kex;
  uint64_t *kr = kex + klen;
  uint64_t *kn = kex + (uint32_t)10U * klen;
  Hacl_Impl_AES_CoreBitSlice_xor_state_key1(st, k0);
  KRML_MAYBE_FOR9(i,
    (uint32_t)0U,
    (uint32_t)9U,
    (uint32_t)1U,
    uint64_t *sub_key = kr + i * (uint32_t)8U;
    Hacl_Impl_AES_CoreBitSlice_aes_enc(st, sub_key););
  Hacl_Impl_AES_CoreBitSlice_aes_enc_last(st, kn);
  Hacl_Impl_AES_CoreBitSlice_store_block0(kb, st);
}

/* SNIPPET_END: Hacl_AES_128_BitSlice_aes128_key_block */

/* SNIPPET_START: Hacl_AES_128_BitSlice_aes128_ctr_encrypt */

inline void
Hacl_AES_128_BitSlice_aes128_ctr_encrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  uint64_t ctx[96U] = { 0U };
  uint64_t *kex = ctx + (uint32_t)8U;
  uint64_t *n1 = ctx;
  uint32_t klen = (uint32_t)8U;
  Hacl_Impl_AES_CoreBitSlice_load_key1(kex, k);
  uint64_t *prev = kex;
  uint64_t *next = kex + klen;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next, prev, (uint8_t)0x01U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next, prev);
  uint64_t *prev1 = kex + klen;
  uint64_t *next1 = kex + (uint32_t)2U * klen;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next1, prev1, (uint8_t)0x02U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next1[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next1[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next1, prev1);
  uint64_t *prev2 = kex + klen * (uint32_t)2U;
  uint64_t *next2 = kex + klen * (uint32_t)3U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next2, prev2, (uint8_t)0x04U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next2[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next2[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next2, prev2);
  uint64_t *prev3 = kex + klen * (uint32_t)3U;
  uint64_t *next3 = kex + klen * (uint32_t)4U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next3, prev3, (uint8_t)0x08U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next3[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next3[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next3, prev3);
  uint64_t *prev4 = kex + klen * (uint32_t)4U;
  uint64_t *next4 = kex + klen * (uint32_t)5U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next4, prev4, (uint8_t)0x10U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next4[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next4[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next4, prev4);
  uint64_t *prev5 = kex + klen * (uint32_t)5U;
  uint64_t *next5 = kex + klen * (uint32_t)6U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next5, prev5, (uint8_t)0x20U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next5[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next5[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next5, prev5);
  uint64_t *prev6 = kex + klen * (uint32_t)6U;
  uint64_t *next6 = kex + klen * (uint32_t)7U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next6, prev6, (uint8_t)0x40U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next6[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next6[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next6, prev6);
  uint64_t *prev7 = kex + klen * (uint32_t)7U;
  uint64_t *next7 = kex + klen * (uint32_t)8U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next7, prev7, (uint8_t)0x80U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next7[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next7[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next7, prev7);
  uint64_t *prev8 = kex + klen * (uint32_t)8U;
  uint64_t *next8 = kex + klen * (uint32_t)9U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next8, prev8, (uint8_t)0x1bU);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next8[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next8[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next8, prev8);
  uint64_t *prev9 = kex + klen * (uint32_t)9U;
  uint64_t *next9 = kex + klen * (uint32_t)10U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next9, prev9, (uint8_t)0x36U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next9[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next9[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next9, prev9);
  Hacl_Impl_AES_CoreBitSlice_load_nonce(n1, n);
  Hacl_Impl_AES_Generic_aes128_ctr_bitslice(len, out, inp, ctx, c);
}

/* SNIPPET_END: Hacl_AES_128_BitSlice_aes128_ctr_encrypt */

/* SNIPPET_START: Hacl_AES_128_BitSlice_aes128_ctr_decrypt */

inline void
Hacl_AES_128_BitSlice_aes128_ctr_decrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  uint64_t ctx[96U] = { 0U };
  uint64_t *kex = ctx + (uint32_t)8U;
  uint64_t *n1 = ctx;
  uint32_t klen = (uint32_t)8U;
  Hacl_Impl_AES_CoreBitSlice_load_key1(kex, k);
  uint64_t *prev = kex;
  uint64_t *next = kex + klen;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next, prev, (uint8_t)0x01U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next, prev);
  uint64_t *prev1 = kex + klen;
  uint64_t *next1 = kex + (uint32_t)2U * klen;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next1, prev1, (uint8_t)0x02U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next1[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next1[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next1, prev1);
  uint64_t *prev2 = kex + klen * (uint32_t)2U;
  uint64_t *next2 = kex + klen * (uint32_t)3U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next2, prev2, (uint8_t)0x04U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next2[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next2[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next2, prev2);
  uint64_t *prev3 = kex + klen * (uint32_t)3U;
  uint64_t *next3 = kex + klen * (uint32_t)4U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next3, prev3, (uint8_t)0x08U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next3[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next3[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next3, prev3);
  uint64_t *prev4 = kex + klen * (uint32_t)4U;
  uint64_t *next4 = kex + klen * (uint32_t)5U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next4, prev4, (uint8_t)0x10U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next4[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next4[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next4, prev4);
  uint64_t *prev5 = kex + klen * (uint32_t)5U;
  uint64_t *next5 = kex + klen * (uint32_t)6U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next5, prev5, (uint8_t)0x20U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next5[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next5[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next5, prev5);
  uint64_t *prev6 = kex + klen * (uint32_t)6U;
  uint64_t *next6 = kex + klen * (uint32_t)7U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next6, prev6, (uint8_t)0x40U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next6[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next6[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next6, prev6);
  uint64_t *prev7 = kex + klen * (uint32_t)7U;
  uint64_t *next7 = kex + klen * (uint32_t)8U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next7, prev7, (uint8_t)0x80U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next7[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next7[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next7, prev7);
  uint64_t *prev8 = kex + klen * (uint32_t)8U;
  uint64_t *next8 = kex + klen * (uint32_t)9U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next8, prev8, (uint8_t)0x1bU);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next8[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next8[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next8, prev8);
  uint64_t *prev9 = kex + klen * (uint32_t)9U;
  uint64_t *next9 = kex + klen * (uint32_t)10U;
  Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(next9, prev9, (uint8_t)0x36U);
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t n2 = next9[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next9[i] = n5;);
  Hacl_Impl_AES_CoreBitSlice_key_expansion_step(next9, prev9);
  Hacl_Impl_AES_CoreBitSlice_load_nonce(n1, n);
  Hacl_Impl_AES_Generic_aes128_ctr_bitslice(len, out, inp, ctx, c);
}

/* SNIPPET_END: Hacl_AES_128_BitSlice_aes128_ctr_decrypt */

