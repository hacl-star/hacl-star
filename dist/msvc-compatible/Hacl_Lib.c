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


#include "internal/Hacl_Lib.h"

static Lib_Transposition64x8_uint64x2 transpose_aux_aux32(uint64_t a, uint64_t b)
{
  uint64_t m = (uint64_t)18446744069414584320U;
  return
    (
      (Lib_Transposition64x8_uint64x2){
        .fst = (a & ~m) ^ (b << (uint32_t)32U & m),
        .snd = (a >> (uint32_t)32U & ~m) ^ (b & m)
      }
    );
}

static Lib_Transposition64x8_uint64x2 transpose_aux_aux16(uint64_t a, uint64_t b)
{
  uint64_t m = (uint64_t)18446462603027742720U;
  return
    (
      (Lib_Transposition64x8_uint64x2){
        .fst = (a & ~m) ^ (b << (uint32_t)16U & m),
        .snd = (a >> (uint32_t)16U & ~m) ^ (b & m)
      }
    );
}

static Lib_Transposition64x8_uint64x2 transpose_aux_aux8(uint64_t a, uint64_t b)
{
  uint64_t m = (uint64_t)18374966859414961920U;
  return
    (
      (Lib_Transposition64x8_uint64x2){
        .fst = (a & ~m) ^ (b << (uint32_t)8U & m),
        .snd = (a >> (uint32_t)8U & ~m) ^ (b & m)
      }
    );
}

static Lib_Transposition64x8_uint64x8 transpose_aux32(Lib_Transposition64x8_uint64x8 x)
{
  uint64_t x7 = x.snd.snd.snd;
  uint64_t x6 = x.snd.snd.fst;
  uint64_t x5 = x.snd.fst.snd;
  uint64_t x4 = x.snd.fst.fst;
  uint64_t x3 = x.fst.snd.snd;
  uint64_t x2 = x.fst.snd.fst;
  uint64_t x1 = x.fst.fst.snd;
  uint64_t x0 = x.fst.fst.fst;
  Lib_Transposition64x8_uint64x2 scrut0 = transpose_aux_aux32(x0, x4);
  uint64_t y0 = scrut0.fst;
  uint64_t y4 = scrut0.snd;
  Lib_Transposition64x8_uint64x2 scrut1 = transpose_aux_aux32(x1, x5);
  uint64_t y1 = scrut1.fst;
  uint64_t y5 = scrut1.snd;
  Lib_Transposition64x8_uint64x2 scrut2 = transpose_aux_aux32(x2, x6);
  uint64_t y2 = scrut2.fst;
  uint64_t y6 = scrut2.snd;
  Lib_Transposition64x8_uint64x2 scrut = transpose_aux_aux32(x3, x7);
  uint64_t y3 = scrut.fst;
  uint64_t y7 = scrut.snd;
  return
    (
      (Lib_Transposition64x8_uint64x8){
        .fst = { .fst = { .fst = y0, .snd = y1 }, .snd = { .fst = y2, .snd = y3 } },
        .snd = { .fst = { .fst = y4, .snd = y5 }, .snd = { .fst = y6, .snd = y7 } }
      }
    );
}

static Lib_Transposition64x8_uint64x4 transpose_aux16(Lib_Transposition64x8_uint64x4 x)
{
  uint64_t x3 = x.snd.snd;
  uint64_t x2 = x.snd.fst;
  uint64_t x1 = x.fst.snd;
  uint64_t x0 = x.fst.fst;
  Lib_Transposition64x8_uint64x2 scrut0 = transpose_aux_aux16(x0, x2);
  uint64_t y0 = scrut0.fst;
  uint64_t y2 = scrut0.snd;
  Lib_Transposition64x8_uint64x2 scrut = transpose_aux_aux16(x1, x3);
  uint64_t y1 = scrut.fst;
  uint64_t y3 = scrut.snd;
  return
    (
      (Lib_Transposition64x8_uint64x4){
        .fst = { .fst = y0, .snd = y1 },
        .snd = { .fst = y2, .snd = y3 }
      }
    );
}

static Lib_Transposition64x8_uint64x2 transpose_aux8(Lib_Transposition64x8_uint64x2 x)
{
  uint64_t x0 = x.fst;
  uint64_t x1 = x.snd;
  Lib_Transposition64x8_uint64x2 scrut = transpose_aux_aux8(x0, x1);
  uint64_t y0 = scrut.fst;
  uint64_t y1 = scrut.snd;
  return ((Lib_Transposition64x8_uint64x2){ .fst = y0, .snd = y1 });
}

uint64_t Lib_Transposition64x8_transpose_bits64(uint64_t x)
{
  uint64_t m0 = (uint64_t)0x8040201008040201U;
  uint64_t m1 = (uint64_t)0x4020100804020100U;
  uint64_t m2 = (uint64_t)0x2010080402010000U;
  uint64_t m3 = (uint64_t)0x1008040201000000U;
  uint64_t m4 = (uint64_t)0x0804020100000000U;
  uint64_t m5 = (uint64_t)0x0402010000000000U;
  uint64_t m6 = (uint64_t)0x0201000000000000U;
  uint64_t m7 = (uint64_t)0x0100000000000000U;
  uint64_t y0 = x & m0;
  uint64_t y1 = y0 | (x & m1) >> (uint32_t)7U;
  uint64_t y2 = y1 | (x & m2) >> (uint32_t)14U;
  uint64_t y3 = y2 | (x & m3) >> (uint32_t)21U;
  uint64_t y4 = y3 | (x & m4) >> (uint32_t)28U;
  uint64_t y5 = y4 | (x & m5) >> (uint32_t)35U;
  uint64_t y6 = y5 | (x & m6) >> (uint32_t)42U;
  uint64_t y7 = y6 | (x & m7) >> (uint32_t)49U;
  uint64_t y8 = y7 | (x << (uint32_t)7U & m1);
  uint64_t y9 = y8 | (x << (uint32_t)14U & m2);
  uint64_t y10 = y9 | (x << (uint32_t)21U & m3);
  uint64_t y11 = y10 | (x << (uint32_t)28U & m4);
  uint64_t y12 = y11 | (x << (uint32_t)35U & m5);
  uint64_t y13 = y12 | (x << (uint32_t)42U & m6);
  return y13 | (x << (uint32_t)49U & m7);
}

Lib_Transposition64x8_uint64x8
Lib_Transposition64x8_transpose_bits64x8(Lib_Transposition64x8_uint64x8 a)
{
  Lib_Transposition64x8_uint64x8 scrut0 = transpose_aux32(a);
  Lib_Transposition64x8_uint64x4 b0 = scrut0.fst;
  Lib_Transposition64x8_uint64x4 b1 = scrut0.snd;
  Lib_Transposition64x8_uint64x4 scrut1 = transpose_aux16(b0);
  Lib_Transposition64x8_uint64x2 c0 = scrut1.fst;
  Lib_Transposition64x8_uint64x2 c1 = scrut1.snd;
  Lib_Transposition64x8_uint64x4 scrut2 = transpose_aux16(b1);
  Lib_Transposition64x8_uint64x2 c2 = scrut2.fst;
  Lib_Transposition64x8_uint64x2 c3 = scrut2.snd;
  Lib_Transposition64x8_uint64x2 scrut3 = transpose_aux8(c0);
  uint64_t d0 = scrut3.fst;
  uint64_t d1 = scrut3.snd;
  Lib_Transposition64x8_uint64x2 scrut4 = transpose_aux8(c1);
  uint64_t d2 = scrut4.fst;
  uint64_t d3 = scrut4.snd;
  Lib_Transposition64x8_uint64x2 scrut5 = transpose_aux8(c2);
  uint64_t d4 = scrut5.fst;
  uint64_t d5 = scrut5.snd;
  Lib_Transposition64x8_uint64x2 scrut = transpose_aux8(c3);
  uint64_t d6 = scrut.fst;
  uint64_t d7 = scrut.snd;
  uint64_t e0 = Lib_Transposition64x8_transpose_bits64(d0);
  uint64_t e1 = Lib_Transposition64x8_transpose_bits64(d1);
  uint64_t e2 = Lib_Transposition64x8_transpose_bits64(d2);
  uint64_t e3 = Lib_Transposition64x8_transpose_bits64(d3);
  uint64_t e4 = Lib_Transposition64x8_transpose_bits64(d4);
  uint64_t e5 = Lib_Transposition64x8_transpose_bits64(d5);
  uint64_t e6 = Lib_Transposition64x8_transpose_bits64(d6);
  uint64_t e7 = Lib_Transposition64x8_transpose_bits64(d7);
  return
    (
      (Lib_Transposition64x8_uint64x8){
        .fst = { .fst = { .fst = e0, .snd = e1 }, .snd = { .fst = e2, .snd = e3 } },
        .snd = { .fst = { .fst = e4, .snd = e5 }, .snd = { .fst = e6, .snd = e7 } }
      }
    );
}

Lib_Transposition64x8_uint64x8
Lib_Transposition64x8_transpose_bits64x8_inv(Lib_Transposition64x8_uint64x8 a)
{
  uint64_t a7 = a.snd.snd.snd;
  uint64_t a6 = a.snd.snd.fst;
  uint64_t a5 = a.snd.fst.snd;
  uint64_t a4 = a.snd.fst.fst;
  uint64_t a3 = a.fst.snd.snd;
  uint64_t a2 = a.fst.snd.fst;
  uint64_t a1 = a.fst.fst.snd;
  uint64_t a0 = a.fst.fst.fst;
  uint64_t b0 = Lib_Transposition64x8_transpose_bits64(a0);
  uint64_t b1 = Lib_Transposition64x8_transpose_bits64(a1);
  uint64_t b2 = Lib_Transposition64x8_transpose_bits64(a2);
  uint64_t b3 = Lib_Transposition64x8_transpose_bits64(a3);
  uint64_t b4 = Lib_Transposition64x8_transpose_bits64(a4);
  uint64_t b5 = Lib_Transposition64x8_transpose_bits64(a5);
  uint64_t b6 = Lib_Transposition64x8_transpose_bits64(a6);
  uint64_t b7 = Lib_Transposition64x8_transpose_bits64(a7);
  Lib_Transposition64x8_uint64x2
  c0 = transpose_aux8(((Lib_Transposition64x8_uint64x2){ .fst = b0, .snd = b1 }));
  Lib_Transposition64x8_uint64x2
  c1 = transpose_aux8(((Lib_Transposition64x8_uint64x2){ .fst = b2, .snd = b3 }));
  Lib_Transposition64x8_uint64x2
  c2 = transpose_aux8(((Lib_Transposition64x8_uint64x2){ .fst = b4, .snd = b5 }));
  Lib_Transposition64x8_uint64x2
  c3 = transpose_aux8(((Lib_Transposition64x8_uint64x2){ .fst = b6, .snd = b7 }));
  Lib_Transposition64x8_uint64x4
  d0 = transpose_aux16(((Lib_Transposition64x8_uint64x4){ .fst = c0, .snd = c1 }));
  Lib_Transposition64x8_uint64x4
  d1 = transpose_aux16(((Lib_Transposition64x8_uint64x4){ .fst = c2, .snd = c3 }));
  Lib_Transposition64x8_uint64x8
  e = transpose_aux32(((Lib_Transposition64x8_uint64x8){ .fst = d0, .snd = d1 }));
  return e;
}

