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


#include "Hacl_Impl_Sparkle1.h"

uint32_t Hacl_Impl_Sparkle1_vsize_rcon = (uint32_t)8U;

const
uint32_t
Hacl_Impl_Sparkle1_rcon[8U] =
  {
    (uint32_t)0xB7E15162U, (uint32_t)0xBF715880U, (uint32_t)0x38B4DA56U, (uint32_t)0x324E7738U,
    (uint32_t)0xBB1185EBU, (uint32_t)0x4F7C7B57U, (uint32_t)0xCFBFA1C8U, (uint32_t)0xC2B3293DU
  };

Spec_SPARKLE2_branch1 Hacl_Impl_Sparkle1_xor(uint32_t l, uint32_t *b)
{
  uint32_t tx = (uint32_t)0U;
  uint32_t ty = (uint32_t)0U;
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint32_t xi = b[(uint32_t)2U * i];
    uint32_t yi = b[(uint32_t)2U * i + (uint32_t)1U];
    uint32_t tx_0 = tx;
    uint32_t ty_0 = ty;
    tx = xi ^ tx_0;
    ty = yi ^ ty_0;
  }
  uint32_t r0 = tx;
  uint32_t r1 = ty;
  return ((Spec_SPARKLE2_branch1){ .fst = r0, .snd = r1 });
}

void
Hacl_Impl_Sparkle1_xor_x(uint32_t n, uint32_t *b, uint32_t lty, uint32_t ltx, uint32_t *temp)
{
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    uint32_t xi = b[(uint32_t)2U * i];
    uint32_t yi = b[(uint32_t)2U * i + (uint32_t)1U];
    uint32_t xi_n = xi ^ lty;
    uint32_t yi_n = yi ^ ltx;
    temp[(uint32_t)2U * i] = xi_n;
    temp[(uint32_t)2U * i + (uint32_t)1U] = yi_n;
  }
}

void Hacl_Impl_Sparkle1_m(uint32_t n, uint32_t *b, uint32_t *temp)
{
  uint32_t tx = (uint32_t)0U;
  uint32_t ty = (uint32_t)0U;
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    uint32_t xi = b[(uint32_t)2U * i];
    uint32_t yi = b[(uint32_t)2U * i + (uint32_t)1U];
    uint32_t tx_0 = tx;
    uint32_t ty_0 = ty;
    tx = xi ^ tx_0;
    ty = yi ^ ty_0;
  }
  uint32_t r0 = tx;
  uint32_t r1 = ty;
  Spec_SPARKLE2_branch1 scrut = { .fst = r0, .snd = r1 };
  uint32_t ltx = scrut.fst;
  uint32_t lty = scrut.snd;
  Hacl_Impl_Sparkle1_xor_x(n,
    b,
    (lty << (uint32_t)16U | lty >> (uint32_t)16U) ^ (lty & (uint32_t)0xffffU),
    (ltx << (uint32_t)16U | ltx >> (uint32_t)16U) ^ (ltx & (uint32_t)0xffffU),
    temp);
}

void Hacl_Impl_Sparkle1_l_step(uint32_t n, uint32_t *right, uint32_t i, uint32_t *m1)
{
  uint32_t xi = right[(uint32_t)2U * i];
  uint32_t yi = right[(uint32_t)2U * i + (uint32_t)1U];
  uint32_t p0i = m1[(uint32_t)2U * i];
  uint32_t p1i = m1[(uint32_t)2U * i + (uint32_t)1U];
  Spec_SPARKLE2_branch1 branchIUpd = { .fst = p0i ^ xi, .snd = p1i ^ yi };
  uint32_t x = branchIUpd.fst;
  uint32_t y = branchIUpd.snd;
  m1[(uint32_t)2U * i] = x;
  m1[(uint32_t)2U * i + (uint32_t)1U] = y;
}

void Hacl_Impl_Sparkle1_l(uint32_t n, uint32_t *b)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), n);
  uint32_t result[n];
  memset(result, 0U, n * sizeof (uint32_t));
  uint32_t *left = b;
  uint32_t *right = b + n;
  Hacl_Impl_Sparkle1_m(n >> (uint32_t)1U, left, result);
  for (uint32_t i = (uint32_t)0U; i < n >> (uint32_t)1U; i++)
  {
    uint32_t xi = right[(uint32_t)2U * i];
    uint32_t yi = right[(uint32_t)2U * i + (uint32_t)1U];
    uint32_t p0i = result[(uint32_t)2U * i];
    uint32_t p1i = result[(uint32_t)2U * i + (uint32_t)1U];
    Spec_SPARKLE2_branch1 branchIUpd = { .fst = p0i ^ xi, .snd = p1i ^ yi };
    uint32_t x = branchIUpd.fst;
    uint32_t y = branchIUpd.snd;
    result[(uint32_t)2U * i] = x;
    result[(uint32_t)2U * i + (uint32_t)1U] = y;
  }
  for (uint32_t i = (uint32_t)0U; i < n >> (uint32_t)1U; i++)
  {
    Spec_SPARKLE2_branch1
    left_i = { .fst = left[(uint32_t)2U * i], .snd = left[(uint32_t)2U * i + (uint32_t)1U] };
    uint32_t x = left_i.fst;
    uint32_t y = left_i.snd;
    right[(uint32_t)2U * i] = x;
    right[(uint32_t)2U * i + (uint32_t)1U] = y;
  }
  for (uint32_t i = (uint32_t)0U; i < n >> (uint32_t)1U; i++)
  {
    uint32_t index = i - (uint32_t)1U;
    uint32_t k = n >> (uint32_t)1U;
    uint32_t j = index % k;
    uint32_t x = result[(uint32_t)2U * i];
    uint32_t y = result[(uint32_t)2U * i + (uint32_t)1U];
    left[(uint32_t)2U * j] = x;
    left[(uint32_t)2U * j + (uint32_t)1U] = y;
  }
}

void Hacl_Impl_Sparkle1_add2(uint32_t n, uint32_t i, uint32_t *b)
{
  uint32_t x0 = b[0U];
  uint32_t y0 = b[1U];
  uint32_t x1 = b[2U];
  uint32_t y1 = b[3U];
  uint32_t i0 = i & (uint32_t)7U;
  uint32_t y01 = y0 ^ Hacl_Impl_Sparkle1_rcon[i0];
  uint32_t y11 = y1 ^ i;
  b[0U] = x0;
  b[1U] = y01;
  b[2U] = x1;
  b[3U] = y11;
}

void Hacl_Impl_Sparkle1_toBranch(uint32_t n, uint8_t *i, uint32_t *o)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)2U * n; i0++)
  {
    uint32_t *os = o;
    uint8_t *bj = i + i0 * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i0] = x;
  }
}

void Hacl_Impl_Sparkle1_fromBranch(uint32_t n, uint32_t *i, uint8_t *o)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)2U * n; i0++)
  {
    store32_le(o + i0 * (uint32_t)4U, i[i0]);
  }
}

void Hacl_Impl_Sparkle1_arx_n_step(uint32_t n, uint32_t i, uint32_t *b)
{
  Spec_SPARKLE2_branch1
  branchI = { .fst = b[(uint32_t)2U * i], .snd = b[(uint32_t)2U * i + (uint32_t)1U] };
  uint32_t rcon_i = Hacl_Impl_Sparkle1_rcon[i];
  uint32_t x0 = branchI.fst;
  uint32_t y0 = branchI.snd;
  uint32_t x1 = x0 + (y0 >> (uint32_t)31U | y0 << (uint32_t)1U);
  uint32_t y1 = y0 ^ (x1 >> (uint32_t)24U | x1 << (uint32_t)8U);
  uint32_t x2 = x1 ^ rcon_i;
  uint32_t x3 = x2 + (y1 >> (uint32_t)17U | y1 << (uint32_t)15U);
  uint32_t y2 = y1 ^ (x3 >> (uint32_t)17U | x3 << (uint32_t)15U);
  uint32_t x4 = x3 ^ rcon_i;
  uint32_t x5 = x4 + y2;
  uint32_t y3 = y2 ^ (x5 >> (uint32_t)31U | x5 << (uint32_t)1U);
  uint32_t x6 = x5 ^ rcon_i;
  uint32_t x7 = x6 + (y3 >> (uint32_t)24U | y3 << (uint32_t)8U);
  uint32_t y4 = y3 ^ (x7 >> (uint32_t)16U | x7 << (uint32_t)16U);
  uint32_t x8 = x7 ^ rcon_i;
  Spec_SPARKLE2_branch1 scrut = { .fst = x8, .snd = y4 };
  uint32_t x = scrut.fst;
  uint32_t y = scrut.snd;
  b[(uint32_t)2U * i] = x;
  b[(uint32_t)2U * i + (uint32_t)1U] = y;
}

void Hacl_Impl_Sparkle1_sparkle256(uint32_t steps, uint8_t *i, uint8_t *o)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint32_t), len * (uint32_t)2U);
  uint32_t temp[len * (uint32_t)2U];
  memset(temp, 0U, len * (uint32_t)2U * sizeof (uint32_t));
  Hacl_Impl_Sparkle1_toBranch(len, i, temp);
  for (uint32_t i0 = (uint32_t)0U; i0 < steps; i0++)
  {
    Hacl_Impl_Sparkle1_add2(len, i0, temp);
    for (uint32_t i1 = (uint32_t)0U; i1 < len; i1++)
    {
      Hacl_Impl_Sparkle1_arx_n_step(len, i1, temp);
    }
    Hacl_Impl_Sparkle1_l(len, temp);
  }
  Hacl_Impl_Sparkle1_fromBranch(len, temp, o);
}

void Hacl_Impl_Sparkle1_sparkle384(uint32_t steps, uint8_t *i, uint8_t *o)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint32_t), len * (uint32_t)2U);
  uint32_t temp[len * (uint32_t)2U];
  memset(temp, 0U, len * (uint32_t)2U * sizeof (uint32_t));
  Hacl_Impl_Sparkle1_toBranch(len, i, temp);
  for (uint32_t i0 = (uint32_t)0U; i0 < steps; i0++)
  {
    Hacl_Impl_Sparkle1_add2(len, i0, temp);
    for (uint32_t i1 = (uint32_t)0U; i1 < len; i1++)
    {
      Hacl_Impl_Sparkle1_arx_n_step(len, i1, temp);
    }
    Hacl_Impl_Sparkle1_l(len, temp);
  }
  Hacl_Impl_Sparkle1_fromBranch(len, temp, o);
}

void Hacl_Impl_Sparkle1_sparkle512(uint32_t steps, uint8_t *i, uint8_t *o)
{
  uint32_t len = (uint32_t)8U;
  KRML_CHECK_SIZE(sizeof (uint32_t), len * (uint32_t)2U);
  uint32_t temp[len * (uint32_t)2U];
  memset(temp, 0U, len * (uint32_t)2U * sizeof (uint32_t));
  Hacl_Impl_Sparkle1_toBranch(len, i, temp);
  for (uint32_t i0 = (uint32_t)0U; i0 < steps; i0++)
  {
    Hacl_Impl_Sparkle1_add2(len, i0, temp);
    for (uint32_t i1 = (uint32_t)0U; i1 < len; i1++)
    {
      Hacl_Impl_Sparkle1_arx_n_step(len, i1, temp);
    }
    Hacl_Impl_Sparkle1_l(len, temp);
  }
  Hacl_Impl_Sparkle1_fromBranch(len, temp, o);
}

