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


#include "Hacl_Impl_Sparkle.h"

uint32_t Hacl_Impl_Sparkle_size_word = (uint32_t)4U;

uint32_t Hacl_Impl_Sparkle_vsize_rcon = (uint32_t)8U;

const
uint32_t
Hacl_Impl_Sparkle_rcon[8U] =
  {
    (uint32_t)0xB7E15162U, (uint32_t)0xBF715880U, (uint32_t)0x38B4DA56U, (uint32_t)0x324E7738U,
    (uint32_t)0xBB1185EBU, (uint32_t)0x4F7C7B57U, (uint32_t)0xCFBFA1C8U, (uint32_t)0xC2B3293DU
  };

void Hacl_Impl_Sparkle_arx(uint32_t c, uint32_t *b)
{
  uint32_t x = b[0U];
  uint32_t y = b[1U];
  uint32_t x1 = x + (y >> (uint32_t)31U | y << (uint32_t)1U);
  uint32_t y1 = y ^ (x1 >> (uint32_t)24U | x1 << (uint32_t)8U);
  uint32_t x2 = x1 ^ c;
  uint32_t x3 = x2 + (y1 >> (uint32_t)17U | y1 << (uint32_t)15U);
  uint32_t y2 = y1 ^ (x3 >> (uint32_t)17U | x3 << (uint32_t)15U);
  uint32_t x4 = x3 ^ c;
  uint32_t x5 = x4 + y2;
  uint32_t y3 = y2 ^ (x5 >> (uint32_t)31U | x5 << (uint32_t)1U);
  uint32_t x6 = x5 ^ c;
  uint32_t x7 = x6 + (y3 >> (uint32_t)24U | y3 << (uint32_t)8U);
  uint32_t y4 = y3 ^ (x7 >> (uint32_t)16U | x7 << (uint32_t)16U);
  uint32_t x8 = x7 ^ c;
  b[0U] = x8;
  b[1U] = y4;
}

void Hacl_Impl_Sparkle_xor(uint32_t l, uint32_t *b, uint32_t *tx, uint32_t *ty)
{
  for (uint32_t i = (uint32_t)0U; i < l >> (uint32_t)1U; i++)
  {
    uint32_t xi = b[(uint32_t)2U * i];
    uint32_t yi = b[(uint32_t)2U * i + (uint32_t)1U];
    uint32_t tx_0 = tx[0U];
    uint32_t ty_0 = ty[0U];
    tx[0U] = xi ^ tx_0;
    ty[0U] = yi ^ ty_0;
  }
}

void Hacl_Impl_Sparkle_xor_x(uint32_t n, uint32_t *b, uint32_t lty, uint32_t ltx)
{
  for (uint32_t i = (uint32_t)0U; i < n >> (uint32_t)1U; i++)
  {
    uint32_t xi = b[(uint32_t)2U * i];
    uint32_t yi = b[(uint32_t)2U * i + (uint32_t)1U];
    uint32_t xi_n = xi ^ lty;
    uint32_t yi_n = yi ^ ltx;
    b[(uint32_t)2U * (i + n)] = xi_n;
    b[(uint32_t)2U * (i + n) + (uint32_t)1U] = yi_n;
  }
}

typedef struct branch1_s
{
  uint32_t fst;
  uint32_t snd;
}
branch1;

void Hacl_Impl_Sparkle_l_step(uint32_t n, uint32_t *perm, uint32_t i, uint32_t *result)
{
  uint32_t xi = result[(uint32_t)2U * i];
  uint32_t yi = result[(uint32_t)2U * i + (uint32_t)1U];
  uint32_t p0i = perm[(uint32_t)2U * i];
  uint32_t p1i = perm[(uint32_t)2U * i + (uint32_t)1U];
  branch1 branchIUpd = { .fst = xi ^ p0i, .snd = yi ^ p1i };
  uint32_t x = branchIUpd.fst;
  uint32_t y = branchIUpd.snd;
  perm[(uint32_t)2U * i] = x;
  perm[(uint32_t)2U * i + (uint32_t)1U] = y;
}

void Hacl_Impl_Sparkle_l(uint32_t n, uint32_t *b)
{
  uint32_t *leftBranch = b;
  uint32_t *rightBranch = b + n;
  uint32_t *result = b + (uint32_t)2U * n;
  uint32_t tx = (uint32_t)0U;
  uint32_t ty = (uint32_t)0U;
  Hacl_Impl_Sparkle_xor(n, b, &tx, &ty);
  uint32_t uu____0 = tx;
  uint32_t
  ltx = (uu____0 << (uint32_t)16U | uu____0 >> (uint32_t)16U) ^ (uu____0 & (uint32_t)0xffffU);
  uint32_t uu____1 = ty;
  uint32_t
  lty = (uu____1 << (uint32_t)16U | uu____1 >> (uint32_t)16U) ^ (uu____1 & (uint32_t)0xffffU);
  Hacl_Impl_Sparkle_xor_x(n, b, lty, ltx);
  for (uint32_t i = (uint32_t)0U; i < n >> (uint32_t)1U; i++)
  {
    uint32_t xi = rightBranch[(uint32_t)2U * i];
    uint32_t yi = rightBranch[(uint32_t)2U * i + (uint32_t)1U];
    uint32_t p0i = result[(uint32_t)2U * i];
    uint32_t p1i = result[(uint32_t)2U * i + (uint32_t)1U];
    branch1 branchIUpd = { .fst = xi ^ p0i, .snd = yi ^ p1i };
    uint32_t x = branchIUpd.fst;
    uint32_t y = branchIUpd.snd;
    result[(uint32_t)2U * i] = x;
    result[(uint32_t)2U * i + (uint32_t)1U] = y;
  }
  for (uint32_t i = (uint32_t)0U; i < n >> (uint32_t)1U; i++)
  {
    uint32_t x = leftBranch[(uint32_t)2U * i];
    uint32_t y = leftBranch[(uint32_t)2U * i + (uint32_t)1U];
    rightBranch[(uint32_t)2U * i] = x;
    rightBranch[(uint32_t)2U * i + (uint32_t)1U] = y;
  }
  for (uint32_t i = (uint32_t)0U; i < n >> (uint32_t)1U; i++)
  {
    uint32_t index = i - (uint32_t)1U;
    uint32_t k = n >> (uint32_t)1U;
    uint32_t j = index % k;
    uint32_t x = result[(uint32_t)2U * i];
    uint32_t y = result[(uint32_t)2U * i + (uint32_t)1U];
    leftBranch[(uint32_t)2U * j] = x;
    leftBranch[(uint32_t)2U * j + (uint32_t)1U] = y;
  }
}

void Hacl_Impl_Sparkle_add2(uint32_t n, uint32_t i, uint32_t *b)
{
  uint32_t x0 = b[0U];
  uint32_t y0 = b[1U];
  uint32_t x1 = b[2U];
  uint32_t y1 = b[3U];
  uint32_t i0 = i & (uint32_t)7U;
  uint32_t y01 = y0 ^ Hacl_Impl_Sparkle_rcon[i0];
  uint32_t y11 = y1 ^ i;
  b[0U] = x0;
  b[1U] = y01;
  b[2U] = x1;
  b[3U] = y11;
}

void Hacl_Impl_Sparkle_toBranch(uint32_t n, uint8_t *i, uint32_t *o)
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

void Hacl_Impl_Sparkle_fromBranch(uint32_t n, uint32_t *i, uint8_t *o)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)2U * n; i0++)
  {
    store32_le(o + i0 * (uint32_t)4U, i[i0]);
  }
}

void Hacl_Impl_Sparkle_arx_n_step(uint32_t n, uint32_t i, uint32_t *b)
{
  uint32_t *branchI = b + (uint32_t)2U * i;
  uint32_t rcon_i = Hacl_Impl_Sparkle_rcon[i];
  Hacl_Impl_Sparkle_arx(rcon_i, branchI);
}

void Hacl_Impl_Sparkle_arx_n(uint32_t n, uint32_t *b)
{
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    Hacl_Impl_Sparkle_arx_n_step(n, i, b);
  }
}

void Hacl_Impl_Sparkle_mainLoop_step(uint32_t n, uint32_t i, uint32_t *b)
{
  Hacl_Impl_Sparkle_add2(n, i, b);
  Hacl_Impl_Sparkle_arx_n(n, b);
  Hacl_Impl_Sparkle_l(n, b);
}

void Hacl_Impl_Sparkle_mainLoop(uint32_t n, uint32_t *b, uint32_t steps)
{
  for (uint32_t i = (uint32_t)0U; i < steps; i++)
  {
    Hacl_Impl_Sparkle_mainLoop_step(n, i, b);
  }
}

void Hacl_Impl_Sparkle_sparkle256(uint32_t steps, uint8_t *i, uint8_t *o)
{
  uint32_t temp[12U] = { 0U };
  Hacl_Impl_Sparkle_toBranch((uint32_t)4U, i, temp);
  Hacl_Impl_Sparkle_mainLoop((uint32_t)4U, temp, steps);
  Hacl_Impl_Sparkle_fromBranch((uint32_t)4U, temp, o);
}

