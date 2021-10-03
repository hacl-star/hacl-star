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

const uint32_t *Hacl_Impl_Sparkle_rcon_buffer;

void Hacl_Impl_Sparkle_xor(uint32_t l, uint32_t *b, uint32_t *tx, uint32_t *ty)
{
  for (uint32_t i = (uint32_t)0U; i < l >> (uint32_t)1U; i++)
  {
    uint32_t xi = b[i];
    uint32_t yi = b[i + (uint32_t)1U];
    uint32_t tx_0 = tx[0U];
    uint32_t ty_0 = ty[0U];
    tx[0U] = xi ^ tx_0;
    tx[0U] = yi ^ ty_0;
  }
}

void Hacl_Impl_Sparkle_xor_x(uint32_t l, uint32_t *b, uint32_t lty, uint32_t ltx)
{
  for (uint32_t i = (uint32_t)0U; i < l >> (uint32_t)1U; i++)
  {
    uint32_t xi = b[i];
    uint32_t yi = b[i + (uint32_t)1U];
    uint32_t xi_n = xi ^ lty;
    uint32_t yi_n = yi ^ ltx;
    b[(uint32_t)2U * i] = xi_n;
    b[(uint32_t)2U * i + (uint32_t)1U] = yi_n;
  }
}

void Hacl_Impl_Sparkle_m(uint32_t n, uint32_t *b)
{
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
}

typedef struct branch1_s
{
  uint32_t fst;
  uint32_t snd;
}
branch1;

void Hacl_Impl_Sparkle_l_step(uint32_t n, uint32_t *perm, uint32_t i, uint32_t *rightBranch)
{
  uint32_t xi = rightBranch[i];
  uint32_t yi = rightBranch[i + (uint32_t)1U];
  uint32_t p0i = perm[i];
  uint32_t p1i = perm[i + (uint32_t)1U];
  branch1 branchIUpd = { .fst = xi ^ p0i, .snd = yi ^ p1i };
  uint32_t index = n >> (uint32_t)1U | n << (uint32_t)31U;
  uint32_t x = branchIUpd.fst;
  uint32_t y = branchIUpd.snd;
  rightBranch[(uint32_t)2U * index] = x;
  rightBranch[(uint32_t)2U * index + (uint32_t)1U] = y;
}

void Hacl_Impl_Sparkle_sparkle256(uint32_t steps, uint8_t *i, uint8_t *o)
{
  
}

