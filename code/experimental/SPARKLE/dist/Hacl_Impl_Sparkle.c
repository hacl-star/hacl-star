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

