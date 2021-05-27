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


#ifndef __Hacl_Impl_Sparkle_H
#define __Hacl_Impl_Sparkle_H
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>




extern uint32_t Hacl_Impl_Sparkle_size_word;

extern uint32_t Hacl_Impl_Sparkle_vsize_rcon;

extern const uint32_t *Hacl_Impl_Sparkle_rcon_buffer;

typedef uint32_t Hacl_Impl_Sparkle_branch_len;

void Hacl_Impl_Sparkle_arx(uint32_t c, uint32_t *b);

uint32_t Hacl_Impl_Sparkle_l1(uint32_t x);

typedef struct Spec_SPARKLE2_branch1_s
{
  uint32_t fst;
  uint32_t snd;
}
Spec_SPARKLE2_branch1;

Spec_SPARKLE2_branch1 Hacl_Impl_Sparkle_xor(uint32_t l, uint32_t *b);


#define __Hacl_Impl_Sparkle_H_DEFINED
#endif
