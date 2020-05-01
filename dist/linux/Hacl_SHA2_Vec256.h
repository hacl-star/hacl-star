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

#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"

#ifndef __Hacl_SHA2_Vec256_H
#define __Hacl_SHA2_Vec256_H

#include "Hacl_Kremlib.h"
#include "Hacl_SHA2_Generic.h"


typedef struct K____u8___u8__s
{
  u8 *fst;
  u8 *snd;
}
K____u8___u8_;

typedef struct K____u8__K____u8___u8__s
{
  u8 *fst;
  K____u8___u8_ snd;
}
K____u8__K____u8___u8_;

typedef struct K____u8__K____u8__K____u8___u8__s
{
  u8 *fst;
  K____u8__K____u8___u8_ snd;
}
K____u8__K____u8__K____u8___u8_;

typedef struct K____u8__K____u8__K____u8__K____u8___u8__s
{
  u8 *fst;
  K____u8__K____u8__K____u8___u8_ snd;
}
K____u8__K____u8__K____u8__K____u8___u8_;

typedef struct K____u8__K____u8__K____u8__K____u8__K____u8___u8__s
{
  u8 *fst;
  K____u8__K____u8__K____u8__K____u8___u8_ snd;
}
K____u8__K____u8__K____u8__K____u8__K____u8___u8_;

typedef struct K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8__s
{
  u8 *fst;
  K____u8__K____u8__K____u8__K____u8__K____u8___u8_ snd;
}
K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_;

typedef struct K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8__s
{
  u8 *fst;
  K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_ snd;
}
K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_;

typedef struct
K___K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8__s
{
  K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_ fst;
  K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_ snd;
}
K___K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_;

void
Hacl_SHA2_Vec256_sha256_8(
  u8 *r0,
  u8 *r1,
  u8 *r2,
  u8 *r3,
  u8 *r4,
  u8 *r5,
  u8 *r6,
  u8 *r7,
  u32 len,
  u8 *b0,
  u8 *b1,
  u8 *b2,
  u8 *b3,
  u8 *b4,
  u8 *b5,
  u8 *b6,
  u8 *b7
);

typedef struct K___K____u8__K____u8__K____u8___u8__K____u8__K____u8__K____u8___u8__s
{
  K____u8__K____u8__K____u8___u8_ fst;
  K____u8__K____u8__K____u8___u8_ snd;
}
K___K____u8__K____u8__K____u8___u8__K____u8__K____u8__K____u8___u8_;

void
Hacl_SHA2_Vec256_sha512_4(
  u8 *r0,
  u8 *r1,
  u8 *r2,
  u8 *r3,
  u32 len,
  u8 *b0,
  u8 *b1,
  u8 *b2,
  u8 *b3
);

#define __Hacl_SHA2_Vec256_H_DEFINED
#endif
