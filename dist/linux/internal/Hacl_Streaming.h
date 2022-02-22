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


#ifndef __internal_Hacl_Streaming_H
#define __internal_Hacl_Streaming_H

#if defined(__cplusplus)
extern "C" {
#endif




#include "internal/Hacl_Hash_SHA2.h"
#include "Hacl_Kremlib.h"
#include "Hacl_Hash_SHA2.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"
typedef struct Hacl_Streaming_SHA2_state_sha2_384_s
{
  u64 *block_state;
  u8 *buf;
  u64 total_len;
}
Hacl_Streaming_SHA2_state_sha2_384;

void Hacl_Streaming_SHA2_update_512(Hacl_Streaming_SHA2_state_sha2_384 *p, u8 *data, u32 len);

void Hacl_Streaming_SHA2_finish_512(Hacl_Streaming_SHA2_state_sha2_384 *p, u8 *dst);

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_Streaming_H_DEFINED
#endif
