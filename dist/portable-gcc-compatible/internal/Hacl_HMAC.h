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


#ifndef __internal_Hacl_HMAC_H
#define __internal_Hacl_HMAC_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

#include "internal/Hacl_Krmllib.h"
#include "internal/Hacl_Hash_SHA2.h"
#include "internal/Hacl_Hash_SHA1.h"
#include "internal/Hacl_Hash_Blake2s.h"
#include "internal/Hacl_Hash_Blake2b.h"
#include "../Hacl_HMAC.h"

/* SNIPPET_START: Hacl_Impl_Blake2_Core_blake2s_params */

typedef struct Hacl_Impl_Blake2_Core_blake2s_params_s
{
  uint8_t digest_length;
  uint8_t key_length;
  uint8_t fanout;
  uint8_t depth;
  uint32_t leaf_length;
  uint32_t node_offset;
  uint16_t xof_length;
  uint8_t node_depth;
  uint8_t inner_length;
  uint8_t *salt;
  uint8_t *personal;
}
Hacl_Impl_Blake2_Core_blake2s_params;

/* SNIPPET_END: Hacl_Impl_Blake2_Core_blake2s_params */

/* SNIPPET_START: Hacl_Impl_Blake2_Core_blake2b_params */

typedef struct Hacl_Impl_Blake2_Core_blake2b_params_s
{
  uint8_t digest_length1;
  uint8_t key_length1;
  uint8_t fanout1;
  uint8_t depth1;
  uint32_t leaf_length1;
  uint32_t node_offset1;
  uint32_t xof_length1;
  uint8_t node_depth1;
  uint8_t inner_length1;
  uint8_t *salt1;
  uint8_t *personal1;
}
Hacl_Impl_Blake2_Core_blake2b_params;

/* SNIPPET_END: Hacl_Impl_Blake2_Core_blake2b_params */

/* SNIPPET_START: K___uint32_t_uint32_t */

typedef struct K___uint32_t_uint32_t_s
{
  uint32_t fst;
  uint32_t snd;
}
K___uint32_t_uint32_t;

/* SNIPPET_END: K___uint32_t_uint32_t */

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_HMAC_H_DEFINED
#endif
