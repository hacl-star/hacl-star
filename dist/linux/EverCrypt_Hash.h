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

#ifndef __EverCrypt_Hash_H
#define __EverCrypt_Hash_H

#include "Hacl_Kremlib.h"
#include "Vale.h"
#include "Hacl_Hash.h"
#include "EverCrypt_AutoConfig2.h"
#include "Hacl_Spec.h"


typedef Spec_Hash_Definitions_hash_alg EverCrypt_Hash_alg;

C_String_t EverCrypt_Hash_string_of_alg(Spec_Hash_Definitions_hash_alg uu___0_6);

typedef Spec_Hash_Definitions_hash_alg EverCrypt_Hash_broken_alg;

typedef Spec_Hash_Definitions_hash_alg EverCrypt_Hash_alg13;

typedef void *EverCrypt_Hash_e_alg;

#define EverCrypt_Hash_MD5_s 0
#define EverCrypt_Hash_SHA1_s 1
#define EverCrypt_Hash_SHA2_224_s 2
#define EverCrypt_Hash_SHA2_256_s 3
#define EverCrypt_Hash_SHA2_384_s 4
#define EverCrypt_Hash_SHA2_512_s 5

typedef u8 EverCrypt_Hash_state_s_tags;

typedef struct EverCrypt_Hash_state_s_s
{
  EverCrypt_Hash_state_s_tags tag;
  union {
    u32 *case_MD5_s;
    u32 *case_SHA1_s;
    u32 *case_SHA2_224_s;
    u32 *case_SHA2_256_s;
    u64 *case_SHA2_384_s;
    u64 *case_SHA2_512_s;
  }
  ;
}
EverCrypt_Hash_state_s;

bool
EverCrypt_Hash_uu___is_MD5_s(
  Spec_Hash_Definitions_hash_alg uu____151,
  EverCrypt_Hash_state_s projectee
);

u32
*EverCrypt_Hash___proj__MD5_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____179,
  EverCrypt_Hash_state_s projectee
);

bool
EverCrypt_Hash_uu___is_SHA1_s(
  Spec_Hash_Definitions_hash_alg uu____202,
  EverCrypt_Hash_state_s projectee
);

u32
*EverCrypt_Hash___proj__SHA1_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____230,
  EverCrypt_Hash_state_s projectee
);

bool
EverCrypt_Hash_uu___is_SHA2_224_s(
  Spec_Hash_Definitions_hash_alg uu____253,
  EverCrypt_Hash_state_s projectee
);

u32
*EverCrypt_Hash___proj__SHA2_224_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____281,
  EverCrypt_Hash_state_s projectee
);

bool
EverCrypt_Hash_uu___is_SHA2_256_s(
  Spec_Hash_Definitions_hash_alg uu____304,
  EverCrypt_Hash_state_s projectee
);

u32
*EverCrypt_Hash___proj__SHA2_256_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____332,
  EverCrypt_Hash_state_s projectee
);

bool
EverCrypt_Hash_uu___is_SHA2_384_s(
  Spec_Hash_Definitions_hash_alg uu____355,
  EverCrypt_Hash_state_s projectee
);

u64
*EverCrypt_Hash___proj__SHA2_384_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____383,
  EverCrypt_Hash_state_s projectee
);

bool
EverCrypt_Hash_uu___is_SHA2_512_s(
  Spec_Hash_Definitions_hash_alg uu____406,
  EverCrypt_Hash_state_s projectee
);

u64
*EverCrypt_Hash___proj__SHA2_512_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____434,
  EverCrypt_Hash_state_s projectee
);

Spec_Hash_Definitions_hash_alg EverCrypt_Hash_alg_of_state(EverCrypt_Hash_state_s *s);

EverCrypt_Hash_state_s *EverCrypt_Hash_create_in(Spec_Hash_Definitions_hash_alg a);

EverCrypt_Hash_state_s *EverCrypt_Hash_create(Spec_Hash_Definitions_hash_alg a);

void EverCrypt_Hash_init(EverCrypt_Hash_state_s *s);

void EverCrypt_Hash_update_multi_256(u32 *s, u8 *blocks, u32 n1);

void EverCrypt_Hash_update(EverCrypt_Hash_state_s *s, u8 *block1);

void EverCrypt_Hash_update_multi(EverCrypt_Hash_state_s *s, u8 *blocks, u32 len);

void EverCrypt_Hash_update_last_256(u32 *s, u64 prev_len, u8 *input, u32 input_len);

void EverCrypt_Hash_update_last(EverCrypt_Hash_state_s *s, u8 *last1, u64 total_len);

void EverCrypt_Hash_finish(EverCrypt_Hash_state_s *s, u8 *dst);

void EverCrypt_Hash_free(EverCrypt_Hash_state_s *s);

void EverCrypt_Hash_copy(EverCrypt_Hash_state_s *s_src, EverCrypt_Hash_state_s *s_dst);

void EverCrypt_Hash_hash_256(u8 *input, u32 input_len, u8 *dst);

void EverCrypt_Hash_hash_224(u8 *input, u32 input_len, u8 *dst);

void EverCrypt_Hash_hash(Spec_Hash_Definitions_hash_alg a, u8 *dst, u8 *input, u32 len);

typedef u8 *EverCrypt_Hash_Incremental_any_hash_t;

typedef struct EverCrypt_Hash_Incremental_state_s_s EverCrypt_Hash_Incremental_state_s;

bool
EverCrypt_Hash_Incremental_uu___is_State(
  Spec_Hash_Definitions_hash_alg a,
  EverCrypt_Hash_Incremental_state_s projectee
);

EverCrypt_Hash_state_s
*EverCrypt_Hash_Incremental___proj__State__item__hash_state(
  Spec_Hash_Definitions_hash_alg a,
  EverCrypt_Hash_Incremental_state_s projectee
);

u8
*EverCrypt_Hash_Incremental___proj__State__item__buf(
  Spec_Hash_Definitions_hash_alg a,
  EverCrypt_Hash_Incremental_state_s projectee
);

u64
EverCrypt_Hash_Incremental___proj__State__item__total_len(
  Spec_Hash_Definitions_hash_alg a,
  EverCrypt_Hash_Incremental_state_s projectee
);

Spec_Hash_Definitions_hash_alg
EverCrypt_Hash_Incremental_alg_of_state(EverCrypt_Hash_Incremental_state_s *s);

EverCrypt_Hash_Incremental_state_s
*EverCrypt_Hash_Incremental_create_in(Spec_Hash_Definitions_hash_alg a);

void EverCrypt_Hash_Incremental_init(EverCrypt_Hash_Incremental_state_s *s);

void
EverCrypt_Hash_Incremental_update(EverCrypt_Hash_Incremental_state_s *p1, u8 *data, u32 len);

void EverCrypt_Hash_Incremental_finish(EverCrypt_Hash_Incremental_state_s *s, u8 *dst);

void EverCrypt_Hash_Incremental_free(EverCrypt_Hash_Incremental_state_s *s);

#define __EverCrypt_Hash_H_DEFINED
#endif
