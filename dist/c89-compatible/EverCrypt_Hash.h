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

#include "evercrypt_targetconfig.h"
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

typedef uint8_t EverCrypt_Hash_state_s_tags;

typedef struct EverCrypt_Hash_state_s_s
{
  EverCrypt_Hash_state_s_tags tag;
  union {
    uint32_t *case_MD5_s;
    uint32_t *case_SHA1_s;
    uint32_t *case_SHA2_224_s;
    uint32_t *case_SHA2_256_s;
    uint64_t *case_SHA2_384_s;
    uint64_t *case_SHA2_512_s;
  }
  val;
}
EverCrypt_Hash_state_s;

bool
EverCrypt_Hash_uu___is_MD5_s(
  Spec_Hash_Definitions_hash_alg uu____159,
  EverCrypt_Hash_state_s projectee
);

uint32_t
*EverCrypt_Hash___proj__MD5_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____189,
  EverCrypt_Hash_state_s projectee
);

bool
EverCrypt_Hash_uu___is_SHA1_s(
  Spec_Hash_Definitions_hash_alg uu____213,
  EverCrypt_Hash_state_s projectee
);

uint32_t
*EverCrypt_Hash___proj__SHA1_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____243,
  EverCrypt_Hash_state_s projectee
);

bool
EverCrypt_Hash_uu___is_SHA2_224_s(
  Spec_Hash_Definitions_hash_alg uu____267,
  EverCrypt_Hash_state_s projectee
);

uint32_t
*EverCrypt_Hash___proj__SHA2_224_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____297,
  EverCrypt_Hash_state_s projectee
);

bool
EverCrypt_Hash_uu___is_SHA2_256_s(
  Spec_Hash_Definitions_hash_alg uu____321,
  EverCrypt_Hash_state_s projectee
);

uint32_t
*EverCrypt_Hash___proj__SHA2_256_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____351,
  EverCrypt_Hash_state_s projectee
);

bool
EverCrypt_Hash_uu___is_SHA2_384_s(
  Spec_Hash_Definitions_hash_alg uu____375,
  EverCrypt_Hash_state_s projectee
);

uint64_t
*EverCrypt_Hash___proj__SHA2_384_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____405,
  EverCrypt_Hash_state_s projectee
);

bool
EverCrypt_Hash_uu___is_SHA2_512_s(
  Spec_Hash_Definitions_hash_alg uu____429,
  EverCrypt_Hash_state_s projectee
);

uint64_t
*EverCrypt_Hash___proj__SHA2_512_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____459,
  EverCrypt_Hash_state_s projectee
);

Spec_Hash_Definitions_hash_alg EverCrypt_Hash_alg_of_state(EverCrypt_Hash_state_s *s);

EverCrypt_Hash_state_s *EverCrypt_Hash_create_in(Spec_Hash_Definitions_hash_alg a);

EverCrypt_Hash_state_s *EverCrypt_Hash_create(Spec_Hash_Definitions_hash_alg a);

void EverCrypt_Hash_init(EverCrypt_Hash_state_s *s);

void EverCrypt_Hash_update_multi_256(uint32_t *s, uint8_t *blocks, uint32_t n);

void EverCrypt_Hash_update(EverCrypt_Hash_state_s *s, uint8_t *block);

void EverCrypt_Hash_update_multi(EverCrypt_Hash_state_s *s, uint8_t *blocks, uint32_t len);

void
EverCrypt_Hash_update_last_256(
  uint32_t *s,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
);

void EverCrypt_Hash_update_last(EverCrypt_Hash_state_s *s, uint8_t *last, uint64_t total_len);

void EverCrypt_Hash_finish(EverCrypt_Hash_state_s *s, uint8_t *dst);

void EverCrypt_Hash_free(EverCrypt_Hash_state_s *s);

void EverCrypt_Hash_copy(EverCrypt_Hash_state_s *s_src, EverCrypt_Hash_state_s *s_dst);

void EverCrypt_Hash_hash_256(uint8_t *input, uint32_t input_len, uint8_t *dst);

void EverCrypt_Hash_hash_224(uint8_t *input, uint32_t input_len, uint8_t *dst);

void
EverCrypt_Hash_hash(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *dst,
  uint8_t *input,
  uint32_t len
);

typedef struct Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s_____s
Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____;

Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____
*EverCrypt_Hash_Incremental_create_in(Spec_Hash_Definitions_hash_alg a);

void
EverCrypt_Hash_Incremental_init(Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s);

void
EverCrypt_Hash_Incremental_update(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *data,
  uint32_t len
);

void
EverCrypt_Hash_Incremental_finish_md5(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

void
EverCrypt_Hash_Incremental_finish_sha1(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

void
EverCrypt_Hash_Incremental_finish_sha224(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

void
EverCrypt_Hash_Incremental_finish_sha256(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

void
EverCrypt_Hash_Incremental_finish_sha384(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

void
EverCrypt_Hash_Incremental_finish_sha512(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

Spec_Hash_Definitions_hash_alg
EverCrypt_Hash_Incremental_alg_of_state(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s
);

void
EverCrypt_Hash_Incremental_finish(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s,
  uint8_t *dst
);

void
EverCrypt_Hash_Incremental_free(Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s);

#define __EverCrypt_Hash_H_DEFINED
#endif
