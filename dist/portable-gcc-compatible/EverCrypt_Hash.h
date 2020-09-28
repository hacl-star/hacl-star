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


#ifndef __EverCrypt_Hash_H
#define __EverCrypt_Hash_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Kremlib.h"
#include "Hacl_Impl_Blake2_Constants.h"
#include "Vale.h"
#include "Hacl_Hash.h"
#include "EverCrypt_AutoConfig2.h"
#include "Hacl_Spec.h"

/* SNIPPET_START: EverCrypt_Hash_alg */

typedef Spec_Hash_Definitions_hash_alg EverCrypt_Hash_alg;

/* SNIPPET_END: EverCrypt_Hash_alg */

/* SNIPPET_START: EverCrypt_Hash_string_of_alg */

C_String_t EverCrypt_Hash_string_of_alg(Spec_Hash_Definitions_hash_alg uu___);

/* SNIPPET_END: EverCrypt_Hash_string_of_alg */

/* SNIPPET_START: EverCrypt_Hash_broken_alg */

typedef Spec_Hash_Definitions_hash_alg EverCrypt_Hash_broken_alg;

/* SNIPPET_END: EverCrypt_Hash_broken_alg */

/* SNIPPET_START: EverCrypt_Hash_alg13 */

typedef Spec_Hash_Definitions_hash_alg EverCrypt_Hash_alg13;

/* SNIPPET_END: EverCrypt_Hash_alg13 */

/* SNIPPET_START: EverCrypt_Hash_e_alg */

typedef void *EverCrypt_Hash_e_alg;

/* SNIPPET_END: EverCrypt_Hash_e_alg */

/* SNIPPET_START: EverCrypt_Hash_state_s_tags */

#define EverCrypt_Hash_MD5_s 0
#define EverCrypt_Hash_SHA1_s 1
#define EverCrypt_Hash_SHA2_224_s 2
#define EverCrypt_Hash_SHA2_256_s 3
#define EverCrypt_Hash_SHA2_384_s 4
#define EverCrypt_Hash_SHA2_512_s 5
#define EverCrypt_Hash_Blake2S_s 6
#define EverCrypt_Hash_Blake2B_s 7

/* SNIPPET_END: EverCrypt_Hash_state_s_tags */

typedef uint8_t EverCrypt_Hash_state_s_tags;

/* SNIPPET_START: EverCrypt_Hash_state_s */

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
    uint32_t *case_Blake2S_s;
    uint64_t *case_Blake2B_s;
  }
  ;
}
EverCrypt_Hash_state_s;

/* SNIPPET_END: EverCrypt_Hash_state_s */

/* SNIPPET_START: EverCrypt_Hash_uu___is_MD5_s */

bool
EverCrypt_Hash_uu___is_MD5_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash_uu___is_MD5_s */

/* SNIPPET_START: EverCrypt_Hash___proj__MD5_s__item__p */

uint32_t
*EverCrypt_Hash___proj__MD5_s__item__p(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash___proj__MD5_s__item__p */

/* SNIPPET_START: EverCrypt_Hash_uu___is_SHA1_s */

bool
EverCrypt_Hash_uu___is_SHA1_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash_uu___is_SHA1_s */

/* SNIPPET_START: EverCrypt_Hash___proj__SHA1_s__item__p */

uint32_t
*EverCrypt_Hash___proj__SHA1_s__item__p(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash___proj__SHA1_s__item__p */

/* SNIPPET_START: EverCrypt_Hash_uu___is_SHA2_224_s */

bool
EverCrypt_Hash_uu___is_SHA2_224_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash_uu___is_SHA2_224_s */

/* SNIPPET_START: EverCrypt_Hash___proj__SHA2_224_s__item__p */

uint32_t
*EverCrypt_Hash___proj__SHA2_224_s__item__p(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash___proj__SHA2_224_s__item__p */

/* SNIPPET_START: EverCrypt_Hash_uu___is_SHA2_256_s */

bool
EverCrypt_Hash_uu___is_SHA2_256_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash_uu___is_SHA2_256_s */

/* SNIPPET_START: EverCrypt_Hash___proj__SHA2_256_s__item__p */

uint32_t
*EverCrypt_Hash___proj__SHA2_256_s__item__p(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash___proj__SHA2_256_s__item__p */

/* SNIPPET_START: EverCrypt_Hash_uu___is_SHA2_384_s */

bool
EverCrypt_Hash_uu___is_SHA2_384_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash_uu___is_SHA2_384_s */

/* SNIPPET_START: EverCrypt_Hash___proj__SHA2_384_s__item__p */

uint64_t
*EverCrypt_Hash___proj__SHA2_384_s__item__p(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash___proj__SHA2_384_s__item__p */

/* SNIPPET_START: EverCrypt_Hash_uu___is_SHA2_512_s */

bool
EverCrypt_Hash_uu___is_SHA2_512_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash_uu___is_SHA2_512_s */

/* SNIPPET_START: EverCrypt_Hash___proj__SHA2_512_s__item__p */

uint64_t
*EverCrypt_Hash___proj__SHA2_512_s__item__p(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash___proj__SHA2_512_s__item__p */

/* SNIPPET_START: EverCrypt_Hash_uu___is_Blake2S_s */

bool
EverCrypt_Hash_uu___is_Blake2S_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash_uu___is_Blake2S_s */

/* SNIPPET_START: EverCrypt_Hash___proj__Blake2S_s__item__p */

uint32_t
*EverCrypt_Hash___proj__Blake2S_s__item__p(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash___proj__Blake2S_s__item__p */

/* SNIPPET_START: EverCrypt_Hash_uu___is_Blake2B_s */

bool
EverCrypt_Hash_uu___is_Blake2B_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash_uu___is_Blake2B_s */

/* SNIPPET_START: EverCrypt_Hash___proj__Blake2B_s__item__p */

uint64_t
*EverCrypt_Hash___proj__Blake2B_s__item__p(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash___proj__Blake2B_s__item__p */

/* SNIPPET_START: EverCrypt_Hash_alg_of_state */

Spec_Hash_Definitions_hash_alg EverCrypt_Hash_alg_of_state(EverCrypt_Hash_state_s *s);

/* SNIPPET_END: EverCrypt_Hash_alg_of_state */

/* SNIPPET_START: EverCrypt_Hash_create_in */

EverCrypt_Hash_state_s *EverCrypt_Hash_create_in(Spec_Hash_Definitions_hash_alg a);

/* SNIPPET_END: EverCrypt_Hash_create_in */

/* SNIPPET_START: EverCrypt_Hash_create */

EverCrypt_Hash_state_s *EverCrypt_Hash_create(Spec_Hash_Definitions_hash_alg a);

/* SNIPPET_END: EverCrypt_Hash_create */

/* SNIPPET_START: EverCrypt_Hash_init */

void EverCrypt_Hash_init(EverCrypt_Hash_state_s *s);

/* SNIPPET_END: EverCrypt_Hash_init */

/* SNIPPET_START: EverCrypt_Hash_update_multi_256 */

void EverCrypt_Hash_update_multi_256(uint32_t *s, uint8_t *blocks, uint32_t n);

/* SNIPPET_END: EverCrypt_Hash_update_multi_256 */

/* SNIPPET_START: EverCrypt_Hash_update2 */

void EverCrypt_Hash_update2(EverCrypt_Hash_state_s *s, uint64_t prevlen, uint8_t *block);

/* SNIPPET_END: EverCrypt_Hash_update2 */

/* SNIPPET_START: EverCrypt_Hash_update */

KRML_DEPRECATED("Use update2 instead")

void EverCrypt_Hash_update(EverCrypt_Hash_state_s *s, uint8_t *block);

/* SNIPPET_END: EverCrypt_Hash_update */

/* SNIPPET_START: EverCrypt_Hash_update_multi2 */

void
EverCrypt_Hash_update_multi2(
  EverCrypt_Hash_state_s *s,
  uint64_t prevlen,
  uint8_t *blocks,
  uint32_t len
);

/* SNIPPET_END: EverCrypt_Hash_update_multi2 */

/* SNIPPET_START: EverCrypt_Hash_update_multi */

KRML_DEPRECATED("Use update_multi2 instead")

void EverCrypt_Hash_update_multi(EverCrypt_Hash_state_s *s, uint8_t *blocks, uint32_t len);

/* SNIPPET_END: EverCrypt_Hash_update_multi */

/* SNIPPET_START: EverCrypt_Hash_update_last_256 */

void
EverCrypt_Hash_update_last_256(
  uint32_t *s,
  uint64_t input,
  uint8_t *input_len,
  uint32_t input_len1
);

/* SNIPPET_END: EverCrypt_Hash_update_last_256 */

/* SNIPPET_START: EverCrypt_Hash_update_last2 */

void
EverCrypt_Hash_update_last2(
  EverCrypt_Hash_state_s *s,
  uint64_t prev_len,
  uint8_t *last,
  uint32_t last_len
);

/* SNIPPET_END: EverCrypt_Hash_update_last2 */

/* SNIPPET_START: EverCrypt_Hash_update_last */

KRML_DEPRECATED("Use update_last2 instead")

void EverCrypt_Hash_update_last(EverCrypt_Hash_state_s *s, uint8_t *last, uint64_t total_len);

/* SNIPPET_END: EverCrypt_Hash_update_last */

/* SNIPPET_START: EverCrypt_Hash_finish */

void EverCrypt_Hash_finish(EverCrypt_Hash_state_s *s, uint8_t *dst);

/* SNIPPET_END: EverCrypt_Hash_finish */

/* SNIPPET_START: EverCrypt_Hash_free */

void EverCrypt_Hash_free(EverCrypt_Hash_state_s *s);

/* SNIPPET_END: EverCrypt_Hash_free */

/* SNIPPET_START: EverCrypt_Hash_copy */

void EverCrypt_Hash_copy(EverCrypt_Hash_state_s *s_src, EverCrypt_Hash_state_s *s_dst);

/* SNIPPET_END: EverCrypt_Hash_copy */

/* SNIPPET_START: EverCrypt_Hash_hash_256 */

void EverCrypt_Hash_hash_256(uint8_t *input, uint32_t input_len, uint8_t *dst);

/* SNIPPET_END: EverCrypt_Hash_hash_256 */

/* SNIPPET_START: EverCrypt_Hash_hash_224 */

void EverCrypt_Hash_hash_224(uint8_t *input, uint32_t input_len, uint8_t *dst);

/* SNIPPET_END: EverCrypt_Hash_hash_224 */

/* SNIPPET_START: EverCrypt_Hash_hash */

void
EverCrypt_Hash_hash(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *dst,
  uint8_t *input,
  uint32_t len
);

/* SNIPPET_END: EverCrypt_Hash_hash */

/* SNIPPET_START: EverCrypt_Hash_Incremental_hash_len */

uint32_t EverCrypt_Hash_Incremental_hash_len(Spec_Hash_Definitions_hash_alg a);

/* SNIPPET_END: EverCrypt_Hash_Incremental_hash_len */

/* SNIPPET_START: EverCrypt_Hash_Incremental_block_len */

uint32_t EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_hash_alg a);

/* SNIPPET_END: EverCrypt_Hash_Incremental_block_len */

/* SNIPPET_START: Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ */

typedef struct Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s_____s
{
  EverCrypt_Hash_state_s *block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____;

/* SNIPPET_END: Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ */

/* SNIPPET_START: EverCrypt_Hash_Incremental_create_in */

Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____
*EverCrypt_Hash_Incremental_create_in(Spec_Hash_Definitions_hash_alg a);

/* SNIPPET_END: EverCrypt_Hash_Incremental_create_in */

/* SNIPPET_START: EverCrypt_Hash_Incremental_init */

void
EverCrypt_Hash_Incremental_init(Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s);

/* SNIPPET_END: EverCrypt_Hash_Incremental_init */

/* SNIPPET_START: EverCrypt_Hash_Incremental_update */

void
EverCrypt_Hash_Incremental_update(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *data,
  uint32_t len
);

/* SNIPPET_END: EverCrypt_Hash_Incremental_update */

/* SNIPPET_START: EverCrypt_Hash_Incremental_finish_md5 */

void
EverCrypt_Hash_Incremental_finish_md5(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

/* SNIPPET_END: EverCrypt_Hash_Incremental_finish_md5 */

/* SNIPPET_START: EverCrypt_Hash_Incremental_finish_sha1 */

void
EverCrypt_Hash_Incremental_finish_sha1(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

/* SNIPPET_END: EverCrypt_Hash_Incremental_finish_sha1 */

/* SNIPPET_START: EverCrypt_Hash_Incremental_finish_sha224 */

void
EverCrypt_Hash_Incremental_finish_sha224(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

/* SNIPPET_END: EverCrypt_Hash_Incremental_finish_sha224 */

/* SNIPPET_START: EverCrypt_Hash_Incremental_finish_sha256 */

void
EverCrypt_Hash_Incremental_finish_sha256(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

/* SNIPPET_END: EverCrypt_Hash_Incremental_finish_sha256 */

/* SNIPPET_START: EverCrypt_Hash_Incremental_finish_sha384 */

void
EverCrypt_Hash_Incremental_finish_sha384(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

/* SNIPPET_END: EverCrypt_Hash_Incremental_finish_sha384 */

/* SNIPPET_START: EverCrypt_Hash_Incremental_finish_sha512 */

void
EverCrypt_Hash_Incremental_finish_sha512(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

/* SNIPPET_END: EverCrypt_Hash_Incremental_finish_sha512 */

/* SNIPPET_START: EverCrypt_Hash_Incremental_finish_blake2s */

void
EverCrypt_Hash_Incremental_finish_blake2s(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

/* SNIPPET_END: EverCrypt_Hash_Incremental_finish_blake2s */

/* SNIPPET_START: EverCrypt_Hash_Incremental_finish_blake2b */

void
EverCrypt_Hash_Incremental_finish_blake2b(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

/* SNIPPET_END: EverCrypt_Hash_Incremental_finish_blake2b */

/* SNIPPET_START: EverCrypt_Hash_Incremental_alg_of_state */

Spec_Hash_Definitions_hash_alg
EverCrypt_Hash_Incremental_alg_of_state(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s
);

/* SNIPPET_END: EverCrypt_Hash_Incremental_alg_of_state */

/* SNIPPET_START: EverCrypt_Hash_Incremental_finish */

void
EverCrypt_Hash_Incremental_finish(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s,
  uint8_t *dst
);

/* SNIPPET_END: EverCrypt_Hash_Incremental_finish */

/* SNIPPET_START: EverCrypt_Hash_Incremental_free */

void
EverCrypt_Hash_Incremental_free(Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s);

/* SNIPPET_END: EverCrypt_Hash_Incremental_free */

#if defined(__cplusplus)
}
#endif

#define __EverCrypt_Hash_H_DEFINED
#endif
