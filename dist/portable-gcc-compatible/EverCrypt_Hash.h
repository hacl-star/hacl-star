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


/* SNIPPET_START: EverCrypt_Hash_alg */

typedef Spec_Hash_Definitions_hash_alg EverCrypt_Hash_alg;

/* SNIPPET_END: EverCrypt_Hash_alg */

/* SNIPPET_START: EverCrypt_Hash_string_of_alg */

C_String_t EverCrypt_Hash_string_of_alg(Spec_Hash_Definitions_hash_alg uu___0_6);

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
  }
  ;
}
EverCrypt_Hash_state_s;

/* SNIPPET_END: EverCrypt_Hash_state_s */

/* SNIPPET_START: EverCrypt_Hash_uu___is_MD5_s */

bool
EverCrypt_Hash_uu___is_MD5_s(
  Spec_Hash_Definitions_hash_alg uu____151,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash_uu___is_MD5_s */

/* SNIPPET_START: EverCrypt_Hash___proj__MD5_s__item__p */

uint32_t
*EverCrypt_Hash___proj__MD5_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____179,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash___proj__MD5_s__item__p */

/* SNIPPET_START: EverCrypt_Hash_uu___is_SHA1_s */

bool
EverCrypt_Hash_uu___is_SHA1_s(
  Spec_Hash_Definitions_hash_alg uu____202,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash_uu___is_SHA1_s */

/* SNIPPET_START: EverCrypt_Hash___proj__SHA1_s__item__p */

uint32_t
*EverCrypt_Hash___proj__SHA1_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____230,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash___proj__SHA1_s__item__p */

/* SNIPPET_START: EverCrypt_Hash_uu___is_SHA2_224_s */

bool
EverCrypt_Hash_uu___is_SHA2_224_s(
  Spec_Hash_Definitions_hash_alg uu____253,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash_uu___is_SHA2_224_s */

/* SNIPPET_START: EverCrypt_Hash___proj__SHA2_224_s__item__p */

uint32_t
*EverCrypt_Hash___proj__SHA2_224_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____281,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash___proj__SHA2_224_s__item__p */

/* SNIPPET_START: EverCrypt_Hash_uu___is_SHA2_256_s */

bool
EverCrypt_Hash_uu___is_SHA2_256_s(
  Spec_Hash_Definitions_hash_alg uu____304,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash_uu___is_SHA2_256_s */

/* SNIPPET_START: EverCrypt_Hash___proj__SHA2_256_s__item__p */

uint32_t
*EverCrypt_Hash___proj__SHA2_256_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____332,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash___proj__SHA2_256_s__item__p */

/* SNIPPET_START: EverCrypt_Hash_uu___is_SHA2_384_s */

bool
EverCrypt_Hash_uu___is_SHA2_384_s(
  Spec_Hash_Definitions_hash_alg uu____355,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash_uu___is_SHA2_384_s */

/* SNIPPET_START: EverCrypt_Hash___proj__SHA2_384_s__item__p */

uint64_t
*EverCrypt_Hash___proj__SHA2_384_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____383,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash___proj__SHA2_384_s__item__p */

/* SNIPPET_START: EverCrypt_Hash_uu___is_SHA2_512_s */

bool
EverCrypt_Hash_uu___is_SHA2_512_s(
  Spec_Hash_Definitions_hash_alg uu____406,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash_uu___is_SHA2_512_s */

/* SNIPPET_START: EverCrypt_Hash___proj__SHA2_512_s__item__p */

uint64_t
*EverCrypt_Hash___proj__SHA2_512_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____434,
  EverCrypt_Hash_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash___proj__SHA2_512_s__item__p */

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

void EverCrypt_Hash_update_multi_256(uint32_t *s, uint8_t *blocks, uint32_t n1);

/* SNIPPET_END: EverCrypt_Hash_update_multi_256 */

/* SNIPPET_START: EverCrypt_Hash_update */

void EverCrypt_Hash_update(EverCrypt_Hash_state_s *s, uint8_t *block1);

/* SNIPPET_END: EverCrypt_Hash_update */

/* SNIPPET_START: EverCrypt_Hash_update_multi */

void EverCrypt_Hash_update_multi(EverCrypt_Hash_state_s *s, uint8_t *blocks, uint32_t len);

/* SNIPPET_END: EverCrypt_Hash_update_multi */

/* SNIPPET_START: EverCrypt_Hash_update_last_256 */

void
EverCrypt_Hash_update_last_256(
  uint32_t *s,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
);

/* SNIPPET_END: EverCrypt_Hash_update_last_256 */

/* SNIPPET_START: EverCrypt_Hash_update_last */

void EverCrypt_Hash_update_last(EverCrypt_Hash_state_s *s, uint8_t *last1, uint64_t total_len);

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

/* SNIPPET_START: EverCrypt_Hash_Incremental_any_hash_t */

typedef uint8_t *EverCrypt_Hash_Incremental_any_hash_t;

/* SNIPPET_END: EverCrypt_Hash_Incremental_any_hash_t */

/* SNIPPET_START: EverCrypt_Hash_Incremental_state_s */

typedef struct EverCrypt_Hash_Incremental_state_s_s EverCrypt_Hash_Incremental_state_s;

/* SNIPPET_END: EverCrypt_Hash_Incremental_state_s */

/* SNIPPET_START: EverCrypt_Hash_Incremental_uu___is_State */

bool
EverCrypt_Hash_Incremental_uu___is_State(
  Spec_Hash_Definitions_hash_alg a,
  EverCrypt_Hash_Incremental_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash_Incremental_uu___is_State */

/* SNIPPET_START: EverCrypt_Hash_Incremental___proj__State__item__hash_state */

EverCrypt_Hash_state_s
*EverCrypt_Hash_Incremental___proj__State__item__hash_state(
  Spec_Hash_Definitions_hash_alg a,
  EverCrypt_Hash_Incremental_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash_Incremental___proj__State__item__hash_state */

/* SNIPPET_START: EverCrypt_Hash_Incremental___proj__State__item__buf */

uint8_t
*EverCrypt_Hash_Incremental___proj__State__item__buf(
  Spec_Hash_Definitions_hash_alg a,
  EverCrypt_Hash_Incremental_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash_Incremental___proj__State__item__buf */

/* SNIPPET_START: EverCrypt_Hash_Incremental___proj__State__item__total_len */

uint64_t
EverCrypt_Hash_Incremental___proj__State__item__total_len(
  Spec_Hash_Definitions_hash_alg a,
  EverCrypt_Hash_Incremental_state_s projectee
);

/* SNIPPET_END: EverCrypt_Hash_Incremental___proj__State__item__total_len */

/* SNIPPET_START: EverCrypt_Hash_Incremental_alg_of_state */

Spec_Hash_Definitions_hash_alg
EverCrypt_Hash_Incremental_alg_of_state(EverCrypt_Hash_Incremental_state_s *s);

/* SNIPPET_END: EverCrypt_Hash_Incremental_alg_of_state */

/* SNIPPET_START: EverCrypt_Hash_Incremental_create_in */

EverCrypt_Hash_Incremental_state_s
*EverCrypt_Hash_Incremental_create_in(Spec_Hash_Definitions_hash_alg a);

/* SNIPPET_END: EverCrypt_Hash_Incremental_create_in */

/* SNIPPET_START: EverCrypt_Hash_Incremental_init */

void EverCrypt_Hash_Incremental_init(EverCrypt_Hash_Incremental_state_s *s);

/* SNIPPET_END: EverCrypt_Hash_Incremental_init */

/* SNIPPET_START: EverCrypt_Hash_Incremental_update */

void
EverCrypt_Hash_Incremental_update(
  EverCrypt_Hash_Incremental_state_s *p1,
  uint8_t *data,
  uint32_t len
);

/* SNIPPET_END: EverCrypt_Hash_Incremental_update */

/* SNIPPET_START: EverCrypt_Hash_Incremental_finish */

void EverCrypt_Hash_Incremental_finish(EverCrypt_Hash_Incremental_state_s *s, uint8_t *dst);

/* SNIPPET_END: EverCrypt_Hash_Incremental_finish */

/* SNIPPET_START: EverCrypt_Hash_Incremental_free */

void EverCrypt_Hash_Incremental_free(EverCrypt_Hash_Incremental_state_s *s);

/* SNIPPET_END: EverCrypt_Hash_Incremental_free */

#define __EverCrypt_Hash_H_DEFINED
#endif
