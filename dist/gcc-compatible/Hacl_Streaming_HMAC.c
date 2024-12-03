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


#include "internal/Hacl_Streaming_HMAC.h"

#include "internal/Hacl_Hash_SHA3.h"
#include "internal/Hacl_Hash_SHA2.h"
#include "internal/Hacl_Hash_SHA1.h"
#include "internal/Hacl_Hash_MD5.h"
#include "internal/Hacl_Hash_Blake2s_Simd128.h"
#include "internal/Hacl_Hash_Blake2s.h"
#include "internal/Hacl_Hash_Blake2b_Simd256.h"
#include "internal/Hacl_Hash_Blake2b.h"

static Spec_Hash_Definitions_hash_alg alg_of_impl(Hacl_Agile_Hash_impl i)
{
  switch (i)
  {
    case Hacl_Agile_Hash_MD5:
      {
        return Spec_Hash_Definitions_MD5;
      }
    case Hacl_Agile_Hash_SHA1:
      {
        return Spec_Hash_Definitions_SHA1;
      }
    case Hacl_Agile_Hash_SHA2_224:
      {
        return Spec_Hash_Definitions_SHA2_224;
      }
    case Hacl_Agile_Hash_SHA2_256:
      {
        return Spec_Hash_Definitions_SHA2_256;
      }
    case Hacl_Agile_Hash_SHA2_384:
      {
        return Spec_Hash_Definitions_SHA2_384;
      }
    case Hacl_Agile_Hash_SHA2_512:
      {
        return Spec_Hash_Definitions_SHA2_512;
      }
    case Hacl_Agile_Hash_SHA3_224:
      {
        return Spec_Hash_Definitions_SHA3_224;
      }
    case Hacl_Agile_Hash_SHA3_256:
      {
        return Spec_Hash_Definitions_SHA3_256;
      }
    case Hacl_Agile_Hash_SHA3_384:
      {
        return Spec_Hash_Definitions_SHA3_384;
      }
    case Hacl_Agile_Hash_SHA3_512:
      {
        return Spec_Hash_Definitions_SHA3_512;
      }
    case Hacl_Agile_Hash_Blake2S_32:
      {
        return Spec_Hash_Definitions_Blake2S;
      }
    case Hacl_Agile_Hash_Blake2S_128:
      {
        return Spec_Hash_Definitions_Blake2S;
      }
    case Hacl_Agile_Hash_Blake2B_32:
      {
        return Spec_Hash_Definitions_Blake2B;
      }
    case Hacl_Agile_Hash_Blake2B_256:
      {
        return Spec_Hash_Definitions_Blake2B;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

#define MD5_s 0
#define SHA1_s 1
#define SHA2_224_s 2
#define SHA2_256_s 3
#define SHA2_384_s 4
#define SHA2_512_s 5
#define SHA3_224_s 6
#define SHA3_256_s 7
#define SHA3_384_s 8
#define SHA3_512_s 9
#define Blake2S_s 10
#define Blake2S_128_s 11
#define Blake2B_s 12
#define Blake2B_256_s 13

typedef uint8_t state_s_tags;

typedef struct Hacl_Agile_Hash_state_s_s
{
  state_s_tags tag;
  union {
    uint32_t *case_MD5_s;
    uint32_t *case_SHA1_s;
    uint32_t *case_SHA2_224_s;
    uint32_t *case_SHA2_256_s;
    uint64_t *case_SHA2_384_s;
    uint64_t *case_SHA2_512_s;
    uint64_t *case_SHA3_224_s;
    uint64_t *case_SHA3_256_s;
    uint64_t *case_SHA3_384_s;
    uint64_t *case_SHA3_512_s;
    uint32_t *case_Blake2S_s;
    Lib_IntVector_Intrinsics_vec128 *case_Blake2S_128_s;
    uint64_t *case_Blake2B_s;
    Lib_IntVector_Intrinsics_vec256 *case_Blake2B_256_s;
  }
  ;
}
Hacl_Agile_Hash_state_s;

static Hacl_Agile_Hash_impl impl_of_state_s(Hacl_Agile_Hash_state_s s)
{
  if (s.tag == MD5_s)
  {
    return Hacl_Agile_Hash_MD5;
  }
  if (s.tag == SHA1_s)
  {
    return Hacl_Agile_Hash_SHA1;
  }
  if (s.tag == SHA2_224_s)
  {
    return Hacl_Agile_Hash_SHA2_224;
  }
  if (s.tag == SHA2_256_s)
  {
    return Hacl_Agile_Hash_SHA2_256;
  }
  if (s.tag == SHA2_384_s)
  {
    return Hacl_Agile_Hash_SHA2_384;
  }
  if (s.tag == SHA2_512_s)
  {
    return Hacl_Agile_Hash_SHA2_512;
  }
  if (s.tag == SHA3_224_s)
  {
    return Hacl_Agile_Hash_SHA3_224;
  }
  if (s.tag == SHA3_256_s)
  {
    return Hacl_Agile_Hash_SHA3_256;
  }
  if (s.tag == SHA3_384_s)
  {
    return Hacl_Agile_Hash_SHA3_384;
  }
  if (s.tag == SHA3_512_s)
  {
    return Hacl_Agile_Hash_SHA3_512;
  }
  if (s.tag == Blake2S_s)
  {
    return Hacl_Agile_Hash_Blake2S_32;
  }
  if (s.tag == Blake2S_128_s)
  {
    return Hacl_Agile_Hash_Blake2S_128;
  }
  if (s.tag == Blake2B_s)
  {
    return Hacl_Agile_Hash_Blake2B_32;
  }
  if (s.tag == Blake2B_256_s)
  {
    return Hacl_Agile_Hash_Blake2B_256;
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

static Hacl_Agile_Hash_impl impl_of_state(Hacl_Agile_Hash_state_s *s)
{
  return impl_of_state_s(*s);
}

Hacl_Agile_Hash_state_s FStar_Pervasives_false_elim__Hacl_Agile_Hash_state_s(void)
{
  return FStar_Pervasives_false_elim__Hacl_Agile_Hash_state_s();
}

static Hacl_Agile_Hash_state_s *create_in(Hacl_Agile_Hash_impl a)
{
  Hacl_Agile_Hash_state_s s;
  switch (a)
  {
    case Hacl_Agile_Hash_MD5:
      {
        uint32_t *buf = (uint32_t *)KRML_HOST_CALLOC(4U, sizeof (uint32_t));
        s = ((Hacl_Agile_Hash_state_s){ .tag = MD5_s, { .case_MD5_s = buf } });
        break;
      }
    case Hacl_Agile_Hash_SHA1:
      {
        uint32_t *buf = (uint32_t *)KRML_HOST_CALLOC(5U, sizeof (uint32_t));
        s = ((Hacl_Agile_Hash_state_s){ .tag = SHA1_s, { .case_SHA1_s = buf } });
        break;
      }
    case Hacl_Agile_Hash_SHA2_224:
      {
        uint32_t *buf = (uint32_t *)KRML_HOST_CALLOC(8U, sizeof (uint32_t));
        s = ((Hacl_Agile_Hash_state_s){ .tag = SHA2_224_s, { .case_SHA2_224_s = buf } });
        break;
      }
    case Hacl_Agile_Hash_SHA2_256:
      {
        uint32_t *buf = (uint32_t *)KRML_HOST_CALLOC(8U, sizeof (uint32_t));
        s = ((Hacl_Agile_Hash_state_s){ .tag = SHA2_256_s, { .case_SHA2_256_s = buf } });
        break;
      }
    case Hacl_Agile_Hash_SHA2_384:
      {
        uint64_t *buf = (uint64_t *)KRML_HOST_CALLOC(8U, sizeof (uint64_t));
        s = ((Hacl_Agile_Hash_state_s){ .tag = SHA2_384_s, { .case_SHA2_384_s = buf } });
        break;
      }
    case Hacl_Agile_Hash_SHA2_512:
      {
        uint64_t *buf = (uint64_t *)KRML_HOST_CALLOC(8U, sizeof (uint64_t));
        s = ((Hacl_Agile_Hash_state_s){ .tag = SHA2_512_s, { .case_SHA2_512_s = buf } });
        break;
      }
    case Hacl_Agile_Hash_SHA3_224:
      {
        uint64_t *buf = (uint64_t *)KRML_HOST_CALLOC(25U, sizeof (uint64_t));
        s = ((Hacl_Agile_Hash_state_s){ .tag = SHA3_224_s, { .case_SHA3_224_s = buf } });
        break;
      }
    case Hacl_Agile_Hash_SHA3_256:
      {
        uint64_t *buf = (uint64_t *)KRML_HOST_CALLOC(25U, sizeof (uint64_t));
        s = ((Hacl_Agile_Hash_state_s){ .tag = SHA3_256_s, { .case_SHA3_256_s = buf } });
        break;
      }
    case Hacl_Agile_Hash_SHA3_384:
      {
        uint64_t *buf = (uint64_t *)KRML_HOST_CALLOC(25U, sizeof (uint64_t));
        s = ((Hacl_Agile_Hash_state_s){ .tag = SHA3_384_s, { .case_SHA3_384_s = buf } });
        break;
      }
    case Hacl_Agile_Hash_SHA3_512:
      {
        uint64_t *buf = (uint64_t *)KRML_HOST_CALLOC(25U, sizeof (uint64_t));
        s = ((Hacl_Agile_Hash_state_s){ .tag = SHA3_512_s, { .case_SHA3_512_s = buf } });
        break;
      }
    case Hacl_Agile_Hash_Blake2S_32:
      {
        uint32_t *buf = (uint32_t *)KRML_HOST_CALLOC(16U, sizeof (uint32_t));
        s = ((Hacl_Agile_Hash_state_s){ .tag = Blake2S_s, { .case_Blake2S_s = buf } });
        break;
      }
    case Hacl_Agile_Hash_Blake2S_128:
      {
        #if HACL_CAN_COMPILE_VEC128
        s =
          (
            (Hacl_Agile_Hash_state_s){
              .tag = Blake2S_128_s,
              { .case_Blake2S_128_s = Hacl_Hash_Blake2s_Simd128_malloc_with_key() }
            }
          );
        #else
        s = FStar_Pervasives_false_elim__Hacl_Agile_Hash_state_s();
        #endif
        break;
      }
    case Hacl_Agile_Hash_Blake2B_32:
      {
        uint64_t *buf = (uint64_t *)KRML_HOST_CALLOC(16U, sizeof (uint64_t));
        s = ((Hacl_Agile_Hash_state_s){ .tag = Blake2B_s, { .case_Blake2B_s = buf } });
        break;
      }
    case Hacl_Agile_Hash_Blake2B_256:
      {
        #if HACL_CAN_COMPILE_VEC256
        s =
          (
            (Hacl_Agile_Hash_state_s){
              .tag = Blake2B_256_s,
              { .case_Blake2B_256_s = Hacl_Hash_Blake2b_Simd256_malloc_with_key() }
            }
          );
        #else
        s = FStar_Pervasives_false_elim__Hacl_Agile_Hash_state_s();
        #endif
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  Hacl_Agile_Hash_state_s
  *buf = (Hacl_Agile_Hash_state_s *)KRML_HOST_MALLOC(sizeof (Hacl_Agile_Hash_state_s));
  buf[0U] = s;
  return buf;
}

static void init(Hacl_Agile_Hash_state_s *s)
{
  Hacl_Agile_Hash_state_s scrut = *s;
  if (scrut.tag == MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    Hacl_Hash_MD5_init(p1);
    return;
  }
  if (scrut.tag == SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    Hacl_Hash_SHA1_init(p1);
    return;
  }
  if (scrut.tag == SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    Hacl_Hash_SHA2_sha224_init(p1);
    return;
  }
  if (scrut.tag == SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    Hacl_Hash_SHA2_sha256_init(p1);
    return;
  }
  if (scrut.tag == SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    Hacl_Hash_SHA2_sha384_init(p1);
    return;
  }
  if (scrut.tag == SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    Hacl_Hash_SHA2_sha512_init(p1);
    return;
  }
  if (scrut.tag == SHA3_224_s)
  {
    uint64_t *p1 = scrut.case_SHA3_224_s;
    memset(p1, 0U, 25U * sizeof (uint64_t));
    return;
  }
  if (scrut.tag == SHA3_256_s)
  {
    uint64_t *p1 = scrut.case_SHA3_256_s;
    memset(p1, 0U, 25U * sizeof (uint64_t));
    return;
  }
  if (scrut.tag == SHA3_384_s)
  {
    uint64_t *p1 = scrut.case_SHA3_384_s;
    memset(p1, 0U, 25U * sizeof (uint64_t));
    return;
  }
  if (scrut.tag == SHA3_512_s)
  {
    uint64_t *p1 = scrut.case_SHA3_512_s;
    memset(p1, 0U, 25U * sizeof (uint64_t));
    return;
  }
  if (scrut.tag == Blake2S_s)
  {
    uint32_t *p1 = scrut.case_Blake2S_s;
    Hacl_Hash_Blake2s_init(p1, 0U, 32U);
    return;
  }
  if (scrut.tag == Blake2S_128_s)
  {
    Lib_IntVector_Intrinsics_vec128 *p1 = scrut.case_Blake2S_128_s;
    #if HACL_CAN_COMPILE_VEC128
    Hacl_Hash_Blake2s_Simd128_init(p1, 0U, 32U);
    return;
    #else
    KRML_MAYBE_UNUSED_VAR(p1);
    return;
    #endif
  }
  if (scrut.tag == Blake2B_s)
  {
    uint64_t *p1 = scrut.case_Blake2B_s;
    Hacl_Hash_Blake2b_init(p1, 0U, 64U);
    return;
  }
  if (scrut.tag == Blake2B_256_s)
  {
    Lib_IntVector_Intrinsics_vec256 *p1 = scrut.case_Blake2B_256_s;
    #if HACL_CAN_COMPILE_VEC256
    Hacl_Hash_Blake2b_Simd256_init(p1, 0U, 64U);
    return;
    #else
    KRML_MAYBE_UNUSED_VAR(p1);
    return;
    #endif
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

static void
update_multi(Hacl_Agile_Hash_state_s *s, uint64_t prevlen, uint8_t *blocks, uint32_t len)
{
  Hacl_Agile_Hash_state_s scrut = *s;
  if (scrut.tag == MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    uint32_t n = len / 64U;
    Hacl_Hash_MD5_update_multi(p1, blocks, n);
    return;
  }
  if (scrut.tag == SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    uint32_t n = len / 64U;
    Hacl_Hash_SHA1_update_multi(p1, blocks, n);
    return;
  }
  if (scrut.tag == SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    uint32_t n = len / 64U;
    Hacl_Hash_SHA2_sha224_update_nblocks(n * 64U, blocks, p1);
    return;
  }
  if (scrut.tag == SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    uint32_t n = len / 64U;
    Hacl_Hash_SHA2_sha256_update_nblocks(n * 64U, blocks, p1);
    return;
  }
  if (scrut.tag == SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    uint32_t n = len / 128U;
    Hacl_Hash_SHA2_sha384_update_nblocks(n * 128U, blocks, p1);
    return;
  }
  if (scrut.tag == SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    uint32_t n = len / 128U;
    Hacl_Hash_SHA2_sha512_update_nblocks(n * 128U, blocks, p1);
    return;
  }
  if (scrut.tag == SHA3_224_s)
  {
    uint64_t *p1 = scrut.case_SHA3_224_s;
    uint32_t n = len / 144U;
    Hacl_Hash_SHA3_update_multi_sha3(Spec_Hash_Definitions_SHA3_224, p1, blocks, n);
    return;
  }
  if (scrut.tag == SHA3_256_s)
  {
    uint64_t *p1 = scrut.case_SHA3_256_s;
    uint32_t n = len / 136U;
    Hacl_Hash_SHA3_update_multi_sha3(Spec_Hash_Definitions_SHA3_256, p1, blocks, n);
    return;
  }
  if (scrut.tag == SHA3_384_s)
  {
    uint64_t *p1 = scrut.case_SHA3_384_s;
    uint32_t n = len / 104U;
    Hacl_Hash_SHA3_update_multi_sha3(Spec_Hash_Definitions_SHA3_384, p1, blocks, n);
    return;
  }
  if (scrut.tag == SHA3_512_s)
  {
    uint64_t *p1 = scrut.case_SHA3_512_s;
    uint32_t n = len / 72U;
    Hacl_Hash_SHA3_update_multi_sha3(Spec_Hash_Definitions_SHA3_512, p1, blocks, n);
    return;
  }
  if (scrut.tag == Blake2S_s)
  {
    uint32_t *p1 = scrut.case_Blake2S_s;
    uint32_t n = len / 64U;
    uint32_t wv[16U] = { 0U };
    Hacl_Hash_Blake2s_update_multi(n * 64U, wv, p1, prevlen, blocks, n);
    return;
  }
  if (scrut.tag == Blake2S_128_s)
  {
    Lib_IntVector_Intrinsics_vec128 *p1 = scrut.case_Blake2S_128_s;
    #if HACL_CAN_COMPILE_VEC128
    uint32_t n = len / 64U;
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 wv[4U] KRML_POST_ALIGN(16) = { 0U };
    Hacl_Hash_Blake2s_Simd128_update_multi(n * 64U, wv, p1, prevlen, blocks, n);
    return;
    #else
    KRML_MAYBE_UNUSED_VAR(p1);
    return;
    #endif
  }
  if (scrut.tag == Blake2B_s)
  {
    uint64_t *p1 = scrut.case_Blake2B_s;
    uint32_t n = len / 128U;
    uint64_t wv[16U] = { 0U };
    Hacl_Hash_Blake2b_update_multi(n * 128U,
      wv,
      p1,
      FStar_UInt128_uint64_to_uint128(prevlen),
      blocks,
      n);
    return;
  }
  if (scrut.tag == Blake2B_256_s)
  {
    Lib_IntVector_Intrinsics_vec256 *p1 = scrut.case_Blake2B_256_s;
    #if HACL_CAN_COMPILE_VEC256
    uint32_t n = len / 128U;
    KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 wv[4U] KRML_POST_ALIGN(32) = { 0U };
    Hacl_Hash_Blake2b_Simd256_update_multi(n * 128U,
      wv,
      p1,
      FStar_UInt128_uint64_to_uint128(prevlen),
      blocks,
      n);
    return;
    #else
    KRML_MAYBE_UNUSED_VAR(p1);
    return;
    #endif
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

static void free_(Hacl_Agile_Hash_state_s *s)
{
  Hacl_Agile_Hash_state_s scrut = *s;
  if (scrut.tag == MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == SHA3_224_s)
  {
    uint64_t *p1 = scrut.case_SHA3_224_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == SHA3_256_s)
  {
    uint64_t *p1 = scrut.case_SHA3_256_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == SHA3_384_s)
  {
    uint64_t *p1 = scrut.case_SHA3_384_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == SHA3_512_s)
  {
    uint64_t *p1 = scrut.case_SHA3_512_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == Blake2S_s)
  {
    uint32_t *p1 = scrut.case_Blake2S_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == Blake2S_128_s)
  {
    Lib_IntVector_Intrinsics_vec128 *p1 = scrut.case_Blake2S_128_s;
    KRML_ALIGNED_FREE(p1);
  }
  else if (scrut.tag == Blake2B_s)
  {
    uint64_t *p1 = scrut.case_Blake2B_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == Blake2B_256_s)
  {
    Lib_IntVector_Intrinsics_vec256 *p1 = scrut.case_Blake2B_256_s;
    KRML_ALIGNED_FREE(p1);
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
  KRML_HOST_FREE(s);
}

static void hash(Hacl_Agile_Hash_impl i, uint8_t *dst, uint8_t *input, uint32_t input_len)
{
  switch (i)
  {
    case Hacl_Agile_Hash_MD5:
      {
        Hacl_Hash_MD5_hash_oneshot(dst, input, input_len);
        break;
      }
    case Hacl_Agile_Hash_SHA1:
      {
        Hacl_Hash_SHA1_hash_oneshot(dst, input, input_len);
        break;
      }
    case Hacl_Agile_Hash_SHA2_224:
      {
        Hacl_Hash_SHA2_hash_224(dst, input, input_len);
        break;
      }
    case Hacl_Agile_Hash_SHA2_256:
      {
        Hacl_Hash_SHA2_hash_256(dst, input, input_len);
        break;
      }
    case Hacl_Agile_Hash_SHA2_384:
      {
        Hacl_Hash_SHA2_hash_384(dst, input, input_len);
        break;
      }
    case Hacl_Agile_Hash_SHA2_512:
      {
        Hacl_Hash_SHA2_hash_512(dst, input, input_len);
        break;
      }
    case Hacl_Agile_Hash_SHA3_224:
      {
        Hacl_Hash_SHA3_sha3_224(dst, input, input_len);
        break;
      }
    case Hacl_Agile_Hash_SHA3_256:
      {
        Hacl_Hash_SHA3_sha3_256(dst, input, input_len);
        break;
      }
    case Hacl_Agile_Hash_SHA3_384:
      {
        Hacl_Hash_SHA3_sha3_384(dst, input, input_len);
        break;
      }
    case Hacl_Agile_Hash_SHA3_512:
      {
        Hacl_Hash_SHA3_sha3_512(dst, input, input_len);
        break;
      }
    case Hacl_Agile_Hash_Blake2S_32:
      {
        Hacl_Hash_Blake2s_hash_with_key(dst, 32U, input, input_len, NULL, 0U);
        break;
      }
    case Hacl_Agile_Hash_Blake2S_128:
      {
        #if HACL_CAN_COMPILE_VEC128
        Hacl_Hash_Blake2s_Simd128_hash_with_key(dst, 32U, input, input_len, NULL, 0U);
        #endif
        break;
      }
    case Hacl_Agile_Hash_Blake2B_32:
      {
        Hacl_Hash_Blake2b_hash_with_key(dst, 64U, input, input_len, NULL, 0U);
        break;
      }
    case Hacl_Agile_Hash_Blake2B_256:
      {
        #if HACL_CAN_COMPILE_VEC256
        Hacl_Hash_Blake2b_Simd256_hash_with_key(dst, 64U, input, input_len, NULL, 0U);
        #endif
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static uint32_t block_len(Spec_Hash_Definitions_hash_alg a)
{
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        return 64U;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        return 64U;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        return 64U;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        return 64U;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        return 128U;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        return 128U;
      }
    case Spec_Hash_Definitions_SHA3_224:
      {
        return 144U;
      }
    case Spec_Hash_Definitions_SHA3_256:
      {
        return 136U;
      }
    case Spec_Hash_Definitions_SHA3_384:
      {
        return 104U;
      }
    case Spec_Hash_Definitions_SHA3_512:
      {
        return 72U;
      }
    case Spec_Hash_Definitions_Shake128:
      {
        return 168U;
      }
    case Spec_Hash_Definitions_Shake256:
      {
        return 136U;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        return 64U;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        return 128U;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static uint64_t max_input_len64(Spec_Hash_Definitions_hash_alg a)
{
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        return 2305843009213693951ULL;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        return 2305843009213693951ULL;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        return 2305843009213693951ULL;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        return 2305843009213693951ULL;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        return 18446744073709551615ULL;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        return 18446744073709551615ULL;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        return 18446744073709551615ULL;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        return 18446744073709551615ULL;
      }
    case Spec_Hash_Definitions_SHA3_224:
      {
        return 18446744073709551615ULL;
      }
    case Spec_Hash_Definitions_SHA3_256:
      {
        return 18446744073709551615ULL;
      }
    case Spec_Hash_Definitions_SHA3_384:
      {
        return 18446744073709551615ULL;
      }
    case Spec_Hash_Definitions_SHA3_512:
      {
        return 18446744073709551615ULL;
      }
    case Spec_Hash_Definitions_Shake128:
      {
        return 18446744073709551615ULL;
      }
    case Spec_Hash_Definitions_Shake256:
      {
        return 18446744073709551615ULL;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static Hacl_Streaming_HMAC_Definitions_index
index_of_state(Hacl_Agile_Hash_state_s *s, Hacl_Streaming_HMAC_Definitions_key_and_len k)
{
  Hacl_Streaming_HMAC_Definitions_key_and_len k1 = k;
  uint32_t kl = k1.snd;
  Hacl_Agile_Hash_impl i1 = impl_of_state(s);
  return ((Hacl_Streaming_HMAC_Definitions_index){ .fst = i1, .snd = kl });
}

static void wrap_key(Hacl_Agile_Hash_impl impl, uint8_t *output, uint8_t *key, uint32_t len)
{
  uint8_t *nkey = output;
  uint32_t sw;
  switch (alg_of_impl(impl))
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw = 64U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw = 64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw = 64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw = 64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw = 128U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw = 128U;
        break;
      }
    case Spec_Hash_Definitions_SHA3_224:
      {
        sw = 144U;
        break;
      }
    case Spec_Hash_Definitions_SHA3_256:
      {
        sw = 136U;
        break;
      }
    case Spec_Hash_Definitions_SHA3_384:
      {
        sw = 104U;
        break;
      }
    case Spec_Hash_Definitions_SHA3_512:
      {
        sw = 72U;
        break;
      }
    case Spec_Hash_Definitions_Shake128:
      {
        sw = 168U;
        break;
      }
    case Spec_Hash_Definitions_Shake256:
      {
        sw = 136U;
        break;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        sw = 64U;
        break;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        sw = 128U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t ite;
  if (len <= sw)
  {
    ite = len;
  }
  else
  {
    switch (alg_of_impl(impl))
    {
      case Spec_Hash_Definitions_MD5:
        {
          ite = 16U;
          break;
        }
      case Spec_Hash_Definitions_SHA1:
        {
          ite = 20U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_224:
        {
          ite = 28U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_256:
        {
          ite = 32U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_384:
        {
          ite = 48U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_512:
        {
          ite = 64U;
          break;
        }
      case Spec_Hash_Definitions_Blake2S:
        {
          ite = 32U;
          break;
        }
      case Spec_Hash_Definitions_Blake2B:
        {
          ite = 64U;
          break;
        }
      case Spec_Hash_Definitions_SHA3_224:
        {
          ite = 28U;
          break;
        }
      case Spec_Hash_Definitions_SHA3_256:
        {
          ite = 32U;
          break;
        }
      case Spec_Hash_Definitions_SHA3_384:
        {
          ite = 48U;
          break;
        }
      case Spec_Hash_Definitions_SHA3_512:
        {
          ite = 64U;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
  }
  uint8_t *zeroes = output + ite;
  KRML_MAYBE_UNUSED_VAR(zeroes);
  if (len <= block_len(alg_of_impl(impl)))
  {
    if (len > 0U)
    {
      memcpy(nkey, key, len * sizeof (uint8_t));
      return;
    }
    return;
  }
  hash(impl, nkey, key, len);
}

static void
init0(Hacl_Streaming_HMAC_Definitions_key_and_len k, uint8_t *buf, Hacl_Agile_Hash_state_s *s)
{
  init(s);
  Hacl_Agile_Hash_impl i1 = impl_of_state(s);
  Spec_Hash_Definitions_hash_alg a = alg_of_impl(i1);
  uint8_t b[168U] = { 0U };
  uint8_t *block = b;
  uint8_t *k1 = k.fst;
  uint32_t k_len = k.snd;
  wrap_key(i1, block, k1, k_len);
  uint8_t b0[168U];
  memset(b0, 0x36U, 168U * sizeof (uint8_t));
  uint8_t *ipad = b0;
  for (uint32_t i = 0U; i < block_len(a); i++)
  {
    uint8_t xi = ipad[i];
    uint8_t yi = block[i];
    buf[i] = (uint32_t)xi ^ (uint32_t)yi;
  }
}

static Hacl_Agile_Hash_impl
__proj__Mkdtuple2__item___1__Hacl_Agile_Hash_impl_uint32_t(
  Hacl_Streaming_HMAC_Definitions_index pair
)
{
  return pair.fst;
}

static Hacl_Agile_Hash_impl
dfst__Hacl_Agile_Hash_impl_uint32_t(Hacl_Streaming_HMAC_Definitions_index t)
{
  return __proj__Mkdtuple2__item___1__Hacl_Agile_Hash_impl_uint32_t(t);
}

static uint32_t
__proj__Mkdtuple2__item___2__Hacl_Agile_Hash_impl_uint32_t(
  Hacl_Streaming_HMAC_Definitions_index pair
)
{
  return pair.snd;
}

static uint32_t dsnd__Hacl_Agile_Hash_impl_uint32_t(Hacl_Streaming_HMAC_Definitions_index t)
{
  return __proj__Mkdtuple2__item___2__Hacl_Agile_Hash_impl_uint32_t(t);
}

Hacl_Streaming_HMAC_agile_state
*Hacl_Streaming_HMAC_malloc(
  Hacl_Streaming_HMAC_Definitions_index i,
  Hacl_Streaming_HMAC_Definitions_key_and_len key
)
{
  KRML_CHECK_SIZE(sizeof (uint8_t),
    block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i))));
  uint8_t
  *buf0 =
    (uint8_t *)KRML_HOST_CALLOC(block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i))),
      sizeof (uint8_t));
  Hacl_Agile_Hash_state_s *block_state = create_in(dfst__Hacl_Agile_Hash_impl_uint32_t(i));
  uint8_t *uu____0;
  if (dsnd__Hacl_Agile_Hash_impl_uint32_t(i) == 0U)
  {
    uu____0 = NULL;
  }
  else
  {
    KRML_CHECK_SIZE(sizeof (uint8_t), dsnd__Hacl_Agile_Hash_impl_uint32_t(i));
    uint8_t
    *buf = (uint8_t *)KRML_HOST_CALLOC(dsnd__Hacl_Agile_Hash_impl_uint32_t(i), sizeof (uint8_t));
    uu____0 = buf;
  }
  Hacl_Streaming_HMAC_Definitions_key_and_len
  k_ = { .fst = uu____0, .snd = dsnd__Hacl_Agile_Hash_impl_uint32_t(i) };
  uint8_t *k_src = key.fst;
  uint32_t l_src = key.snd;
  uint8_t *k_dst = k_.fst;
  if (l_src != 0U)
  {
    memcpy(k_dst, k_src, l_src * sizeof (uint8_t));
  }
  Hacl_Streaming_HMAC_Definitions_key_and_len k_0 = k_;
  Hacl_Streaming_HMAC_agile_state
  s =
    {
      .block_state = block_state,
      .buf = buf0,
      .total_len = (uint64_t)block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i))),
      .p_key = k_0
    };
  Hacl_Streaming_HMAC_agile_state
  *p =
    (Hacl_Streaming_HMAC_agile_state *)KRML_HOST_MALLOC(sizeof (Hacl_Streaming_HMAC_agile_state));
  p[0U] = s;
  init0(key, buf0, block_state);
  return p;
}

void
Hacl_Streaming_HMAC_reset(
  Hacl_Streaming_HMAC_agile_state *state,
  Hacl_Streaming_HMAC_Definitions_key_and_len key
)
{
  Hacl_Streaming_HMAC_agile_state scrut = *state;
  Hacl_Streaming_HMAC_Definitions_key_and_len k_ = scrut.p_key;
  uint8_t *buf = scrut.buf;
  Hacl_Agile_Hash_state_s *block_state = scrut.block_state;
  Hacl_Streaming_HMAC_Definitions_index i1 = index_of_state(block_state, k_);
  KRML_MAYBE_UNUSED_VAR(i1);
  init0(key, buf, block_state);
  uint8_t *k_src = key.fst;
  uint32_t l_src = key.snd;
  uint8_t *k_dst = k_.fst;
  if (l_src != 0U)
  {
    memcpy(k_dst, k_src, l_src * sizeof (uint8_t));
  }
  Hacl_Streaming_HMAC_Definitions_key_and_len k_1 = k_;
  Hacl_Streaming_HMAC_agile_state
  tmp =
    {
      .block_state = block_state,
      .buf = buf,
      .total_len = (uint64_t)block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1))),
      .p_key = k_1
    };
  state[0U] = tmp;
}

Hacl_Streaming_Types_error_code
Hacl_Streaming_HMAC_update(
  Hacl_Streaming_HMAC_agile_state *state,
  uint8_t *chunk,
  uint32_t chunk_len
)
{
  Hacl_Streaming_HMAC_agile_state s = *state;
  Hacl_Agile_Hash_state_s *block_state = s.block_state;
  uint64_t total_len = s.total_len;
  Hacl_Streaming_HMAC_Definitions_key_and_len k_ = s.p_key;
  Hacl_Streaming_HMAC_Definitions_index i1 = index_of_state(block_state, k_);
  if
  (
    (uint64_t)chunk_len
    > max_input_len64(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1))) - total_len
  )
  {
    return Hacl_Streaming_Types_MaximumLengthExceeded;
  }
  uint32_t sz;
  if
  (
    total_len
    % (uint64_t)block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1)))
    == 0ULL
    && total_len > 0ULL
  )
  {
    sz = block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1)));
  }
  else
  {
    sz =
      (uint32_t)(total_len
      % (uint64_t)block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1))));
  }
  if (chunk_len <= block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1))) - sz)
  {
    Hacl_Streaming_HMAC_agile_state s1 = *state;
    Hacl_Agile_Hash_state_s *block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    Hacl_Streaming_HMAC_Definitions_key_and_len k_1 = s1.p_key;
    uint32_t sz1;
    if
    (
      total_len1
      % (uint64_t)block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1)))
      == 0ULL
      && total_len1 > 0ULL
    )
    {
      sz1 = block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1)));
    }
    else
    {
      sz1 =
        (uint32_t)(total_len1
        % (uint64_t)block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1))));
    }
    uint8_t *buf2 = buf + sz1;
    memcpy(buf2, chunk, chunk_len * sizeof (uint8_t));
    uint64_t total_len2 = total_len1 + (uint64_t)chunk_len;
    *state
    =
      (
        (Hacl_Streaming_HMAC_agile_state){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len2,
          .p_key = k_1
        }
      );
  }
  else if (sz == 0U)
  {
    Hacl_Streaming_HMAC_agile_state s1 = *state;
    Hacl_Agile_Hash_state_s *block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    Hacl_Streaming_HMAC_Definitions_key_and_len k_1 = s1.p_key;
    uint32_t sz1;
    if
    (
      total_len1
      % (uint64_t)block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1)))
      == 0ULL
      && total_len1 > 0ULL
    )
    {
      sz1 = block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1)));
    }
    else
    {
      sz1 =
        (uint32_t)(total_len1
        % (uint64_t)block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1))));
    }
    if (!(sz1 == 0U))
    {
      uint64_t prevlen = total_len1 - (uint64_t)sz1;
      update_multi(block_state1,
        prevlen,
        buf,
        block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1))));
    }
    uint32_t ite;
    if
    (
      (uint64_t)chunk_len
      % (uint64_t)block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1)))
      == 0ULL
      && (uint64_t)chunk_len > 0ULL
    )
    {
      ite = block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1)));
    }
    else
    {
      ite =
        (uint32_t)((uint64_t)chunk_len
        % (uint64_t)block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1))));
    }
    uint32_t
    n_blocks = (chunk_len - ite) / block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1)));
    uint32_t
    data1_len = n_blocks * block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1)));
    uint32_t data2_len = chunk_len - data1_len;
    uint8_t *data1 = chunk;
    uint8_t *data2 = chunk + data1_len;
    update_multi(block_state1, total_len1, data1, data1_len);
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *state
    =
      (
        (Hacl_Streaming_HMAC_agile_state){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)chunk_len,
          .p_key = k_1
        }
      );
  }
  else
  {
    uint32_t diff = block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1))) - sz;
    uint8_t *chunk1 = chunk;
    uint8_t *chunk2 = chunk + diff;
    Hacl_Streaming_HMAC_agile_state s1 = *state;
    Hacl_Agile_Hash_state_s *block_state10 = s1.block_state;
    uint8_t *buf0 = s1.buf;
    uint64_t total_len10 = s1.total_len;
    Hacl_Streaming_HMAC_Definitions_key_and_len k_1 = s1.p_key;
    uint32_t sz10;
    if
    (
      total_len10
      % (uint64_t)block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1)))
      == 0ULL
      && total_len10 > 0ULL
    )
    {
      sz10 = block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1)));
    }
    else
    {
      sz10 =
        (uint32_t)(total_len10
        % (uint64_t)block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1))));
    }
    uint8_t *buf2 = buf0 + sz10;
    memcpy(buf2, chunk1, diff * sizeof (uint8_t));
    uint64_t total_len2 = total_len10 + (uint64_t)diff;
    *state
    =
      (
        (Hacl_Streaming_HMAC_agile_state){
          .block_state = block_state10,
          .buf = buf0,
          .total_len = total_len2,
          .p_key = k_1
        }
      );
    Hacl_Streaming_HMAC_agile_state s10 = *state;
    Hacl_Agile_Hash_state_s *block_state1 = s10.block_state;
    uint8_t *buf = s10.buf;
    uint64_t total_len1 = s10.total_len;
    Hacl_Streaming_HMAC_Definitions_key_and_len k_10 = s10.p_key;
    uint32_t sz1;
    if
    (
      total_len1
      % (uint64_t)block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1)))
      == 0ULL
      && total_len1 > 0ULL
    )
    {
      sz1 = block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1)));
    }
    else
    {
      sz1 =
        (uint32_t)(total_len1
        % (uint64_t)block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1))));
    }
    if (!(sz1 == 0U))
    {
      uint64_t prevlen = total_len1 - (uint64_t)sz1;
      update_multi(block_state1,
        prevlen,
        buf,
        block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1))));
    }
    uint32_t ite;
    if
    (
      (uint64_t)(chunk_len - diff)
      % (uint64_t)block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1)))
      == 0ULL
      && (uint64_t)(chunk_len - diff) > 0ULL
    )
    {
      ite = block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1)));
    }
    else
    {
      ite =
        (uint32_t)((uint64_t)(chunk_len - diff)
        % (uint64_t)block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1))));
    }
    uint32_t
    n_blocks =
      (chunk_len - diff - ite)
      / block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1)));
    uint32_t
    data1_len = n_blocks * block_len(alg_of_impl(dfst__Hacl_Agile_Hash_impl_uint32_t(i1)));
    uint32_t data2_len = chunk_len - diff - data1_len;
    uint8_t *data1 = chunk2;
    uint8_t *data2 = chunk2 + data1_len;
    update_multi(block_state1, total_len1, data1, data1_len);
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *state
    =
      (
        (Hacl_Streaming_HMAC_agile_state){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)(chunk_len - diff),
          .p_key = k_10
        }
      );
  }
  return Hacl_Streaming_Types_Success;
}

void Hacl_Streaming_HMAC_free(Hacl_Streaming_HMAC_agile_state *state)
{
  Hacl_Streaming_HMAC_agile_state scrut = *state;
  Hacl_Streaming_HMAC_Definitions_key_and_len k_ = scrut.p_key;
  uint8_t *buf = scrut.buf;
  Hacl_Agile_Hash_state_s *block_state = scrut.block_state;
  uint8_t *k = k_.fst;
  uint32_t l = k_.snd;
  if (l != 0U)
  {
    KRML_HOST_FREE(k);
  }
  free_(block_state);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(state);
}

