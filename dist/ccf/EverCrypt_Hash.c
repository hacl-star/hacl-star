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


#include "EverCrypt_Hash.h"

C_String_t EverCrypt_Hash_string_of_alg(Spec_Hash_Definitions_hash_alg uu___0_6)
{
  switch (uu___0_6)
  {
    case Spec_Hash_Definitions_MD5:
      {
        return "MD5";
      }
    case Spec_Hash_Definitions_SHA1:
      {
        return "SHA1";
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        return "SHA2_224";
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        return "SHA2_256";
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        return "SHA2_384";
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        return "SHA2_512";
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

bool
EverCrypt_Hash_uu___is_MD5_s(
  Spec_Hash_Definitions_hash_alg uu____151,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_MD5_s)
  {
    return true;
  }
  return false;
}

uint32_t
*EverCrypt_Hash___proj__MD5_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____179,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_MD5_s)
  {
    return projectee.case_MD5_s;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

bool
EverCrypt_Hash_uu___is_SHA1_s(
  Spec_Hash_Definitions_hash_alg uu____202,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA1_s)
  {
    return true;
  }
  return false;
}

uint32_t
*EverCrypt_Hash___proj__SHA1_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____230,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA1_s)
  {
    return projectee.case_SHA1_s;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

bool
EverCrypt_Hash_uu___is_SHA2_224_s(
  Spec_Hash_Definitions_hash_alg uu____253,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_224_s)
  {
    return true;
  }
  return false;
}

uint32_t
*EverCrypt_Hash___proj__SHA2_224_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____281,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_224_s)
  {
    return projectee.case_SHA2_224_s;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

bool
EverCrypt_Hash_uu___is_SHA2_256_s(
  Spec_Hash_Definitions_hash_alg uu____304,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_256_s)
  {
    return true;
  }
  return false;
}

uint32_t
*EverCrypt_Hash___proj__SHA2_256_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____332,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_256_s)
  {
    return projectee.case_SHA2_256_s;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

bool
EverCrypt_Hash_uu___is_SHA2_384_s(
  Spec_Hash_Definitions_hash_alg uu____355,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_384_s)
  {
    return true;
  }
  return false;
}

uint64_t
*EverCrypt_Hash___proj__SHA2_384_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____383,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_384_s)
  {
    return projectee.case_SHA2_384_s;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

bool
EverCrypt_Hash_uu___is_SHA2_512_s(
  Spec_Hash_Definitions_hash_alg uu____406,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_512_s)
  {
    return true;
  }
  return false;
}

uint64_t
*EverCrypt_Hash___proj__SHA2_512_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____434,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_512_s)
  {
    return projectee.case_SHA2_512_s;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

Spec_Hash_Definitions_hash_alg EverCrypt_Hash_alg_of_state(EverCrypt_Hash_state_s *s)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    return Spec_Hash_Definitions_MD5;
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    return Spec_Hash_Definitions_SHA1;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    return Spec_Hash_Definitions_SHA2_224;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    return Spec_Hash_Definitions_SHA2_256;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    return Spec_Hash_Definitions_SHA2_384;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    return Spec_Hash_Definitions_SHA2_512;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

EverCrypt_Hash_state_s *EverCrypt_Hash_create_in(Spec_Hash_Definitions_hash_alg a)
{
  EverCrypt_Hash_state_s s;
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        uint32_t *buf = KRML_HOST_CALLOC((uint32_t)4U, sizeof (uint32_t));
        s = ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_MD5_s, { .case_MD5_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        uint32_t *buf = KRML_HOST_CALLOC((uint32_t)5U, sizeof (uint32_t));
        s = ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_SHA1_s, { .case_SHA1_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        uint32_t *buf = KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint32_t));
        s =
          ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_SHA2_224_s, { .case_SHA2_224_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        uint32_t *buf = KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint32_t));
        s =
          ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_SHA2_256_s, { .case_SHA2_256_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        uint64_t *buf = KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint64_t));
        s =
          ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_SHA2_384_s, { .case_SHA2_384_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        uint64_t *buf = KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint64_t));
        s =
          ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_SHA2_512_s, { .case_SHA2_512_s = buf } });
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  KRML_CHECK_SIZE(sizeof (EverCrypt_Hash_state_s), (uint32_t)1U);
  EverCrypt_Hash_state_s *buf = KRML_HOST_MALLOC(sizeof (EverCrypt_Hash_state_s));
  buf[0U] = s;
  return buf;
}

EverCrypt_Hash_state_s *EverCrypt_Hash_create(Spec_Hash_Definitions_hash_alg a)
{
  return EverCrypt_Hash_create_in(a);
}

void EverCrypt_Hash_init(EverCrypt_Hash_state_s *s)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    Hacl_Hash_Core_MD5_legacy_init(p1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    Hacl_Hash_Core_SHA1_legacy_init(p1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    Hacl_Hash_Core_SHA2_init_224(p1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    Hacl_Hash_Core_SHA2_init_256(p1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    Hacl_Hash_Core_SHA2_init_384(p1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    Hacl_Hash_Core_SHA2_init_512(p1);
    return;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

void EverCrypt_Hash_update_multi_256(uint32_t *s, uint8_t *blocks, uint32_t n1)
{
  bool has_shaext1 = EverCrypt_AutoConfig2_has_shaext();
  bool has_sse1 = EverCrypt_AutoConfig2_has_sse();
  if (true && has_shaext1 && has_sse1)
  {
    uint64_t n2 = (uint64_t)n1;
    uint64_t scrut = sha256_update(s, blocks, n2, Hacl_Hash_Core_SHA2_Constants_k224_256);
    return;
  }
  Hacl_Hash_SHA2_update_multi_256(s, blocks, n1);
}

void EverCrypt_Hash_update(EverCrypt_Hash_state_s *s, uint8_t *block1)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    Hacl_Hash_Core_MD5_legacy_update(p1, block1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    Hacl_Hash_Core_SHA1_legacy_update(p1, block1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    EverCrypt_Hash_update_multi_256(p1, block1, (uint32_t)1U);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    EverCrypt_Hash_update_multi_256(p1, block1, (uint32_t)1U);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    Hacl_Hash_Core_SHA2_update_384(p1, block1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    Hacl_Hash_Core_SHA2_update_512(p1, block1);
    return;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

void EverCrypt_Hash_update_multi(EverCrypt_Hash_state_s *s, uint8_t *blocks, uint32_t len)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    uint32_t n1 = len / (uint32_t)64U;
    Hacl_Hash_MD5_legacy_update_multi(p1, blocks, n1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    uint32_t n1 = len / (uint32_t)64U;
    Hacl_Hash_SHA1_legacy_update_multi(p1, blocks, n1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    uint32_t n1 = len / (uint32_t)64U;
    EverCrypt_Hash_update_multi_256(p1, blocks, n1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    uint32_t n1 = len / (uint32_t)64U;
    EverCrypt_Hash_update_multi_256(p1, blocks, n1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    uint32_t n1 = len / (uint32_t)128U;
    Hacl_Hash_SHA2_update_multi_384(p1, blocks, n1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    uint32_t n1 = len / (uint32_t)128U;
    Hacl_Hash_SHA2_update_multi_512(p1, blocks, n1);
    return;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

void
EverCrypt_Hash_update_last_256(
  uint32_t *s,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
)
{
  uint32_t blocks_n = input_len / (uint32_t)64U;
  uint32_t blocks_len = blocks_n * (uint32_t)64U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  EverCrypt_Hash_update_multi_256(s, blocks, blocks_n);
  uint64_t total_input_len = prev_len + (uint64_t)input_len;
  uint32_t
  pad_len1 =
    (uint32_t)1U
    +
      ((uint32_t)128U - ((uint32_t)9U + (uint32_t)(total_input_len % (uint64_t)(uint32_t)64U)))
      % (uint32_t)64U
    + (uint32_t)8U;
  uint32_t tmp_len = rest_len + pad_len1;
  uint8_t tmp_twoblocks[128U] = { 0U };
  uint8_t *tmp = tmp_twoblocks;
  uint8_t *tmp_rest = tmp;
  uint8_t *tmp_pad = tmp + rest_len;
  memcpy(tmp_rest, rest, rest_len * sizeof rest[0U]);
  Hacl_Hash_Core_SHA2_pad_256(total_input_len, tmp_pad);
  EverCrypt_Hash_update_multi_256(s, tmp, tmp_len / (uint32_t)64U);
}

void EverCrypt_Hash_update_last(EverCrypt_Hash_state_s *s, uint8_t *last1, uint64_t total_len)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    uint64_t input_len = total_len % (uint64_t)(uint32_t)64U;
    uint64_t prev_len = total_len - input_len;
    Hacl_Hash_MD5_legacy_update_last(p1, prev_len, last1, (uint32_t)input_len);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    uint64_t input_len = total_len % (uint64_t)(uint32_t)64U;
    uint64_t prev_len = total_len - input_len;
    Hacl_Hash_SHA1_legacy_update_last(p1, prev_len, last1, (uint32_t)input_len);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    uint64_t input_len = total_len % (uint64_t)(uint32_t)64U;
    uint64_t prev_len = total_len - input_len;
    EverCrypt_Hash_update_last_256(p1, prev_len, last1, (uint32_t)input_len);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    uint64_t input_len = total_len % (uint64_t)(uint32_t)64U;
    uint64_t prev_len = total_len - input_len;
    EverCrypt_Hash_update_last_256(p1, prev_len, last1, (uint32_t)input_len);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    uint64_t input_len = total_len % (uint64_t)(uint32_t)128U;
    uint128_t prev_len = (uint128_t)(total_len - input_len);
    Hacl_Hash_SHA2_update_last_384(p1, prev_len, last1, (uint32_t)input_len);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    uint64_t input_len = total_len % (uint64_t)(uint32_t)128U;
    uint128_t prev_len = (uint128_t)(total_len - input_len);
    Hacl_Hash_SHA2_update_last_512(p1, prev_len, last1, (uint32_t)input_len);
    return;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

void EverCrypt_Hash_finish(EverCrypt_Hash_state_s *s, uint8_t *dst)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    Hacl_Hash_Core_MD5_legacy_finish(p1, dst);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    Hacl_Hash_Core_SHA1_legacy_finish(p1, dst);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    Hacl_Hash_Core_SHA2_finish_224(p1, dst);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    Hacl_Hash_Core_SHA2_finish_256(p1, dst);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    Hacl_Hash_Core_SHA2_finish_384(p1, dst);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    Hacl_Hash_Core_SHA2_finish_512(p1, dst);
    return;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

void EverCrypt_Hash_free(EverCrypt_Hash_state_s *s)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    KRML_HOST_FREE(p1);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
  KRML_HOST_FREE(s);
}

void EverCrypt_Hash_copy(EverCrypt_Hash_state_s *s_src, EverCrypt_Hash_state_s *s_dst)
{
  EverCrypt_Hash_state_s scrut = *s_src;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    uint32_t *p_src = scrut.case_MD5_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint32_t *p_dst;
    if (x1.tag == EverCrypt_Hash_MD5_s)
    {
      p_dst = x1.case_MD5_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint32_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)4U * sizeof p_src[0U]);
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p_src = scrut.case_SHA1_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint32_t *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA1_s)
    {
      p_dst = x1.case_SHA1_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint32_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)5U * sizeof p_src[0U]);
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p_src = scrut.case_SHA2_224_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint32_t *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA2_224_s)
    {
      p_dst = x1.case_SHA2_224_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint32_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)8U * sizeof p_src[0U]);
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p_src = scrut.case_SHA2_256_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint32_t *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA2_256_s)
    {
      p_dst = x1.case_SHA2_256_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint32_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)8U * sizeof p_src[0U]);
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p_src = scrut.case_SHA2_384_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint64_t *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA2_384_s)
    {
      p_dst = x1.case_SHA2_384_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint64_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)8U * sizeof p_src[0U]);
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p_src = scrut.case_SHA2_512_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint64_t *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA2_512_s)
    {
      p_dst = x1.case_SHA2_512_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint64_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)8U * sizeof p_src[0U]);
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

void EverCrypt_Hash_hash_256(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint32_t
  s[8U] =
    {
      (uint32_t)0x6a09e667U, (uint32_t)0xbb67ae85U, (uint32_t)0x3c6ef372U, (uint32_t)0xa54ff53aU,
      (uint32_t)0x510e527fU, (uint32_t)0x9b05688cU, (uint32_t)0x1f83d9abU, (uint32_t)0x5be0cd19U
    };
  uint32_t blocks_n = input_len / (uint32_t)64U;
  uint32_t blocks_len = blocks_n * (uint32_t)64U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  EverCrypt_Hash_update_multi_256(s, blocks, blocks_n);
  EverCrypt_Hash_update_last_256(s, (uint64_t)blocks_len, rest, rest_len);
  Hacl_Hash_Core_SHA2_finish_256(s, dst);
}

void EverCrypt_Hash_hash_224(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint32_t
  s[8U] =
    {
      (uint32_t)0xc1059ed8U, (uint32_t)0x367cd507U, (uint32_t)0x3070dd17U, (uint32_t)0xf70e5939U,
      (uint32_t)0xffc00b31U, (uint32_t)0x68581511U, (uint32_t)0x64f98fa7U, (uint32_t)0xbefa4fa4U
    };
  uint32_t blocks_n = input_len / (uint32_t)64U;
  uint32_t blocks_len = blocks_n * (uint32_t)64U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  EverCrypt_Hash_update_multi_256(s, blocks, blocks_n);
  EverCrypt_Hash_update_last_256(s, (uint64_t)blocks_len, rest, rest_len);
  Hacl_Hash_Core_SHA2_finish_224(s, dst);
}

void
EverCrypt_Hash_hash(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *dst,
  uint8_t *input,
  uint32_t len
)
{
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        Hacl_Hash_MD5_legacy_hash(input, len, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        Hacl_Hash_SHA1_legacy_hash(input, len, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        EverCrypt_Hash_hash_224(input, len, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        EverCrypt_Hash_hash_256(input, len, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        Hacl_Hash_SHA2_hash_384(input, len, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        Hacl_Hash_SHA2_hash_512(input, len, dst);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

typedef struct EverCrypt_Hash_Incremental_state_s_s
{
  EverCrypt_Hash_state_s *hash_state;
  uint8_t *buf;
  uint64_t total_len;
}
EverCrypt_Hash_Incremental_state_s;

bool
EverCrypt_Hash_Incremental_uu___is_State(
  Spec_Hash_Definitions_hash_alg a,
  EverCrypt_Hash_Incremental_state_s projectee
)
{
  return true;
}

EverCrypt_Hash_state_s
*EverCrypt_Hash_Incremental___proj__State__item__hash_state(
  Spec_Hash_Definitions_hash_alg a,
  EverCrypt_Hash_Incremental_state_s projectee
)
{
  return projectee.hash_state;
}

uint8_t
*EverCrypt_Hash_Incremental___proj__State__item__buf(
  Spec_Hash_Definitions_hash_alg a,
  EverCrypt_Hash_Incremental_state_s projectee
)
{
  return projectee.buf;
}

uint64_t
EverCrypt_Hash_Incremental___proj__State__item__total_len(
  Spec_Hash_Definitions_hash_alg a,
  EverCrypt_Hash_Incremental_state_s projectee
)
{
  return projectee.total_len;
}

Spec_Hash_Definitions_hash_alg
EverCrypt_Hash_Incremental_alg_of_state(EverCrypt_Hash_Incremental_state_s *s)
{
  EverCrypt_Hash_Incremental_state_s scrut = *s;
  EverCrypt_Hash_state_s *hash_state = scrut.hash_state;
  return EverCrypt_Hash_alg_of_state(hash_state);
}

EverCrypt_Hash_Incremental_state_s
*EverCrypt_Hash_Incremental_create_in(Spec_Hash_Definitions_hash_alg a)
{
  uint32_t sw;
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw = (uint32_t)128U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw = (uint32_t)128U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), sw);
  uint8_t *buf1 = KRML_HOST_CALLOC(sw, sizeof (uint8_t));
  EverCrypt_Hash_state_s *hash_state = EverCrypt_Hash_create_in(a);
  EverCrypt_Hash_Incremental_state_s
  s = { .hash_state = hash_state, .buf = buf1, .total_len = (uint64_t)0U };
  KRML_CHECK_SIZE(sizeof (EverCrypt_Hash_Incremental_state_s), (uint32_t)1U);
  EverCrypt_Hash_Incremental_state_s
  *p1 = KRML_HOST_MALLOC(sizeof (EverCrypt_Hash_Incremental_state_s));
  p1[0U] = s;
  EverCrypt_Hash_init(hash_state);
  return p1;
}

void EverCrypt_Hash_Incremental_init(EverCrypt_Hash_Incremental_state_s *s)
{
  EverCrypt_Hash_Incremental_state_s scrut = *s;
  uint8_t *buf1 = scrut.buf;
  EverCrypt_Hash_state_s *hash_state = scrut.hash_state;
  Spec_Hash_Definitions_hash_alg a1 = EverCrypt_Hash_alg_of_state(hash_state);
  EverCrypt_Hash_init(hash_state);
  s[0U] =
    (
      (EverCrypt_Hash_Incremental_state_s){
        .hash_state = hash_state,
        .buf = buf1,
        .total_len = (uint64_t)0U
      }
    );
}

static void
EverCrypt_Hash_Incremental_update_small(
  EverCrypt_Hash_Incremental_state_s *p1,
  uint8_t *data,
  uint32_t len
)
{
  EverCrypt_Hash_Incremental_state_s s = *p1;
  EverCrypt_Hash_state_s *hash_state = s.hash_state;
  uint8_t *buf1 = s.buf;
  uint64_t total_len = s.total_len;
  Spec_Hash_Definitions_hash_alg a1 = EverCrypt_Hash_alg_of_state(hash_state);
  uint32_t sw;
  switch (a1)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw = (uint32_t)128U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw = (uint32_t)128U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t sz = (uint32_t)(total_len % (uint64_t)sw);
  uint8_t *buf2 = buf1 + sz;
  memcpy(buf2, data, len * sizeof data[0U]);
  uint64_t total_len1 = total_len + (uint64_t)len;
  *p1
  =
    (
      (EverCrypt_Hash_Incremental_state_s){
        .hash_state = hash_state,
        .buf = buf1,
        .total_len = total_len1
      }
    );
}

static void
EverCrypt_Hash_Incremental_update_empty_buf(
  EverCrypt_Hash_Incremental_state_s *p1,
  uint8_t *data,
  uint32_t len
)
{
  EverCrypt_Hash_Incremental_state_s s = *p1;
  EverCrypt_Hash_state_s *hash_state = s.hash_state;
  uint8_t *buf1 = s.buf;
  uint64_t total_len = s.total_len;
  Spec_Hash_Definitions_hash_alg a1 = EverCrypt_Hash_alg_of_state(hash_state);
  uint32_t sw0;
  switch (a1)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw0 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw0 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw0 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw0 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw0 = (uint32_t)128U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw0 = (uint32_t)128U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t sz = (uint32_t)(total_len % (uint64_t)sw0);
  uint32_t sw1;
  switch (a1)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw1 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw1 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw1 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw1 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw1 = (uint32_t)128U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw1 = (uint32_t)128U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t n_blocks = len / sw1;
  uint32_t sw;
  switch (a1)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw = (uint32_t)128U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw = (uint32_t)128U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t data1_len = n_blocks * sw;
  uint32_t data2_len = len - data1_len;
  uint8_t *data1 = data;
  uint8_t *data2 = data + data1_len;
  EverCrypt_Hash_update_multi(hash_state, data1, data1_len);
  uint8_t *dst = buf1;
  memcpy(dst, data2, data2_len * sizeof data2[0U]);
  *p1
  =
    (
      (EverCrypt_Hash_Incremental_state_s){
        .hash_state = hash_state,
        .buf = buf1,
        .total_len = total_len + (uint64_t)len
      }
    );
}

static void
EverCrypt_Hash_Incremental_update_round(
  EverCrypt_Hash_Incremental_state_s *p1,
  uint8_t *data,
  uint32_t len
)
{
  EverCrypt_Hash_Incremental_state_s s = *p1;
  EverCrypt_Hash_state_s *hash_state = s.hash_state;
  uint8_t *buf_ = s.buf;
  uint64_t total_len = s.total_len;
  Spec_Hash_Definitions_hash_alg a1 = EverCrypt_Hash_alg_of_state(hash_state);
  uint32_t sw0;
  switch (a1)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw0 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw0 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw0 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw0 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw0 = (uint32_t)128U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw0 = (uint32_t)128U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t sz = (uint32_t)(total_len % (uint64_t)sw0);
  uint32_t sw;
  switch (a1)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw = (uint32_t)128U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw = (uint32_t)128U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t diff = sw - sz;
  uint8_t *buf0 = buf_;
  uint8_t *buf2 = buf0 + sz;
  memcpy(buf2, data, diff * sizeof data[0U]);
  uint32_t sw1;
  switch (a1)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw1 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw1 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw1 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw1 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw1 = (uint32_t)128U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw1 = (uint32_t)128U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  EverCrypt_Hash_update_multi(hash_state, buf0, sw1);
  *p1
  =
    (
      (EverCrypt_Hash_Incremental_state_s){
        .hash_state = hash_state,
        .buf = buf_,
        .total_len = total_len + (uint64_t)len
      }
    );
}

void
EverCrypt_Hash_Incremental_update(
  EverCrypt_Hash_Incremental_state_s *p1,
  uint8_t *data,
  uint32_t len
)
{
  EverCrypt_Hash_Incremental_state_s s = *p1;
  EverCrypt_Hash_state_s *hash_state = s.hash_state;
  uint64_t total_len = s.total_len;
  Spec_Hash_Definitions_hash_alg a1 = EverCrypt_Hash_alg_of_state(hash_state);
  uint32_t sw0;
  switch (a1)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw0 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw0 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw0 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw0 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw0 = (uint32_t)128U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw0 = (uint32_t)128U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t sz = (uint32_t)(total_len % (uint64_t)sw0);
  uint32_t sw;
  switch (a1)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw = (uint32_t)128U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw = (uint32_t)128U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  if (len < sw - sz)
  {
    EverCrypt_Hash_Incremental_update_small(p1, data, len);
    return;
  }
  if (sz == (uint32_t)0U)
  {
    EverCrypt_Hash_Incremental_update_empty_buf(p1, data, len);
    return;
  }
  uint32_t sw1;
  switch (a1)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw1 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw1 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw1 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw1 = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw1 = (uint32_t)128U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw1 = (uint32_t)128U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t diff = sw1 - sz;
  uint8_t *data1 = data;
  uint8_t *data2 = data + diff;
  EverCrypt_Hash_Incremental_update_round(p1, data1, diff);
  EverCrypt_Hash_Incremental_update_empty_buf(p1, data2, len - diff);
}

static void
EverCrypt_Hash_Incremental_finish_md5(EverCrypt_Hash_Incremental_state_s *p1, uint8_t *dst)
{
  EverCrypt_Hash_Incremental_state_s scrut = *p1;
  EverCrypt_Hash_state_s *hash_state = scrut.hash_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint8_t *buf_1 = buf_;
  uint32_t buf[4U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_MD5_s, { .case_MD5_s = buf } };
  EverCrypt_Hash_state_s tmp_hash_state = s;
  EverCrypt_Hash_copy(hash_state, &tmp_hash_state);
  EverCrypt_Hash_update_last(&tmp_hash_state, buf_1, total_len);
  EverCrypt_Hash_finish(&tmp_hash_state, dst);
}

static void
EverCrypt_Hash_Incremental_finish_sha1(EverCrypt_Hash_Incremental_state_s *p1, uint8_t *dst)
{
  EverCrypt_Hash_Incremental_state_s scrut = *p1;
  EverCrypt_Hash_state_s *hash_state = scrut.hash_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint8_t *buf_1 = buf_;
  uint32_t buf[5U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_SHA1_s, { .case_SHA1_s = buf } };
  EverCrypt_Hash_state_s tmp_hash_state = s;
  EverCrypt_Hash_copy(hash_state, &tmp_hash_state);
  EverCrypt_Hash_update_last(&tmp_hash_state, buf_1, total_len);
  EverCrypt_Hash_finish(&tmp_hash_state, dst);
}

static void
EverCrypt_Hash_Incremental_finish_sha224(EverCrypt_Hash_Incremental_state_s *p1, uint8_t *dst)
{
  EverCrypt_Hash_Incremental_state_s scrut = *p1;
  EverCrypt_Hash_state_s *hash_state = scrut.hash_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint8_t *buf_1 = buf_;
  uint32_t buf[8U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_SHA2_224_s, { .case_SHA2_224_s = buf } };
  EverCrypt_Hash_state_s tmp_hash_state = s;
  EverCrypt_Hash_copy(hash_state, &tmp_hash_state);
  EverCrypt_Hash_update_last(&tmp_hash_state, buf_1, total_len);
  EverCrypt_Hash_finish(&tmp_hash_state, dst);
}

static void
EverCrypt_Hash_Incremental_finish_sha256(EverCrypt_Hash_Incremental_state_s *p1, uint8_t *dst)
{
  EverCrypt_Hash_Incremental_state_s scrut = *p1;
  EverCrypt_Hash_state_s *hash_state = scrut.hash_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint8_t *buf_1 = buf_;
  uint32_t buf[8U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_SHA2_256_s, { .case_SHA2_256_s = buf } };
  EverCrypt_Hash_state_s tmp_hash_state = s;
  EverCrypt_Hash_copy(hash_state, &tmp_hash_state);
  EverCrypt_Hash_update_last(&tmp_hash_state, buf_1, total_len);
  EverCrypt_Hash_finish(&tmp_hash_state, dst);
}

static void
EverCrypt_Hash_Incremental_finish_sha384(EverCrypt_Hash_Incremental_state_s *p1, uint8_t *dst)
{
  EverCrypt_Hash_Incremental_state_s scrut = *p1;
  EverCrypt_Hash_state_s *hash_state = scrut.hash_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint8_t *buf_1 = buf_;
  uint64_t buf[8U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_SHA2_384_s, { .case_SHA2_384_s = buf } };
  EverCrypt_Hash_state_s tmp_hash_state = s;
  EverCrypt_Hash_copy(hash_state, &tmp_hash_state);
  EverCrypt_Hash_update_last(&tmp_hash_state, buf_1, total_len);
  EverCrypt_Hash_finish(&tmp_hash_state, dst);
}

static void
EverCrypt_Hash_Incremental_finish_sha512(EverCrypt_Hash_Incremental_state_s *p1, uint8_t *dst)
{
  EverCrypt_Hash_Incremental_state_s scrut = *p1;
  EverCrypt_Hash_state_s *hash_state = scrut.hash_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint8_t *buf_1 = buf_;
  uint64_t buf[8U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_SHA2_512_s, { .case_SHA2_512_s = buf } };
  EverCrypt_Hash_state_s tmp_hash_state = s;
  EverCrypt_Hash_copy(hash_state, &tmp_hash_state);
  EverCrypt_Hash_update_last(&tmp_hash_state, buf_1, total_len);
  EverCrypt_Hash_finish(&tmp_hash_state, dst);
}

void EverCrypt_Hash_Incremental_finish(EverCrypt_Hash_Incremental_state_s *s, uint8_t *dst)
{
  EverCrypt_Hash_Incremental_state_s scrut = *s;
  EverCrypt_Hash_state_s *hash_state = scrut.hash_state;
  Spec_Hash_Definitions_hash_alg a1 = EverCrypt_Hash_alg_of_state(hash_state);
  switch (a1)
  {
    case Spec_Hash_Definitions_MD5:
      {
        EverCrypt_Hash_Incremental_finish_md5(s, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        EverCrypt_Hash_Incremental_finish_sha1(s, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        EverCrypt_Hash_Incremental_finish_sha224(s, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        EverCrypt_Hash_Incremental_finish_sha256(s, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        EverCrypt_Hash_Incremental_finish_sha384(s, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        EverCrypt_Hash_Incremental_finish_sha512(s, dst);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

void EverCrypt_Hash_Incremental_free(EverCrypt_Hash_Incremental_state_s *s)
{
  EverCrypt_Hash_Incremental_state_s scrut = *s;
  uint8_t *buf1 = scrut.buf;
  EverCrypt_Hash_state_s *hash_state = scrut.hash_state;
  EverCrypt_Hash_free(hash_state);
  KRML_HOST_FREE(buf1);
  KRML_HOST_FREE(s);
}

