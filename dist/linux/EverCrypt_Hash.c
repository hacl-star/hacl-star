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
  else
  {
    return false;
  }
}

u32
*EverCrypt_Hash___proj__MD5_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____179,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_MD5_s)
  {
    return projectee.case_MD5_s;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
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
  else
  {
    return false;
  }
}

u32
*EverCrypt_Hash___proj__SHA1_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____230,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA1_s)
  {
    return projectee.case_SHA1_s;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
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
  else
  {
    return false;
  }
}

u32
*EverCrypt_Hash___proj__SHA2_224_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____281,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_224_s)
  {
    return projectee.case_SHA2_224_s;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
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
  else
  {
    return false;
  }
}

u32
*EverCrypt_Hash___proj__SHA2_256_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____332,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_256_s)
  {
    return projectee.case_SHA2_256_s;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
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
  else
  {
    return false;
  }
}

u64
*EverCrypt_Hash___proj__SHA2_384_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____383,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_384_s)
  {
    return projectee.case_SHA2_384_s;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
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
  else
  {
    return false;
  }
}

u64
*EverCrypt_Hash___proj__SHA2_512_s__item__p(
  Spec_Hash_Definitions_hash_alg uu____434,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_512_s)
  {
    return projectee.case_SHA2_512_s;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

Spec_Hash_Definitions_hash_alg EverCrypt_Hash_alg_of_state(EverCrypt_Hash_state_s *s)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    return Spec_Hash_Definitions_MD5;
  }
  else if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    return Spec_Hash_Definitions_SHA1;
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    return Spec_Hash_Definitions_SHA2_224;
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    return Spec_Hash_Definitions_SHA2_256;
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    return Spec_Hash_Definitions_SHA2_384;
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    return Spec_Hash_Definitions_SHA2_512;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

EverCrypt_Hash_state_s *EverCrypt_Hash_create_in(Spec_Hash_Definitions_hash_alg a)
{
  EverCrypt_Hash_state_s s;
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        u32 *buf = KRML_HOST_CALLOC((u32)4U, sizeof (u32));
        s = ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_MD5_s, { .case_MD5_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        u32 *buf = KRML_HOST_CALLOC((u32)5U, sizeof (u32));
        s = ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_SHA1_s, { .case_SHA1_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        u32 *buf = KRML_HOST_CALLOC((u32)8U, sizeof (u32));
        s =
          ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_SHA2_224_s, { .case_SHA2_224_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        u32 *buf = KRML_HOST_CALLOC((u32)8U, sizeof (u32));
        s =
          ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_SHA2_256_s, { .case_SHA2_256_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        u64 *buf = KRML_HOST_CALLOC((u32)8U, sizeof (u64));
        s =
          ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_SHA2_384_s, { .case_SHA2_384_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        u64 *buf = KRML_HOST_CALLOC((u32)8U, sizeof (u64));
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
  KRML_CHECK_SIZE(sizeof (EverCrypt_Hash_state_s), (u32)1U);
  {
    EverCrypt_Hash_state_s *buf = KRML_HOST_MALLOC(sizeof (EverCrypt_Hash_state_s));
    buf[0U] = s;
    return buf;
  }
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
    u32 *p1 = scrut.case_MD5_s;
    Hacl_Hash_Core_MD5_legacy_init(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    u32 *p1 = scrut.case_SHA1_s;
    Hacl_Hash_Core_SHA1_legacy_init(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    u32 *p1 = scrut.case_SHA2_224_s;
    Hacl_Hash_Core_SHA2_init_224(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    u32 *p1 = scrut.case_SHA2_256_s;
    Hacl_Hash_Core_SHA2_init_256(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    u64 *p1 = scrut.case_SHA2_384_s;
    Hacl_Hash_Core_SHA2_init_384(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    u64 *p1 = scrut.case_SHA2_512_s;
    Hacl_Hash_Core_SHA2_init_512(p1);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

void EverCrypt_Hash_update_multi_256(u32 *s, u8 *blocks, u32 n1)
{
  bool has_shaext1 = EverCrypt_AutoConfig2_has_shaext();
  bool has_sse1 = EverCrypt_AutoConfig2_has_sse();
  if (true && has_shaext1 && has_sse1)
  {
    u64 n2 = (u64)n1;
    u64 scrut = sha256_update(s, blocks, n2, Hacl_Hash_Core_SHA2_Constants_k224_256);
  }
  else
  {
    Hacl_Hash_SHA2_update_multi_256(s, blocks, n1);
  }
}

void EverCrypt_Hash_update(EverCrypt_Hash_state_s *s, u8 *block1)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    u32 *p1 = scrut.case_MD5_s;
    Hacl_Hash_Core_MD5_legacy_update(p1, block1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    u32 *p1 = scrut.case_SHA1_s;
    Hacl_Hash_Core_SHA1_legacy_update(p1, block1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    u32 *p1 = scrut.case_SHA2_224_s;
    EverCrypt_Hash_update_multi_256(p1, block1, (u32)1U);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    u32 *p1 = scrut.case_SHA2_256_s;
    EverCrypt_Hash_update_multi_256(p1, block1, (u32)1U);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    u64 *p1 = scrut.case_SHA2_384_s;
    Hacl_Hash_Core_SHA2_update_384(p1, block1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    u64 *p1 = scrut.case_SHA2_512_s;
    Hacl_Hash_Core_SHA2_update_512(p1, block1);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

void EverCrypt_Hash_update_multi(EverCrypt_Hash_state_s *s, u8 *blocks, u32 len)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    u32 *p1 = scrut.case_MD5_s;
    u32 n1 = len / (u32)64U;
    Hacl_Hash_MD5_legacy_update_multi(p1, blocks, n1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    u32 *p1 = scrut.case_SHA1_s;
    u32 n1 = len / (u32)64U;
    Hacl_Hash_SHA1_legacy_update_multi(p1, blocks, n1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    u32 *p1 = scrut.case_SHA2_224_s;
    u32 n1 = len / (u32)64U;
    EverCrypt_Hash_update_multi_256(p1, blocks, n1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    u32 *p1 = scrut.case_SHA2_256_s;
    u32 n1 = len / (u32)64U;
    EverCrypt_Hash_update_multi_256(p1, blocks, n1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    u64 *p1 = scrut.case_SHA2_384_s;
    u32 n1 = len / (u32)128U;
    Hacl_Hash_SHA2_update_multi_384(p1, blocks, n1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    u64 *p1 = scrut.case_SHA2_512_s;
    u32 n1 = len / (u32)128U;
    Hacl_Hash_SHA2_update_multi_512(p1, blocks, n1);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

void EverCrypt_Hash_update_last_256(u32 *s, u64 prev_len, u8 *input, u32 input_len)
{
  u32 blocks_n = input_len / (u32)64U;
  u32 blocks_len = blocks_n * (u32)64U;
  u8 *blocks = input;
  u32 rest_len = input_len - blocks_len;
  u8 *rest = input + blocks_len;
  u64 total_input_len;
  u32 pad_len1;
  u32 tmp_len;
  EverCrypt_Hash_update_multi_256(s, blocks, blocks_n);
  total_input_len = prev_len + (u64)input_len;
  pad_len1 =
    (u32)1U
    + ((u32)128U - ((u32)9U + (u32)(total_input_len % (u64)(u32)64U))) % (u32)64U
    + (u32)8U;
  tmp_len = rest_len + pad_len1;
  {
    u8 tmp_twoblocks[128U] = { 0U };
    u8 *tmp = tmp_twoblocks;
    u8 *tmp_rest = tmp;
    u8 *tmp_pad = tmp + rest_len;
    memcpy(tmp_rest, rest, rest_len * sizeof rest[0U]);
    Hacl_Hash_Core_SHA2_pad_256(total_input_len, tmp_pad);
    EverCrypt_Hash_update_multi_256(s, tmp, tmp_len / (u32)64U);
  }
}

void EverCrypt_Hash_update_last(EverCrypt_Hash_state_s *s, u8 *last1, u64 total_len)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    u32 *p1 = scrut.case_MD5_s;
    u64 input_len = total_len % (u64)(u32)64U;
    u64 prev_len = total_len - input_len;
    Hacl_Hash_MD5_legacy_update_last(p1, prev_len, last1, (u32)input_len);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    u32 *p1 = scrut.case_SHA1_s;
    u64 input_len = total_len % (u64)(u32)64U;
    u64 prev_len = total_len - input_len;
    Hacl_Hash_SHA1_legacy_update_last(p1, prev_len, last1, (u32)input_len);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    u32 *p1 = scrut.case_SHA2_224_s;
    u64 input_len = total_len % (u64)(u32)64U;
    u64 prev_len = total_len - input_len;
    EverCrypt_Hash_update_last_256(p1, prev_len, last1, (u32)input_len);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    u32 *p1 = scrut.case_SHA2_256_s;
    u64 input_len = total_len % (u64)(u32)64U;
    u64 prev_len = total_len - input_len;
    EverCrypt_Hash_update_last_256(p1, prev_len, last1, (u32)input_len);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    u64 *p1 = scrut.case_SHA2_384_s;
    u64 input_len = total_len % (u64)(u32)128U;
    uint128_t prev_len = (uint128_t)(total_len - input_len);
    Hacl_Hash_SHA2_update_last_384(p1, prev_len, last1, (u32)input_len);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    u64 *p1 = scrut.case_SHA2_512_s;
    u64 input_len = total_len % (u64)(u32)128U;
    uint128_t prev_len = (uint128_t)(total_len - input_len);
    Hacl_Hash_SHA2_update_last_512(p1, prev_len, last1, (u32)input_len);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

void EverCrypt_Hash_finish(EverCrypt_Hash_state_s *s, u8 *dst)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    u32 *p1 = scrut.case_MD5_s;
    Hacl_Hash_Core_MD5_legacy_finish(p1, dst);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    u32 *p1 = scrut.case_SHA1_s;
    Hacl_Hash_Core_SHA1_legacy_finish(p1, dst);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    u32 *p1 = scrut.case_SHA2_224_s;
    Hacl_Hash_Core_SHA2_finish_224(p1, dst);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    u32 *p1 = scrut.case_SHA2_256_s;
    Hacl_Hash_Core_SHA2_finish_256(p1, dst);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    u64 *p1 = scrut.case_SHA2_384_s;
    Hacl_Hash_Core_SHA2_finish_384(p1, dst);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    u64 *p1 = scrut.case_SHA2_512_s;
    Hacl_Hash_Core_SHA2_finish_512(p1, dst);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

void EverCrypt_Hash_free(EverCrypt_Hash_state_s *s)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    u32 *p1 = scrut.case_MD5_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    u32 *p1 = scrut.case_SHA1_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    u32 *p1 = scrut.case_SHA2_224_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    u32 *p1 = scrut.case_SHA2_256_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    u64 *p1 = scrut.case_SHA2_384_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    u64 *p1 = scrut.case_SHA2_512_s;
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
    u32 *p_src = scrut.case_MD5_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    u32 *p_dst;
    if (x1.tag == EverCrypt_Hash_MD5_s)
    {
      p_dst = x1.case_MD5_s;
    }
    else
    {
      p_dst = KRML_EABORT(u32 *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (u32)4U * sizeof p_src[0U]);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    u32 *p_src = scrut.case_SHA1_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    u32 *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA1_s)
    {
      p_dst = x1.case_SHA1_s;
    }
    else
    {
      p_dst = KRML_EABORT(u32 *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (u32)5U * sizeof p_src[0U]);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    u32 *p_src = scrut.case_SHA2_224_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    u32 *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA2_224_s)
    {
      p_dst = x1.case_SHA2_224_s;
    }
    else
    {
      p_dst = KRML_EABORT(u32 *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (u32)8U * sizeof p_src[0U]);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    u32 *p_src = scrut.case_SHA2_256_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    u32 *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA2_256_s)
    {
      p_dst = x1.case_SHA2_256_s;
    }
    else
    {
      p_dst = KRML_EABORT(u32 *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (u32)8U * sizeof p_src[0U]);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    u64 *p_src = scrut.case_SHA2_384_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    u64 *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA2_384_s)
    {
      p_dst = x1.case_SHA2_384_s;
    }
    else
    {
      p_dst = KRML_EABORT(u64 *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (u32)8U * sizeof p_src[0U]);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    u64 *p_src = scrut.case_SHA2_512_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    u64 *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA2_512_s)
    {
      p_dst = x1.case_SHA2_512_s;
    }
    else
    {
      p_dst = KRML_EABORT(u64 *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (u32)8U * sizeof p_src[0U]);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

void EverCrypt_Hash_hash_256(u8 *input, u32 input_len, u8 *dst)
{
  u32
  s[8U] =
    {
      (u32)0x6a09e667U, (u32)0xbb67ae85U, (u32)0x3c6ef372U, (u32)0xa54ff53aU, (u32)0x510e527fU,
      (u32)0x9b05688cU, (u32)0x1f83d9abU, (u32)0x5be0cd19U
    };
  u32 blocks_n = input_len / (u32)64U;
  u32 blocks_len = blocks_n * (u32)64U;
  u8 *blocks = input;
  u32 rest_len = input_len - blocks_len;
  u8 *rest = input + blocks_len;
  EverCrypt_Hash_update_multi_256(s, blocks, blocks_n);
  EverCrypt_Hash_update_last_256(s, (u64)blocks_len, rest, rest_len);
  Hacl_Hash_Core_SHA2_finish_256(s, dst);
}

void EverCrypt_Hash_hash_224(u8 *input, u32 input_len, u8 *dst)
{
  u32
  s[8U] =
    {
      (u32)0xc1059ed8U, (u32)0x367cd507U, (u32)0x3070dd17U, (u32)0xf70e5939U, (u32)0xffc00b31U,
      (u32)0x68581511U, (u32)0x64f98fa7U, (u32)0xbefa4fa4U
    };
  u32 blocks_n = input_len / (u32)64U;
  u32 blocks_len = blocks_n * (u32)64U;
  u8 *blocks = input;
  u32 rest_len = input_len - blocks_len;
  u8 *rest = input + blocks_len;
  EverCrypt_Hash_update_multi_256(s, blocks, blocks_n);
  EverCrypt_Hash_update_last_256(s, (u64)blocks_len, rest, rest_len);
  Hacl_Hash_Core_SHA2_finish_224(s, dst);
}

void EverCrypt_Hash_hash(Spec_Hash_Definitions_hash_alg a, u8 *dst, u8 *input, u32 len)
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
  u8 *buf;
  u64 total_len;
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

u8
*EverCrypt_Hash_Incremental___proj__State__item__buf(
  Spec_Hash_Definitions_hash_alg a,
  EverCrypt_Hash_Incremental_state_s projectee
)
{
  return projectee.buf;
}

u64
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
  u32 sw;
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw = (u32)128U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw = (u32)128U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  KRML_CHECK_SIZE(sizeof (u8), sw);
  {
    u8 *buf1 = KRML_HOST_CALLOC(sw, sizeof (u8));
    EverCrypt_Hash_state_s *hash_state = EverCrypt_Hash_create_in(a);
    EverCrypt_Hash_Incremental_state_s
    s = { .hash_state = hash_state, .buf = buf1, .total_len = (u64)0U };
    KRML_CHECK_SIZE(sizeof (EverCrypt_Hash_Incremental_state_s), (u32)1U);
    {
      EverCrypt_Hash_Incremental_state_s
      *p1 = KRML_HOST_MALLOC(sizeof (EverCrypt_Hash_Incremental_state_s));
      p1[0U] = s;
      EverCrypt_Hash_init(hash_state);
      return p1;
    }
  }
}

void EverCrypt_Hash_Incremental_init(EverCrypt_Hash_Incremental_state_s *s)
{
  EverCrypt_Hash_Incremental_state_s scrut = *s;
  u8 *buf1 = scrut.buf;
  EverCrypt_Hash_state_s *hash_state = scrut.hash_state;
  Spec_Hash_Definitions_hash_alg a1 = EverCrypt_Hash_alg_of_state(hash_state);
  EverCrypt_Hash_init(hash_state);
  s[0U] =
    (
      (EverCrypt_Hash_Incremental_state_s){
        .hash_state = hash_state,
        .buf = buf1,
        .total_len = (u64)0U
      }
    );
}

static void
EverCrypt_Hash_Incremental_update_small(
  EverCrypt_Hash_Incremental_state_s *p1,
  u8 *data,
  u32 len
)
{
  EverCrypt_Hash_Incremental_state_s s = *p1;
  EverCrypt_Hash_state_s *hash_state = s.hash_state;
  u8 *buf1 = s.buf;
  u64 total_len = s.total_len;
  Spec_Hash_Definitions_hash_alg a1 = EverCrypt_Hash_alg_of_state(hash_state);
  u32 sw;
  switch (a1)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw = (u32)128U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw = (u32)128U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  {
    u32 sz = (u32)(total_len % (u64)sw);
    u8 *buf2 = buf1 + sz;
    u64 total_len1;
    memcpy(buf2, data, len * sizeof data[0U]);
    total_len1 = total_len + (u64)len;
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
}

static void
EverCrypt_Hash_Incremental_update_empty_buf(
  EverCrypt_Hash_Incremental_state_s *p1,
  u8 *data,
  u32 len
)
{
  EverCrypt_Hash_Incremental_state_s s = *p1;
  EverCrypt_Hash_state_s *hash_state = s.hash_state;
  u8 *buf1 = s.buf;
  u64 total_len = s.total_len;
  Spec_Hash_Definitions_hash_alg a1 = EverCrypt_Hash_alg_of_state(hash_state);
  u32 sw0;
  switch (a1)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw0 = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw0 = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw0 = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw0 = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw0 = (u32)128U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw0 = (u32)128U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  {
    u32 sz = (u32)(total_len % (u64)sw0);
    u32 sw1;
    switch (a1)
    {
      case Spec_Hash_Definitions_MD5:
        {
          sw1 = (u32)64U;
          break;
        }
      case Spec_Hash_Definitions_SHA1:
        {
          sw1 = (u32)64U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_224:
        {
          sw1 = (u32)64U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_256:
        {
          sw1 = (u32)64U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_384:
        {
          sw1 = (u32)128U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_512:
        {
          sw1 = (u32)128U;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    {
      u32 n_blocks = len / sw1;
      u32 sw;
      switch (a1)
      {
        case Spec_Hash_Definitions_MD5:
          {
            sw = (u32)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA1:
          {
            sw = (u32)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_224:
          {
            sw = (u32)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_256:
          {
            sw = (u32)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_384:
          {
            sw = (u32)128U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_512:
          {
            sw = (u32)128U;
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      {
        u32 data1_len = n_blocks * sw;
        u32 data2_len = len - data1_len;
        u8 *data1 = data;
        u8 *data2 = data + data1_len;
        u8 *dst;
        EverCrypt_Hash_update_multi(hash_state, data1, data1_len);
        dst = buf1;
        memcpy(dst, data2, data2_len * sizeof data2[0U]);
        *p1
        =
          (
            (EverCrypt_Hash_Incremental_state_s){
              .hash_state = hash_state,
              .buf = buf1,
              .total_len = total_len + (u64)len
            }
          );
      }
    }
  }
}

static void
EverCrypt_Hash_Incremental_update_round(
  EverCrypt_Hash_Incremental_state_s *p1,
  u8 *data,
  u32 len
)
{
  EverCrypt_Hash_Incremental_state_s s = *p1;
  EverCrypt_Hash_state_s *hash_state = s.hash_state;
  u8 *buf_ = s.buf;
  u64 total_len = s.total_len;
  Spec_Hash_Definitions_hash_alg a1 = EverCrypt_Hash_alg_of_state(hash_state);
  u32 sw0;
  switch (a1)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw0 = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw0 = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw0 = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw0 = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw0 = (u32)128U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw0 = (u32)128U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  {
    u32 sz = (u32)(total_len % (u64)sw0);
    u32 sw1;
    switch (a1)
    {
      case Spec_Hash_Definitions_MD5:
        {
          sw1 = (u32)64U;
          break;
        }
      case Spec_Hash_Definitions_SHA1:
        {
          sw1 = (u32)64U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_224:
        {
          sw1 = (u32)64U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_256:
        {
          sw1 = (u32)64U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_384:
        {
          sw1 = (u32)128U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_512:
        {
          sw1 = (u32)128U;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    {
      u32 diff = sw1 - sz;
      u8 *buf0 = buf_;
      u8 *buf2 = buf0 + sz;
      u32 sw;
      memcpy(buf2, data, diff * sizeof data[0U]);
      switch (a1)
      {
        case Spec_Hash_Definitions_MD5:
          {
            sw = (u32)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA1:
          {
            sw = (u32)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_224:
          {
            sw = (u32)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_256:
          {
            sw = (u32)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_384:
          {
            sw = (u32)128U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_512:
          {
            sw = (u32)128U;
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      EverCrypt_Hash_update_multi(hash_state, buf0, sw);
      *p1
      =
        (
          (EverCrypt_Hash_Incremental_state_s){
            .hash_state = hash_state,
            .buf = buf_,
            .total_len = total_len + (u64)len
          }
        );
    }
  }
}

void
EverCrypt_Hash_Incremental_update(EverCrypt_Hash_Incremental_state_s *p1, u8 *data, u32 len)
{
  EverCrypt_Hash_Incremental_state_s s = *p1;
  EverCrypt_Hash_state_s *hash_state = s.hash_state;
  u64 total_len = s.total_len;
  Spec_Hash_Definitions_hash_alg a1 = EverCrypt_Hash_alg_of_state(hash_state);
  u32 sw0;
  switch (a1)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw0 = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw0 = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw0 = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw0 = (u32)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw0 = (u32)128U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw0 = (u32)128U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  {
    u32 sz = (u32)(total_len % (u64)sw0);
    u32 sw;
    switch (a1)
    {
      case Spec_Hash_Definitions_MD5:
        {
          sw = (u32)64U;
          break;
        }
      case Spec_Hash_Definitions_SHA1:
        {
          sw = (u32)64U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_224:
        {
          sw = (u32)64U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_256:
        {
          sw = (u32)64U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_384:
        {
          sw = (u32)128U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_512:
        {
          sw = (u32)128U;
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
    }
    else if (sz == (u32)0U)
    {
      EverCrypt_Hash_Incremental_update_empty_buf(p1, data, len);
    }
    else
    {
      u32 sw1;
      switch (a1)
      {
        case Spec_Hash_Definitions_MD5:
          {
            sw1 = (u32)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA1:
          {
            sw1 = (u32)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_224:
          {
            sw1 = (u32)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_256:
          {
            sw1 = (u32)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_384:
          {
            sw1 = (u32)128U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_512:
          {
            sw1 = (u32)128U;
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      {
        u32 diff = sw1 - sz;
        u8 *data1 = data;
        u8 *data2 = data + diff;
        EverCrypt_Hash_Incremental_update_round(p1, data1, diff);
        EverCrypt_Hash_Incremental_update_empty_buf(p1, data2, len - diff);
      }
    }
  }
}

static void
EverCrypt_Hash_Incremental_finish_md5(EverCrypt_Hash_Incremental_state_s *p1, u8 *dst)
{
  EverCrypt_Hash_Incremental_state_s scrut = *p1;
  EverCrypt_Hash_state_s *hash_state = scrut.hash_state;
  u8 *buf_ = scrut.buf;
  u64 total_len = scrut.total_len;
  u8 *buf_1 = buf_;
  u32 buf[4U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_MD5_s, { .case_MD5_s = buf } };
  EverCrypt_Hash_state_s tmp_hash_state = s;
  EverCrypt_Hash_copy(hash_state, &tmp_hash_state);
  EverCrypt_Hash_update_last(&tmp_hash_state, buf_1, total_len);
  EverCrypt_Hash_finish(&tmp_hash_state, dst);
}

static void
EverCrypt_Hash_Incremental_finish_sha1(EverCrypt_Hash_Incremental_state_s *p1, u8 *dst)
{
  EverCrypt_Hash_Incremental_state_s scrut = *p1;
  EverCrypt_Hash_state_s *hash_state = scrut.hash_state;
  u8 *buf_ = scrut.buf;
  u64 total_len = scrut.total_len;
  u8 *buf_1 = buf_;
  u32 buf[5U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_SHA1_s, { .case_SHA1_s = buf } };
  EverCrypt_Hash_state_s tmp_hash_state = s;
  EverCrypt_Hash_copy(hash_state, &tmp_hash_state);
  EverCrypt_Hash_update_last(&tmp_hash_state, buf_1, total_len);
  EverCrypt_Hash_finish(&tmp_hash_state, dst);
}

static void
EverCrypt_Hash_Incremental_finish_sha224(EverCrypt_Hash_Incremental_state_s *p1, u8 *dst)
{
  EverCrypt_Hash_Incremental_state_s scrut = *p1;
  EverCrypt_Hash_state_s *hash_state = scrut.hash_state;
  u8 *buf_ = scrut.buf;
  u64 total_len = scrut.total_len;
  u8 *buf_1 = buf_;
  u32 buf[8U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_SHA2_224_s, { .case_SHA2_224_s = buf } };
  EverCrypt_Hash_state_s tmp_hash_state = s;
  EverCrypt_Hash_copy(hash_state, &tmp_hash_state);
  EverCrypt_Hash_update_last(&tmp_hash_state, buf_1, total_len);
  EverCrypt_Hash_finish(&tmp_hash_state, dst);
}

static void
EverCrypt_Hash_Incremental_finish_sha256(EverCrypt_Hash_Incremental_state_s *p1, u8 *dst)
{
  EverCrypt_Hash_Incremental_state_s scrut = *p1;
  EverCrypt_Hash_state_s *hash_state = scrut.hash_state;
  u8 *buf_ = scrut.buf;
  u64 total_len = scrut.total_len;
  u8 *buf_1 = buf_;
  u32 buf[8U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_SHA2_256_s, { .case_SHA2_256_s = buf } };
  EverCrypt_Hash_state_s tmp_hash_state = s;
  EverCrypt_Hash_copy(hash_state, &tmp_hash_state);
  EverCrypt_Hash_update_last(&tmp_hash_state, buf_1, total_len);
  EverCrypt_Hash_finish(&tmp_hash_state, dst);
}

static void
EverCrypt_Hash_Incremental_finish_sha384(EverCrypt_Hash_Incremental_state_s *p1, u8 *dst)
{
  EverCrypt_Hash_Incremental_state_s scrut = *p1;
  EverCrypt_Hash_state_s *hash_state = scrut.hash_state;
  u8 *buf_ = scrut.buf;
  u64 total_len = scrut.total_len;
  u8 *buf_1 = buf_;
  u64 buf[8U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_SHA2_384_s, { .case_SHA2_384_s = buf } };
  EverCrypt_Hash_state_s tmp_hash_state = s;
  EverCrypt_Hash_copy(hash_state, &tmp_hash_state);
  EverCrypt_Hash_update_last(&tmp_hash_state, buf_1, total_len);
  EverCrypt_Hash_finish(&tmp_hash_state, dst);
}

static void
EverCrypt_Hash_Incremental_finish_sha512(EverCrypt_Hash_Incremental_state_s *p1, u8 *dst)
{
  EverCrypt_Hash_Incremental_state_s scrut = *p1;
  EverCrypt_Hash_state_s *hash_state = scrut.hash_state;
  u8 *buf_ = scrut.buf;
  u64 total_len = scrut.total_len;
  u8 *buf_1 = buf_;
  u64 buf[8U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_SHA2_512_s, { .case_SHA2_512_s = buf } };
  EverCrypt_Hash_state_s tmp_hash_state = s;
  EverCrypt_Hash_copy(hash_state, &tmp_hash_state);
  EverCrypt_Hash_update_last(&tmp_hash_state, buf_1, total_len);
  EverCrypt_Hash_finish(&tmp_hash_state, dst);
}

void EverCrypt_Hash_Incremental_finish(EverCrypt_Hash_Incremental_state_s *s, u8 *dst)
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
  u8 *buf1 = scrut.buf;
  EverCrypt_Hash_state_s *hash_state = scrut.hash_state;
  EverCrypt_Hash_free(hash_state);
  KRML_HOST_FREE(buf1);
  KRML_HOST_FREE(s);
}

