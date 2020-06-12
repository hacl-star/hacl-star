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
        KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

bool
EverCrypt_Hash_uu___is_MD5_s(
  Spec_Hash_Definitions_hash_alg uu____159,
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
  Spec_Hash_Definitions_hash_alg uu____189,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_MD5_s)
  {
    return projectee.val.case_MD5_s;
  }
  KRML_HOST_PRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

bool
EverCrypt_Hash_uu___is_SHA1_s(
  Spec_Hash_Definitions_hash_alg uu____213,
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
  Spec_Hash_Definitions_hash_alg uu____243,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA1_s)
  {
    return projectee.val.case_SHA1_s;
  }
  KRML_HOST_PRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

bool
EverCrypt_Hash_uu___is_SHA2_224_s(
  Spec_Hash_Definitions_hash_alg uu____267,
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
  Spec_Hash_Definitions_hash_alg uu____297,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_224_s)
  {
    return projectee.val.case_SHA2_224_s;
  }
  KRML_HOST_PRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

bool
EverCrypt_Hash_uu___is_SHA2_256_s(
  Spec_Hash_Definitions_hash_alg uu____321,
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
  Spec_Hash_Definitions_hash_alg uu____351,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_256_s)
  {
    return projectee.val.case_SHA2_256_s;
  }
  KRML_HOST_PRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

bool
EverCrypt_Hash_uu___is_SHA2_384_s(
  Spec_Hash_Definitions_hash_alg uu____375,
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
  Spec_Hash_Definitions_hash_alg uu____405,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_384_s)
  {
    return projectee.val.case_SHA2_384_s;
  }
  KRML_HOST_PRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

bool
EverCrypt_Hash_uu___is_SHA2_512_s(
  Spec_Hash_Definitions_hash_alg uu____429,
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
  Spec_Hash_Definitions_hash_alg uu____459,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_512_s)
  {
    return projectee.val.case_SHA2_512_s;
  }
  KRML_HOST_PRINTF("KreMLin abort at %s:%d\n%s\n",
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
  KRML_HOST_PRINTF("KreMLin abort at %s:%d\n%s\n",
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
        EverCrypt_Hash_state_s lit;
        lit.tag = EverCrypt_Hash_MD5_s;
        {
          uint32_t *buf = KRML_HOST_CALLOC((uint32_t)4U, sizeof (uint32_t));
          lit.val.case_MD5_s = buf;
          s = lit;
        }
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        EverCrypt_Hash_state_s lit;
        lit.tag = EverCrypt_Hash_SHA1_s;
        {
          uint32_t *buf = KRML_HOST_CALLOC((uint32_t)5U, sizeof (uint32_t));
          lit.val.case_SHA1_s = buf;
          s = lit;
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        EverCrypt_Hash_state_s lit;
        lit.tag = EverCrypt_Hash_SHA2_224_s;
        {
          uint32_t *buf = KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint32_t));
          lit.val.case_SHA2_224_s = buf;
          s = lit;
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        EverCrypt_Hash_state_s lit;
        lit.tag = EverCrypt_Hash_SHA2_256_s;
        {
          uint32_t *buf = KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint32_t));
          lit.val.case_SHA2_256_s = buf;
          s = lit;
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        EverCrypt_Hash_state_s lit;
        lit.tag = EverCrypt_Hash_SHA2_384_s;
        {
          uint64_t *buf = KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint64_t));
          lit.val.case_SHA2_384_s = buf;
          s = lit;
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        EverCrypt_Hash_state_s lit;
        lit.tag = EverCrypt_Hash_SHA2_512_s;
        {
          uint64_t *buf = KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint64_t));
          lit.val.case_SHA2_512_s = buf;
          s = lit;
        }
        break;
      }
    default:
      {
        KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  KRML_CHECK_SIZE(sizeof (EverCrypt_Hash_state_s), (uint32_t)1U);
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
    uint32_t *p1 = scrut.val.case_MD5_s;
    Hacl_Hash_Core_MD5_legacy_init(p1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p1 = scrut.val.case_SHA1_s;
    Hacl_Hash_Core_SHA1_legacy_init(p1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p1 = scrut.val.case_SHA2_224_s;
    Hacl_Hash_Core_SHA2_init_224(p1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p1 = scrut.val.case_SHA2_256_s;
    Hacl_Hash_Core_SHA2_init_256(p1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p1 = scrut.val.case_SHA2_384_s;
    Hacl_Hash_Core_SHA2_init_384(p1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p1 = scrut.val.case_SHA2_512_s;
    Hacl_Hash_Core_SHA2_init_512(p1);
    return;
  }
  KRML_HOST_PRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

static uint32_t
k224_256[64U] =
  {
    (uint32_t)0x428a2f98U, (uint32_t)0x71374491U, (uint32_t)0xb5c0fbcfU, (uint32_t)0xe9b5dba5U,
    (uint32_t)0x3956c25bU, (uint32_t)0x59f111f1U, (uint32_t)0x923f82a4U, (uint32_t)0xab1c5ed5U,
    (uint32_t)0xd807aa98U, (uint32_t)0x12835b01U, (uint32_t)0x243185beU, (uint32_t)0x550c7dc3U,
    (uint32_t)0x72be5d74U, (uint32_t)0x80deb1feU, (uint32_t)0x9bdc06a7U, (uint32_t)0xc19bf174U,
    (uint32_t)0xe49b69c1U, (uint32_t)0xefbe4786U, (uint32_t)0x0fc19dc6U, (uint32_t)0x240ca1ccU,
    (uint32_t)0x2de92c6fU, (uint32_t)0x4a7484aaU, (uint32_t)0x5cb0a9dcU, (uint32_t)0x76f988daU,
    (uint32_t)0x983e5152U, (uint32_t)0xa831c66dU, (uint32_t)0xb00327c8U, (uint32_t)0xbf597fc7U,
    (uint32_t)0xc6e00bf3U, (uint32_t)0xd5a79147U, (uint32_t)0x06ca6351U, (uint32_t)0x14292967U,
    (uint32_t)0x27b70a85U, (uint32_t)0x2e1b2138U, (uint32_t)0x4d2c6dfcU, (uint32_t)0x53380d13U,
    (uint32_t)0x650a7354U, (uint32_t)0x766a0abbU, (uint32_t)0x81c2c92eU, (uint32_t)0x92722c85U,
    (uint32_t)0xa2bfe8a1U, (uint32_t)0xa81a664bU, (uint32_t)0xc24b8b70U, (uint32_t)0xc76c51a3U,
    (uint32_t)0xd192e819U, (uint32_t)0xd6990624U, (uint32_t)0xf40e3585U, (uint32_t)0x106aa070U,
    (uint32_t)0x19a4c116U, (uint32_t)0x1e376c08U, (uint32_t)0x2748774cU, (uint32_t)0x34b0bcb5U,
    (uint32_t)0x391c0cb3U, (uint32_t)0x4ed8aa4aU, (uint32_t)0x5b9cca4fU, (uint32_t)0x682e6ff3U,
    (uint32_t)0x748f82eeU, (uint32_t)0x78a5636fU, (uint32_t)0x84c87814U, (uint32_t)0x8cc70208U,
    (uint32_t)0x90befffaU, (uint32_t)0xa4506cebU, (uint32_t)0xbef9a3f7U, (uint32_t)0xc67178f2U
  };

void EverCrypt_Hash_update_multi_256(uint32_t *s, uint8_t *blocks, uint32_t n)
{
  bool has_shaext = EverCrypt_AutoConfig2_has_shaext();
  bool has_sse = EverCrypt_AutoConfig2_has_sse();
  #if EVERCRYPT_TARGETCONFIG_X64
  if (true && has_shaext && has_sse)
  {
    uint64_t n1 = (uint64_t)n;
    uint64_t scrut = sha256_update(s, blocks, n1, k224_256);
    return;
  }
  #endif
  Hacl_Hash_SHA2_update_multi_256(s, blocks, n);
}

void EverCrypt_Hash_update(EverCrypt_Hash_state_s *s, uint8_t *block)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    uint32_t *p1 = scrut.val.case_MD5_s;
    Hacl_Hash_Core_MD5_legacy_update(p1, block);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p1 = scrut.val.case_SHA1_s;
    Hacl_Hash_Core_SHA1_legacy_update(p1, block);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p1 = scrut.val.case_SHA2_224_s;
    EverCrypt_Hash_update_multi_256(p1, block, (uint32_t)1U);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p1 = scrut.val.case_SHA2_256_s;
    EverCrypt_Hash_update_multi_256(p1, block, (uint32_t)1U);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p1 = scrut.val.case_SHA2_384_s;
    Hacl_Hash_Core_SHA2_update_384(p1, block);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p1 = scrut.val.case_SHA2_512_s;
    Hacl_Hash_Core_SHA2_update_512(p1, block);
    return;
  }
  KRML_HOST_PRINTF("KreMLin abort at %s:%d\n%s\n",
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
    uint32_t *p1 = scrut.val.case_MD5_s;
    uint32_t n = len / (uint32_t)64U;
    Hacl_Hash_MD5_legacy_update_multi(p1, blocks, n);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p1 = scrut.val.case_SHA1_s;
    uint32_t n = len / (uint32_t)64U;
    Hacl_Hash_SHA1_legacy_update_multi(p1, blocks, n);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p1 = scrut.val.case_SHA2_224_s;
    uint32_t n = len / (uint32_t)64U;
    EverCrypt_Hash_update_multi_256(p1, blocks, n);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p1 = scrut.val.case_SHA2_256_s;
    uint32_t n = len / (uint32_t)64U;
    EverCrypt_Hash_update_multi_256(p1, blocks, n);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p1 = scrut.val.case_SHA2_384_s;
    uint32_t n = len / (uint32_t)128U;
    Hacl_Hash_SHA2_update_multi_384(p1, blocks, n);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p1 = scrut.val.case_SHA2_512_s;
    uint32_t n = len / (uint32_t)128U;
    Hacl_Hash_SHA2_update_multi_512(p1, blocks, n);
    return;
  }
  KRML_HOST_PRINTF("KreMLin abort at %s:%d\n%s\n",
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
  uint64_t total_input_len;
  uint32_t pad_len;
  uint32_t tmp_len;
  EverCrypt_Hash_update_multi_256(s, blocks, blocks_n);
  total_input_len = prev_len + (uint64_t)input_len;
  pad_len =
    (uint32_t)1U
    +
      ((uint32_t)128U - ((uint32_t)9U + (uint32_t)(total_input_len % (uint64_t)(uint32_t)64U)))
      % (uint32_t)64U
    + (uint32_t)8U;
  tmp_len = rest_len + pad_len;
  {
    uint8_t tmp_twoblocks[128U] = { 0U };
    uint8_t *tmp = tmp_twoblocks;
    uint8_t *tmp_rest = tmp;
    uint8_t *tmp_pad = tmp + rest_len;
    memcpy(tmp_rest, rest, rest_len * sizeof (rest[0U]));
    Hacl_Hash_Core_SHA2_pad_256(total_input_len, tmp_pad);
    EverCrypt_Hash_update_multi_256(s, tmp, tmp_len / (uint32_t)64U);
  }
}

void EverCrypt_Hash_update_last(EverCrypt_Hash_state_s *s, uint8_t *last, uint64_t total_len)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    uint32_t *p1 = scrut.val.case_MD5_s;
    uint64_t input_len = total_len % (uint64_t)(uint32_t)64U;
    uint64_t prev_len = total_len - input_len;
    Hacl_Hash_MD5_legacy_update_last(p1, prev_len, last, (uint32_t)input_len);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p1 = scrut.val.case_SHA1_s;
    uint64_t input_len = total_len % (uint64_t)(uint32_t)64U;
    uint64_t prev_len = total_len - input_len;
    Hacl_Hash_SHA1_legacy_update_last(p1, prev_len, last, (uint32_t)input_len);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p1 = scrut.val.case_SHA2_224_s;
    uint64_t input_len = total_len % (uint64_t)(uint32_t)64U;
    uint64_t prev_len = total_len - input_len;
    EverCrypt_Hash_update_last_256(p1, prev_len, last, (uint32_t)input_len);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p1 = scrut.val.case_SHA2_256_s;
    uint64_t input_len = total_len % (uint64_t)(uint32_t)64U;
    uint64_t prev_len = total_len - input_len;
    EverCrypt_Hash_update_last_256(p1, prev_len, last, (uint32_t)input_len);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p1 = scrut.val.case_SHA2_384_s;
    uint64_t input_len = total_len % (uint64_t)(uint32_t)128U;
    FStar_UInt128_uint128 prev_len = FStar_UInt128_uint64_to_uint128(total_len - input_len);
    Hacl_Hash_SHA2_update_last_384(p1, prev_len, last, (uint32_t)input_len);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p1 = scrut.val.case_SHA2_512_s;
    uint64_t input_len = total_len % (uint64_t)(uint32_t)128U;
    FStar_UInt128_uint128 prev_len = FStar_UInt128_uint64_to_uint128(total_len - input_len);
    Hacl_Hash_SHA2_update_last_512(p1, prev_len, last, (uint32_t)input_len);
    return;
  }
  KRML_HOST_PRINTF("KreMLin abort at %s:%d\n%s\n",
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
    uint32_t *p1 = scrut.val.case_MD5_s;
    Hacl_Hash_Core_MD5_legacy_finish(p1, dst);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p1 = scrut.val.case_SHA1_s;
    Hacl_Hash_Core_SHA1_legacy_finish(p1, dst);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p1 = scrut.val.case_SHA2_224_s;
    Hacl_Hash_Core_SHA2_finish_224(p1, dst);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p1 = scrut.val.case_SHA2_256_s;
    Hacl_Hash_Core_SHA2_finish_256(p1, dst);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p1 = scrut.val.case_SHA2_384_s;
    Hacl_Hash_Core_SHA2_finish_384(p1, dst);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p1 = scrut.val.case_SHA2_512_s;
    Hacl_Hash_Core_SHA2_finish_512(p1, dst);
    return;
  }
  KRML_HOST_PRINTF("KreMLin abort at %s:%d\n%s\n",
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
    uint32_t *p1 = scrut.val.case_MD5_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p1 = scrut.val.case_SHA1_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p1 = scrut.val.case_SHA2_224_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p1 = scrut.val.case_SHA2_256_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p1 = scrut.val.case_SHA2_384_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p1 = scrut.val.case_SHA2_512_s;
    KRML_HOST_FREE(p1);
  }
  else
  {
    KRML_HOST_PRINTF("KreMLin abort at %s:%d\n%s\n",
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
    uint32_t *p_src = scrut.val.case_MD5_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint32_t *p_dst;
    if (x1.tag == EverCrypt_Hash_MD5_s)
    {
      p_dst = x1.val.case_MD5_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint32_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)4U * sizeof (p_src[0U]));
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p_src = scrut.val.case_SHA1_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint32_t *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA1_s)
    {
      p_dst = x1.val.case_SHA1_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint32_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)5U * sizeof (p_src[0U]));
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p_src = scrut.val.case_SHA2_224_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint32_t *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA2_224_s)
    {
      p_dst = x1.val.case_SHA2_224_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint32_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)8U * sizeof (p_src[0U]));
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p_src = scrut.val.case_SHA2_256_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint32_t *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA2_256_s)
    {
      p_dst = x1.val.case_SHA2_256_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint32_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)8U * sizeof (p_src[0U]));
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p_src = scrut.val.case_SHA2_384_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint64_t *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA2_384_s)
    {
      p_dst = x1.val.case_SHA2_384_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint64_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)8U * sizeof (p_src[0U]));
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p_src = scrut.val.case_SHA2_512_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint64_t *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA2_512_s)
    {
      p_dst = x1.val.case_SHA2_512_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint64_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)8U * sizeof (p_src[0U]));
    return;
  }
  KRML_HOST_PRINTF("KreMLin abort at %s:%d\n%s\n",
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
        KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

typedef struct Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s_____s
{
  EverCrypt_Hash_state_s *block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____;

Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____
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
        KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), sw);
  {
    uint8_t *buf = KRML_HOST_CALLOC(sw, sizeof (uint8_t));
    EverCrypt_Hash_state_s *block_state = EverCrypt_Hash_create_in(a);
    Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ s;
    s.block_state = block_state;
    s.buf = buf;
    s.total_len = (uint64_t)0U;
    KRML_CHECK_SIZE(sizeof (Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____),
      (uint32_t)1U);
    {
      Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____
      *p = KRML_HOST_MALLOC(sizeof (Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____));
      p[0U] = s;
      EverCrypt_Hash_init(block_state);
      return p;
    }
  }
}

void
EverCrypt_Hash_Incremental_init(Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *s;
  uint8_t *buf = scrut.buf;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  Spec_Hash_Definitions_hash_alg i = EverCrypt_Hash_alg_of_state(block_state);
  EverCrypt_Hash_init(block_state);
  {
    Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ lit;
    lit.block_state = block_state;
    lit.buf = buf;
    lit.total_len = (uint64_t)0U;
    s[0U] = lit;
  }
}

void
EverCrypt_Hash_Incremental_update(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ s = *p;
  EverCrypt_Hash_state_s *block_state = s.block_state;
  uint64_t total_len = s.total_len;
  Spec_Hash_Definitions_hash_alg i1 = EverCrypt_Hash_alg_of_state(block_state);
  uint32_t sw0;
  switch (i1)
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
        KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  {
    uint64_t x0 = total_len % (uint64_t)sw0;
    uint32_t sz = (uint32_t)x0;
    uint32_t sw1;
    switch (i1)
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
          KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    if (len < sw1 - sz)
    {
      Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ s1 = *p;
      EverCrypt_Hash_state_s *block_state1 = s1.block_state;
      uint8_t *buf = s1.buf;
      uint64_t total_len1 = s1.total_len;
      Spec_Hash_Definitions_hash_alg i2 = EverCrypt_Hash_alg_of_state(block_state1);
      uint32_t sw;
      switch (i2)
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
            KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      {
        uint64_t x = total_len1 % (uint64_t)sw;
        uint32_t sz1 = (uint32_t)x;
        uint8_t *buf2 = buf + sz1;
        uint64_t total_len2;
        memcpy(buf2, data, len * sizeof (data[0U]));
        total_len2 = total_len1 + (uint64_t)len;
        {
          Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ lit;
          lit.block_state = block_state1;
          lit.buf = buf;
          lit.total_len = total_len2;
          *p = lit;
          return;
        }
      }
    }
    if (sz == (uint32_t)0U)
    {
      Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ s1 = *p;
      EverCrypt_Hash_state_s *block_state1 = s1.block_state;
      uint8_t *buf = s1.buf;
      uint64_t total_len1 = s1.total_len;
      Spec_Hash_Definitions_hash_alg i2 = EverCrypt_Hash_alg_of_state(block_state1);
      uint32_t sw2;
      switch (i2)
      {
        case Spec_Hash_Definitions_MD5:
          {
            sw2 = (uint32_t)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA1:
          {
            sw2 = (uint32_t)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_224:
          {
            sw2 = (uint32_t)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_256:
          {
            sw2 = (uint32_t)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_384:
          {
            sw2 = (uint32_t)128U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_512:
          {
            sw2 = (uint32_t)128U;
            break;
          }
        default:
          {
            KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      {
        uint64_t x = total_len1 % (uint64_t)sw2;
        uint32_t sz1 = (uint32_t)x;
        uint32_t sw3;
        switch (i2)
        {
          case Spec_Hash_Definitions_MD5:
            {
              sw3 = (uint32_t)64U;
              break;
            }
          case Spec_Hash_Definitions_SHA1:
            {
              sw3 = (uint32_t)64U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_224:
            {
              sw3 = (uint32_t)64U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_256:
            {
              sw3 = (uint32_t)64U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_384:
            {
              sw3 = (uint32_t)128U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_512:
            {
              sw3 = (uint32_t)128U;
              break;
            }
          default:
            {
              KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        {
          uint32_t n_blocks = len / sw3;
          uint32_t sw;
          switch (i2)
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
                KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          {
            uint32_t data1_len = n_blocks * sw;
            uint32_t data2_len = len - data1_len;
            uint8_t *data1 = data;
            uint8_t *data2 = data + data1_len;
            uint8_t *dst;
            EverCrypt_Hash_update_multi(block_state1, data1, data1_len);
            dst = buf;
            memcpy(dst, data2, data2_len * sizeof (data2[0U]));
            {
              Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ lit;
              lit.block_state = block_state1;
              lit.buf = buf;
              lit.total_len = total_len1 + (uint64_t)len;
              *p = lit;
              return;
            }
          }
        }
      }
    }
    {
      uint32_t sw2;
      switch (i1)
      {
        case Spec_Hash_Definitions_MD5:
          {
            sw2 = (uint32_t)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA1:
          {
            sw2 = (uint32_t)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_224:
          {
            sw2 = (uint32_t)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_256:
          {
            sw2 = (uint32_t)64U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_384:
          {
            sw2 = (uint32_t)128U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_512:
          {
            sw2 = (uint32_t)128U;
            break;
          }
        default:
          {
            KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      {
        uint32_t diff = sw2 - sz;
        uint8_t *data1 = data;
        uint8_t *data2 = data + diff;
        Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ s10 = *p;
        EverCrypt_Hash_state_s *block_state10 = s10.block_state;
        uint8_t *buf_1 = s10.buf;
        uint64_t total_len10 = s10.total_len;
        Spec_Hash_Definitions_hash_alg i20 = EverCrypt_Hash_alg_of_state(block_state10);
        uint32_t sw3;
        switch (i20)
        {
          case Spec_Hash_Definitions_MD5:
            {
              sw3 = (uint32_t)64U;
              break;
            }
          case Spec_Hash_Definitions_SHA1:
            {
              sw3 = (uint32_t)64U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_224:
            {
              sw3 = (uint32_t)64U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_256:
            {
              sw3 = (uint32_t)64U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_384:
            {
              sw3 = (uint32_t)128U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_512:
            {
              sw3 = (uint32_t)128U;
              break;
            }
          default:
            {
              KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        {
          uint64_t x1 = total_len10 % (uint64_t)sw3;
          uint32_t sz10 = (uint32_t)x1;
          uint32_t sw4;
          switch (i20)
          {
            case Spec_Hash_Definitions_MD5:
              {
                sw4 = (uint32_t)64U;
                break;
              }
            case Spec_Hash_Definitions_SHA1:
              {
                sw4 = (uint32_t)64U;
                break;
              }
            case Spec_Hash_Definitions_SHA2_224:
              {
                sw4 = (uint32_t)64U;
                break;
              }
            case Spec_Hash_Definitions_SHA2_256:
              {
                sw4 = (uint32_t)64U;
                break;
              }
            case Spec_Hash_Definitions_SHA2_384:
              {
                sw4 = (uint32_t)128U;
                break;
              }
            case Spec_Hash_Definitions_SHA2_512:
              {
                sw4 = (uint32_t)128U;
                break;
              }
            default:
              {
                KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
                KRML_HOST_EXIT(253U);
              }
          }
          {
            uint32_t diff1 = sw4 - sz10;
            uint8_t *buf0 = buf_1;
            uint8_t *buf2 = buf0 + sz10;
            uint32_t sw5;
            memcpy(buf2, data1, diff1 * sizeof (data1[0U]));
            switch (i20)
            {
              case Spec_Hash_Definitions_MD5:
                {
                  sw5 = (uint32_t)64U;
                  break;
                }
              case Spec_Hash_Definitions_SHA1:
                {
                  sw5 = (uint32_t)64U;
                  break;
                }
              case Spec_Hash_Definitions_SHA2_224:
                {
                  sw5 = (uint32_t)64U;
                  break;
                }
              case Spec_Hash_Definitions_SHA2_256:
                {
                  sw5 = (uint32_t)64U;
                  break;
                }
              case Spec_Hash_Definitions_SHA2_384:
                {
                  sw5 = (uint32_t)128U;
                  break;
                }
              case Spec_Hash_Definitions_SHA2_512:
                {
                  sw5 = (uint32_t)128U;
                  break;
                }
              default:
                {
                  KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
                  KRML_HOST_EXIT(253U);
                }
            }
            EverCrypt_Hash_update_multi(block_state10, buf0, sw5);
            {
              Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ lit;
              Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ s1;
              EverCrypt_Hash_state_s *block_state1;
              uint8_t *buf;
              uint64_t total_len1;
              Spec_Hash_Definitions_hash_alg i2;
              uint32_t sw6;
              uint64_t x;
              uint32_t sz1;
              uint32_t sw7;
              uint32_t n_blocks;
              uint32_t sw;
              uint32_t data1_len;
              uint32_t data2_len;
              uint8_t *data11;
              uint8_t *data21;
              uint8_t *dst;
              lit.block_state = block_state10;
              lit.buf = buf_1;
              lit.total_len = total_len10 + (uint64_t)diff;
              *p = lit;
              s1 = *p;
              block_state1 = s1.block_state;
              buf = s1.buf;
              total_len1 = s1.total_len;
              i2 = EverCrypt_Hash_alg_of_state(block_state1);
              switch (i2)
              {
                case Spec_Hash_Definitions_MD5:
                  {
                    sw6 = (uint32_t)64U;
                    break;
                  }
                case Spec_Hash_Definitions_SHA1:
                  {
                    sw6 = (uint32_t)64U;
                    break;
                  }
                case Spec_Hash_Definitions_SHA2_224:
                  {
                    sw6 = (uint32_t)64U;
                    break;
                  }
                case Spec_Hash_Definitions_SHA2_256:
                  {
                    sw6 = (uint32_t)64U;
                    break;
                  }
                case Spec_Hash_Definitions_SHA2_384:
                  {
                    sw6 = (uint32_t)128U;
                    break;
                  }
                case Spec_Hash_Definitions_SHA2_512:
                  {
                    sw6 = (uint32_t)128U;
                    break;
                  }
                default:
                  {
                    KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
                    KRML_HOST_EXIT(253U);
                  }
              }
              x = total_len1 % (uint64_t)sw6;
              sz1 = (uint32_t)x;
              switch (i2)
              {
                case Spec_Hash_Definitions_MD5:
                  {
                    sw7 = (uint32_t)64U;
                    break;
                  }
                case Spec_Hash_Definitions_SHA1:
                  {
                    sw7 = (uint32_t)64U;
                    break;
                  }
                case Spec_Hash_Definitions_SHA2_224:
                  {
                    sw7 = (uint32_t)64U;
                    break;
                  }
                case Spec_Hash_Definitions_SHA2_256:
                  {
                    sw7 = (uint32_t)64U;
                    break;
                  }
                case Spec_Hash_Definitions_SHA2_384:
                  {
                    sw7 = (uint32_t)128U;
                    break;
                  }
                case Spec_Hash_Definitions_SHA2_512:
                  {
                    sw7 = (uint32_t)128U;
                    break;
                  }
                default:
                  {
                    KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
                    KRML_HOST_EXIT(253U);
                  }
              }
              n_blocks = (len - diff) / sw7;
              switch (i2)
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
                    KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
                    KRML_HOST_EXIT(253U);
                  }
              }
              data1_len = n_blocks * sw;
              data2_len = len - diff - data1_len;
              data11 = data2;
              data21 = data2 + data1_len;
              EverCrypt_Hash_update_multi(block_state1, data11, data1_len);
              dst = buf;
              memcpy(dst, data21, data2_len * sizeof (data21[0U]));
              {
                Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ lit0;
                lit0.block_state = block_state1;
                lit0.buf = buf;
                lit0.total_len = total_len1 + (uint64_t)(len - diff);
                *p = lit0;
              }
            }
          }
        }
      }
    }
  }
}

void
EverCrypt_Hash_Incremental_finish_md5(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *p;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint8_t *buf_1 = buf_;
  EverCrypt_Hash_state_s s;
  s.tag = EverCrypt_Hash_MD5_s;
  {
    uint32_t buf[4U] = { 0U };
    s.val.case_MD5_s = buf;
    {
      EverCrypt_Hash_state_s tmp_block_state = s;
      EverCrypt_Hash_copy(block_state, &tmp_block_state);
      EverCrypt_Hash_update_last(&tmp_block_state, buf_1, total_len);
      EverCrypt_Hash_finish(&tmp_block_state, dst);
    }
  }
}

void
EverCrypt_Hash_Incremental_finish_sha1(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *p;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint8_t *buf_1 = buf_;
  EverCrypt_Hash_state_s s;
  s.tag = EverCrypt_Hash_SHA1_s;
  {
    uint32_t buf[5U] = { 0U };
    s.val.case_SHA1_s = buf;
    {
      EverCrypt_Hash_state_s tmp_block_state = s;
      EverCrypt_Hash_copy(block_state, &tmp_block_state);
      EverCrypt_Hash_update_last(&tmp_block_state, buf_1, total_len);
      EverCrypt_Hash_finish(&tmp_block_state, dst);
    }
  }
}

void
EverCrypt_Hash_Incremental_finish_sha224(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *p;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint8_t *buf_1 = buf_;
  EverCrypt_Hash_state_s s;
  s.tag = EverCrypt_Hash_SHA2_224_s;
  {
    uint32_t buf[8U] = { 0U };
    s.val.case_SHA2_224_s = buf;
    {
      EverCrypt_Hash_state_s tmp_block_state = s;
      EverCrypt_Hash_copy(block_state, &tmp_block_state);
      EverCrypt_Hash_update_last(&tmp_block_state, buf_1, total_len);
      EverCrypt_Hash_finish(&tmp_block_state, dst);
    }
  }
}

void
EverCrypt_Hash_Incremental_finish_sha256(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *p;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint8_t *buf_1 = buf_;
  EverCrypt_Hash_state_s s;
  s.tag = EverCrypt_Hash_SHA2_256_s;
  {
    uint32_t buf[8U] = { 0U };
    s.val.case_SHA2_256_s = buf;
    {
      EverCrypt_Hash_state_s tmp_block_state = s;
      EverCrypt_Hash_copy(block_state, &tmp_block_state);
      EverCrypt_Hash_update_last(&tmp_block_state, buf_1, total_len);
      EverCrypt_Hash_finish(&tmp_block_state, dst);
    }
  }
}

void
EverCrypt_Hash_Incremental_finish_sha384(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *p;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint8_t *buf_1 = buf_;
  EverCrypt_Hash_state_s s;
  s.tag = EverCrypt_Hash_SHA2_384_s;
  {
    uint64_t buf[8U] = { 0U };
    s.val.case_SHA2_384_s = buf;
    {
      EverCrypt_Hash_state_s tmp_block_state = s;
      EverCrypt_Hash_copy(block_state, &tmp_block_state);
      EverCrypt_Hash_update_last(&tmp_block_state, buf_1, total_len);
      EverCrypt_Hash_finish(&tmp_block_state, dst);
    }
  }
}

void
EverCrypt_Hash_Incremental_finish_sha512(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *p;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint8_t *buf_1 = buf_;
  EverCrypt_Hash_state_s s;
  s.tag = EverCrypt_Hash_SHA2_512_s;
  {
    uint64_t buf[8U] = { 0U };
    s.val.case_SHA2_512_s = buf;
    {
      EverCrypt_Hash_state_s tmp_block_state = s;
      EverCrypt_Hash_copy(block_state, &tmp_block_state);
      EverCrypt_Hash_update_last(&tmp_block_state, buf_1, total_len);
      EverCrypt_Hash_finish(&tmp_block_state, dst);
    }
  }
}

Spec_Hash_Definitions_hash_alg
EverCrypt_Hash_Incremental_alg_of_state(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s
)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *s;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  return EverCrypt_Hash_alg_of_state(block_state);
}

void
EverCrypt_Hash_Incremental_finish(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s,
  uint8_t *dst
)
{
  Spec_Hash_Definitions_hash_alg a1 = EverCrypt_Hash_Incremental_alg_of_state(s);
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
        KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

void
EverCrypt_Hash_Incremental_free(Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *s;
  uint8_t *buf = scrut.buf;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  EverCrypt_Hash_free(block_state);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s);
}

