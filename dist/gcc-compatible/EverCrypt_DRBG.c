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


#include "EverCrypt_DRBG.h"

uint32_t EverCrypt_DRBG_reseed_interval = (uint32_t)1024U;

uint32_t EverCrypt_DRBG_max_output_length = (uint32_t)65536U;

uint32_t EverCrypt_DRBG_max_length = (uint32_t)65536U;

uint32_t EverCrypt_DRBG_max_personalization_string_length = (uint32_t)65536U;

uint32_t EverCrypt_DRBG_max_additional_input_length = (uint32_t)65536U;

uint32_t EverCrypt_DRBG_min_length(Spec_Hash_Definitions_hash_alg a)
{
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        return (uint32_t)16U;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        return (uint32_t)32U;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        return (uint32_t)32U;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        return (uint32_t)32U;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

typedef struct EverCrypt_DRBG_state_s_s
{
  EverCrypt_DRBG_state_s_tags tag;
  union {
    Hacl_HMAC_DRBG_state case_SHA1_s;
    Hacl_HMAC_DRBG_state case_SHA2_256_s;
    Hacl_HMAC_DRBG_state case_SHA2_384_s;
    Hacl_HMAC_DRBG_state case_SHA2_512_s;
  }
  ;
}
EverCrypt_DRBG_state_s;

bool
EverCrypt_DRBG_uu___is_SHA1_s(
  Spec_Hash_Definitions_hash_alg uu____164,
  EverCrypt_DRBG_state_s projectee
)
{
  if (projectee.tag == EverCrypt_DRBG_SHA1_s)
  {
    return true;
  }
  return false;
}

Hacl_HMAC_DRBG_state
EverCrypt_DRBG___proj__SHA1_s__item___0(
  Spec_Hash_Definitions_hash_alg uu____207,
  EverCrypt_DRBG_state_s projectee
)
{
  if (projectee.tag == EverCrypt_DRBG_SHA1_s)
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
EverCrypt_DRBG_uu___is_SHA2_256_s(
  Spec_Hash_Definitions_hash_alg uu____239,
  EverCrypt_DRBG_state_s projectee
)
{
  if (projectee.tag == EverCrypt_DRBG_SHA2_256_s)
  {
    return true;
  }
  return false;
}

Hacl_HMAC_DRBG_state
EverCrypt_DRBG___proj__SHA2_256_s__item___0(
  Spec_Hash_Definitions_hash_alg uu____282,
  EverCrypt_DRBG_state_s projectee
)
{
  if (projectee.tag == EverCrypt_DRBG_SHA2_256_s)
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
EverCrypt_DRBG_uu___is_SHA2_384_s(
  Spec_Hash_Definitions_hash_alg uu____314,
  EverCrypt_DRBG_state_s projectee
)
{
  if (projectee.tag == EverCrypt_DRBG_SHA2_384_s)
  {
    return true;
  }
  return false;
}

Hacl_HMAC_DRBG_state
EverCrypt_DRBG___proj__SHA2_384_s__item___0(
  Spec_Hash_Definitions_hash_alg uu____357,
  EverCrypt_DRBG_state_s projectee
)
{
  if (projectee.tag == EverCrypt_DRBG_SHA2_384_s)
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
EverCrypt_DRBG_uu___is_SHA2_512_s(
  Spec_Hash_Definitions_hash_alg uu____389,
  EverCrypt_DRBG_state_s projectee
)
{
  if (projectee.tag == EverCrypt_DRBG_SHA2_512_s)
  {
    return true;
  }
  return false;
}

Hacl_HMAC_DRBG_state
EverCrypt_DRBG___proj__SHA2_512_s__item___0(
  Spec_Hash_Definitions_hash_alg uu____432,
  EverCrypt_DRBG_state_s projectee
)
{
  if (projectee.tag == EverCrypt_DRBG_SHA2_512_s)
  {
    return projectee.case_SHA2_512_s;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

EverCrypt_DRBG_state_s *EverCrypt_DRBG_create(Spec_Hash_Definitions_hash_alg a)
{
  EverCrypt_DRBG_state_s st;
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        uint8_t *k1 = KRML_HOST_CALLOC((uint32_t)20U, sizeof (uint8_t));
        uint8_t *v1 = KRML_HOST_CALLOC((uint32_t)20U, sizeof (uint8_t));
        uint32_t *ctr = KRML_HOST_MALLOC(sizeof (uint32_t));
        ctr[0U] = (uint32_t)1U;
        st =
          (
            (EverCrypt_DRBG_state_s){
              .tag = EverCrypt_DRBG_SHA1_s,
              { .case_SHA1_s = { .k = k1, .v = v1, .reseed_counter = ctr } }
            }
          );
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        uint8_t *k1 = KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
        uint8_t *v1 = KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
        uint32_t *ctr = KRML_HOST_MALLOC(sizeof (uint32_t));
        ctr[0U] = (uint32_t)1U;
        st =
          (
            (EverCrypt_DRBG_state_s){
              .tag = EverCrypt_DRBG_SHA2_256_s,
              { .case_SHA2_256_s = { .k = k1, .v = v1, .reseed_counter = ctr } }
            }
          );
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        uint8_t *k1 = KRML_HOST_CALLOC((uint32_t)48U, sizeof (uint8_t));
        uint8_t *v1 = KRML_HOST_CALLOC((uint32_t)48U, sizeof (uint8_t));
        uint32_t *ctr = KRML_HOST_MALLOC(sizeof (uint32_t));
        ctr[0U] = (uint32_t)1U;
        st =
          (
            (EverCrypt_DRBG_state_s){
              .tag = EverCrypt_DRBG_SHA2_384_s,
              { .case_SHA2_384_s = { .k = k1, .v = v1, .reseed_counter = ctr } }
            }
          );
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        uint8_t *k1 = KRML_HOST_CALLOC((uint32_t)64U, sizeof (uint8_t));
        uint8_t *v1 = KRML_HOST_CALLOC((uint32_t)64U, sizeof (uint8_t));
        uint32_t *ctr = KRML_HOST_MALLOC(sizeof (uint32_t));
        ctr[0U] = (uint32_t)1U;
        st =
          (
            (EverCrypt_DRBG_state_s){
              .tag = EverCrypt_DRBG_SHA2_512_s,
              { .case_SHA2_512_s = { .k = k1, .v = v1, .reseed_counter = ctr } }
            }
          );
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  KRML_CHECK_SIZE(sizeof (EverCrypt_DRBG_state_s), (uint32_t)1U);
  EverCrypt_DRBG_state_s *buf = KRML_HOST_MALLOC(sizeof (EverCrypt_DRBG_state_s));
  buf[0U] = st;
  return buf;
}

bool
EverCrypt_DRBG_instantiate_sha1(
  EverCrypt_DRBG_state_s *st,
  uint8_t *personalization_string,
  uint32_t personalization_string_len
)
{
  if (personalization_string_len > Hacl_HMAC_DRBG_max_personalization_string_length)
  {
    return false;
  }
  uint32_t entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA1);
  uint32_t nonce_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA1) / (uint32_t)2U;
  uint32_t min_entropy = entropy_input_len + nonce_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), min_entropy);
  uint8_t entropy[min_entropy];
  memset(entropy, 0U, min_entropy * sizeof entropy[0U]);
  bool ok = Lib_RandomBuffer_System_randombytes(entropy, min_entropy);
  if (!ok)
  {
    return false;
  }
  uint8_t *entropy_input = entropy;
  uint8_t *nonce = entropy + entropy_input_len;
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + nonce_len + personalization_string_len);
  uint8_t seed_material[entropy_input_len + nonce_len + personalization_string_len];
  memset(seed_material,
    0U,
    (entropy_input_len + nonce_len + personalization_string_len) * sizeof seed_material[0U]);
  memcpy(seed_material, entropy_input, entropy_input_len * sizeof entropy_input[0U]);
  memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof nonce[0U]);
  memcpy(seed_material + entropy_input_len + nonce_len,
    personalization_string,
    personalization_string_len * sizeof personalization_string[0U]);
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == EverCrypt_DRBG_SHA1_s)
  {
    scrut = st_s.case_SHA1_s;
  }
  else
  {
    scrut = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k1 = scrut.k;
  uint8_t *v1 = scrut.v;
  uint32_t *ctr = scrut.reseed_counter;
  memset(k1, 0U, (uint32_t)20U * sizeof k1[0U]);
  memset(v1, (uint8_t)1U, (uint32_t)20U * sizeof v1[0U]);
  ctr[0U] = (uint32_t)1U;
  uint32_t
  input_len = (uint32_t)21U + entropy_input_len + nonce_len + personalization_string_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t input0[input_len];
  memset(input0, 0U, input_len * sizeof input0[0U]);
  uint8_t *k_ = input0;
  memcpy(k_, v1, (uint32_t)20U * sizeof v1[0U]);
  if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
  {
    memcpy(input0 + (uint32_t)21U,
      seed_material,
      (entropy_input_len + nonce_len + personalization_string_len) * sizeof seed_material[0U]);
  }
  input0[20U] = (uint8_t)0U;
  EverCrypt_HMAC_compute_sha1(k_, k1, (uint32_t)20U, input0, input_len);
  EverCrypt_HMAC_compute_sha1(v1, k_, (uint32_t)20U, v1, (uint32_t)20U);
  memcpy(k1, k_, (uint32_t)20U * sizeof k_[0U]);
  if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
  {
    uint32_t
    input_len0 = (uint32_t)21U + entropy_input_len + nonce_len + personalization_string_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t input[input_len0];
    memset(input, 0U, input_len0 * sizeof input[0U]);
    uint8_t *k_0 = input;
    memcpy(k_0, v1, (uint32_t)20U * sizeof v1[0U]);
    if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
    {
      memcpy(input + (uint32_t)21U,
        seed_material,
        (entropy_input_len + nonce_len + personalization_string_len) * sizeof seed_material[0U]);
    }
    input[20U] = (uint8_t)1U;
    EverCrypt_HMAC_compute_sha1(k_0, k1, (uint32_t)20U, input, input_len0);
    EverCrypt_HMAC_compute_sha1(v1, k_0, (uint32_t)20U, v1, (uint32_t)20U);
    memcpy(k1, k_0, (uint32_t)20U * sizeof k_0[0U]);
  }
  return true;
}

bool
EverCrypt_DRBG_instantiate_sha2_256(
  EverCrypt_DRBG_state_s *st,
  uint8_t *personalization_string,
  uint32_t personalization_string_len
)
{
  if (personalization_string_len > Hacl_HMAC_DRBG_max_personalization_string_length)
  {
    return false;
  }
  uint32_t entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_256);
  uint32_t nonce_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_256) / (uint32_t)2U;
  uint32_t min_entropy = entropy_input_len + nonce_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), min_entropy);
  uint8_t entropy[min_entropy];
  memset(entropy, 0U, min_entropy * sizeof entropy[0U]);
  bool ok = Lib_RandomBuffer_System_randombytes(entropy, min_entropy);
  if (!ok)
  {
    return false;
  }
  uint8_t *entropy_input = entropy;
  uint8_t *nonce = entropy + entropy_input_len;
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + nonce_len + personalization_string_len);
  uint8_t seed_material[entropy_input_len + nonce_len + personalization_string_len];
  memset(seed_material,
    0U,
    (entropy_input_len + nonce_len + personalization_string_len) * sizeof seed_material[0U]);
  memcpy(seed_material, entropy_input, entropy_input_len * sizeof entropy_input[0U]);
  memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof nonce[0U]);
  memcpy(seed_material + entropy_input_len + nonce_len,
    personalization_string,
    personalization_string_len * sizeof personalization_string[0U]);
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == EverCrypt_DRBG_SHA2_256_s)
  {
    scrut = st_s.case_SHA2_256_s;
  }
  else
  {
    scrut = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k1 = scrut.k;
  uint8_t *v1 = scrut.v;
  uint32_t *ctr = scrut.reseed_counter;
  memset(k1, 0U, (uint32_t)32U * sizeof k1[0U]);
  memset(v1, (uint8_t)1U, (uint32_t)32U * sizeof v1[0U]);
  ctr[0U] = (uint32_t)1U;
  uint32_t
  input_len = (uint32_t)33U + entropy_input_len + nonce_len + personalization_string_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t input0[input_len];
  memset(input0, 0U, input_len * sizeof input0[0U]);
  uint8_t *k_ = input0;
  memcpy(k_, v1, (uint32_t)32U * sizeof v1[0U]);
  if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
  {
    memcpy(input0 + (uint32_t)33U,
      seed_material,
      (entropy_input_len + nonce_len + personalization_string_len) * sizeof seed_material[0U]);
  }
  input0[32U] = (uint8_t)0U;
  EverCrypt_HMAC_compute_sha2_256(k_, k1, (uint32_t)32U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_256(v1, k_, (uint32_t)32U, v1, (uint32_t)32U);
  memcpy(k1, k_, (uint32_t)32U * sizeof k_[0U]);
  if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
  {
    uint32_t
    input_len0 = (uint32_t)33U + entropy_input_len + nonce_len + personalization_string_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t input[input_len0];
    memset(input, 0U, input_len0 * sizeof input[0U]);
    uint8_t *k_0 = input;
    memcpy(k_0, v1, (uint32_t)32U * sizeof v1[0U]);
    if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
    {
      memcpy(input + (uint32_t)33U,
        seed_material,
        (entropy_input_len + nonce_len + personalization_string_len) * sizeof seed_material[0U]);
    }
    input[32U] = (uint8_t)1U;
    EverCrypt_HMAC_compute_sha2_256(k_0, k1, (uint32_t)32U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_256(v1, k_0, (uint32_t)32U, v1, (uint32_t)32U);
    memcpy(k1, k_0, (uint32_t)32U * sizeof k_0[0U]);
  }
  return true;
}

bool
EverCrypt_DRBG_instantiate_sha2_384(
  EverCrypt_DRBG_state_s *st,
  uint8_t *personalization_string,
  uint32_t personalization_string_len
)
{
  if (personalization_string_len > Hacl_HMAC_DRBG_max_personalization_string_length)
  {
    return false;
  }
  uint32_t entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_384);
  uint32_t nonce_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_384) / (uint32_t)2U;
  uint32_t min_entropy = entropy_input_len + nonce_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), min_entropy);
  uint8_t entropy[min_entropy];
  memset(entropy, 0U, min_entropy * sizeof entropy[0U]);
  bool ok = Lib_RandomBuffer_System_randombytes(entropy, min_entropy);
  if (!ok)
  {
    return false;
  }
  uint8_t *entropy_input = entropy;
  uint8_t *nonce = entropy + entropy_input_len;
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + nonce_len + personalization_string_len);
  uint8_t seed_material[entropy_input_len + nonce_len + personalization_string_len];
  memset(seed_material,
    0U,
    (entropy_input_len + nonce_len + personalization_string_len) * sizeof seed_material[0U]);
  memcpy(seed_material, entropy_input, entropy_input_len * sizeof entropy_input[0U]);
  memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof nonce[0U]);
  memcpy(seed_material + entropy_input_len + nonce_len,
    personalization_string,
    personalization_string_len * sizeof personalization_string[0U]);
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == EverCrypt_DRBG_SHA2_384_s)
  {
    scrut = st_s.case_SHA2_384_s;
  }
  else
  {
    scrut = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k1 = scrut.k;
  uint8_t *v1 = scrut.v;
  uint32_t *ctr = scrut.reseed_counter;
  memset(k1, 0U, (uint32_t)48U * sizeof k1[0U]);
  memset(v1, (uint8_t)1U, (uint32_t)48U * sizeof v1[0U]);
  ctr[0U] = (uint32_t)1U;
  uint32_t
  input_len = (uint32_t)49U + entropy_input_len + nonce_len + personalization_string_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t input0[input_len];
  memset(input0, 0U, input_len * sizeof input0[0U]);
  uint8_t *k_ = input0;
  memcpy(k_, v1, (uint32_t)48U * sizeof v1[0U]);
  if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
  {
    memcpy(input0 + (uint32_t)49U,
      seed_material,
      (entropy_input_len + nonce_len + personalization_string_len) * sizeof seed_material[0U]);
  }
  input0[48U] = (uint8_t)0U;
  EverCrypt_HMAC_compute_sha2_384(k_, k1, (uint32_t)48U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_384(v1, k_, (uint32_t)48U, v1, (uint32_t)48U);
  memcpy(k1, k_, (uint32_t)48U * sizeof k_[0U]);
  if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
  {
    uint32_t
    input_len0 = (uint32_t)49U + entropy_input_len + nonce_len + personalization_string_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t input[input_len0];
    memset(input, 0U, input_len0 * sizeof input[0U]);
    uint8_t *k_0 = input;
    memcpy(k_0, v1, (uint32_t)48U * sizeof v1[0U]);
    if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
    {
      memcpy(input + (uint32_t)49U,
        seed_material,
        (entropy_input_len + nonce_len + personalization_string_len) * sizeof seed_material[0U]);
    }
    input[48U] = (uint8_t)1U;
    EverCrypt_HMAC_compute_sha2_384(k_0, k1, (uint32_t)48U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_384(v1, k_0, (uint32_t)48U, v1, (uint32_t)48U);
    memcpy(k1, k_0, (uint32_t)48U * sizeof k_0[0U]);
  }
  return true;
}

bool
EverCrypt_DRBG_instantiate_sha2_512(
  EverCrypt_DRBG_state_s *st,
  uint8_t *personalization_string,
  uint32_t personalization_string_len
)
{
  if (personalization_string_len > Hacl_HMAC_DRBG_max_personalization_string_length)
  {
    return false;
  }
  uint32_t entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_512);
  uint32_t nonce_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_512) / (uint32_t)2U;
  uint32_t min_entropy = entropy_input_len + nonce_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), min_entropy);
  uint8_t entropy[min_entropy];
  memset(entropy, 0U, min_entropy * sizeof entropy[0U]);
  bool ok = Lib_RandomBuffer_System_randombytes(entropy, min_entropy);
  if (!ok)
  {
    return false;
  }
  uint8_t *entropy_input = entropy;
  uint8_t *nonce = entropy + entropy_input_len;
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + nonce_len + personalization_string_len);
  uint8_t seed_material[entropy_input_len + nonce_len + personalization_string_len];
  memset(seed_material,
    0U,
    (entropy_input_len + nonce_len + personalization_string_len) * sizeof seed_material[0U]);
  memcpy(seed_material, entropy_input, entropy_input_len * sizeof entropy_input[0U]);
  memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof nonce[0U]);
  memcpy(seed_material + entropy_input_len + nonce_len,
    personalization_string,
    personalization_string_len * sizeof personalization_string[0U]);
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == EverCrypt_DRBG_SHA2_512_s)
  {
    scrut = st_s.case_SHA2_512_s;
  }
  else
  {
    scrut = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k1 = scrut.k;
  uint8_t *v1 = scrut.v;
  uint32_t *ctr = scrut.reseed_counter;
  memset(k1, 0U, (uint32_t)64U * sizeof k1[0U]);
  memset(v1, (uint8_t)1U, (uint32_t)64U * sizeof v1[0U]);
  ctr[0U] = (uint32_t)1U;
  uint32_t
  input_len = (uint32_t)65U + entropy_input_len + nonce_len + personalization_string_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t input0[input_len];
  memset(input0, 0U, input_len * sizeof input0[0U]);
  uint8_t *k_ = input0;
  memcpy(k_, v1, (uint32_t)64U * sizeof v1[0U]);
  if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
  {
    memcpy(input0 + (uint32_t)65U,
      seed_material,
      (entropy_input_len + nonce_len + personalization_string_len) * sizeof seed_material[0U]);
  }
  input0[64U] = (uint8_t)0U;
  EverCrypt_HMAC_compute_sha2_512(k_, k1, (uint32_t)64U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_512(v1, k_, (uint32_t)64U, v1, (uint32_t)64U);
  memcpy(k1, k_, (uint32_t)64U * sizeof k_[0U]);
  if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
  {
    uint32_t
    input_len0 = (uint32_t)65U + entropy_input_len + nonce_len + personalization_string_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t input[input_len0];
    memset(input, 0U, input_len0 * sizeof input[0U]);
    uint8_t *k_0 = input;
    memcpy(k_0, v1, (uint32_t)64U * sizeof v1[0U]);
    if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
    {
      memcpy(input + (uint32_t)65U,
        seed_material,
        (entropy_input_len + nonce_len + personalization_string_len) * sizeof seed_material[0U]);
    }
    input[64U] = (uint8_t)1U;
    EverCrypt_HMAC_compute_sha2_512(k_0, k1, (uint32_t)64U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_512(v1, k_0, (uint32_t)64U, v1, (uint32_t)64U);
    memcpy(k1, k_0, (uint32_t)64U * sizeof k_0[0U]);
  }
  return true;
}

bool
EverCrypt_DRBG_reseed_sha1(
  EverCrypt_DRBG_state_s *st,
  uint8_t *additional_input,
  uint32_t additional_input_len
)
{
  if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
  {
    return false;
  }
  uint32_t entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA1);
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len);
  uint8_t entropy_input[entropy_input_len];
  memset(entropy_input, 0U, entropy_input_len * sizeof entropy_input[0U]);
  bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len);
  if (!ok)
  {
    return false;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_len);
  uint8_t seed_material[entropy_input_len + additional_input_len];
  memset(seed_material,
    0U,
    (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
  memcpy(seed_material, entropy_input, entropy_input_len * sizeof entropy_input[0U]);
  memcpy(seed_material + entropy_input_len,
    additional_input,
    additional_input_len * sizeof additional_input[0U]);
  Hacl_HMAC_DRBG_state uu____0;
  if (st_s.tag == EverCrypt_DRBG_SHA1_s)
  {
    uu____0 = st_s.case_SHA1_s;
  }
  else
  {
    uu____0 =
      KRML_EABORT(Hacl_HMAC_DRBG_state,
        "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k1 = uu____0.k;
  uint8_t *v1 = uu____0.v;
  uint32_t *ctr = uu____0.reseed_counter;
  uint32_t input_len = (uint32_t)21U + entropy_input_len + additional_input_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t input0[input_len];
  memset(input0, 0U, input_len * sizeof input0[0U]);
  uint8_t *k_ = input0;
  memcpy(k_, v1, (uint32_t)20U * sizeof v1[0U]);
  if (entropy_input_len + additional_input_len != (uint32_t)0U)
  {
    memcpy(input0 + (uint32_t)21U,
      seed_material,
      (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
  }
  input0[20U] = (uint8_t)0U;
  EverCrypt_HMAC_compute_sha1(k_, k1, (uint32_t)20U, input0, input_len);
  EverCrypt_HMAC_compute_sha1(v1, k_, (uint32_t)20U, v1, (uint32_t)20U);
  memcpy(k1, k_, (uint32_t)20U * sizeof k_[0U]);
  if (entropy_input_len + additional_input_len != (uint32_t)0U)
  {
    uint32_t input_len0 = (uint32_t)21U + entropy_input_len + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t input[input_len0];
    memset(input, 0U, input_len0 * sizeof input[0U]);
    uint8_t *k_0 = input;
    memcpy(k_0, v1, (uint32_t)20U * sizeof v1[0U]);
    if (entropy_input_len + additional_input_len != (uint32_t)0U)
    {
      memcpy(input + (uint32_t)21U,
        seed_material,
        (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
    }
    input[20U] = (uint8_t)1U;
    EverCrypt_HMAC_compute_sha1(k_0, k1, (uint32_t)20U, input, input_len0);
    EverCrypt_HMAC_compute_sha1(v1, k_0, (uint32_t)20U, v1, (uint32_t)20U);
    memcpy(k1, k_0, (uint32_t)20U * sizeof k_0[0U]);
  }
  ctr[0U] = (uint32_t)1U;
  return true;
}

bool
EverCrypt_DRBG_reseed_sha2_256(
  EverCrypt_DRBG_state_s *st,
  uint8_t *additional_input,
  uint32_t additional_input_len
)
{
  if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
  {
    return false;
  }
  uint32_t entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_256);
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len);
  uint8_t entropy_input[entropy_input_len];
  memset(entropy_input, 0U, entropy_input_len * sizeof entropy_input[0U]);
  bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len);
  if (!ok)
  {
    return false;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_len);
  uint8_t seed_material[entropy_input_len + additional_input_len];
  memset(seed_material,
    0U,
    (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
  memcpy(seed_material, entropy_input, entropy_input_len * sizeof entropy_input[0U]);
  memcpy(seed_material + entropy_input_len,
    additional_input,
    additional_input_len * sizeof additional_input[0U]);
  Hacl_HMAC_DRBG_state uu____0;
  if (st_s.tag == EverCrypt_DRBG_SHA2_256_s)
  {
    uu____0 = st_s.case_SHA2_256_s;
  }
  else
  {
    uu____0 =
      KRML_EABORT(Hacl_HMAC_DRBG_state,
        "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k1 = uu____0.k;
  uint8_t *v1 = uu____0.v;
  uint32_t *ctr = uu____0.reseed_counter;
  uint32_t input_len = (uint32_t)33U + entropy_input_len + additional_input_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t input0[input_len];
  memset(input0, 0U, input_len * sizeof input0[0U]);
  uint8_t *k_ = input0;
  memcpy(k_, v1, (uint32_t)32U * sizeof v1[0U]);
  if (entropy_input_len + additional_input_len != (uint32_t)0U)
  {
    memcpy(input0 + (uint32_t)33U,
      seed_material,
      (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
  }
  input0[32U] = (uint8_t)0U;
  EverCrypt_HMAC_compute_sha2_256(k_, k1, (uint32_t)32U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_256(v1, k_, (uint32_t)32U, v1, (uint32_t)32U);
  memcpy(k1, k_, (uint32_t)32U * sizeof k_[0U]);
  if (entropy_input_len + additional_input_len != (uint32_t)0U)
  {
    uint32_t input_len0 = (uint32_t)33U + entropy_input_len + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t input[input_len0];
    memset(input, 0U, input_len0 * sizeof input[0U]);
    uint8_t *k_0 = input;
    memcpy(k_0, v1, (uint32_t)32U * sizeof v1[0U]);
    if (entropy_input_len + additional_input_len != (uint32_t)0U)
    {
      memcpy(input + (uint32_t)33U,
        seed_material,
        (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
    }
    input[32U] = (uint8_t)1U;
    EverCrypt_HMAC_compute_sha2_256(k_0, k1, (uint32_t)32U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_256(v1, k_0, (uint32_t)32U, v1, (uint32_t)32U);
    memcpy(k1, k_0, (uint32_t)32U * sizeof k_0[0U]);
  }
  ctr[0U] = (uint32_t)1U;
  return true;
}

bool
EverCrypt_DRBG_reseed_sha2_384(
  EverCrypt_DRBG_state_s *st,
  uint8_t *additional_input,
  uint32_t additional_input_len
)
{
  if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
  {
    return false;
  }
  uint32_t entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_384);
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len);
  uint8_t entropy_input[entropy_input_len];
  memset(entropy_input, 0U, entropy_input_len * sizeof entropy_input[0U]);
  bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len);
  if (!ok)
  {
    return false;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_len);
  uint8_t seed_material[entropy_input_len + additional_input_len];
  memset(seed_material,
    0U,
    (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
  memcpy(seed_material, entropy_input, entropy_input_len * sizeof entropy_input[0U]);
  memcpy(seed_material + entropy_input_len,
    additional_input,
    additional_input_len * sizeof additional_input[0U]);
  Hacl_HMAC_DRBG_state uu____0;
  if (st_s.tag == EverCrypt_DRBG_SHA2_384_s)
  {
    uu____0 = st_s.case_SHA2_384_s;
  }
  else
  {
    uu____0 =
      KRML_EABORT(Hacl_HMAC_DRBG_state,
        "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k1 = uu____0.k;
  uint8_t *v1 = uu____0.v;
  uint32_t *ctr = uu____0.reseed_counter;
  uint32_t input_len = (uint32_t)49U + entropy_input_len + additional_input_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t input0[input_len];
  memset(input0, 0U, input_len * sizeof input0[0U]);
  uint8_t *k_ = input0;
  memcpy(k_, v1, (uint32_t)48U * sizeof v1[0U]);
  if (entropy_input_len + additional_input_len != (uint32_t)0U)
  {
    memcpy(input0 + (uint32_t)49U,
      seed_material,
      (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
  }
  input0[48U] = (uint8_t)0U;
  EverCrypt_HMAC_compute_sha2_384(k_, k1, (uint32_t)48U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_384(v1, k_, (uint32_t)48U, v1, (uint32_t)48U);
  memcpy(k1, k_, (uint32_t)48U * sizeof k_[0U]);
  if (entropy_input_len + additional_input_len != (uint32_t)0U)
  {
    uint32_t input_len0 = (uint32_t)49U + entropy_input_len + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t input[input_len0];
    memset(input, 0U, input_len0 * sizeof input[0U]);
    uint8_t *k_0 = input;
    memcpy(k_0, v1, (uint32_t)48U * sizeof v1[0U]);
    if (entropy_input_len + additional_input_len != (uint32_t)0U)
    {
      memcpy(input + (uint32_t)49U,
        seed_material,
        (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
    }
    input[48U] = (uint8_t)1U;
    EverCrypt_HMAC_compute_sha2_384(k_0, k1, (uint32_t)48U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_384(v1, k_0, (uint32_t)48U, v1, (uint32_t)48U);
    memcpy(k1, k_0, (uint32_t)48U * sizeof k_0[0U]);
  }
  ctr[0U] = (uint32_t)1U;
  return true;
}

bool
EverCrypt_DRBG_reseed_sha2_512(
  EverCrypt_DRBG_state_s *st,
  uint8_t *additional_input,
  uint32_t additional_input_len
)
{
  if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
  {
    return false;
  }
  uint32_t entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_512);
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len);
  uint8_t entropy_input[entropy_input_len];
  memset(entropy_input, 0U, entropy_input_len * sizeof entropy_input[0U]);
  bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len);
  if (!ok)
  {
    return false;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_len);
  uint8_t seed_material[entropy_input_len + additional_input_len];
  memset(seed_material,
    0U,
    (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
  memcpy(seed_material, entropy_input, entropy_input_len * sizeof entropy_input[0U]);
  memcpy(seed_material + entropy_input_len,
    additional_input,
    additional_input_len * sizeof additional_input[0U]);
  Hacl_HMAC_DRBG_state uu____0;
  if (st_s.tag == EverCrypt_DRBG_SHA2_512_s)
  {
    uu____0 = st_s.case_SHA2_512_s;
  }
  else
  {
    uu____0 =
      KRML_EABORT(Hacl_HMAC_DRBG_state,
        "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k1 = uu____0.k;
  uint8_t *v1 = uu____0.v;
  uint32_t *ctr = uu____0.reseed_counter;
  uint32_t input_len = (uint32_t)65U + entropy_input_len + additional_input_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t input0[input_len];
  memset(input0, 0U, input_len * sizeof input0[0U]);
  uint8_t *k_ = input0;
  memcpy(k_, v1, (uint32_t)64U * sizeof v1[0U]);
  if (entropy_input_len + additional_input_len != (uint32_t)0U)
  {
    memcpy(input0 + (uint32_t)65U,
      seed_material,
      (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
  }
  input0[64U] = (uint8_t)0U;
  EverCrypt_HMAC_compute_sha2_512(k_, k1, (uint32_t)64U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_512(v1, k_, (uint32_t)64U, v1, (uint32_t)64U);
  memcpy(k1, k_, (uint32_t)64U * sizeof k_[0U]);
  if (entropy_input_len + additional_input_len != (uint32_t)0U)
  {
    uint32_t input_len0 = (uint32_t)65U + entropy_input_len + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t input[input_len0];
    memset(input, 0U, input_len0 * sizeof input[0U]);
    uint8_t *k_0 = input;
    memcpy(k_0, v1, (uint32_t)64U * sizeof v1[0U]);
    if (entropy_input_len + additional_input_len != (uint32_t)0U)
    {
      memcpy(input + (uint32_t)65U,
        seed_material,
        (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
    }
    input[64U] = (uint8_t)1U;
    EverCrypt_HMAC_compute_sha2_512(k_0, k1, (uint32_t)64U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_512(v1, k_0, (uint32_t)64U, v1, (uint32_t)64U);
    memcpy(k1, k_0, (uint32_t)64U * sizeof k_0[0U]);
  }
  ctr[0U] = (uint32_t)1U;
  return true;
}

bool
EverCrypt_DRBG_generate_sha1(
  uint8_t *output,
  EverCrypt_DRBG_state_s *st,
  uint32_t n1,
  uint8_t *additional_input,
  uint32_t additional_input_len
)
{
  if
  (
    additional_input_len
    > Hacl_HMAC_DRBG_max_additional_input_length
    || n1 > Hacl_HMAC_DRBG_max_output_length
  )
  {
    return false;
  }
  uint32_t entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA1);
  bool ok0;
  if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
  {
    ok0 = false;
  }
  else
  {
    uint32_t entropy_input_len1 = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA1);
    KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len1);
    uint8_t entropy_input[entropy_input_len1];
    memset(entropy_input, 0U, entropy_input_len1 * sizeof entropy_input[0U]);
    bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len1);
    bool result;
    if (!ok)
    {
      result = false;
    }
    else
    {
      EverCrypt_DRBG_state_s st_s = *st;
      KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len1 + additional_input_len);
      uint8_t seed_material[entropy_input_len1 + additional_input_len];
      memset(seed_material,
        0U,
        (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
      memcpy(seed_material, entropy_input, entropy_input_len1 * sizeof entropy_input[0U]);
      memcpy(seed_material + entropy_input_len1,
        additional_input,
        additional_input_len * sizeof additional_input[0U]);
      Hacl_HMAC_DRBG_state uu____0;
      if (st_s.tag == EverCrypt_DRBG_SHA1_s)
      {
        uu____0 = st_s.case_SHA1_s;
      }
      else
      {
        uu____0 =
          KRML_EABORT(Hacl_HMAC_DRBG_state,
            "unreachable (pattern matches are exhaustive in F*)");
      }
      uint8_t *k1 = uu____0.k;
      uint8_t *v1 = uu____0.v;
      uint32_t *ctr = uu____0.reseed_counter;
      uint32_t input_len = (uint32_t)21U + entropy_input_len1 + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t input0[input_len];
      memset(input0, 0U, input_len * sizeof input0[0U]);
      uint8_t *k_ = input0;
      memcpy(k_, v1, (uint32_t)20U * sizeof v1[0U]);
      if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
      {
        memcpy(input0 + (uint32_t)21U,
          seed_material,
          (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
      }
      input0[20U] = (uint8_t)0U;
      EverCrypt_HMAC_compute_sha1(k_, k1, (uint32_t)20U, input0, input_len);
      EverCrypt_HMAC_compute_sha1(v1, k_, (uint32_t)20U, v1, (uint32_t)20U);
      memcpy(k1, k_, (uint32_t)20U * sizeof k_[0U]);
      if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
      {
        uint32_t input_len0 = (uint32_t)21U + entropy_input_len1 + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t input[input_len0];
        memset(input, 0U, input_len0 * sizeof input[0U]);
        uint8_t *k_0 = input;
        memcpy(k_0, v1, (uint32_t)20U * sizeof v1[0U]);
        if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
        {
          memcpy(input + (uint32_t)21U,
            seed_material,
            (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
        }
        input[20U] = (uint8_t)1U;
        EverCrypt_HMAC_compute_sha1(k_0, k1, (uint32_t)20U, input, input_len0);
        EverCrypt_HMAC_compute_sha1(v1, k_0, (uint32_t)20U, v1, (uint32_t)20U);
        memcpy(k1, k_0, (uint32_t)20U * sizeof k_0[0U]);
      }
      ctr[0U] = (uint32_t)1U;
      result = true;
    }
    ok0 = result;
  }
  if (!ok0)
  {
    return false;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  Hacl_HMAC_DRBG_state x1;
  if (st_s.tag == EverCrypt_DRBG_SHA1_s)
  {
    x1 = st_s.case_SHA1_s;
  }
  else
  {
    x1 = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  bool b;
  if (x1.reseed_counter[0U] > Hacl_HMAC_DRBG_reseed_interval)
  {
    b = false;
  }
  else
  {
    Hacl_HMAC_DRBG_state scrut;
    if (st_s.tag == EverCrypt_DRBG_SHA1_s)
    {
      scrut = st_s.case_SHA1_s;
    }
    else
    {
      scrut =
        KRML_EABORT(Hacl_HMAC_DRBG_state,
          "unreachable (pattern matches are exhaustive in F*)");
    }
    uint8_t *k1 = scrut.k;
    uint8_t *v1 = scrut.v;
    uint32_t *ctr = scrut.reseed_counter;
    if (additional_input_len > (uint32_t)0U)
    {
      uint32_t input_len = (uint32_t)21U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t input0[input_len];
      memset(input0, 0U, input_len * sizeof input0[0U]);
      uint8_t *k_ = input0;
      memcpy(k_, v1, (uint32_t)20U * sizeof v1[0U]);
      if (additional_input_len != (uint32_t)0U)
      {
        memcpy(input0 + (uint32_t)21U,
          additional_input,
          additional_input_len * sizeof additional_input[0U]);
      }
      input0[20U] = (uint8_t)0U;
      EverCrypt_HMAC_compute_sha1(k_, k1, (uint32_t)20U, input0, input_len);
      EverCrypt_HMAC_compute_sha1(v1, k_, (uint32_t)20U, v1, (uint32_t)20U);
      memcpy(k1, k_, (uint32_t)20U * sizeof k_[0U]);
      if (additional_input_len != (uint32_t)0U)
      {
        uint32_t input_len0 = (uint32_t)21U + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t input[input_len0];
        memset(input, 0U, input_len0 * sizeof input[0U]);
        uint8_t *k_0 = input;
        memcpy(k_0, v1, (uint32_t)20U * sizeof v1[0U]);
        if (additional_input_len != (uint32_t)0U)
        {
          memcpy(input + (uint32_t)21U,
            additional_input,
            additional_input_len * sizeof additional_input[0U]);
        }
        input[20U] = (uint8_t)1U;
        EverCrypt_HMAC_compute_sha1(k_0, k1, (uint32_t)20U, input, input_len0);
        EverCrypt_HMAC_compute_sha1(v1, k_0, (uint32_t)20U, v1, (uint32_t)20U);
        memcpy(k1, k_0, (uint32_t)20U * sizeof k_0[0U]);
      }
    }
    uint8_t *output1 = output;
    uint32_t max1 = n1 / (uint32_t)20U;
    uint8_t *out = output1;
    for (uint32_t i = (uint32_t)0U; i < max1; i = i + (uint32_t)1U)
    {
      EverCrypt_HMAC_compute_sha1(v1, k1, (uint32_t)20U, v1, (uint32_t)20U);
      memcpy(out + i * (uint32_t)20U, v1, (uint32_t)20U * sizeof v1[0U]);
    }
    if (max1 * (uint32_t)20U < n1)
    {
      uint8_t *block = output1 + max1 * (uint32_t)20U;
      EverCrypt_HMAC_compute_sha1(v1, k1, (uint32_t)20U, v1, (uint32_t)20U);
      memcpy(block, v1, (n1 - max1 * (uint32_t)20U) * sizeof v1[0U]);
    }
    uint32_t input_len = (uint32_t)21U + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
    uint8_t input0[input_len];
    memset(input0, 0U, input_len * sizeof input0[0U]);
    uint8_t *k_ = input0;
    memcpy(k_, v1, (uint32_t)20U * sizeof v1[0U]);
    if (additional_input_len != (uint32_t)0U)
    {
      memcpy(input0 + (uint32_t)21U,
        additional_input,
        additional_input_len * sizeof additional_input[0U]);
    }
    input0[20U] = (uint8_t)0U;
    EverCrypt_HMAC_compute_sha1(k_, k1, (uint32_t)20U, input0, input_len);
    EverCrypt_HMAC_compute_sha1(v1, k_, (uint32_t)20U, v1, (uint32_t)20U);
    memcpy(k1, k_, (uint32_t)20U * sizeof k_[0U]);
    if (additional_input_len != (uint32_t)0U)
    {
      uint32_t input_len0 = (uint32_t)21U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
      uint8_t input[input_len0];
      memset(input, 0U, input_len0 * sizeof input[0U]);
      uint8_t *k_0 = input;
      memcpy(k_0, v1, (uint32_t)20U * sizeof v1[0U]);
      if (additional_input_len != (uint32_t)0U)
      {
        memcpy(input + (uint32_t)21U,
          additional_input,
          additional_input_len * sizeof additional_input[0U]);
      }
      input[20U] = (uint8_t)1U;
      EverCrypt_HMAC_compute_sha1(k_0, k1, (uint32_t)20U, input, input_len0);
      EverCrypt_HMAC_compute_sha1(v1, k_0, (uint32_t)20U, v1, (uint32_t)20U);
      memcpy(k1, k_0, (uint32_t)20U * sizeof k_0[0U]);
    }
    uint32_t old_ctr = ctr[0U];
    ctr[0U] = old_ctr + (uint32_t)1U;
    b = true;
  }
  return true;
}

bool
EverCrypt_DRBG_generate_sha2_256(
  uint8_t *output,
  EverCrypt_DRBG_state_s *st,
  uint32_t n1,
  uint8_t *additional_input,
  uint32_t additional_input_len
)
{
  if
  (
    additional_input_len
    > Hacl_HMAC_DRBG_max_additional_input_length
    || n1 > Hacl_HMAC_DRBG_max_output_length
  )
  {
    return false;
  }
  uint32_t entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_256);
  bool ok0;
  if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
  {
    ok0 = false;
  }
  else
  {
    uint32_t entropy_input_len1 = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_256);
    KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len1);
    uint8_t entropy_input[entropy_input_len1];
    memset(entropy_input, 0U, entropy_input_len1 * sizeof entropy_input[0U]);
    bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len1);
    bool result;
    if (!ok)
    {
      result = false;
    }
    else
    {
      EverCrypt_DRBG_state_s st_s = *st;
      KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len1 + additional_input_len);
      uint8_t seed_material[entropy_input_len1 + additional_input_len];
      memset(seed_material,
        0U,
        (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
      memcpy(seed_material, entropy_input, entropy_input_len1 * sizeof entropy_input[0U]);
      memcpy(seed_material + entropy_input_len1,
        additional_input,
        additional_input_len * sizeof additional_input[0U]);
      Hacl_HMAC_DRBG_state uu____0;
      if (st_s.tag == EverCrypt_DRBG_SHA2_256_s)
      {
        uu____0 = st_s.case_SHA2_256_s;
      }
      else
      {
        uu____0 =
          KRML_EABORT(Hacl_HMAC_DRBG_state,
            "unreachable (pattern matches are exhaustive in F*)");
      }
      uint8_t *k1 = uu____0.k;
      uint8_t *v1 = uu____0.v;
      uint32_t *ctr = uu____0.reseed_counter;
      uint32_t input_len = (uint32_t)33U + entropy_input_len1 + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t input0[input_len];
      memset(input0, 0U, input_len * sizeof input0[0U]);
      uint8_t *k_ = input0;
      memcpy(k_, v1, (uint32_t)32U * sizeof v1[0U]);
      if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
      {
        memcpy(input0 + (uint32_t)33U,
          seed_material,
          (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
      }
      input0[32U] = (uint8_t)0U;
      EverCrypt_HMAC_compute_sha2_256(k_, k1, (uint32_t)32U, input0, input_len);
      EverCrypt_HMAC_compute_sha2_256(v1, k_, (uint32_t)32U, v1, (uint32_t)32U);
      memcpy(k1, k_, (uint32_t)32U * sizeof k_[0U]);
      if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
      {
        uint32_t input_len0 = (uint32_t)33U + entropy_input_len1 + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t input[input_len0];
        memset(input, 0U, input_len0 * sizeof input[0U]);
        uint8_t *k_0 = input;
        memcpy(k_0, v1, (uint32_t)32U * sizeof v1[0U]);
        if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
        {
          memcpy(input + (uint32_t)33U,
            seed_material,
            (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
        }
        input[32U] = (uint8_t)1U;
        EverCrypt_HMAC_compute_sha2_256(k_0, k1, (uint32_t)32U, input, input_len0);
        EverCrypt_HMAC_compute_sha2_256(v1, k_0, (uint32_t)32U, v1, (uint32_t)32U);
        memcpy(k1, k_0, (uint32_t)32U * sizeof k_0[0U]);
      }
      ctr[0U] = (uint32_t)1U;
      result = true;
    }
    ok0 = result;
  }
  if (!ok0)
  {
    return false;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  Hacl_HMAC_DRBG_state x1;
  if (st_s.tag == EverCrypt_DRBG_SHA2_256_s)
  {
    x1 = st_s.case_SHA2_256_s;
  }
  else
  {
    x1 = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  bool b;
  if (x1.reseed_counter[0U] > Hacl_HMAC_DRBG_reseed_interval)
  {
    b = false;
  }
  else
  {
    Hacl_HMAC_DRBG_state scrut;
    if (st_s.tag == EverCrypt_DRBG_SHA2_256_s)
    {
      scrut = st_s.case_SHA2_256_s;
    }
    else
    {
      scrut =
        KRML_EABORT(Hacl_HMAC_DRBG_state,
          "unreachable (pattern matches are exhaustive in F*)");
    }
    uint8_t *k1 = scrut.k;
    uint8_t *v1 = scrut.v;
    uint32_t *ctr = scrut.reseed_counter;
    if (additional_input_len > (uint32_t)0U)
    {
      uint32_t input_len = (uint32_t)33U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t input0[input_len];
      memset(input0, 0U, input_len * sizeof input0[0U]);
      uint8_t *k_ = input0;
      memcpy(k_, v1, (uint32_t)32U * sizeof v1[0U]);
      if (additional_input_len != (uint32_t)0U)
      {
        memcpy(input0 + (uint32_t)33U,
          additional_input,
          additional_input_len * sizeof additional_input[0U]);
      }
      input0[32U] = (uint8_t)0U;
      EverCrypt_HMAC_compute_sha2_256(k_, k1, (uint32_t)32U, input0, input_len);
      EverCrypt_HMAC_compute_sha2_256(v1, k_, (uint32_t)32U, v1, (uint32_t)32U);
      memcpy(k1, k_, (uint32_t)32U * sizeof k_[0U]);
      if (additional_input_len != (uint32_t)0U)
      {
        uint32_t input_len0 = (uint32_t)33U + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t input[input_len0];
        memset(input, 0U, input_len0 * sizeof input[0U]);
        uint8_t *k_0 = input;
        memcpy(k_0, v1, (uint32_t)32U * sizeof v1[0U]);
        if (additional_input_len != (uint32_t)0U)
        {
          memcpy(input + (uint32_t)33U,
            additional_input,
            additional_input_len * sizeof additional_input[0U]);
        }
        input[32U] = (uint8_t)1U;
        EverCrypt_HMAC_compute_sha2_256(k_0, k1, (uint32_t)32U, input, input_len0);
        EverCrypt_HMAC_compute_sha2_256(v1, k_0, (uint32_t)32U, v1, (uint32_t)32U);
        memcpy(k1, k_0, (uint32_t)32U * sizeof k_0[0U]);
      }
    }
    uint8_t *output1 = output;
    uint32_t max1 = n1 / (uint32_t)32U;
    uint8_t *out = output1;
    for (uint32_t i = (uint32_t)0U; i < max1; i = i + (uint32_t)1U)
    {
      EverCrypt_HMAC_compute_sha2_256(v1, k1, (uint32_t)32U, v1, (uint32_t)32U);
      memcpy(out + i * (uint32_t)32U, v1, (uint32_t)32U * sizeof v1[0U]);
    }
    if (max1 * (uint32_t)32U < n1)
    {
      uint8_t *block = output1 + max1 * (uint32_t)32U;
      EverCrypt_HMAC_compute_sha2_256(v1, k1, (uint32_t)32U, v1, (uint32_t)32U);
      memcpy(block, v1, (n1 - max1 * (uint32_t)32U) * sizeof v1[0U]);
    }
    uint32_t input_len = (uint32_t)33U + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
    uint8_t input0[input_len];
    memset(input0, 0U, input_len * sizeof input0[0U]);
    uint8_t *k_ = input0;
    memcpy(k_, v1, (uint32_t)32U * sizeof v1[0U]);
    if (additional_input_len != (uint32_t)0U)
    {
      memcpy(input0 + (uint32_t)33U,
        additional_input,
        additional_input_len * sizeof additional_input[0U]);
    }
    input0[32U] = (uint8_t)0U;
    EverCrypt_HMAC_compute_sha2_256(k_, k1, (uint32_t)32U, input0, input_len);
    EverCrypt_HMAC_compute_sha2_256(v1, k_, (uint32_t)32U, v1, (uint32_t)32U);
    memcpy(k1, k_, (uint32_t)32U * sizeof k_[0U]);
    if (additional_input_len != (uint32_t)0U)
    {
      uint32_t input_len0 = (uint32_t)33U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
      uint8_t input[input_len0];
      memset(input, 0U, input_len0 * sizeof input[0U]);
      uint8_t *k_0 = input;
      memcpy(k_0, v1, (uint32_t)32U * sizeof v1[0U]);
      if (additional_input_len != (uint32_t)0U)
      {
        memcpy(input + (uint32_t)33U,
          additional_input,
          additional_input_len * sizeof additional_input[0U]);
      }
      input[32U] = (uint8_t)1U;
      EverCrypt_HMAC_compute_sha2_256(k_0, k1, (uint32_t)32U, input, input_len0);
      EverCrypt_HMAC_compute_sha2_256(v1, k_0, (uint32_t)32U, v1, (uint32_t)32U);
      memcpy(k1, k_0, (uint32_t)32U * sizeof k_0[0U]);
    }
    uint32_t old_ctr = ctr[0U];
    ctr[0U] = old_ctr + (uint32_t)1U;
    b = true;
  }
  return true;
}

bool
EverCrypt_DRBG_generate_sha2_384(
  uint8_t *output,
  EverCrypt_DRBG_state_s *st,
  uint32_t n1,
  uint8_t *additional_input,
  uint32_t additional_input_len
)
{
  if
  (
    additional_input_len
    > Hacl_HMAC_DRBG_max_additional_input_length
    || n1 > Hacl_HMAC_DRBG_max_output_length
  )
  {
    return false;
  }
  uint32_t entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_384);
  bool ok0;
  if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
  {
    ok0 = false;
  }
  else
  {
    uint32_t entropy_input_len1 = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_384);
    KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len1);
    uint8_t entropy_input[entropy_input_len1];
    memset(entropy_input, 0U, entropy_input_len1 * sizeof entropy_input[0U]);
    bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len1);
    bool result;
    if (!ok)
    {
      result = false;
    }
    else
    {
      EverCrypt_DRBG_state_s st_s = *st;
      KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len1 + additional_input_len);
      uint8_t seed_material[entropy_input_len1 + additional_input_len];
      memset(seed_material,
        0U,
        (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
      memcpy(seed_material, entropy_input, entropy_input_len1 * sizeof entropy_input[0U]);
      memcpy(seed_material + entropy_input_len1,
        additional_input,
        additional_input_len * sizeof additional_input[0U]);
      Hacl_HMAC_DRBG_state uu____0;
      if (st_s.tag == EverCrypt_DRBG_SHA2_384_s)
      {
        uu____0 = st_s.case_SHA2_384_s;
      }
      else
      {
        uu____0 =
          KRML_EABORT(Hacl_HMAC_DRBG_state,
            "unreachable (pattern matches are exhaustive in F*)");
      }
      uint8_t *k1 = uu____0.k;
      uint8_t *v1 = uu____0.v;
      uint32_t *ctr = uu____0.reseed_counter;
      uint32_t input_len = (uint32_t)49U + entropy_input_len1 + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t input0[input_len];
      memset(input0, 0U, input_len * sizeof input0[0U]);
      uint8_t *k_ = input0;
      memcpy(k_, v1, (uint32_t)48U * sizeof v1[0U]);
      if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
      {
        memcpy(input0 + (uint32_t)49U,
          seed_material,
          (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
      }
      input0[48U] = (uint8_t)0U;
      EverCrypt_HMAC_compute_sha2_384(k_, k1, (uint32_t)48U, input0, input_len);
      EverCrypt_HMAC_compute_sha2_384(v1, k_, (uint32_t)48U, v1, (uint32_t)48U);
      memcpy(k1, k_, (uint32_t)48U * sizeof k_[0U]);
      if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
      {
        uint32_t input_len0 = (uint32_t)49U + entropy_input_len1 + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t input[input_len0];
        memset(input, 0U, input_len0 * sizeof input[0U]);
        uint8_t *k_0 = input;
        memcpy(k_0, v1, (uint32_t)48U * sizeof v1[0U]);
        if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
        {
          memcpy(input + (uint32_t)49U,
            seed_material,
            (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
        }
        input[48U] = (uint8_t)1U;
        EverCrypt_HMAC_compute_sha2_384(k_0, k1, (uint32_t)48U, input, input_len0);
        EverCrypt_HMAC_compute_sha2_384(v1, k_0, (uint32_t)48U, v1, (uint32_t)48U);
        memcpy(k1, k_0, (uint32_t)48U * sizeof k_0[0U]);
      }
      ctr[0U] = (uint32_t)1U;
      result = true;
    }
    ok0 = result;
  }
  if (!ok0)
  {
    return false;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  Hacl_HMAC_DRBG_state x1;
  if (st_s.tag == EverCrypt_DRBG_SHA2_384_s)
  {
    x1 = st_s.case_SHA2_384_s;
  }
  else
  {
    x1 = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  bool b;
  if (x1.reseed_counter[0U] > Hacl_HMAC_DRBG_reseed_interval)
  {
    b = false;
  }
  else
  {
    Hacl_HMAC_DRBG_state scrut;
    if (st_s.tag == EverCrypt_DRBG_SHA2_384_s)
    {
      scrut = st_s.case_SHA2_384_s;
    }
    else
    {
      scrut =
        KRML_EABORT(Hacl_HMAC_DRBG_state,
          "unreachable (pattern matches are exhaustive in F*)");
    }
    uint8_t *k1 = scrut.k;
    uint8_t *v1 = scrut.v;
    uint32_t *ctr = scrut.reseed_counter;
    if (additional_input_len > (uint32_t)0U)
    {
      uint32_t input_len = (uint32_t)49U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t input0[input_len];
      memset(input0, 0U, input_len * sizeof input0[0U]);
      uint8_t *k_ = input0;
      memcpy(k_, v1, (uint32_t)48U * sizeof v1[0U]);
      if (additional_input_len != (uint32_t)0U)
      {
        memcpy(input0 + (uint32_t)49U,
          additional_input,
          additional_input_len * sizeof additional_input[0U]);
      }
      input0[48U] = (uint8_t)0U;
      EverCrypt_HMAC_compute_sha2_384(k_, k1, (uint32_t)48U, input0, input_len);
      EverCrypt_HMAC_compute_sha2_384(v1, k_, (uint32_t)48U, v1, (uint32_t)48U);
      memcpy(k1, k_, (uint32_t)48U * sizeof k_[0U]);
      if (additional_input_len != (uint32_t)0U)
      {
        uint32_t input_len0 = (uint32_t)49U + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t input[input_len0];
        memset(input, 0U, input_len0 * sizeof input[0U]);
        uint8_t *k_0 = input;
        memcpy(k_0, v1, (uint32_t)48U * sizeof v1[0U]);
        if (additional_input_len != (uint32_t)0U)
        {
          memcpy(input + (uint32_t)49U,
            additional_input,
            additional_input_len * sizeof additional_input[0U]);
        }
        input[48U] = (uint8_t)1U;
        EverCrypt_HMAC_compute_sha2_384(k_0, k1, (uint32_t)48U, input, input_len0);
        EverCrypt_HMAC_compute_sha2_384(v1, k_0, (uint32_t)48U, v1, (uint32_t)48U);
        memcpy(k1, k_0, (uint32_t)48U * sizeof k_0[0U]);
      }
    }
    uint8_t *output1 = output;
    uint32_t max1 = n1 / (uint32_t)48U;
    uint8_t *out = output1;
    for (uint32_t i = (uint32_t)0U; i < max1; i = i + (uint32_t)1U)
    {
      EverCrypt_HMAC_compute_sha2_384(v1, k1, (uint32_t)48U, v1, (uint32_t)48U);
      memcpy(out + i * (uint32_t)48U, v1, (uint32_t)48U * sizeof v1[0U]);
    }
    if (max1 * (uint32_t)48U < n1)
    {
      uint8_t *block = output1 + max1 * (uint32_t)48U;
      EverCrypt_HMAC_compute_sha2_384(v1, k1, (uint32_t)48U, v1, (uint32_t)48U);
      memcpy(block, v1, (n1 - max1 * (uint32_t)48U) * sizeof v1[0U]);
    }
    uint32_t input_len = (uint32_t)49U + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
    uint8_t input0[input_len];
    memset(input0, 0U, input_len * sizeof input0[0U]);
    uint8_t *k_ = input0;
    memcpy(k_, v1, (uint32_t)48U * sizeof v1[0U]);
    if (additional_input_len != (uint32_t)0U)
    {
      memcpy(input0 + (uint32_t)49U,
        additional_input,
        additional_input_len * sizeof additional_input[0U]);
    }
    input0[48U] = (uint8_t)0U;
    EverCrypt_HMAC_compute_sha2_384(k_, k1, (uint32_t)48U, input0, input_len);
    EverCrypt_HMAC_compute_sha2_384(v1, k_, (uint32_t)48U, v1, (uint32_t)48U);
    memcpy(k1, k_, (uint32_t)48U * sizeof k_[0U]);
    if (additional_input_len != (uint32_t)0U)
    {
      uint32_t input_len0 = (uint32_t)49U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
      uint8_t input[input_len0];
      memset(input, 0U, input_len0 * sizeof input[0U]);
      uint8_t *k_0 = input;
      memcpy(k_0, v1, (uint32_t)48U * sizeof v1[0U]);
      if (additional_input_len != (uint32_t)0U)
      {
        memcpy(input + (uint32_t)49U,
          additional_input,
          additional_input_len * sizeof additional_input[0U]);
      }
      input[48U] = (uint8_t)1U;
      EverCrypt_HMAC_compute_sha2_384(k_0, k1, (uint32_t)48U, input, input_len0);
      EverCrypt_HMAC_compute_sha2_384(v1, k_0, (uint32_t)48U, v1, (uint32_t)48U);
      memcpy(k1, k_0, (uint32_t)48U * sizeof k_0[0U]);
    }
    uint32_t old_ctr = ctr[0U];
    ctr[0U] = old_ctr + (uint32_t)1U;
    b = true;
  }
  return true;
}

bool
EverCrypt_DRBG_generate_sha2_512(
  uint8_t *output,
  EverCrypt_DRBG_state_s *st,
  uint32_t n1,
  uint8_t *additional_input,
  uint32_t additional_input_len
)
{
  if
  (
    additional_input_len
    > Hacl_HMAC_DRBG_max_additional_input_length
    || n1 > Hacl_HMAC_DRBG_max_output_length
  )
  {
    return false;
  }
  uint32_t entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_512);
  bool ok0;
  if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
  {
    ok0 = false;
  }
  else
  {
    uint32_t entropy_input_len1 = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_512);
    KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len1);
    uint8_t entropy_input[entropy_input_len1];
    memset(entropy_input, 0U, entropy_input_len1 * sizeof entropy_input[0U]);
    bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len1);
    bool result;
    if (!ok)
    {
      result = false;
    }
    else
    {
      EverCrypt_DRBG_state_s st_s = *st;
      KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len1 + additional_input_len);
      uint8_t seed_material[entropy_input_len1 + additional_input_len];
      memset(seed_material,
        0U,
        (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
      memcpy(seed_material, entropy_input, entropy_input_len1 * sizeof entropy_input[0U]);
      memcpy(seed_material + entropy_input_len1,
        additional_input,
        additional_input_len * sizeof additional_input[0U]);
      Hacl_HMAC_DRBG_state uu____0;
      if (st_s.tag == EverCrypt_DRBG_SHA2_512_s)
      {
        uu____0 = st_s.case_SHA2_512_s;
      }
      else
      {
        uu____0 =
          KRML_EABORT(Hacl_HMAC_DRBG_state,
            "unreachable (pattern matches are exhaustive in F*)");
      }
      uint8_t *k1 = uu____0.k;
      uint8_t *v1 = uu____0.v;
      uint32_t *ctr = uu____0.reseed_counter;
      uint32_t input_len = (uint32_t)65U + entropy_input_len1 + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t input0[input_len];
      memset(input0, 0U, input_len * sizeof input0[0U]);
      uint8_t *k_ = input0;
      memcpy(k_, v1, (uint32_t)64U * sizeof v1[0U]);
      if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
      {
        memcpy(input0 + (uint32_t)65U,
          seed_material,
          (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
      }
      input0[64U] = (uint8_t)0U;
      EverCrypt_HMAC_compute_sha2_512(k_, k1, (uint32_t)64U, input0, input_len);
      EverCrypt_HMAC_compute_sha2_512(v1, k_, (uint32_t)64U, v1, (uint32_t)64U);
      memcpy(k1, k_, (uint32_t)64U * sizeof k_[0U]);
      if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
      {
        uint32_t input_len0 = (uint32_t)65U + entropy_input_len1 + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t input[input_len0];
        memset(input, 0U, input_len0 * sizeof input[0U]);
        uint8_t *k_0 = input;
        memcpy(k_0, v1, (uint32_t)64U * sizeof v1[0U]);
        if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
        {
          memcpy(input + (uint32_t)65U,
            seed_material,
            (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
        }
        input[64U] = (uint8_t)1U;
        EverCrypt_HMAC_compute_sha2_512(k_0, k1, (uint32_t)64U, input, input_len0);
        EverCrypt_HMAC_compute_sha2_512(v1, k_0, (uint32_t)64U, v1, (uint32_t)64U);
        memcpy(k1, k_0, (uint32_t)64U * sizeof k_0[0U]);
      }
      ctr[0U] = (uint32_t)1U;
      result = true;
    }
    ok0 = result;
  }
  if (!ok0)
  {
    return false;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  Hacl_HMAC_DRBG_state x1;
  if (st_s.tag == EverCrypt_DRBG_SHA2_512_s)
  {
    x1 = st_s.case_SHA2_512_s;
  }
  else
  {
    x1 = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  bool b;
  if (x1.reseed_counter[0U] > Hacl_HMAC_DRBG_reseed_interval)
  {
    b = false;
  }
  else
  {
    Hacl_HMAC_DRBG_state scrut;
    if (st_s.tag == EverCrypt_DRBG_SHA2_512_s)
    {
      scrut = st_s.case_SHA2_512_s;
    }
    else
    {
      scrut =
        KRML_EABORT(Hacl_HMAC_DRBG_state,
          "unreachable (pattern matches are exhaustive in F*)");
    }
    uint8_t *k1 = scrut.k;
    uint8_t *v1 = scrut.v;
    uint32_t *ctr = scrut.reseed_counter;
    if (additional_input_len > (uint32_t)0U)
    {
      uint32_t input_len = (uint32_t)65U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t input0[input_len];
      memset(input0, 0U, input_len * sizeof input0[0U]);
      uint8_t *k_ = input0;
      memcpy(k_, v1, (uint32_t)64U * sizeof v1[0U]);
      if (additional_input_len != (uint32_t)0U)
      {
        memcpy(input0 + (uint32_t)65U,
          additional_input,
          additional_input_len * sizeof additional_input[0U]);
      }
      input0[64U] = (uint8_t)0U;
      EverCrypt_HMAC_compute_sha2_512(k_, k1, (uint32_t)64U, input0, input_len);
      EverCrypt_HMAC_compute_sha2_512(v1, k_, (uint32_t)64U, v1, (uint32_t)64U);
      memcpy(k1, k_, (uint32_t)64U * sizeof k_[0U]);
      if (additional_input_len != (uint32_t)0U)
      {
        uint32_t input_len0 = (uint32_t)65U + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t input[input_len0];
        memset(input, 0U, input_len0 * sizeof input[0U]);
        uint8_t *k_0 = input;
        memcpy(k_0, v1, (uint32_t)64U * sizeof v1[0U]);
        if (additional_input_len != (uint32_t)0U)
        {
          memcpy(input + (uint32_t)65U,
            additional_input,
            additional_input_len * sizeof additional_input[0U]);
        }
        input[64U] = (uint8_t)1U;
        EverCrypt_HMAC_compute_sha2_512(k_0, k1, (uint32_t)64U, input, input_len0);
        EverCrypt_HMAC_compute_sha2_512(v1, k_0, (uint32_t)64U, v1, (uint32_t)64U);
        memcpy(k1, k_0, (uint32_t)64U * sizeof k_0[0U]);
      }
    }
    uint8_t *output1 = output;
    uint32_t max1 = n1 / (uint32_t)64U;
    uint8_t *out = output1;
    for (uint32_t i = (uint32_t)0U; i < max1; i = i + (uint32_t)1U)
    {
      EverCrypt_HMAC_compute_sha2_512(v1, k1, (uint32_t)64U, v1, (uint32_t)64U);
      memcpy(out + i * (uint32_t)64U, v1, (uint32_t)64U * sizeof v1[0U]);
    }
    if (max1 * (uint32_t)64U < n1)
    {
      uint8_t *block = output1 + max1 * (uint32_t)64U;
      EverCrypt_HMAC_compute_sha2_512(v1, k1, (uint32_t)64U, v1, (uint32_t)64U);
      memcpy(block, v1, (n1 - max1 * (uint32_t)64U) * sizeof v1[0U]);
    }
    uint32_t input_len = (uint32_t)65U + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
    uint8_t input0[input_len];
    memset(input0, 0U, input_len * sizeof input0[0U]);
    uint8_t *k_ = input0;
    memcpy(k_, v1, (uint32_t)64U * sizeof v1[0U]);
    if (additional_input_len != (uint32_t)0U)
    {
      memcpy(input0 + (uint32_t)65U,
        additional_input,
        additional_input_len * sizeof additional_input[0U]);
    }
    input0[64U] = (uint8_t)0U;
    EverCrypt_HMAC_compute_sha2_512(k_, k1, (uint32_t)64U, input0, input_len);
    EverCrypt_HMAC_compute_sha2_512(v1, k_, (uint32_t)64U, v1, (uint32_t)64U);
    memcpy(k1, k_, (uint32_t)64U * sizeof k_[0U]);
    if (additional_input_len != (uint32_t)0U)
    {
      uint32_t input_len0 = (uint32_t)65U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
      uint8_t input[input_len0];
      memset(input, 0U, input_len0 * sizeof input[0U]);
      uint8_t *k_0 = input;
      memcpy(k_0, v1, (uint32_t)64U * sizeof v1[0U]);
      if (additional_input_len != (uint32_t)0U)
      {
        memcpy(input + (uint32_t)65U,
          additional_input,
          additional_input_len * sizeof additional_input[0U]);
      }
      input[64U] = (uint8_t)1U;
      EverCrypt_HMAC_compute_sha2_512(k_0, k1, (uint32_t)64U, input, input_len0);
      EverCrypt_HMAC_compute_sha2_512(v1, k_0, (uint32_t)64U, v1, (uint32_t)64U);
      memcpy(k1, k_0, (uint32_t)64U * sizeof k_0[0U]);
    }
    uint32_t old_ctr = ctr[0U];
    ctr[0U] = old_ctr + (uint32_t)1U;
    b = true;
  }
  return true;
}

void EverCrypt_DRBG_uninstantiate_sha1(EverCrypt_DRBG_state_s *st)
{
  EverCrypt_DRBG_state_s st_s = *st;
  Hacl_HMAC_DRBG_state s;
  if (st_s.tag == EverCrypt_DRBG_SHA1_s)
  {
    s = st_s.case_SHA1_s;
  }
  else
  {
    s = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k1 = s.k;
  uint8_t *v1 = s.v;
  uint32_t *ctr = s.reseed_counter;
  Lib_Memzero_clear_words_u8((uint32_t)20U, k1);
  Lib_Memzero_clear_words_u8((uint32_t)20U, v1);
  ctr[0U] = (uint32_t)0U;
  KRML_HOST_FREE(k1);
  KRML_HOST_FREE(v1);
  KRML_HOST_FREE(ctr);
  KRML_HOST_FREE(st);
}

void EverCrypt_DRBG_uninstantiate_sha2_256(EverCrypt_DRBG_state_s *st)
{
  EverCrypt_DRBG_state_s st_s = *st;
  Hacl_HMAC_DRBG_state s;
  if (st_s.tag == EverCrypt_DRBG_SHA2_256_s)
  {
    s = st_s.case_SHA2_256_s;
  }
  else
  {
    s = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k1 = s.k;
  uint8_t *v1 = s.v;
  uint32_t *ctr = s.reseed_counter;
  Lib_Memzero_clear_words_u8((uint32_t)32U, k1);
  Lib_Memzero_clear_words_u8((uint32_t)32U, v1);
  ctr[0U] = (uint32_t)0U;
  KRML_HOST_FREE(k1);
  KRML_HOST_FREE(v1);
  KRML_HOST_FREE(ctr);
  KRML_HOST_FREE(st);
}

void EverCrypt_DRBG_uninstantiate_sha2_384(EverCrypt_DRBG_state_s *st)
{
  EverCrypt_DRBG_state_s st_s = *st;
  Hacl_HMAC_DRBG_state s;
  if (st_s.tag == EverCrypt_DRBG_SHA2_384_s)
  {
    s = st_s.case_SHA2_384_s;
  }
  else
  {
    s = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k1 = s.k;
  uint8_t *v1 = s.v;
  uint32_t *ctr = s.reseed_counter;
  Lib_Memzero_clear_words_u8((uint32_t)48U, k1);
  Lib_Memzero_clear_words_u8((uint32_t)48U, v1);
  ctr[0U] = (uint32_t)0U;
  KRML_HOST_FREE(k1);
  KRML_HOST_FREE(v1);
  KRML_HOST_FREE(ctr);
  KRML_HOST_FREE(st);
}

void EverCrypt_DRBG_uninstantiate_sha2_512(EverCrypt_DRBG_state_s *st)
{
  EverCrypt_DRBG_state_s st_s = *st;
  Hacl_HMAC_DRBG_state s;
  if (st_s.tag == EverCrypt_DRBG_SHA2_512_s)
  {
    s = st_s.case_SHA2_512_s;
  }
  else
  {
    s = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k1 = s.k;
  uint8_t *v1 = s.v;
  uint32_t *ctr = s.reseed_counter;
  Lib_Memzero_clear_words_u8((uint32_t)64U, k1);
  Lib_Memzero_clear_words_u8((uint32_t)64U, v1);
  ctr[0U] = (uint32_t)0U;
  KRML_HOST_FREE(k1);
  KRML_HOST_FREE(v1);
  KRML_HOST_FREE(ctr);
  KRML_HOST_FREE(st);
}

bool
EverCrypt_DRBG_instantiate(
  EverCrypt_DRBG_state_s *st,
  uint8_t *personalization_string,
  uint32_t personalization_string_len
)
{
  EverCrypt_DRBG_state_s scrut = *st;
  if (scrut.tag == EverCrypt_DRBG_SHA1_s)
  {
    return EverCrypt_DRBG_instantiate_sha1(st, personalization_string, personalization_string_len);
  }
  if (scrut.tag == EverCrypt_DRBG_SHA2_256_s)
  {
    return
      EverCrypt_DRBG_instantiate_sha2_256(st,
        personalization_string,
        personalization_string_len);
  }
  if (scrut.tag == EverCrypt_DRBG_SHA2_384_s)
  {
    return
      EverCrypt_DRBG_instantiate_sha2_384(st,
        personalization_string,
        personalization_string_len);
  }
  if (scrut.tag == EverCrypt_DRBG_SHA2_512_s)
  {
    return
      EverCrypt_DRBG_instantiate_sha2_512(st,
        personalization_string,
        personalization_string_len);
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

bool
EverCrypt_DRBG_reseed(
  EverCrypt_DRBG_state_s *st,
  uint8_t *additional_input,
  uint32_t additional_input_len
)
{
  EverCrypt_DRBG_state_s scrut = *st;
  if (scrut.tag == EverCrypt_DRBG_SHA1_s)
  {
    return EverCrypt_DRBG_reseed_sha1(st, additional_input, additional_input_len);
  }
  if (scrut.tag == EverCrypt_DRBG_SHA2_256_s)
  {
    return EverCrypt_DRBG_reseed_sha2_256(st, additional_input, additional_input_len);
  }
  if (scrut.tag == EverCrypt_DRBG_SHA2_384_s)
  {
    return EverCrypt_DRBG_reseed_sha2_384(st, additional_input, additional_input_len);
  }
  if (scrut.tag == EverCrypt_DRBG_SHA2_512_s)
  {
    return EverCrypt_DRBG_reseed_sha2_512(st, additional_input, additional_input_len);
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

bool
EverCrypt_DRBG_generate(
  uint8_t *output,
  EverCrypt_DRBG_state_s *st,
  uint32_t n1,
  uint8_t *additional_input,
  uint32_t additional_input_len
)
{
  EverCrypt_DRBG_state_s scrut = *st;
  if (scrut.tag == EverCrypt_DRBG_SHA1_s)
  {
    return EverCrypt_DRBG_generate_sha1(output, st, n1, additional_input, additional_input_len);
  }
  if (scrut.tag == EverCrypt_DRBG_SHA2_256_s)
  {
    return
      EverCrypt_DRBG_generate_sha2_256(output,
        st,
        n1,
        additional_input,
        additional_input_len);
  }
  if (scrut.tag == EverCrypt_DRBG_SHA2_384_s)
  {
    return
      EverCrypt_DRBG_generate_sha2_384(output,
        st,
        n1,
        additional_input,
        additional_input_len);
  }
  if (scrut.tag == EverCrypt_DRBG_SHA2_512_s)
  {
    return
      EverCrypt_DRBG_generate_sha2_512(output,
        st,
        n1,
        additional_input,
        additional_input_len);
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

void EverCrypt_DRBG_uninstantiate(EverCrypt_DRBG_state_s *st)
{
  EverCrypt_DRBG_state_s scrut = *st;
  if (scrut.tag == EverCrypt_DRBG_SHA1_s)
  {
    EverCrypt_DRBG_uninstantiate_sha1(st);
    return;
  }
  if (scrut.tag == EverCrypt_DRBG_SHA2_256_s)
  {
    EverCrypt_DRBG_uninstantiate_sha2_256(st);
    return;
  }
  if (scrut.tag == EverCrypt_DRBG_SHA2_384_s)
  {
    EverCrypt_DRBG_uninstantiate_sha2_384(st);
    return;
  }
  if (scrut.tag == EverCrypt_DRBG_SHA2_512_s)
  {
    EverCrypt_DRBG_uninstantiate_sha2_512(st);
    return;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

