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
  Spec_Hash_Definitions_hash_alg uu____121,
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
  Spec_Hash_Definitions_hash_alg uu____146,
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
  Spec_Hash_Definitions_hash_alg uu____167,
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
  Spec_Hash_Definitions_hash_alg uu____192,
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
  Spec_Hash_Definitions_hash_alg uu____213,
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
  Spec_Hash_Definitions_hash_alg uu____238,
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
  Spec_Hash_Definitions_hash_alg uu____259,
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
  Spec_Hash_Definitions_hash_alg uu____284,
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
        uint8_t *k = KRML_HOST_CALLOC((uint32_t)20U, sizeof (uint8_t));
        uint8_t *v = KRML_HOST_CALLOC((uint32_t)20U, sizeof (uint8_t));
        uint32_t *ctr = KRML_HOST_MALLOC(sizeof (uint32_t));
        ctr[0U] = (uint32_t)1U;
        st =
          (
            (EverCrypt_DRBG_state_s){
              .tag = EverCrypt_DRBG_SHA1_s,
              { .case_SHA1_s = { .k = k, .v = v, .reseed_counter = ctr } }
            }
          );
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        uint8_t *k = KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
        uint8_t *v = KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
        uint32_t *ctr = KRML_HOST_MALLOC(sizeof (uint32_t));
        ctr[0U] = (uint32_t)1U;
        st =
          (
            (EverCrypt_DRBG_state_s){
              .tag = EverCrypt_DRBG_SHA2_256_s,
              { .case_SHA2_256_s = { .k = k, .v = v, .reseed_counter = ctr } }
            }
          );
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        uint8_t *k = KRML_HOST_CALLOC((uint32_t)48U, sizeof (uint8_t));
        uint8_t *v = KRML_HOST_CALLOC((uint32_t)48U, sizeof (uint8_t));
        uint32_t *ctr = KRML_HOST_MALLOC(sizeof (uint32_t));
        ctr[0U] = (uint32_t)1U;
        st =
          (
            (EverCrypt_DRBG_state_s){
              .tag = EverCrypt_DRBG_SHA2_384_s,
              { .case_SHA2_384_s = { .k = k, .v = v, .reseed_counter = ctr } }
            }
          );
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        uint8_t *k = KRML_HOST_CALLOC((uint32_t)64U, sizeof (uint8_t));
        uint8_t *v = KRML_HOST_CALLOC((uint32_t)64U, sizeof (uint8_t));
        uint32_t *ctr = KRML_HOST_MALLOC(sizeof (uint32_t));
        ctr[0U] = (uint32_t)1U;
        st =
          (
            (EverCrypt_DRBG_state_s){
              .tag = EverCrypt_DRBG_SHA2_512_s,
              { .case_SHA2_512_s = { .k = k, .v = v, .reseed_counter = ctr } }
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
  memset(entropy, 0U, min_entropy * sizeof (entropy[0U]));
  bool ok = Lib_RandomBuffer_System_randombytes(entropy, min_entropy);
  if (!ok)
  {
    return false;
  }
  uint8_t *entropy_input;
  if (entropy == NULL)
  {
    entropy_input = NULL;
  }
  else
  {
    entropy_input = entropy;
  }
  uint8_t *nonce;
  if (entropy == NULL)
  {
    nonce = NULL;
  }
  else
  {
    nonce = entropy + entropy_input_len;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + nonce_len + personalization_string_len);
  uint8_t seed_material[entropy_input_len + nonce_len + personalization_string_len];
  memset(seed_material,
    0U,
    (entropy_input_len + nonce_len + personalization_string_len) * sizeof (seed_material[0U]));
  uint8_t *uu____0;
  if (seed_material == NULL)
  {
    uu____0 = NULL;
  }
  else
  {
    uu____0 = seed_material;
  }
  bool uu____1 = entropy_input == NULL;
  if (!(uu____1 || uu____0 == NULL))
  {
    memcpy(uu____0, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
  }
  uint8_t *uu____2;
  if (seed_material == NULL)
  {
    uu____2 = NULL;
  }
  else
  {
    uu____2 = seed_material + entropy_input_len;
  }
  bool uu____3 = nonce == NULL;
  if (!(uu____3 || uu____2 == NULL))
  {
    memcpy(uu____2, nonce, nonce_len * sizeof (nonce[0U]));
  }
  uint8_t *uu____4;
  if (seed_material == NULL)
  {
    uu____4 = NULL;
  }
  else
  {
    uu____4 = seed_material + entropy_input_len + nonce_len;
  }
  bool uu____5 = personalization_string == NULL;
  if (!(uu____5 || uu____4 == NULL))
  {
    memcpy(uu____4,
      personalization_string,
      personalization_string_len * sizeof (personalization_string[0U]));
  }
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == EverCrypt_DRBG_SHA1_s)
  {
    scrut = st_s.case_SHA1_s;
  }
  else
  {
    scrut = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k = scrut.k;
  uint8_t *v = scrut.v;
  uint32_t *ctr = scrut.reseed_counter;
  if (!(k == NULL))
  {
    memset(k, 0U, (uint32_t)20U * sizeof (k[0U]));
  }
  if (!(v == NULL))
  {
    memset(v, (uint8_t)1U, (uint32_t)20U * sizeof (v[0U]));
  }
  ctr[0U] = (uint32_t)1U;
  uint32_t
  input_len = (uint32_t)21U + entropy_input_len + nonce_len + personalization_string_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t input0[input_len];
  memset(input0, 0U, input_len * sizeof (input0[0U]));
  uint8_t *k_;
  if (input0 == NULL)
  {
    k_ = NULL;
  }
  else
  {
    k_ = input0;
  }
  bool uu____6 = v == NULL;
  if (!(uu____6 || k_ == NULL))
  {
    memcpy(k_, v, (uint32_t)20U * sizeof (v[0U]));
  }
  if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
  {
    uint8_t *uu____7;
    if (input0 == NULL)
    {
      uu____7 = NULL;
    }
    else
    {
      uu____7 = input0 + (uint32_t)21U;
    }
    bool uu____8 = seed_material == NULL;
    if (!(uu____8 || uu____7 == NULL))
    {
      memcpy(uu____7,
        seed_material,
        (entropy_input_len + nonce_len + personalization_string_len) * sizeof (seed_material[0U]));
    }
  }
  input0[20U] = (uint8_t)0U;
  EverCrypt_HMAC_compute_sha1(k_, k, (uint32_t)20U, input0, input_len);
  EverCrypt_HMAC_compute_sha1(v, k_, (uint32_t)20U, v, (uint32_t)20U);
  bool uu____9 = k_ == NULL;
  if (!(uu____9 || k == NULL))
  {
    memcpy(k, k_, (uint32_t)20U * sizeof (k_[0U]));
  }
  if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
  {
    uint32_t
    input_len0 = (uint32_t)21U + entropy_input_len + nonce_len + personalization_string_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t input[input_len0];
    memset(input, 0U, input_len0 * sizeof (input[0U]));
    uint8_t *k_0;
    if (input == NULL)
    {
      k_0 = NULL;
    }
    else
    {
      k_0 = input;
    }
    bool uu____10 = v == NULL;
    if (!(uu____10 || k_0 == NULL))
    {
      memcpy(k_0, v, (uint32_t)20U * sizeof (v[0U]));
    }
    if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
    {
      uint8_t *uu____11;
      if (input == NULL)
      {
        uu____11 = NULL;
      }
      else
      {
        uu____11 = input + (uint32_t)21U;
      }
      bool uu____12 = seed_material == NULL;
      if (!(uu____12 || uu____11 == NULL))
      {
        memcpy(uu____11,
          seed_material,
          (entropy_input_len + nonce_len + personalization_string_len) * sizeof (seed_material[0U]));
      }
    }
    input[20U] = (uint8_t)1U;
    EverCrypt_HMAC_compute_sha1(k_0, k, (uint32_t)20U, input, input_len0);
    EverCrypt_HMAC_compute_sha1(v, k_0, (uint32_t)20U, v, (uint32_t)20U);
    bool uu____13 = k_0 == NULL;
    if (!(uu____13 || k == NULL))
    {
      memcpy(k, k_0, (uint32_t)20U * sizeof (k_0[0U]));
    }
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
  memset(entropy, 0U, min_entropy * sizeof (entropy[0U]));
  bool ok = Lib_RandomBuffer_System_randombytes(entropy, min_entropy);
  if (!ok)
  {
    return false;
  }
  uint8_t *entropy_input;
  if (entropy == NULL)
  {
    entropy_input = NULL;
  }
  else
  {
    entropy_input = entropy;
  }
  uint8_t *nonce;
  if (entropy == NULL)
  {
    nonce = NULL;
  }
  else
  {
    nonce = entropy + entropy_input_len;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + nonce_len + personalization_string_len);
  uint8_t seed_material[entropy_input_len + nonce_len + personalization_string_len];
  memset(seed_material,
    0U,
    (entropy_input_len + nonce_len + personalization_string_len) * sizeof (seed_material[0U]));
  uint8_t *uu____0;
  if (seed_material == NULL)
  {
    uu____0 = NULL;
  }
  else
  {
    uu____0 = seed_material;
  }
  bool uu____1 = entropy_input == NULL;
  if (!(uu____1 || uu____0 == NULL))
  {
    memcpy(uu____0, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
  }
  uint8_t *uu____2;
  if (seed_material == NULL)
  {
    uu____2 = NULL;
  }
  else
  {
    uu____2 = seed_material + entropy_input_len;
  }
  bool uu____3 = nonce == NULL;
  if (!(uu____3 || uu____2 == NULL))
  {
    memcpy(uu____2, nonce, nonce_len * sizeof (nonce[0U]));
  }
  uint8_t *uu____4;
  if (seed_material == NULL)
  {
    uu____4 = NULL;
  }
  else
  {
    uu____4 = seed_material + entropy_input_len + nonce_len;
  }
  bool uu____5 = personalization_string == NULL;
  if (!(uu____5 || uu____4 == NULL))
  {
    memcpy(uu____4,
      personalization_string,
      personalization_string_len * sizeof (personalization_string[0U]));
  }
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == EverCrypt_DRBG_SHA2_256_s)
  {
    scrut = st_s.case_SHA2_256_s;
  }
  else
  {
    scrut = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k = scrut.k;
  uint8_t *v = scrut.v;
  uint32_t *ctr = scrut.reseed_counter;
  if (!(k == NULL))
  {
    memset(k, 0U, (uint32_t)32U * sizeof (k[0U]));
  }
  if (!(v == NULL))
  {
    memset(v, (uint8_t)1U, (uint32_t)32U * sizeof (v[0U]));
  }
  ctr[0U] = (uint32_t)1U;
  uint32_t
  input_len = (uint32_t)33U + entropy_input_len + nonce_len + personalization_string_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t input0[input_len];
  memset(input0, 0U, input_len * sizeof (input0[0U]));
  uint8_t *k_;
  if (input0 == NULL)
  {
    k_ = NULL;
  }
  else
  {
    k_ = input0;
  }
  bool uu____6 = v == NULL;
  if (!(uu____6 || k_ == NULL))
  {
    memcpy(k_, v, (uint32_t)32U * sizeof (v[0U]));
  }
  if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
  {
    uint8_t *uu____7;
    if (input0 == NULL)
    {
      uu____7 = NULL;
    }
    else
    {
      uu____7 = input0 + (uint32_t)33U;
    }
    bool uu____8 = seed_material == NULL;
    if (!(uu____8 || uu____7 == NULL))
    {
      memcpy(uu____7,
        seed_material,
        (entropy_input_len + nonce_len + personalization_string_len) * sizeof (seed_material[0U]));
    }
  }
  input0[32U] = (uint8_t)0U;
  EverCrypt_HMAC_compute_sha2_256(k_, k, (uint32_t)32U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_256(v, k_, (uint32_t)32U, v, (uint32_t)32U);
  bool uu____9 = k_ == NULL;
  if (!(uu____9 || k == NULL))
  {
    memcpy(k, k_, (uint32_t)32U * sizeof (k_[0U]));
  }
  if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
  {
    uint32_t
    input_len0 = (uint32_t)33U + entropy_input_len + nonce_len + personalization_string_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t input[input_len0];
    memset(input, 0U, input_len0 * sizeof (input[0U]));
    uint8_t *k_0;
    if (input == NULL)
    {
      k_0 = NULL;
    }
    else
    {
      k_0 = input;
    }
    bool uu____10 = v == NULL;
    if (!(uu____10 || k_0 == NULL))
    {
      memcpy(k_0, v, (uint32_t)32U * sizeof (v[0U]));
    }
    if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
    {
      uint8_t *uu____11;
      if (input == NULL)
      {
        uu____11 = NULL;
      }
      else
      {
        uu____11 = input + (uint32_t)33U;
      }
      bool uu____12 = seed_material == NULL;
      if (!(uu____12 || uu____11 == NULL))
      {
        memcpy(uu____11,
          seed_material,
          (entropy_input_len + nonce_len + personalization_string_len) * sizeof (seed_material[0U]));
      }
    }
    input[32U] = (uint8_t)1U;
    EverCrypt_HMAC_compute_sha2_256(k_0, k, (uint32_t)32U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_256(v, k_0, (uint32_t)32U, v, (uint32_t)32U);
    bool uu____13 = k_0 == NULL;
    if (!(uu____13 || k == NULL))
    {
      memcpy(k, k_0, (uint32_t)32U * sizeof (k_0[0U]));
    }
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
  memset(entropy, 0U, min_entropy * sizeof (entropy[0U]));
  bool ok = Lib_RandomBuffer_System_randombytes(entropy, min_entropy);
  if (!ok)
  {
    return false;
  }
  uint8_t *entropy_input;
  if (entropy == NULL)
  {
    entropy_input = NULL;
  }
  else
  {
    entropy_input = entropy;
  }
  uint8_t *nonce;
  if (entropy == NULL)
  {
    nonce = NULL;
  }
  else
  {
    nonce = entropy + entropy_input_len;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + nonce_len + personalization_string_len);
  uint8_t seed_material[entropy_input_len + nonce_len + personalization_string_len];
  memset(seed_material,
    0U,
    (entropy_input_len + nonce_len + personalization_string_len) * sizeof (seed_material[0U]));
  uint8_t *uu____0;
  if (seed_material == NULL)
  {
    uu____0 = NULL;
  }
  else
  {
    uu____0 = seed_material;
  }
  bool uu____1 = entropy_input == NULL;
  if (!(uu____1 || uu____0 == NULL))
  {
    memcpy(uu____0, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
  }
  uint8_t *uu____2;
  if (seed_material == NULL)
  {
    uu____2 = NULL;
  }
  else
  {
    uu____2 = seed_material + entropy_input_len;
  }
  bool uu____3 = nonce == NULL;
  if (!(uu____3 || uu____2 == NULL))
  {
    memcpy(uu____2, nonce, nonce_len * sizeof (nonce[0U]));
  }
  uint8_t *uu____4;
  if (seed_material == NULL)
  {
    uu____4 = NULL;
  }
  else
  {
    uu____4 = seed_material + entropy_input_len + nonce_len;
  }
  bool uu____5 = personalization_string == NULL;
  if (!(uu____5 || uu____4 == NULL))
  {
    memcpy(uu____4,
      personalization_string,
      personalization_string_len * sizeof (personalization_string[0U]));
  }
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == EverCrypt_DRBG_SHA2_384_s)
  {
    scrut = st_s.case_SHA2_384_s;
  }
  else
  {
    scrut = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k = scrut.k;
  uint8_t *v = scrut.v;
  uint32_t *ctr = scrut.reseed_counter;
  if (!(k == NULL))
  {
    memset(k, 0U, (uint32_t)48U * sizeof (k[0U]));
  }
  if (!(v == NULL))
  {
    memset(v, (uint8_t)1U, (uint32_t)48U * sizeof (v[0U]));
  }
  ctr[0U] = (uint32_t)1U;
  uint32_t
  input_len = (uint32_t)49U + entropy_input_len + nonce_len + personalization_string_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t input0[input_len];
  memset(input0, 0U, input_len * sizeof (input0[0U]));
  uint8_t *k_;
  if (input0 == NULL)
  {
    k_ = NULL;
  }
  else
  {
    k_ = input0;
  }
  bool uu____6 = v == NULL;
  if (!(uu____6 || k_ == NULL))
  {
    memcpy(k_, v, (uint32_t)48U * sizeof (v[0U]));
  }
  if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
  {
    uint8_t *uu____7;
    if (input0 == NULL)
    {
      uu____7 = NULL;
    }
    else
    {
      uu____7 = input0 + (uint32_t)49U;
    }
    bool uu____8 = seed_material == NULL;
    if (!(uu____8 || uu____7 == NULL))
    {
      memcpy(uu____7,
        seed_material,
        (entropy_input_len + nonce_len + personalization_string_len) * sizeof (seed_material[0U]));
    }
  }
  input0[48U] = (uint8_t)0U;
  EverCrypt_HMAC_compute_sha2_384(k_, k, (uint32_t)48U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_384(v, k_, (uint32_t)48U, v, (uint32_t)48U);
  bool uu____9 = k_ == NULL;
  if (!(uu____9 || k == NULL))
  {
    memcpy(k, k_, (uint32_t)48U * sizeof (k_[0U]));
  }
  if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
  {
    uint32_t
    input_len0 = (uint32_t)49U + entropy_input_len + nonce_len + personalization_string_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t input[input_len0];
    memset(input, 0U, input_len0 * sizeof (input[0U]));
    uint8_t *k_0;
    if (input == NULL)
    {
      k_0 = NULL;
    }
    else
    {
      k_0 = input;
    }
    bool uu____10 = v == NULL;
    if (!(uu____10 || k_0 == NULL))
    {
      memcpy(k_0, v, (uint32_t)48U * sizeof (v[0U]));
    }
    if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
    {
      uint8_t *uu____11;
      if (input == NULL)
      {
        uu____11 = NULL;
      }
      else
      {
        uu____11 = input + (uint32_t)49U;
      }
      bool uu____12 = seed_material == NULL;
      if (!(uu____12 || uu____11 == NULL))
      {
        memcpy(uu____11,
          seed_material,
          (entropy_input_len + nonce_len + personalization_string_len) * sizeof (seed_material[0U]));
      }
    }
    input[48U] = (uint8_t)1U;
    EverCrypt_HMAC_compute_sha2_384(k_0, k, (uint32_t)48U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_384(v, k_0, (uint32_t)48U, v, (uint32_t)48U);
    bool uu____13 = k_0 == NULL;
    if (!(uu____13 || k == NULL))
    {
      memcpy(k, k_0, (uint32_t)48U * sizeof (k_0[0U]));
    }
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
  memset(entropy, 0U, min_entropy * sizeof (entropy[0U]));
  bool ok = Lib_RandomBuffer_System_randombytes(entropy, min_entropy);
  if (!ok)
  {
    return false;
  }
  uint8_t *entropy_input;
  if (entropy == NULL)
  {
    entropy_input = NULL;
  }
  else
  {
    entropy_input = entropy;
  }
  uint8_t *nonce;
  if (entropy == NULL)
  {
    nonce = NULL;
  }
  else
  {
    nonce = entropy + entropy_input_len;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + nonce_len + personalization_string_len);
  uint8_t seed_material[entropy_input_len + nonce_len + personalization_string_len];
  memset(seed_material,
    0U,
    (entropy_input_len + nonce_len + personalization_string_len) * sizeof (seed_material[0U]));
  uint8_t *uu____0;
  if (seed_material == NULL)
  {
    uu____0 = NULL;
  }
  else
  {
    uu____0 = seed_material;
  }
  bool uu____1 = entropy_input == NULL;
  if (!(uu____1 || uu____0 == NULL))
  {
    memcpy(uu____0, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
  }
  uint8_t *uu____2;
  if (seed_material == NULL)
  {
    uu____2 = NULL;
  }
  else
  {
    uu____2 = seed_material + entropy_input_len;
  }
  bool uu____3 = nonce == NULL;
  if (!(uu____3 || uu____2 == NULL))
  {
    memcpy(uu____2, nonce, nonce_len * sizeof (nonce[0U]));
  }
  uint8_t *uu____4;
  if (seed_material == NULL)
  {
    uu____4 = NULL;
  }
  else
  {
    uu____4 = seed_material + entropy_input_len + nonce_len;
  }
  bool uu____5 = personalization_string == NULL;
  if (!(uu____5 || uu____4 == NULL))
  {
    memcpy(uu____4,
      personalization_string,
      personalization_string_len * sizeof (personalization_string[0U]));
  }
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == EverCrypt_DRBG_SHA2_512_s)
  {
    scrut = st_s.case_SHA2_512_s;
  }
  else
  {
    scrut = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k = scrut.k;
  uint8_t *v = scrut.v;
  uint32_t *ctr = scrut.reseed_counter;
  if (!(k == NULL))
  {
    memset(k, 0U, (uint32_t)64U * sizeof (k[0U]));
  }
  if (!(v == NULL))
  {
    memset(v, (uint8_t)1U, (uint32_t)64U * sizeof (v[0U]));
  }
  ctr[0U] = (uint32_t)1U;
  uint32_t
  input_len = (uint32_t)65U + entropy_input_len + nonce_len + personalization_string_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t input0[input_len];
  memset(input0, 0U, input_len * sizeof (input0[0U]));
  uint8_t *k_;
  if (input0 == NULL)
  {
    k_ = NULL;
  }
  else
  {
    k_ = input0;
  }
  bool uu____6 = v == NULL;
  if (!(uu____6 || k_ == NULL))
  {
    memcpy(k_, v, (uint32_t)64U * sizeof (v[0U]));
  }
  if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
  {
    uint8_t *uu____7;
    if (input0 == NULL)
    {
      uu____7 = NULL;
    }
    else
    {
      uu____7 = input0 + (uint32_t)65U;
    }
    bool uu____8 = seed_material == NULL;
    if (!(uu____8 || uu____7 == NULL))
    {
      memcpy(uu____7,
        seed_material,
        (entropy_input_len + nonce_len + personalization_string_len) * sizeof (seed_material[0U]));
    }
  }
  input0[64U] = (uint8_t)0U;
  EverCrypt_HMAC_compute_sha2_512(k_, k, (uint32_t)64U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_512(v, k_, (uint32_t)64U, v, (uint32_t)64U);
  bool uu____9 = k_ == NULL;
  if (!(uu____9 || k == NULL))
  {
    memcpy(k, k_, (uint32_t)64U * sizeof (k_[0U]));
  }
  if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
  {
    uint32_t
    input_len0 = (uint32_t)65U + entropy_input_len + nonce_len + personalization_string_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t input[input_len0];
    memset(input, 0U, input_len0 * sizeof (input[0U]));
    uint8_t *k_0;
    if (input == NULL)
    {
      k_0 = NULL;
    }
    else
    {
      k_0 = input;
    }
    bool uu____10 = v == NULL;
    if (!(uu____10 || k_0 == NULL))
    {
      memcpy(k_0, v, (uint32_t)64U * sizeof (v[0U]));
    }
    if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
    {
      uint8_t *uu____11;
      if (input == NULL)
      {
        uu____11 = NULL;
      }
      else
      {
        uu____11 = input + (uint32_t)65U;
      }
      bool uu____12 = seed_material == NULL;
      if (!(uu____12 || uu____11 == NULL))
      {
        memcpy(uu____11,
          seed_material,
          (entropy_input_len + nonce_len + personalization_string_len) * sizeof (seed_material[0U]));
      }
    }
    input[64U] = (uint8_t)1U;
    EverCrypt_HMAC_compute_sha2_512(k_0, k, (uint32_t)64U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_512(v, k_0, (uint32_t)64U, v, (uint32_t)64U);
    bool uu____13 = k_0 == NULL;
    if (!(uu____13 || k == NULL))
    {
      memcpy(k, k_0, (uint32_t)64U * sizeof (k_0[0U]));
    }
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
  memset(entropy_input, 0U, entropy_input_len * sizeof (entropy_input[0U]));
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
    (entropy_input_len + additional_input_len) * sizeof (seed_material[0U]));
  uint8_t *uu____0;
  if (seed_material == NULL)
  {
    uu____0 = NULL;
  }
  else
  {
    uu____0 = seed_material;
  }
  bool uu____1 = entropy_input == NULL;
  if (!(uu____1 || uu____0 == NULL))
  {
    memcpy(uu____0, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
  }
  uint8_t *uu____2;
  if (seed_material == NULL)
  {
    uu____2 = NULL;
  }
  else
  {
    uu____2 = seed_material + entropy_input_len;
  }
  bool uu____3 = additional_input == NULL;
  if (!(uu____3 || uu____2 == NULL))
  {
    memcpy(uu____2, additional_input, additional_input_len * sizeof (additional_input[0U]));
  }
  Hacl_HMAC_DRBG_state uu____4;
  if (st_s.tag == EverCrypt_DRBG_SHA1_s)
  {
    uu____4 = st_s.case_SHA1_s;
  }
  else
  {
    uu____4 =
      KRML_EABORT(Hacl_HMAC_DRBG_state,
        "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k = uu____4.k;
  uint8_t *v = uu____4.v;
  uint32_t *ctr = uu____4.reseed_counter;
  uint32_t input_len = (uint32_t)21U + entropy_input_len + additional_input_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t input0[input_len];
  memset(input0, 0U, input_len * sizeof (input0[0U]));
  uint8_t *k_;
  if (input0 == NULL)
  {
    k_ = NULL;
  }
  else
  {
    k_ = input0;
  }
  bool uu____5 = v == NULL;
  if (!(uu____5 || k_ == NULL))
  {
    memcpy(k_, v, (uint32_t)20U * sizeof (v[0U]));
  }
  if (entropy_input_len + additional_input_len != (uint32_t)0U)
  {
    uint8_t *uu____6;
    if (input0 == NULL)
    {
      uu____6 = NULL;
    }
    else
    {
      uu____6 = input0 + (uint32_t)21U;
    }
    bool uu____7 = seed_material == NULL;
    if (!(uu____7 || uu____6 == NULL))
    {
      memcpy(uu____6,
        seed_material,
        (entropy_input_len + additional_input_len) * sizeof (seed_material[0U]));
    }
  }
  input0[20U] = (uint8_t)0U;
  EverCrypt_HMAC_compute_sha1(k_, k, (uint32_t)20U, input0, input_len);
  EverCrypt_HMAC_compute_sha1(v, k_, (uint32_t)20U, v, (uint32_t)20U);
  bool uu____8 = k_ == NULL;
  if (!(uu____8 || k == NULL))
  {
    memcpy(k, k_, (uint32_t)20U * sizeof (k_[0U]));
  }
  if (entropy_input_len + additional_input_len != (uint32_t)0U)
  {
    uint32_t input_len0 = (uint32_t)21U + entropy_input_len + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t input[input_len0];
    memset(input, 0U, input_len0 * sizeof (input[0U]));
    uint8_t *k_0;
    if (input == NULL)
    {
      k_0 = NULL;
    }
    else
    {
      k_0 = input;
    }
    bool uu____9 = v == NULL;
    if (!(uu____9 || k_0 == NULL))
    {
      memcpy(k_0, v, (uint32_t)20U * sizeof (v[0U]));
    }
    if (entropy_input_len + additional_input_len != (uint32_t)0U)
    {
      uint8_t *uu____10;
      if (input == NULL)
      {
        uu____10 = NULL;
      }
      else
      {
        uu____10 = input + (uint32_t)21U;
      }
      bool uu____11 = seed_material == NULL;
      if (!(uu____11 || uu____10 == NULL))
      {
        memcpy(uu____10,
          seed_material,
          (entropy_input_len + additional_input_len) * sizeof (seed_material[0U]));
      }
    }
    input[20U] = (uint8_t)1U;
    EverCrypt_HMAC_compute_sha1(k_0, k, (uint32_t)20U, input, input_len0);
    EverCrypt_HMAC_compute_sha1(v, k_0, (uint32_t)20U, v, (uint32_t)20U);
    bool uu____12 = k_0 == NULL;
    if (!(uu____12 || k == NULL))
    {
      memcpy(k, k_0, (uint32_t)20U * sizeof (k_0[0U]));
    }
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
  memset(entropy_input, 0U, entropy_input_len * sizeof (entropy_input[0U]));
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
    (entropy_input_len + additional_input_len) * sizeof (seed_material[0U]));
  uint8_t *uu____0;
  if (seed_material == NULL)
  {
    uu____0 = NULL;
  }
  else
  {
    uu____0 = seed_material;
  }
  bool uu____1 = entropy_input == NULL;
  if (!(uu____1 || uu____0 == NULL))
  {
    memcpy(uu____0, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
  }
  uint8_t *uu____2;
  if (seed_material == NULL)
  {
    uu____2 = NULL;
  }
  else
  {
    uu____2 = seed_material + entropy_input_len;
  }
  bool uu____3 = additional_input == NULL;
  if (!(uu____3 || uu____2 == NULL))
  {
    memcpy(uu____2, additional_input, additional_input_len * sizeof (additional_input[0U]));
  }
  Hacl_HMAC_DRBG_state uu____4;
  if (st_s.tag == EverCrypt_DRBG_SHA2_256_s)
  {
    uu____4 = st_s.case_SHA2_256_s;
  }
  else
  {
    uu____4 =
      KRML_EABORT(Hacl_HMAC_DRBG_state,
        "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k = uu____4.k;
  uint8_t *v = uu____4.v;
  uint32_t *ctr = uu____4.reseed_counter;
  uint32_t input_len = (uint32_t)33U + entropy_input_len + additional_input_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t input0[input_len];
  memset(input0, 0U, input_len * sizeof (input0[0U]));
  uint8_t *k_;
  if (input0 == NULL)
  {
    k_ = NULL;
  }
  else
  {
    k_ = input0;
  }
  bool uu____5 = v == NULL;
  if (!(uu____5 || k_ == NULL))
  {
    memcpy(k_, v, (uint32_t)32U * sizeof (v[0U]));
  }
  if (entropy_input_len + additional_input_len != (uint32_t)0U)
  {
    uint8_t *uu____6;
    if (input0 == NULL)
    {
      uu____6 = NULL;
    }
    else
    {
      uu____6 = input0 + (uint32_t)33U;
    }
    bool uu____7 = seed_material == NULL;
    if (!(uu____7 || uu____6 == NULL))
    {
      memcpy(uu____6,
        seed_material,
        (entropy_input_len + additional_input_len) * sizeof (seed_material[0U]));
    }
  }
  input0[32U] = (uint8_t)0U;
  EverCrypt_HMAC_compute_sha2_256(k_, k, (uint32_t)32U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_256(v, k_, (uint32_t)32U, v, (uint32_t)32U);
  bool uu____8 = k_ == NULL;
  if (!(uu____8 || k == NULL))
  {
    memcpy(k, k_, (uint32_t)32U * sizeof (k_[0U]));
  }
  if (entropy_input_len + additional_input_len != (uint32_t)0U)
  {
    uint32_t input_len0 = (uint32_t)33U + entropy_input_len + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t input[input_len0];
    memset(input, 0U, input_len0 * sizeof (input[0U]));
    uint8_t *k_0;
    if (input == NULL)
    {
      k_0 = NULL;
    }
    else
    {
      k_0 = input;
    }
    bool uu____9 = v == NULL;
    if (!(uu____9 || k_0 == NULL))
    {
      memcpy(k_0, v, (uint32_t)32U * sizeof (v[0U]));
    }
    if (entropy_input_len + additional_input_len != (uint32_t)0U)
    {
      uint8_t *uu____10;
      if (input == NULL)
      {
        uu____10 = NULL;
      }
      else
      {
        uu____10 = input + (uint32_t)33U;
      }
      bool uu____11 = seed_material == NULL;
      if (!(uu____11 || uu____10 == NULL))
      {
        memcpy(uu____10,
          seed_material,
          (entropy_input_len + additional_input_len) * sizeof (seed_material[0U]));
      }
    }
    input[32U] = (uint8_t)1U;
    EverCrypt_HMAC_compute_sha2_256(k_0, k, (uint32_t)32U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_256(v, k_0, (uint32_t)32U, v, (uint32_t)32U);
    bool uu____12 = k_0 == NULL;
    if (!(uu____12 || k == NULL))
    {
      memcpy(k, k_0, (uint32_t)32U * sizeof (k_0[0U]));
    }
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
  memset(entropy_input, 0U, entropy_input_len * sizeof (entropy_input[0U]));
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
    (entropy_input_len + additional_input_len) * sizeof (seed_material[0U]));
  uint8_t *uu____0;
  if (seed_material == NULL)
  {
    uu____0 = NULL;
  }
  else
  {
    uu____0 = seed_material;
  }
  bool uu____1 = entropy_input == NULL;
  if (!(uu____1 || uu____0 == NULL))
  {
    memcpy(uu____0, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
  }
  uint8_t *uu____2;
  if (seed_material == NULL)
  {
    uu____2 = NULL;
  }
  else
  {
    uu____2 = seed_material + entropy_input_len;
  }
  bool uu____3 = additional_input == NULL;
  if (!(uu____3 || uu____2 == NULL))
  {
    memcpy(uu____2, additional_input, additional_input_len * sizeof (additional_input[0U]));
  }
  Hacl_HMAC_DRBG_state uu____4;
  if (st_s.tag == EverCrypt_DRBG_SHA2_384_s)
  {
    uu____4 = st_s.case_SHA2_384_s;
  }
  else
  {
    uu____4 =
      KRML_EABORT(Hacl_HMAC_DRBG_state,
        "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k = uu____4.k;
  uint8_t *v = uu____4.v;
  uint32_t *ctr = uu____4.reseed_counter;
  uint32_t input_len = (uint32_t)49U + entropy_input_len + additional_input_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t input0[input_len];
  memset(input0, 0U, input_len * sizeof (input0[0U]));
  uint8_t *k_;
  if (input0 == NULL)
  {
    k_ = NULL;
  }
  else
  {
    k_ = input0;
  }
  bool uu____5 = v == NULL;
  if (!(uu____5 || k_ == NULL))
  {
    memcpy(k_, v, (uint32_t)48U * sizeof (v[0U]));
  }
  if (entropy_input_len + additional_input_len != (uint32_t)0U)
  {
    uint8_t *uu____6;
    if (input0 == NULL)
    {
      uu____6 = NULL;
    }
    else
    {
      uu____6 = input0 + (uint32_t)49U;
    }
    bool uu____7 = seed_material == NULL;
    if (!(uu____7 || uu____6 == NULL))
    {
      memcpy(uu____6,
        seed_material,
        (entropy_input_len + additional_input_len) * sizeof (seed_material[0U]));
    }
  }
  input0[48U] = (uint8_t)0U;
  EverCrypt_HMAC_compute_sha2_384(k_, k, (uint32_t)48U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_384(v, k_, (uint32_t)48U, v, (uint32_t)48U);
  bool uu____8 = k_ == NULL;
  if (!(uu____8 || k == NULL))
  {
    memcpy(k, k_, (uint32_t)48U * sizeof (k_[0U]));
  }
  if (entropy_input_len + additional_input_len != (uint32_t)0U)
  {
    uint32_t input_len0 = (uint32_t)49U + entropy_input_len + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t input[input_len0];
    memset(input, 0U, input_len0 * sizeof (input[0U]));
    uint8_t *k_0;
    if (input == NULL)
    {
      k_0 = NULL;
    }
    else
    {
      k_0 = input;
    }
    bool uu____9 = v == NULL;
    if (!(uu____9 || k_0 == NULL))
    {
      memcpy(k_0, v, (uint32_t)48U * sizeof (v[0U]));
    }
    if (entropy_input_len + additional_input_len != (uint32_t)0U)
    {
      uint8_t *uu____10;
      if (input == NULL)
      {
        uu____10 = NULL;
      }
      else
      {
        uu____10 = input + (uint32_t)49U;
      }
      bool uu____11 = seed_material == NULL;
      if (!(uu____11 || uu____10 == NULL))
      {
        memcpy(uu____10,
          seed_material,
          (entropy_input_len + additional_input_len) * sizeof (seed_material[0U]));
      }
    }
    input[48U] = (uint8_t)1U;
    EverCrypt_HMAC_compute_sha2_384(k_0, k, (uint32_t)48U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_384(v, k_0, (uint32_t)48U, v, (uint32_t)48U);
    bool uu____12 = k_0 == NULL;
    if (!(uu____12 || k == NULL))
    {
      memcpy(k, k_0, (uint32_t)48U * sizeof (k_0[0U]));
    }
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
  memset(entropy_input, 0U, entropy_input_len * sizeof (entropy_input[0U]));
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
    (entropy_input_len + additional_input_len) * sizeof (seed_material[0U]));
  uint8_t *uu____0;
  if (seed_material == NULL)
  {
    uu____0 = NULL;
  }
  else
  {
    uu____0 = seed_material;
  }
  bool uu____1 = entropy_input == NULL;
  if (!(uu____1 || uu____0 == NULL))
  {
    memcpy(uu____0, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
  }
  uint8_t *uu____2;
  if (seed_material == NULL)
  {
    uu____2 = NULL;
  }
  else
  {
    uu____2 = seed_material + entropy_input_len;
  }
  bool uu____3 = additional_input == NULL;
  if (!(uu____3 || uu____2 == NULL))
  {
    memcpy(uu____2, additional_input, additional_input_len * sizeof (additional_input[0U]));
  }
  Hacl_HMAC_DRBG_state uu____4;
  if (st_s.tag == EverCrypt_DRBG_SHA2_512_s)
  {
    uu____4 = st_s.case_SHA2_512_s;
  }
  else
  {
    uu____4 =
      KRML_EABORT(Hacl_HMAC_DRBG_state,
        "unreachable (pattern matches are exhaustive in F*)");
  }
  uint8_t *k = uu____4.k;
  uint8_t *v = uu____4.v;
  uint32_t *ctr = uu____4.reseed_counter;
  uint32_t input_len = (uint32_t)65U + entropy_input_len + additional_input_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t input0[input_len];
  memset(input0, 0U, input_len * sizeof (input0[0U]));
  uint8_t *k_;
  if (input0 == NULL)
  {
    k_ = NULL;
  }
  else
  {
    k_ = input0;
  }
  bool uu____5 = v == NULL;
  if (!(uu____5 || k_ == NULL))
  {
    memcpy(k_, v, (uint32_t)64U * sizeof (v[0U]));
  }
  if (entropy_input_len + additional_input_len != (uint32_t)0U)
  {
    uint8_t *uu____6;
    if (input0 == NULL)
    {
      uu____6 = NULL;
    }
    else
    {
      uu____6 = input0 + (uint32_t)65U;
    }
    bool uu____7 = seed_material == NULL;
    if (!(uu____7 || uu____6 == NULL))
    {
      memcpy(uu____6,
        seed_material,
        (entropy_input_len + additional_input_len) * sizeof (seed_material[0U]));
    }
  }
  input0[64U] = (uint8_t)0U;
  EverCrypt_HMAC_compute_sha2_512(k_, k, (uint32_t)64U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_512(v, k_, (uint32_t)64U, v, (uint32_t)64U);
  bool uu____8 = k_ == NULL;
  if (!(uu____8 || k == NULL))
  {
    memcpy(k, k_, (uint32_t)64U * sizeof (k_[0U]));
  }
  if (entropy_input_len + additional_input_len != (uint32_t)0U)
  {
    uint32_t input_len0 = (uint32_t)65U + entropy_input_len + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t input[input_len0];
    memset(input, 0U, input_len0 * sizeof (input[0U]));
    uint8_t *k_0;
    if (input == NULL)
    {
      k_0 = NULL;
    }
    else
    {
      k_0 = input;
    }
    bool uu____9 = v == NULL;
    if (!(uu____9 || k_0 == NULL))
    {
      memcpy(k_0, v, (uint32_t)64U * sizeof (v[0U]));
    }
    if (entropy_input_len + additional_input_len != (uint32_t)0U)
    {
      uint8_t *uu____10;
      if (input == NULL)
      {
        uu____10 = NULL;
      }
      else
      {
        uu____10 = input + (uint32_t)65U;
      }
      bool uu____11 = seed_material == NULL;
      if (!(uu____11 || uu____10 == NULL))
      {
        memcpy(uu____10,
          seed_material,
          (entropy_input_len + additional_input_len) * sizeof (seed_material[0U]));
      }
    }
    input[64U] = (uint8_t)1U;
    EverCrypt_HMAC_compute_sha2_512(k_0, k, (uint32_t)64U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_512(v, k_0, (uint32_t)64U, v, (uint32_t)64U);
    bool uu____12 = k_0 == NULL;
    if (!(uu____12 || k == NULL))
    {
      memcpy(k, k_0, (uint32_t)64U * sizeof (k_0[0U]));
    }
  }
  ctr[0U] = (uint32_t)1U;
  return true;
}

bool
EverCrypt_DRBG_generate_sha1(
  uint8_t *output,
  EverCrypt_DRBG_state_s *st,
  uint32_t n,
  uint8_t *additional_input,
  uint32_t additional_input_len
)
{
  if
  (
    additional_input_len
    > Hacl_HMAC_DRBG_max_additional_input_length
    || n > Hacl_HMAC_DRBG_max_output_length
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
    memset(entropy_input, 0U, entropy_input_len1 * sizeof (entropy_input[0U]));
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
        (entropy_input_len1 + additional_input_len) * sizeof (seed_material[0U]));
      uint8_t *uu____0;
      if (seed_material == NULL)
      {
        uu____0 = NULL;
      }
      else
      {
        uu____0 = seed_material;
      }
      bool uu____1 = entropy_input == NULL;
      if (!(uu____1 || uu____0 == NULL))
      {
        memcpy(uu____0, entropy_input, entropy_input_len1 * sizeof (entropy_input[0U]));
      }
      uint8_t *uu____2;
      if (seed_material == NULL)
      {
        uu____2 = NULL;
      }
      else
      {
        uu____2 = seed_material + entropy_input_len1;
      }
      bool uu____3 = additional_input == NULL;
      if (!(uu____3 || uu____2 == NULL))
      {
        memcpy(uu____2, additional_input, additional_input_len * sizeof (additional_input[0U]));
      }
      Hacl_HMAC_DRBG_state uu____4;
      if (st_s.tag == EverCrypt_DRBG_SHA1_s)
      {
        uu____4 = st_s.case_SHA1_s;
      }
      else
      {
        uu____4 =
          KRML_EABORT(Hacl_HMAC_DRBG_state,
            "unreachable (pattern matches are exhaustive in F*)");
      }
      uint8_t *k = uu____4.k;
      uint8_t *v = uu____4.v;
      uint32_t *ctr = uu____4.reseed_counter;
      uint32_t input_len = (uint32_t)21U + entropy_input_len1 + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t input0[input_len];
      memset(input0, 0U, input_len * sizeof (input0[0U]));
      uint8_t *k_;
      if (input0 == NULL)
      {
        k_ = NULL;
      }
      else
      {
        k_ = input0;
      }
      bool uu____5 = v == NULL;
      if (!(uu____5 || k_ == NULL))
      {
        memcpy(k_, v, (uint32_t)20U * sizeof (v[0U]));
      }
      if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
      {
        uint8_t *uu____6;
        if (input0 == NULL)
        {
          uu____6 = NULL;
        }
        else
        {
          uu____6 = input0 + (uint32_t)21U;
        }
        bool uu____7 = seed_material == NULL;
        if (!(uu____7 || uu____6 == NULL))
        {
          memcpy(uu____6,
            seed_material,
            (entropy_input_len1 + additional_input_len) * sizeof (seed_material[0U]));
        }
      }
      input0[20U] = (uint8_t)0U;
      EverCrypt_HMAC_compute_sha1(k_, k, (uint32_t)20U, input0, input_len);
      EverCrypt_HMAC_compute_sha1(v, k_, (uint32_t)20U, v, (uint32_t)20U);
      bool uu____8 = k_ == NULL;
      if (!(uu____8 || k == NULL))
      {
        memcpy(k, k_, (uint32_t)20U * sizeof (k_[0U]));
      }
      if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
      {
        uint32_t input_len0 = (uint32_t)21U + entropy_input_len1 + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t input[input_len0];
        memset(input, 0U, input_len0 * sizeof (input[0U]));
        uint8_t *k_0;
        if (input == NULL)
        {
          k_0 = NULL;
        }
        else
        {
          k_0 = input;
        }
        bool uu____9 = v == NULL;
        if (!(uu____9 || k_0 == NULL))
        {
          memcpy(k_0, v, (uint32_t)20U * sizeof (v[0U]));
        }
        if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
        {
          uint8_t *uu____10;
          if (input == NULL)
          {
            uu____10 = NULL;
          }
          else
          {
            uu____10 = input + (uint32_t)21U;
          }
          bool uu____11 = seed_material == NULL;
          if (!(uu____11 || uu____10 == NULL))
          {
            memcpy(uu____10,
              seed_material,
              (entropy_input_len1 + additional_input_len) * sizeof (seed_material[0U]));
          }
        }
        input[20U] = (uint8_t)1U;
        EverCrypt_HMAC_compute_sha1(k_0, k, (uint32_t)20U, input, input_len0);
        EverCrypt_HMAC_compute_sha1(v, k_0, (uint32_t)20U, v, (uint32_t)20U);
        bool uu____12 = k_0 == NULL;
        if (!(uu____12 || k == NULL))
        {
          memcpy(k, k_0, (uint32_t)20U * sizeof (k_0[0U]));
        }
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
    uint8_t *k = scrut.k;
    uint8_t *v = scrut.v;
    uint32_t *ctr = scrut.reseed_counter;
    if (additional_input_len > (uint32_t)0U)
    {
      uint32_t input_len = (uint32_t)21U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t input0[input_len];
      memset(input0, 0U, input_len * sizeof (input0[0U]));
      uint8_t *k_;
      if (input0 == NULL)
      {
        k_ = NULL;
      }
      else
      {
        k_ = input0;
      }
      bool uu____13 = v == NULL;
      if (!(uu____13 || k_ == NULL))
      {
        memcpy(k_, v, (uint32_t)20U * sizeof (v[0U]));
      }
      if (additional_input_len != (uint32_t)0U)
      {
        uint8_t *uu____14;
        if (input0 == NULL)
        {
          uu____14 = NULL;
        }
        else
        {
          uu____14 = input0 + (uint32_t)21U;
        }
        bool uu____15 = additional_input == NULL;
        if (!(uu____15 || uu____14 == NULL))
        {
          memcpy(uu____14, additional_input, additional_input_len * sizeof (additional_input[0U]));
        }
      }
      input0[20U] = (uint8_t)0U;
      EverCrypt_HMAC_compute_sha1(k_, k, (uint32_t)20U, input0, input_len);
      EverCrypt_HMAC_compute_sha1(v, k_, (uint32_t)20U, v, (uint32_t)20U);
      bool uu____16 = k_ == NULL;
      if (!(uu____16 || k == NULL))
      {
        memcpy(k, k_, (uint32_t)20U * sizeof (k_[0U]));
      }
      if (additional_input_len != (uint32_t)0U)
      {
        uint32_t input_len0 = (uint32_t)21U + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t input[input_len0];
        memset(input, 0U, input_len0 * sizeof (input[0U]));
        uint8_t *k_0;
        if (input == NULL)
        {
          k_0 = NULL;
        }
        else
        {
          k_0 = input;
        }
        bool uu____17 = v == NULL;
        if (!(uu____17 || k_0 == NULL))
        {
          memcpy(k_0, v, (uint32_t)20U * sizeof (v[0U]));
        }
        if (additional_input_len != (uint32_t)0U)
        {
          uint8_t *uu____18;
          if (input == NULL)
          {
            uu____18 = NULL;
          }
          else
          {
            uu____18 = input + (uint32_t)21U;
          }
          bool uu____19 = additional_input == NULL;
          if (!(uu____19 || uu____18 == NULL))
          {
            memcpy(uu____18,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
        }
        input[20U] = (uint8_t)1U;
        EverCrypt_HMAC_compute_sha1(k_0, k, (uint32_t)20U, input, input_len0);
        EverCrypt_HMAC_compute_sha1(v, k_0, (uint32_t)20U, v, (uint32_t)20U);
        bool uu____20 = k_0 == NULL;
        if (!(uu____20 || k == NULL))
        {
          memcpy(k, k_0, (uint32_t)20U * sizeof (k_0[0U]));
        }
      }
    }
    uint8_t *output1 = output;
    uint32_t max = n / (uint32_t)20U;
    uint8_t *out;
    if (output1 == NULL)
    {
      out = NULL;
    }
    else
    {
      out = output1;
    }
    for (uint32_t i = (uint32_t)0U; i < max; i++)
    {
      uint8_t *block;
      if (out == NULL)
      {
        block = NULL;
      }
      else
      {
        block = out + i * (uint32_t)20U;
      }
      EverCrypt_HMAC_compute_sha1(v, k, (uint32_t)20U, v, (uint32_t)20U);
      uint8_t *uu____21;
      if (out == NULL)
      {
        uu____21 = NULL;
      }
      else
      {
        uu____21 = out + i * (uint32_t)20U;
      }
      bool uu____22 = v == NULL;
      if (!(uu____22 || uu____21 == NULL))
      {
        memcpy(uu____21, v, (uint32_t)20U * sizeof (v[0U]));
      }
    }
    if (max * (uint32_t)20U < n)
    {
      uint8_t *block;
      if (output1 == NULL)
      {
        block = NULL;
      }
      else
      {
        block = output1 + max * (uint32_t)20U;
      }
      EverCrypt_HMAC_compute_sha1(v, k, (uint32_t)20U, v, (uint32_t)20U);
      uint8_t *uu____23;
      if (v == NULL)
      {
        uu____23 = NULL;
      }
      else
      {
        uu____23 = v;
      }
      bool uu____24 = uu____23 == NULL;
      if (!(uu____24 || block == NULL))
      {
        memcpy(block, uu____23, (n - max * (uint32_t)20U) * sizeof (uu____23[0U]));
      }
    }
    uint32_t input_len = (uint32_t)21U + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
    uint8_t input0[input_len];
    memset(input0, 0U, input_len * sizeof (input0[0U]));
    uint8_t *k_;
    if (input0 == NULL)
    {
      k_ = NULL;
    }
    else
    {
      k_ = input0;
    }
    bool uu____25 = v == NULL;
    if (!(uu____25 || k_ == NULL))
    {
      memcpy(k_, v, (uint32_t)20U * sizeof (v[0U]));
    }
    if (additional_input_len != (uint32_t)0U)
    {
      uint8_t *uu____26;
      if (input0 == NULL)
      {
        uu____26 = NULL;
      }
      else
      {
        uu____26 = input0 + (uint32_t)21U;
      }
      bool uu____27 = additional_input == NULL;
      if (!(uu____27 || uu____26 == NULL))
      {
        memcpy(uu____26, additional_input, additional_input_len * sizeof (additional_input[0U]));
      }
    }
    input0[20U] = (uint8_t)0U;
    EverCrypt_HMAC_compute_sha1(k_, k, (uint32_t)20U, input0, input_len);
    EverCrypt_HMAC_compute_sha1(v, k_, (uint32_t)20U, v, (uint32_t)20U);
    bool uu____28 = k_ == NULL;
    if (!(uu____28 || k == NULL))
    {
      memcpy(k, k_, (uint32_t)20U * sizeof (k_[0U]));
    }
    if (additional_input_len != (uint32_t)0U)
    {
      uint32_t input_len0 = (uint32_t)21U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
      uint8_t input[input_len0];
      memset(input, 0U, input_len0 * sizeof (input[0U]));
      uint8_t *k_0;
      if (input == NULL)
      {
        k_0 = NULL;
      }
      else
      {
        k_0 = input;
      }
      bool uu____29 = v == NULL;
      if (!(uu____29 || k_0 == NULL))
      {
        memcpy(k_0, v, (uint32_t)20U * sizeof (v[0U]));
      }
      if (additional_input_len != (uint32_t)0U)
      {
        uint8_t *uu____30;
        if (input == NULL)
        {
          uu____30 = NULL;
        }
        else
        {
          uu____30 = input + (uint32_t)21U;
        }
        bool uu____31 = additional_input == NULL;
        if (!(uu____31 || uu____30 == NULL))
        {
          memcpy(uu____30, additional_input, additional_input_len * sizeof (additional_input[0U]));
        }
      }
      input[20U] = (uint8_t)1U;
      EverCrypt_HMAC_compute_sha1(k_0, k, (uint32_t)20U, input, input_len0);
      EverCrypt_HMAC_compute_sha1(v, k_0, (uint32_t)20U, v, (uint32_t)20U);
      bool uu____32 = k_0 == NULL;
      if (!(uu____32 || k == NULL))
      {
        memcpy(k, k_0, (uint32_t)20U * sizeof (k_0[0U]));
      }
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
  uint32_t n,
  uint8_t *additional_input,
  uint32_t additional_input_len
)
{
  if
  (
    additional_input_len
    > Hacl_HMAC_DRBG_max_additional_input_length
    || n > Hacl_HMAC_DRBG_max_output_length
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
    memset(entropy_input, 0U, entropy_input_len1 * sizeof (entropy_input[0U]));
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
        (entropy_input_len1 + additional_input_len) * sizeof (seed_material[0U]));
      uint8_t *uu____0;
      if (seed_material == NULL)
      {
        uu____0 = NULL;
      }
      else
      {
        uu____0 = seed_material;
      }
      bool uu____1 = entropy_input == NULL;
      if (!(uu____1 || uu____0 == NULL))
      {
        memcpy(uu____0, entropy_input, entropy_input_len1 * sizeof (entropy_input[0U]));
      }
      uint8_t *uu____2;
      if (seed_material == NULL)
      {
        uu____2 = NULL;
      }
      else
      {
        uu____2 = seed_material + entropy_input_len1;
      }
      bool uu____3 = additional_input == NULL;
      if (!(uu____3 || uu____2 == NULL))
      {
        memcpy(uu____2, additional_input, additional_input_len * sizeof (additional_input[0U]));
      }
      Hacl_HMAC_DRBG_state uu____4;
      if (st_s.tag == EverCrypt_DRBG_SHA2_256_s)
      {
        uu____4 = st_s.case_SHA2_256_s;
      }
      else
      {
        uu____4 =
          KRML_EABORT(Hacl_HMAC_DRBG_state,
            "unreachable (pattern matches are exhaustive in F*)");
      }
      uint8_t *k = uu____4.k;
      uint8_t *v = uu____4.v;
      uint32_t *ctr = uu____4.reseed_counter;
      uint32_t input_len = (uint32_t)33U + entropy_input_len1 + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t input0[input_len];
      memset(input0, 0U, input_len * sizeof (input0[0U]));
      uint8_t *k_;
      if (input0 == NULL)
      {
        k_ = NULL;
      }
      else
      {
        k_ = input0;
      }
      bool uu____5 = v == NULL;
      if (!(uu____5 || k_ == NULL))
      {
        memcpy(k_, v, (uint32_t)32U * sizeof (v[0U]));
      }
      if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
      {
        uint8_t *uu____6;
        if (input0 == NULL)
        {
          uu____6 = NULL;
        }
        else
        {
          uu____6 = input0 + (uint32_t)33U;
        }
        bool uu____7 = seed_material == NULL;
        if (!(uu____7 || uu____6 == NULL))
        {
          memcpy(uu____6,
            seed_material,
            (entropy_input_len1 + additional_input_len) * sizeof (seed_material[0U]));
        }
      }
      input0[32U] = (uint8_t)0U;
      EverCrypt_HMAC_compute_sha2_256(k_, k, (uint32_t)32U, input0, input_len);
      EverCrypt_HMAC_compute_sha2_256(v, k_, (uint32_t)32U, v, (uint32_t)32U);
      bool uu____8 = k_ == NULL;
      if (!(uu____8 || k == NULL))
      {
        memcpy(k, k_, (uint32_t)32U * sizeof (k_[0U]));
      }
      if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
      {
        uint32_t input_len0 = (uint32_t)33U + entropy_input_len1 + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t input[input_len0];
        memset(input, 0U, input_len0 * sizeof (input[0U]));
        uint8_t *k_0;
        if (input == NULL)
        {
          k_0 = NULL;
        }
        else
        {
          k_0 = input;
        }
        bool uu____9 = v == NULL;
        if (!(uu____9 || k_0 == NULL))
        {
          memcpy(k_0, v, (uint32_t)32U * sizeof (v[0U]));
        }
        if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
        {
          uint8_t *uu____10;
          if (input == NULL)
          {
            uu____10 = NULL;
          }
          else
          {
            uu____10 = input + (uint32_t)33U;
          }
          bool uu____11 = seed_material == NULL;
          if (!(uu____11 || uu____10 == NULL))
          {
            memcpy(uu____10,
              seed_material,
              (entropy_input_len1 + additional_input_len) * sizeof (seed_material[0U]));
          }
        }
        input[32U] = (uint8_t)1U;
        EverCrypt_HMAC_compute_sha2_256(k_0, k, (uint32_t)32U, input, input_len0);
        EverCrypt_HMAC_compute_sha2_256(v, k_0, (uint32_t)32U, v, (uint32_t)32U);
        bool uu____12 = k_0 == NULL;
        if (!(uu____12 || k == NULL))
        {
          memcpy(k, k_0, (uint32_t)32U * sizeof (k_0[0U]));
        }
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
    uint8_t *k = scrut.k;
    uint8_t *v = scrut.v;
    uint32_t *ctr = scrut.reseed_counter;
    if (additional_input_len > (uint32_t)0U)
    {
      uint32_t input_len = (uint32_t)33U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t input0[input_len];
      memset(input0, 0U, input_len * sizeof (input0[0U]));
      uint8_t *k_;
      if (input0 == NULL)
      {
        k_ = NULL;
      }
      else
      {
        k_ = input0;
      }
      bool uu____13 = v == NULL;
      if (!(uu____13 || k_ == NULL))
      {
        memcpy(k_, v, (uint32_t)32U * sizeof (v[0U]));
      }
      if (additional_input_len != (uint32_t)0U)
      {
        uint8_t *uu____14;
        if (input0 == NULL)
        {
          uu____14 = NULL;
        }
        else
        {
          uu____14 = input0 + (uint32_t)33U;
        }
        bool uu____15 = additional_input == NULL;
        if (!(uu____15 || uu____14 == NULL))
        {
          memcpy(uu____14, additional_input, additional_input_len * sizeof (additional_input[0U]));
        }
      }
      input0[32U] = (uint8_t)0U;
      EverCrypt_HMAC_compute_sha2_256(k_, k, (uint32_t)32U, input0, input_len);
      EverCrypt_HMAC_compute_sha2_256(v, k_, (uint32_t)32U, v, (uint32_t)32U);
      bool uu____16 = k_ == NULL;
      if (!(uu____16 || k == NULL))
      {
        memcpy(k, k_, (uint32_t)32U * sizeof (k_[0U]));
      }
      if (additional_input_len != (uint32_t)0U)
      {
        uint32_t input_len0 = (uint32_t)33U + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t input[input_len0];
        memset(input, 0U, input_len0 * sizeof (input[0U]));
        uint8_t *k_0;
        if (input == NULL)
        {
          k_0 = NULL;
        }
        else
        {
          k_0 = input;
        }
        bool uu____17 = v == NULL;
        if (!(uu____17 || k_0 == NULL))
        {
          memcpy(k_0, v, (uint32_t)32U * sizeof (v[0U]));
        }
        if (additional_input_len != (uint32_t)0U)
        {
          uint8_t *uu____18;
          if (input == NULL)
          {
            uu____18 = NULL;
          }
          else
          {
            uu____18 = input + (uint32_t)33U;
          }
          bool uu____19 = additional_input == NULL;
          if (!(uu____19 || uu____18 == NULL))
          {
            memcpy(uu____18,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
        }
        input[32U] = (uint8_t)1U;
        EverCrypt_HMAC_compute_sha2_256(k_0, k, (uint32_t)32U, input, input_len0);
        EverCrypt_HMAC_compute_sha2_256(v, k_0, (uint32_t)32U, v, (uint32_t)32U);
        bool uu____20 = k_0 == NULL;
        if (!(uu____20 || k == NULL))
        {
          memcpy(k, k_0, (uint32_t)32U * sizeof (k_0[0U]));
        }
      }
    }
    uint8_t *output1 = output;
    uint32_t max = n / (uint32_t)32U;
    uint8_t *out;
    if (output1 == NULL)
    {
      out = NULL;
    }
    else
    {
      out = output1;
    }
    for (uint32_t i = (uint32_t)0U; i < max; i++)
    {
      uint8_t *block;
      if (out == NULL)
      {
        block = NULL;
      }
      else
      {
        block = out + i * (uint32_t)32U;
      }
      EverCrypt_HMAC_compute_sha2_256(v, k, (uint32_t)32U, v, (uint32_t)32U);
      uint8_t *uu____21;
      if (out == NULL)
      {
        uu____21 = NULL;
      }
      else
      {
        uu____21 = out + i * (uint32_t)32U;
      }
      bool uu____22 = v == NULL;
      if (!(uu____22 || uu____21 == NULL))
      {
        memcpy(uu____21, v, (uint32_t)32U * sizeof (v[0U]));
      }
    }
    if (max * (uint32_t)32U < n)
    {
      uint8_t *block;
      if (output1 == NULL)
      {
        block = NULL;
      }
      else
      {
        block = output1 + max * (uint32_t)32U;
      }
      EverCrypt_HMAC_compute_sha2_256(v, k, (uint32_t)32U, v, (uint32_t)32U);
      uint8_t *uu____23;
      if (v == NULL)
      {
        uu____23 = NULL;
      }
      else
      {
        uu____23 = v;
      }
      bool uu____24 = uu____23 == NULL;
      if (!(uu____24 || block == NULL))
      {
        memcpy(block, uu____23, (n - max * (uint32_t)32U) * sizeof (uu____23[0U]));
      }
    }
    uint32_t input_len = (uint32_t)33U + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
    uint8_t input0[input_len];
    memset(input0, 0U, input_len * sizeof (input0[0U]));
    uint8_t *k_;
    if (input0 == NULL)
    {
      k_ = NULL;
    }
    else
    {
      k_ = input0;
    }
    bool uu____25 = v == NULL;
    if (!(uu____25 || k_ == NULL))
    {
      memcpy(k_, v, (uint32_t)32U * sizeof (v[0U]));
    }
    if (additional_input_len != (uint32_t)0U)
    {
      uint8_t *uu____26;
      if (input0 == NULL)
      {
        uu____26 = NULL;
      }
      else
      {
        uu____26 = input0 + (uint32_t)33U;
      }
      bool uu____27 = additional_input == NULL;
      if (!(uu____27 || uu____26 == NULL))
      {
        memcpy(uu____26, additional_input, additional_input_len * sizeof (additional_input[0U]));
      }
    }
    input0[32U] = (uint8_t)0U;
    EverCrypt_HMAC_compute_sha2_256(k_, k, (uint32_t)32U, input0, input_len);
    EverCrypt_HMAC_compute_sha2_256(v, k_, (uint32_t)32U, v, (uint32_t)32U);
    bool uu____28 = k_ == NULL;
    if (!(uu____28 || k == NULL))
    {
      memcpy(k, k_, (uint32_t)32U * sizeof (k_[0U]));
    }
    if (additional_input_len != (uint32_t)0U)
    {
      uint32_t input_len0 = (uint32_t)33U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
      uint8_t input[input_len0];
      memset(input, 0U, input_len0 * sizeof (input[0U]));
      uint8_t *k_0;
      if (input == NULL)
      {
        k_0 = NULL;
      }
      else
      {
        k_0 = input;
      }
      bool uu____29 = v == NULL;
      if (!(uu____29 || k_0 == NULL))
      {
        memcpy(k_0, v, (uint32_t)32U * sizeof (v[0U]));
      }
      if (additional_input_len != (uint32_t)0U)
      {
        uint8_t *uu____30;
        if (input == NULL)
        {
          uu____30 = NULL;
        }
        else
        {
          uu____30 = input + (uint32_t)33U;
        }
        bool uu____31 = additional_input == NULL;
        if (!(uu____31 || uu____30 == NULL))
        {
          memcpy(uu____30, additional_input, additional_input_len * sizeof (additional_input[0U]));
        }
      }
      input[32U] = (uint8_t)1U;
      EverCrypt_HMAC_compute_sha2_256(k_0, k, (uint32_t)32U, input, input_len0);
      EverCrypt_HMAC_compute_sha2_256(v, k_0, (uint32_t)32U, v, (uint32_t)32U);
      bool uu____32 = k_0 == NULL;
      if (!(uu____32 || k == NULL))
      {
        memcpy(k, k_0, (uint32_t)32U * sizeof (k_0[0U]));
      }
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
  uint32_t n,
  uint8_t *additional_input,
  uint32_t additional_input_len
)
{
  if
  (
    additional_input_len
    > Hacl_HMAC_DRBG_max_additional_input_length
    || n > Hacl_HMAC_DRBG_max_output_length
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
    memset(entropy_input, 0U, entropy_input_len1 * sizeof (entropy_input[0U]));
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
        (entropy_input_len1 + additional_input_len) * sizeof (seed_material[0U]));
      uint8_t *uu____0;
      if (seed_material == NULL)
      {
        uu____0 = NULL;
      }
      else
      {
        uu____0 = seed_material;
      }
      bool uu____1 = entropy_input == NULL;
      if (!(uu____1 || uu____0 == NULL))
      {
        memcpy(uu____0, entropy_input, entropy_input_len1 * sizeof (entropy_input[0U]));
      }
      uint8_t *uu____2;
      if (seed_material == NULL)
      {
        uu____2 = NULL;
      }
      else
      {
        uu____2 = seed_material + entropy_input_len1;
      }
      bool uu____3 = additional_input == NULL;
      if (!(uu____3 || uu____2 == NULL))
      {
        memcpy(uu____2, additional_input, additional_input_len * sizeof (additional_input[0U]));
      }
      Hacl_HMAC_DRBG_state uu____4;
      if (st_s.tag == EverCrypt_DRBG_SHA2_384_s)
      {
        uu____4 = st_s.case_SHA2_384_s;
      }
      else
      {
        uu____4 =
          KRML_EABORT(Hacl_HMAC_DRBG_state,
            "unreachable (pattern matches are exhaustive in F*)");
      }
      uint8_t *k = uu____4.k;
      uint8_t *v = uu____4.v;
      uint32_t *ctr = uu____4.reseed_counter;
      uint32_t input_len = (uint32_t)49U + entropy_input_len1 + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t input0[input_len];
      memset(input0, 0U, input_len * sizeof (input0[0U]));
      uint8_t *k_;
      if (input0 == NULL)
      {
        k_ = NULL;
      }
      else
      {
        k_ = input0;
      }
      bool uu____5 = v == NULL;
      if (!(uu____5 || k_ == NULL))
      {
        memcpy(k_, v, (uint32_t)48U * sizeof (v[0U]));
      }
      if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
      {
        uint8_t *uu____6;
        if (input0 == NULL)
        {
          uu____6 = NULL;
        }
        else
        {
          uu____6 = input0 + (uint32_t)49U;
        }
        bool uu____7 = seed_material == NULL;
        if (!(uu____7 || uu____6 == NULL))
        {
          memcpy(uu____6,
            seed_material,
            (entropy_input_len1 + additional_input_len) * sizeof (seed_material[0U]));
        }
      }
      input0[48U] = (uint8_t)0U;
      EverCrypt_HMAC_compute_sha2_384(k_, k, (uint32_t)48U, input0, input_len);
      EverCrypt_HMAC_compute_sha2_384(v, k_, (uint32_t)48U, v, (uint32_t)48U);
      bool uu____8 = k_ == NULL;
      if (!(uu____8 || k == NULL))
      {
        memcpy(k, k_, (uint32_t)48U * sizeof (k_[0U]));
      }
      if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
      {
        uint32_t input_len0 = (uint32_t)49U + entropy_input_len1 + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t input[input_len0];
        memset(input, 0U, input_len0 * sizeof (input[0U]));
        uint8_t *k_0;
        if (input == NULL)
        {
          k_0 = NULL;
        }
        else
        {
          k_0 = input;
        }
        bool uu____9 = v == NULL;
        if (!(uu____9 || k_0 == NULL))
        {
          memcpy(k_0, v, (uint32_t)48U * sizeof (v[0U]));
        }
        if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
        {
          uint8_t *uu____10;
          if (input == NULL)
          {
            uu____10 = NULL;
          }
          else
          {
            uu____10 = input + (uint32_t)49U;
          }
          bool uu____11 = seed_material == NULL;
          if (!(uu____11 || uu____10 == NULL))
          {
            memcpy(uu____10,
              seed_material,
              (entropy_input_len1 + additional_input_len) * sizeof (seed_material[0U]));
          }
        }
        input[48U] = (uint8_t)1U;
        EverCrypt_HMAC_compute_sha2_384(k_0, k, (uint32_t)48U, input, input_len0);
        EverCrypt_HMAC_compute_sha2_384(v, k_0, (uint32_t)48U, v, (uint32_t)48U);
        bool uu____12 = k_0 == NULL;
        if (!(uu____12 || k == NULL))
        {
          memcpy(k, k_0, (uint32_t)48U * sizeof (k_0[0U]));
        }
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
    uint8_t *k = scrut.k;
    uint8_t *v = scrut.v;
    uint32_t *ctr = scrut.reseed_counter;
    if (additional_input_len > (uint32_t)0U)
    {
      uint32_t input_len = (uint32_t)49U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t input0[input_len];
      memset(input0, 0U, input_len * sizeof (input0[0U]));
      uint8_t *k_;
      if (input0 == NULL)
      {
        k_ = NULL;
      }
      else
      {
        k_ = input0;
      }
      bool uu____13 = v == NULL;
      if (!(uu____13 || k_ == NULL))
      {
        memcpy(k_, v, (uint32_t)48U * sizeof (v[0U]));
      }
      if (additional_input_len != (uint32_t)0U)
      {
        uint8_t *uu____14;
        if (input0 == NULL)
        {
          uu____14 = NULL;
        }
        else
        {
          uu____14 = input0 + (uint32_t)49U;
        }
        bool uu____15 = additional_input == NULL;
        if (!(uu____15 || uu____14 == NULL))
        {
          memcpy(uu____14, additional_input, additional_input_len * sizeof (additional_input[0U]));
        }
      }
      input0[48U] = (uint8_t)0U;
      EverCrypt_HMAC_compute_sha2_384(k_, k, (uint32_t)48U, input0, input_len);
      EverCrypt_HMAC_compute_sha2_384(v, k_, (uint32_t)48U, v, (uint32_t)48U);
      bool uu____16 = k_ == NULL;
      if (!(uu____16 || k == NULL))
      {
        memcpy(k, k_, (uint32_t)48U * sizeof (k_[0U]));
      }
      if (additional_input_len != (uint32_t)0U)
      {
        uint32_t input_len0 = (uint32_t)49U + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t input[input_len0];
        memset(input, 0U, input_len0 * sizeof (input[0U]));
        uint8_t *k_0;
        if (input == NULL)
        {
          k_0 = NULL;
        }
        else
        {
          k_0 = input;
        }
        bool uu____17 = v == NULL;
        if (!(uu____17 || k_0 == NULL))
        {
          memcpy(k_0, v, (uint32_t)48U * sizeof (v[0U]));
        }
        if (additional_input_len != (uint32_t)0U)
        {
          uint8_t *uu____18;
          if (input == NULL)
          {
            uu____18 = NULL;
          }
          else
          {
            uu____18 = input + (uint32_t)49U;
          }
          bool uu____19 = additional_input == NULL;
          if (!(uu____19 || uu____18 == NULL))
          {
            memcpy(uu____18,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
        }
        input[48U] = (uint8_t)1U;
        EverCrypt_HMAC_compute_sha2_384(k_0, k, (uint32_t)48U, input, input_len0);
        EverCrypt_HMAC_compute_sha2_384(v, k_0, (uint32_t)48U, v, (uint32_t)48U);
        bool uu____20 = k_0 == NULL;
        if (!(uu____20 || k == NULL))
        {
          memcpy(k, k_0, (uint32_t)48U * sizeof (k_0[0U]));
        }
      }
    }
    uint8_t *output1 = output;
    uint32_t max = n / (uint32_t)48U;
    uint8_t *out;
    if (output1 == NULL)
    {
      out = NULL;
    }
    else
    {
      out = output1;
    }
    for (uint32_t i = (uint32_t)0U; i < max; i++)
    {
      uint8_t *block;
      if (out == NULL)
      {
        block = NULL;
      }
      else
      {
        block = out + i * (uint32_t)48U;
      }
      EverCrypt_HMAC_compute_sha2_384(v, k, (uint32_t)48U, v, (uint32_t)48U);
      uint8_t *uu____21;
      if (out == NULL)
      {
        uu____21 = NULL;
      }
      else
      {
        uu____21 = out + i * (uint32_t)48U;
      }
      bool uu____22 = v == NULL;
      if (!(uu____22 || uu____21 == NULL))
      {
        memcpy(uu____21, v, (uint32_t)48U * sizeof (v[0U]));
      }
    }
    if (max * (uint32_t)48U < n)
    {
      uint8_t *block;
      if (output1 == NULL)
      {
        block = NULL;
      }
      else
      {
        block = output1 + max * (uint32_t)48U;
      }
      EverCrypt_HMAC_compute_sha2_384(v, k, (uint32_t)48U, v, (uint32_t)48U);
      uint8_t *uu____23;
      if (v == NULL)
      {
        uu____23 = NULL;
      }
      else
      {
        uu____23 = v;
      }
      bool uu____24 = uu____23 == NULL;
      if (!(uu____24 || block == NULL))
      {
        memcpy(block, uu____23, (n - max * (uint32_t)48U) * sizeof (uu____23[0U]));
      }
    }
    uint32_t input_len = (uint32_t)49U + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
    uint8_t input0[input_len];
    memset(input0, 0U, input_len * sizeof (input0[0U]));
    uint8_t *k_;
    if (input0 == NULL)
    {
      k_ = NULL;
    }
    else
    {
      k_ = input0;
    }
    bool uu____25 = v == NULL;
    if (!(uu____25 || k_ == NULL))
    {
      memcpy(k_, v, (uint32_t)48U * sizeof (v[0U]));
    }
    if (additional_input_len != (uint32_t)0U)
    {
      uint8_t *uu____26;
      if (input0 == NULL)
      {
        uu____26 = NULL;
      }
      else
      {
        uu____26 = input0 + (uint32_t)49U;
      }
      bool uu____27 = additional_input == NULL;
      if (!(uu____27 || uu____26 == NULL))
      {
        memcpy(uu____26, additional_input, additional_input_len * sizeof (additional_input[0U]));
      }
    }
    input0[48U] = (uint8_t)0U;
    EverCrypt_HMAC_compute_sha2_384(k_, k, (uint32_t)48U, input0, input_len);
    EverCrypt_HMAC_compute_sha2_384(v, k_, (uint32_t)48U, v, (uint32_t)48U);
    bool uu____28 = k_ == NULL;
    if (!(uu____28 || k == NULL))
    {
      memcpy(k, k_, (uint32_t)48U * sizeof (k_[0U]));
    }
    if (additional_input_len != (uint32_t)0U)
    {
      uint32_t input_len0 = (uint32_t)49U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
      uint8_t input[input_len0];
      memset(input, 0U, input_len0 * sizeof (input[0U]));
      uint8_t *k_0;
      if (input == NULL)
      {
        k_0 = NULL;
      }
      else
      {
        k_0 = input;
      }
      bool uu____29 = v == NULL;
      if (!(uu____29 || k_0 == NULL))
      {
        memcpy(k_0, v, (uint32_t)48U * sizeof (v[0U]));
      }
      if (additional_input_len != (uint32_t)0U)
      {
        uint8_t *uu____30;
        if (input == NULL)
        {
          uu____30 = NULL;
        }
        else
        {
          uu____30 = input + (uint32_t)49U;
        }
        bool uu____31 = additional_input == NULL;
        if (!(uu____31 || uu____30 == NULL))
        {
          memcpy(uu____30, additional_input, additional_input_len * sizeof (additional_input[0U]));
        }
      }
      input[48U] = (uint8_t)1U;
      EverCrypt_HMAC_compute_sha2_384(k_0, k, (uint32_t)48U, input, input_len0);
      EverCrypt_HMAC_compute_sha2_384(v, k_0, (uint32_t)48U, v, (uint32_t)48U);
      bool uu____32 = k_0 == NULL;
      if (!(uu____32 || k == NULL))
      {
        memcpy(k, k_0, (uint32_t)48U * sizeof (k_0[0U]));
      }
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
  uint32_t n,
  uint8_t *additional_input,
  uint32_t additional_input_len
)
{
  if
  (
    additional_input_len
    > Hacl_HMAC_DRBG_max_additional_input_length
    || n > Hacl_HMAC_DRBG_max_output_length
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
    memset(entropy_input, 0U, entropy_input_len1 * sizeof (entropy_input[0U]));
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
        (entropy_input_len1 + additional_input_len) * sizeof (seed_material[0U]));
      uint8_t *uu____0;
      if (seed_material == NULL)
      {
        uu____0 = NULL;
      }
      else
      {
        uu____0 = seed_material;
      }
      bool uu____1 = entropy_input == NULL;
      if (!(uu____1 || uu____0 == NULL))
      {
        memcpy(uu____0, entropy_input, entropy_input_len1 * sizeof (entropy_input[0U]));
      }
      uint8_t *uu____2;
      if (seed_material == NULL)
      {
        uu____2 = NULL;
      }
      else
      {
        uu____2 = seed_material + entropy_input_len1;
      }
      bool uu____3 = additional_input == NULL;
      if (!(uu____3 || uu____2 == NULL))
      {
        memcpy(uu____2, additional_input, additional_input_len * sizeof (additional_input[0U]));
      }
      Hacl_HMAC_DRBG_state uu____4;
      if (st_s.tag == EverCrypt_DRBG_SHA2_512_s)
      {
        uu____4 = st_s.case_SHA2_512_s;
      }
      else
      {
        uu____4 =
          KRML_EABORT(Hacl_HMAC_DRBG_state,
            "unreachable (pattern matches are exhaustive in F*)");
      }
      uint8_t *k = uu____4.k;
      uint8_t *v = uu____4.v;
      uint32_t *ctr = uu____4.reseed_counter;
      uint32_t input_len = (uint32_t)65U + entropy_input_len1 + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t input0[input_len];
      memset(input0, 0U, input_len * sizeof (input0[0U]));
      uint8_t *k_;
      if (input0 == NULL)
      {
        k_ = NULL;
      }
      else
      {
        k_ = input0;
      }
      bool uu____5 = v == NULL;
      if (!(uu____5 || k_ == NULL))
      {
        memcpy(k_, v, (uint32_t)64U * sizeof (v[0U]));
      }
      if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
      {
        uint8_t *uu____6;
        if (input0 == NULL)
        {
          uu____6 = NULL;
        }
        else
        {
          uu____6 = input0 + (uint32_t)65U;
        }
        bool uu____7 = seed_material == NULL;
        if (!(uu____7 || uu____6 == NULL))
        {
          memcpy(uu____6,
            seed_material,
            (entropy_input_len1 + additional_input_len) * sizeof (seed_material[0U]));
        }
      }
      input0[64U] = (uint8_t)0U;
      EverCrypt_HMAC_compute_sha2_512(k_, k, (uint32_t)64U, input0, input_len);
      EverCrypt_HMAC_compute_sha2_512(v, k_, (uint32_t)64U, v, (uint32_t)64U);
      bool uu____8 = k_ == NULL;
      if (!(uu____8 || k == NULL))
      {
        memcpy(k, k_, (uint32_t)64U * sizeof (k_[0U]));
      }
      if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
      {
        uint32_t input_len0 = (uint32_t)65U + entropy_input_len1 + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t input[input_len0];
        memset(input, 0U, input_len0 * sizeof (input[0U]));
        uint8_t *k_0;
        if (input == NULL)
        {
          k_0 = NULL;
        }
        else
        {
          k_0 = input;
        }
        bool uu____9 = v == NULL;
        if (!(uu____9 || k_0 == NULL))
        {
          memcpy(k_0, v, (uint32_t)64U * sizeof (v[0U]));
        }
        if (entropy_input_len1 + additional_input_len != (uint32_t)0U)
        {
          uint8_t *uu____10;
          if (input == NULL)
          {
            uu____10 = NULL;
          }
          else
          {
            uu____10 = input + (uint32_t)65U;
          }
          bool uu____11 = seed_material == NULL;
          if (!(uu____11 || uu____10 == NULL))
          {
            memcpy(uu____10,
              seed_material,
              (entropy_input_len1 + additional_input_len) * sizeof (seed_material[0U]));
          }
        }
        input[64U] = (uint8_t)1U;
        EverCrypt_HMAC_compute_sha2_512(k_0, k, (uint32_t)64U, input, input_len0);
        EverCrypt_HMAC_compute_sha2_512(v, k_0, (uint32_t)64U, v, (uint32_t)64U);
        bool uu____12 = k_0 == NULL;
        if (!(uu____12 || k == NULL))
        {
          memcpy(k, k_0, (uint32_t)64U * sizeof (k_0[0U]));
        }
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
    uint8_t *k = scrut.k;
    uint8_t *v = scrut.v;
    uint32_t *ctr = scrut.reseed_counter;
    if (additional_input_len > (uint32_t)0U)
    {
      uint32_t input_len = (uint32_t)65U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t input0[input_len];
      memset(input0, 0U, input_len * sizeof (input0[0U]));
      uint8_t *k_;
      if (input0 == NULL)
      {
        k_ = NULL;
      }
      else
      {
        k_ = input0;
      }
      bool uu____13 = v == NULL;
      if (!(uu____13 || k_ == NULL))
      {
        memcpy(k_, v, (uint32_t)64U * sizeof (v[0U]));
      }
      if (additional_input_len != (uint32_t)0U)
      {
        uint8_t *uu____14;
        if (input0 == NULL)
        {
          uu____14 = NULL;
        }
        else
        {
          uu____14 = input0 + (uint32_t)65U;
        }
        bool uu____15 = additional_input == NULL;
        if (!(uu____15 || uu____14 == NULL))
        {
          memcpy(uu____14, additional_input, additional_input_len * sizeof (additional_input[0U]));
        }
      }
      input0[64U] = (uint8_t)0U;
      EverCrypt_HMAC_compute_sha2_512(k_, k, (uint32_t)64U, input0, input_len);
      EverCrypt_HMAC_compute_sha2_512(v, k_, (uint32_t)64U, v, (uint32_t)64U);
      bool uu____16 = k_ == NULL;
      if (!(uu____16 || k == NULL))
      {
        memcpy(k, k_, (uint32_t)64U * sizeof (k_[0U]));
      }
      if (additional_input_len != (uint32_t)0U)
      {
        uint32_t input_len0 = (uint32_t)65U + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t input[input_len0];
        memset(input, 0U, input_len0 * sizeof (input[0U]));
        uint8_t *k_0;
        if (input == NULL)
        {
          k_0 = NULL;
        }
        else
        {
          k_0 = input;
        }
        bool uu____17 = v == NULL;
        if (!(uu____17 || k_0 == NULL))
        {
          memcpy(k_0, v, (uint32_t)64U * sizeof (v[0U]));
        }
        if (additional_input_len != (uint32_t)0U)
        {
          uint8_t *uu____18;
          if (input == NULL)
          {
            uu____18 = NULL;
          }
          else
          {
            uu____18 = input + (uint32_t)65U;
          }
          bool uu____19 = additional_input == NULL;
          if (!(uu____19 || uu____18 == NULL))
          {
            memcpy(uu____18,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
        }
        input[64U] = (uint8_t)1U;
        EverCrypt_HMAC_compute_sha2_512(k_0, k, (uint32_t)64U, input, input_len0);
        EverCrypt_HMAC_compute_sha2_512(v, k_0, (uint32_t)64U, v, (uint32_t)64U);
        bool uu____20 = k_0 == NULL;
        if (!(uu____20 || k == NULL))
        {
          memcpy(k, k_0, (uint32_t)64U * sizeof (k_0[0U]));
        }
      }
    }
    uint8_t *output1 = output;
    uint32_t max = n / (uint32_t)64U;
    uint8_t *out;
    if (output1 == NULL)
    {
      out = NULL;
    }
    else
    {
      out = output1;
    }
    for (uint32_t i = (uint32_t)0U; i < max; i++)
    {
      uint8_t *block;
      if (out == NULL)
      {
        block = NULL;
      }
      else
      {
        block = out + i * (uint32_t)64U;
      }
      EverCrypt_HMAC_compute_sha2_512(v, k, (uint32_t)64U, v, (uint32_t)64U);
      uint8_t *uu____21;
      if (out == NULL)
      {
        uu____21 = NULL;
      }
      else
      {
        uu____21 = out + i * (uint32_t)64U;
      }
      bool uu____22 = v == NULL;
      if (!(uu____22 || uu____21 == NULL))
      {
        memcpy(uu____21, v, (uint32_t)64U * sizeof (v[0U]));
      }
    }
    if (max * (uint32_t)64U < n)
    {
      uint8_t *block;
      if (output1 == NULL)
      {
        block = NULL;
      }
      else
      {
        block = output1 + max * (uint32_t)64U;
      }
      EverCrypt_HMAC_compute_sha2_512(v, k, (uint32_t)64U, v, (uint32_t)64U);
      uint8_t *uu____23;
      if (v == NULL)
      {
        uu____23 = NULL;
      }
      else
      {
        uu____23 = v;
      }
      bool uu____24 = uu____23 == NULL;
      if (!(uu____24 || block == NULL))
      {
        memcpy(block, uu____23, (n - max * (uint32_t)64U) * sizeof (uu____23[0U]));
      }
    }
    uint32_t input_len = (uint32_t)65U + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
    uint8_t input0[input_len];
    memset(input0, 0U, input_len * sizeof (input0[0U]));
    uint8_t *k_;
    if (input0 == NULL)
    {
      k_ = NULL;
    }
    else
    {
      k_ = input0;
    }
    bool uu____25 = v == NULL;
    if (!(uu____25 || k_ == NULL))
    {
      memcpy(k_, v, (uint32_t)64U * sizeof (v[0U]));
    }
    if (additional_input_len != (uint32_t)0U)
    {
      uint8_t *uu____26;
      if (input0 == NULL)
      {
        uu____26 = NULL;
      }
      else
      {
        uu____26 = input0 + (uint32_t)65U;
      }
      bool uu____27 = additional_input == NULL;
      if (!(uu____27 || uu____26 == NULL))
      {
        memcpy(uu____26, additional_input, additional_input_len * sizeof (additional_input[0U]));
      }
    }
    input0[64U] = (uint8_t)0U;
    EverCrypt_HMAC_compute_sha2_512(k_, k, (uint32_t)64U, input0, input_len);
    EverCrypt_HMAC_compute_sha2_512(v, k_, (uint32_t)64U, v, (uint32_t)64U);
    bool uu____28 = k_ == NULL;
    if (!(uu____28 || k == NULL))
    {
      memcpy(k, k_, (uint32_t)64U * sizeof (k_[0U]));
    }
    if (additional_input_len != (uint32_t)0U)
    {
      uint32_t input_len0 = (uint32_t)65U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
      uint8_t input[input_len0];
      memset(input, 0U, input_len0 * sizeof (input[0U]));
      uint8_t *k_0;
      if (input == NULL)
      {
        k_0 = NULL;
      }
      else
      {
        k_0 = input;
      }
      bool uu____29 = v == NULL;
      if (!(uu____29 || k_0 == NULL))
      {
        memcpy(k_0, v, (uint32_t)64U * sizeof (v[0U]));
      }
      if (additional_input_len != (uint32_t)0U)
      {
        uint8_t *uu____30;
        if (input == NULL)
        {
          uu____30 = NULL;
        }
        else
        {
          uu____30 = input + (uint32_t)65U;
        }
        bool uu____31 = additional_input == NULL;
        if (!(uu____31 || uu____30 == NULL))
        {
          memcpy(uu____30, additional_input, additional_input_len * sizeof (additional_input[0U]));
        }
      }
      input[64U] = (uint8_t)1U;
      EverCrypt_HMAC_compute_sha2_512(k_0, k, (uint32_t)64U, input, input_len0);
      EverCrypt_HMAC_compute_sha2_512(v, k_0, (uint32_t)64U, v, (uint32_t)64U);
      bool uu____32 = k_0 == NULL;
      if (!(uu____32 || k == NULL))
      {
        memcpy(k, k_0, (uint32_t)64U * sizeof (k_0[0U]));
      }
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
  uint8_t *k = s.k;
  uint8_t *v = s.v;
  uint32_t *ctr = s.reseed_counter;
  Lib_Memzero_clear_words_u8((uint32_t)20U, k);
  Lib_Memzero_clear_words_u8((uint32_t)20U, v);
  ctr[0U] = (uint32_t)0U;
  KRML_HOST_FREE(k);
  KRML_HOST_FREE(v);
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
  uint8_t *k = s.k;
  uint8_t *v = s.v;
  uint32_t *ctr = s.reseed_counter;
  Lib_Memzero_clear_words_u8((uint32_t)32U, k);
  Lib_Memzero_clear_words_u8((uint32_t)32U, v);
  ctr[0U] = (uint32_t)0U;
  KRML_HOST_FREE(k);
  KRML_HOST_FREE(v);
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
  uint8_t *k = s.k;
  uint8_t *v = s.v;
  uint32_t *ctr = s.reseed_counter;
  Lib_Memzero_clear_words_u8((uint32_t)48U, k);
  Lib_Memzero_clear_words_u8((uint32_t)48U, v);
  ctr[0U] = (uint32_t)0U;
  KRML_HOST_FREE(k);
  KRML_HOST_FREE(v);
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
  uint8_t *k = s.k;
  uint8_t *v = s.v;
  uint32_t *ctr = s.reseed_counter;
  Lib_Memzero_clear_words_u8((uint32_t)64U, k);
  Lib_Memzero_clear_words_u8((uint32_t)64U, v);
  ctr[0U] = (uint32_t)0U;
  KRML_HOST_FREE(k);
  KRML_HOST_FREE(v);
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
  uint32_t n,
  uint8_t *additional_input,
  uint32_t additional_input_len
)
{
  EverCrypt_DRBG_state_s scrut = *st;
  if (scrut.tag == EverCrypt_DRBG_SHA1_s)
  {
    return EverCrypt_DRBG_generate_sha1(output, st, n, additional_input, additional_input_len);
  }
  if (scrut.tag == EverCrypt_DRBG_SHA2_256_s)
  {
    return EverCrypt_DRBG_generate_sha2_256(output, st, n, additional_input, additional_input_len);
  }
  if (scrut.tag == EverCrypt_DRBG_SHA2_384_s)
  {
    return EverCrypt_DRBG_generate_sha2_384(output, st, n, additional_input, additional_input_len);
  }
  if (scrut.tag == EverCrypt_DRBG_SHA2_512_s)
  {
    return EverCrypt_DRBG_generate_sha2_512(output, st, n, additional_input, additional_input_len);
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

