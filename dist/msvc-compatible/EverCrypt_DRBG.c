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


#include "EverCrypt_DRBG.h"

#include "internal/EverCrypt_HMAC.h"
#include "lib_memzero0.h"

uint32_t EverCrypt_DRBG_reseed_interval = 1024U;

uint32_t EverCrypt_DRBG_max_output_length = 65536U;

uint32_t EverCrypt_DRBG_max_length = 65536U;

uint32_t EverCrypt_DRBG_max_personalization_string_length = 65536U;

uint32_t EverCrypt_DRBG_max_additional_input_length = 65536U;

uint32_t EverCrypt_DRBG_min_length(Spec_Hash_Definitions_hash_alg a)
{
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        return 16U;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        return 32U;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        return 32U;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        return 32U;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

#define SHA1_s 0
#define SHA2_256_s 1
#define SHA2_384_s 2
#define SHA2_512_s 3

typedef uint8_t state_s_tags;

typedef struct EverCrypt_DRBG_state_s_s
{
  state_s_tags tag;
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
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_DRBG_state_s projectee
)
{
  KRML_MAYBE_UNUSED_VAR(uu___);
  if (projectee.tag == SHA1_s)
  {
    return true;
  }
  return false;
}

bool
EverCrypt_DRBG_uu___is_SHA2_256_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_DRBG_state_s projectee
)
{
  KRML_MAYBE_UNUSED_VAR(uu___);
  if (projectee.tag == SHA2_256_s)
  {
    return true;
  }
  return false;
}

bool
EverCrypt_DRBG_uu___is_SHA2_384_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_DRBG_state_s projectee
)
{
  KRML_MAYBE_UNUSED_VAR(uu___);
  if (projectee.tag == SHA2_384_s)
  {
    return true;
  }
  return false;
}

bool
EverCrypt_DRBG_uu___is_SHA2_512_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_DRBG_state_s projectee
)
{
  KRML_MAYBE_UNUSED_VAR(uu___);
  if (projectee.tag == SHA2_512_s)
  {
    return true;
  }
  return false;
}

EverCrypt_DRBG_state_s *EverCrypt_DRBG_create_in(Spec_Hash_Definitions_hash_alg a)
{
  EverCrypt_DRBG_state_s st;
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        uint8_t *k = (uint8_t *)KRML_HOST_CALLOC(20U, sizeof (uint8_t));
        uint8_t *v = (uint8_t *)KRML_HOST_CALLOC(20U, sizeof (uint8_t));
        uint32_t *ctr = (uint32_t *)KRML_HOST_MALLOC(sizeof (uint32_t));
        ctr[0U] = 1U;
        st =
          (
            (EverCrypt_DRBG_state_s){
              .tag = SHA1_s,
              { .case_SHA1_s = { .k = k, .v = v, .reseed_counter = ctr } }
            }
          );
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        uint8_t *k = (uint8_t *)KRML_HOST_CALLOC(32U, sizeof (uint8_t));
        uint8_t *v = (uint8_t *)KRML_HOST_CALLOC(32U, sizeof (uint8_t));
        uint32_t *ctr = (uint32_t *)KRML_HOST_MALLOC(sizeof (uint32_t));
        ctr[0U] = 1U;
        st =
          (
            (EverCrypt_DRBG_state_s){
              .tag = SHA2_256_s,
              { .case_SHA2_256_s = { .k = k, .v = v, .reseed_counter = ctr } }
            }
          );
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        uint8_t *k = (uint8_t *)KRML_HOST_CALLOC(48U, sizeof (uint8_t));
        uint8_t *v = (uint8_t *)KRML_HOST_CALLOC(48U, sizeof (uint8_t));
        uint32_t *ctr = (uint32_t *)KRML_HOST_MALLOC(sizeof (uint32_t));
        ctr[0U] = 1U;
        st =
          (
            (EverCrypt_DRBG_state_s){
              .tag = SHA2_384_s,
              { .case_SHA2_384_s = { .k = k, .v = v, .reseed_counter = ctr } }
            }
          );
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        uint8_t *k = (uint8_t *)KRML_HOST_CALLOC(64U, sizeof (uint8_t));
        uint8_t *v = (uint8_t *)KRML_HOST_CALLOC(64U, sizeof (uint8_t));
        uint32_t *ctr = (uint32_t *)KRML_HOST_MALLOC(sizeof (uint32_t));
        ctr[0U] = 1U;
        st =
          (
            (EverCrypt_DRBG_state_s){
              .tag = SHA2_512_s,
              { .case_SHA2_512_s = { .k = k, .v = v, .reseed_counter = ctr } }
            }
          );
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  EverCrypt_DRBG_state_s
  *buf = (EverCrypt_DRBG_state_s *)KRML_HOST_MALLOC(sizeof (EverCrypt_DRBG_state_s));
  buf[0U] = st;
  return buf;
}

/**
Create a DRBG state.

@param a Hash algorithm to use. The possible instantiations are ...
  * `Spec_Hash_Definitions_SHA2_256`,
  * `Spec_Hash_Definitions_SHA2_384`,
  * `Spec_Hash_Definitions_SHA2_512`, and
  * `Spec_Hash_Definitions_SHA1`.

@return DRBG state. Needs to be freed via `EverCrypt_DRBG_uninstantiate`.
*/
EverCrypt_DRBG_state_s *EverCrypt_DRBG_create(Spec_Hash_Definitions_hash_alg a)
{
  return EverCrypt_DRBG_create_in(a);
}

static bool
instantiate_sha1(
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
  uint32_t nonce_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA1) / 2U;
  uint32_t min_entropy = entropy_input_len + nonce_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), min_entropy);
  uint8_t *entropy = (uint8_t *)alloca(min_entropy * sizeof (uint8_t));
  memset(entropy, 0U, min_entropy * sizeof (uint8_t));
  bool ok = Lib_RandomBuffer_System_randombytes(entropy, min_entropy);
  if (!ok)
  {
    return false;
  }
  uint8_t *entropy_input = entropy;
  uint8_t *nonce = entropy + entropy_input_len;
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + nonce_len + personalization_string_len);
  uint8_t
  *seed_material =
    (uint8_t *)alloca((entropy_input_len + nonce_len + personalization_string_len)
      * sizeof (uint8_t));
  memset(seed_material,
    0U,
    (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
  memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
  memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof (uint8_t));
  memcpy(seed_material + entropy_input_len + nonce_len,
    personalization_string,
    personalization_string_len * sizeof (uint8_t));
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == SHA1_s)
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
  memset(k, 0U, 20U * sizeof (uint8_t));
  memset(v, 1U, 20U * sizeof (uint8_t));
  ctr[0U] = 1U;
  uint32_t input_len = 21U + entropy_input_len + nonce_len + personalization_string_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
  memset(input0, 0U, input_len * sizeof (uint8_t));
  uint8_t *k_ = input0;
  memcpy(k_, v, 20U * sizeof (uint8_t));
  if (entropy_input_len + nonce_len + personalization_string_len != 0U)
  {
    memcpy(input0 + 21U,
      seed_material,
      (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
  }
  input0[20U] = 0U;
  EverCrypt_HMAC_compute_sha1(k_, k, 20U, input0, input_len);
  EverCrypt_HMAC_compute_sha1(v, k_, 20U, v, 20U);
  memcpy(k, k_, 20U * sizeof (uint8_t));
  if (entropy_input_len + nonce_len + personalization_string_len != 0U)
  {
    uint32_t input_len0 = 21U + entropy_input_len + nonce_len + personalization_string_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
    memset(input, 0U, input_len0 * sizeof (uint8_t));
    uint8_t *k_0 = input;
    memcpy(k_0, v, 20U * sizeof (uint8_t));
    if (entropy_input_len + nonce_len + personalization_string_len != 0U)
    {
      memcpy(input + 21U,
        seed_material,
        (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
    }
    input[20U] = 1U;
    EverCrypt_HMAC_compute_sha1(k_0, k, 20U, input, input_len0);
    EverCrypt_HMAC_compute_sha1(v, k_0, 20U, v, 20U);
    memcpy(k, k_0, 20U * sizeof (uint8_t));
  }
  return true;
}

static bool
instantiate_sha2_256(
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
  uint32_t nonce_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_256) / 2U;
  uint32_t min_entropy = entropy_input_len + nonce_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), min_entropy);
  uint8_t *entropy = (uint8_t *)alloca(min_entropy * sizeof (uint8_t));
  memset(entropy, 0U, min_entropy * sizeof (uint8_t));
  bool ok = Lib_RandomBuffer_System_randombytes(entropy, min_entropy);
  if (!ok)
  {
    return false;
  }
  uint8_t *entropy_input = entropy;
  uint8_t *nonce = entropy + entropy_input_len;
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + nonce_len + personalization_string_len);
  uint8_t
  *seed_material =
    (uint8_t *)alloca((entropy_input_len + nonce_len + personalization_string_len)
      * sizeof (uint8_t));
  memset(seed_material,
    0U,
    (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
  memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
  memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof (uint8_t));
  memcpy(seed_material + entropy_input_len + nonce_len,
    personalization_string,
    personalization_string_len * sizeof (uint8_t));
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == SHA2_256_s)
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
  memset(k, 0U, 32U * sizeof (uint8_t));
  memset(v, 1U, 32U * sizeof (uint8_t));
  ctr[0U] = 1U;
  uint32_t input_len = 33U + entropy_input_len + nonce_len + personalization_string_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
  memset(input0, 0U, input_len * sizeof (uint8_t));
  uint8_t *k_ = input0;
  memcpy(k_, v, 32U * sizeof (uint8_t));
  if (entropy_input_len + nonce_len + personalization_string_len != 0U)
  {
    memcpy(input0 + 33U,
      seed_material,
      (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
  }
  input0[32U] = 0U;
  EverCrypt_HMAC_compute_sha2_256(k_, k, 32U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_256(v, k_, 32U, v, 32U);
  memcpy(k, k_, 32U * sizeof (uint8_t));
  if (entropy_input_len + nonce_len + personalization_string_len != 0U)
  {
    uint32_t input_len0 = 33U + entropy_input_len + nonce_len + personalization_string_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
    memset(input, 0U, input_len0 * sizeof (uint8_t));
    uint8_t *k_0 = input;
    memcpy(k_0, v, 32U * sizeof (uint8_t));
    if (entropy_input_len + nonce_len + personalization_string_len != 0U)
    {
      memcpy(input + 33U,
        seed_material,
        (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
    }
    input[32U] = 1U;
    EverCrypt_HMAC_compute_sha2_256(k_0, k, 32U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_256(v, k_0, 32U, v, 32U);
    memcpy(k, k_0, 32U * sizeof (uint8_t));
  }
  return true;
}

static bool
instantiate_sha2_384(
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
  uint32_t nonce_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_384) / 2U;
  uint32_t min_entropy = entropy_input_len + nonce_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), min_entropy);
  uint8_t *entropy = (uint8_t *)alloca(min_entropy * sizeof (uint8_t));
  memset(entropy, 0U, min_entropy * sizeof (uint8_t));
  bool ok = Lib_RandomBuffer_System_randombytes(entropy, min_entropy);
  if (!ok)
  {
    return false;
  }
  uint8_t *entropy_input = entropy;
  uint8_t *nonce = entropy + entropy_input_len;
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + nonce_len + personalization_string_len);
  uint8_t
  *seed_material =
    (uint8_t *)alloca((entropy_input_len + nonce_len + personalization_string_len)
      * sizeof (uint8_t));
  memset(seed_material,
    0U,
    (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
  memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
  memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof (uint8_t));
  memcpy(seed_material + entropy_input_len + nonce_len,
    personalization_string,
    personalization_string_len * sizeof (uint8_t));
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == SHA2_384_s)
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
  memset(k, 0U, 48U * sizeof (uint8_t));
  memset(v, 1U, 48U * sizeof (uint8_t));
  ctr[0U] = 1U;
  uint32_t input_len = 49U + entropy_input_len + nonce_len + personalization_string_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
  memset(input0, 0U, input_len * sizeof (uint8_t));
  uint8_t *k_ = input0;
  memcpy(k_, v, 48U * sizeof (uint8_t));
  if (entropy_input_len + nonce_len + personalization_string_len != 0U)
  {
    memcpy(input0 + 49U,
      seed_material,
      (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
  }
  input0[48U] = 0U;
  EverCrypt_HMAC_compute_sha2_384(k_, k, 48U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_384(v, k_, 48U, v, 48U);
  memcpy(k, k_, 48U * sizeof (uint8_t));
  if (entropy_input_len + nonce_len + personalization_string_len != 0U)
  {
    uint32_t input_len0 = 49U + entropy_input_len + nonce_len + personalization_string_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
    memset(input, 0U, input_len0 * sizeof (uint8_t));
    uint8_t *k_0 = input;
    memcpy(k_0, v, 48U * sizeof (uint8_t));
    if (entropy_input_len + nonce_len + personalization_string_len != 0U)
    {
      memcpy(input + 49U,
        seed_material,
        (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
    }
    input[48U] = 1U;
    EverCrypt_HMAC_compute_sha2_384(k_0, k, 48U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_384(v, k_0, 48U, v, 48U);
    memcpy(k, k_0, 48U * sizeof (uint8_t));
  }
  return true;
}

static bool
instantiate_sha2_512(
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
  uint32_t nonce_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_512) / 2U;
  uint32_t min_entropy = entropy_input_len + nonce_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), min_entropy);
  uint8_t *entropy = (uint8_t *)alloca(min_entropy * sizeof (uint8_t));
  memset(entropy, 0U, min_entropy * sizeof (uint8_t));
  bool ok = Lib_RandomBuffer_System_randombytes(entropy, min_entropy);
  if (!ok)
  {
    return false;
  }
  uint8_t *entropy_input = entropy;
  uint8_t *nonce = entropy + entropy_input_len;
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + nonce_len + personalization_string_len);
  uint8_t
  *seed_material =
    (uint8_t *)alloca((entropy_input_len + nonce_len + personalization_string_len)
      * sizeof (uint8_t));
  memset(seed_material,
    0U,
    (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
  memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
  memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof (uint8_t));
  memcpy(seed_material + entropy_input_len + nonce_len,
    personalization_string,
    personalization_string_len * sizeof (uint8_t));
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == SHA2_512_s)
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
  memset(k, 0U, 64U * sizeof (uint8_t));
  memset(v, 1U, 64U * sizeof (uint8_t));
  ctr[0U] = 1U;
  uint32_t input_len = 65U + entropy_input_len + nonce_len + personalization_string_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
  memset(input0, 0U, input_len * sizeof (uint8_t));
  uint8_t *k_ = input0;
  memcpy(k_, v, 64U * sizeof (uint8_t));
  if (entropy_input_len + nonce_len + personalization_string_len != 0U)
  {
    memcpy(input0 + 65U,
      seed_material,
      (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
  }
  input0[64U] = 0U;
  EverCrypt_HMAC_compute_sha2_512(k_, k, 64U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_512(v, k_, 64U, v, 64U);
  memcpy(k, k_, 64U * sizeof (uint8_t));
  if (entropy_input_len + nonce_len + personalization_string_len != 0U)
  {
    uint32_t input_len0 = 65U + entropy_input_len + nonce_len + personalization_string_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
    memset(input, 0U, input_len0 * sizeof (uint8_t));
    uint8_t *k_0 = input;
    memcpy(k_0, v, 64U * sizeof (uint8_t));
    if (entropy_input_len + nonce_len + personalization_string_len != 0U)
    {
      memcpy(input + 65U,
        seed_material,
        (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
    }
    input[64U] = 1U;
    EverCrypt_HMAC_compute_sha2_512(k_0, k, 64U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_512(v, k_0, 64U, v, 64U);
    memcpy(k, k_0, 64U * sizeof (uint8_t));
  }
  return true;
}

static bool
reseed_sha1(
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
  uint8_t *entropy_input = (uint8_t *)alloca(entropy_input_len * sizeof (uint8_t));
  memset(entropy_input, 0U, entropy_input_len * sizeof (uint8_t));
  bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len);
  if (!ok)
  {
    return false;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_len);
  uint8_t
  *seed_material =
    (uint8_t *)alloca((entropy_input_len + additional_input_len) * sizeof (uint8_t));
  memset(seed_material, 0U, (entropy_input_len + additional_input_len) * sizeof (uint8_t));
  memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
  memcpy(seed_material + entropy_input_len,
    additional_input,
    additional_input_len * sizeof (uint8_t));
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == SHA1_s)
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
  uint32_t input_len = 21U + entropy_input_len + additional_input_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
  memset(input0, 0U, input_len * sizeof (uint8_t));
  uint8_t *k_ = input0;
  memcpy(k_, v, 20U * sizeof (uint8_t));
  if (entropy_input_len + additional_input_len != 0U)
  {
    memcpy(input0 + 21U,
      seed_material,
      (entropy_input_len + additional_input_len) * sizeof (uint8_t));
  }
  input0[20U] = 0U;
  EverCrypt_HMAC_compute_sha1(k_, k, 20U, input0, input_len);
  EverCrypt_HMAC_compute_sha1(v, k_, 20U, v, 20U);
  memcpy(k, k_, 20U * sizeof (uint8_t));
  if (entropy_input_len + additional_input_len != 0U)
  {
    uint32_t input_len0 = 21U + entropy_input_len + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
    memset(input, 0U, input_len0 * sizeof (uint8_t));
    uint8_t *k_0 = input;
    memcpy(k_0, v, 20U * sizeof (uint8_t));
    if (entropy_input_len + additional_input_len != 0U)
    {
      memcpy(input + 21U,
        seed_material,
        (entropy_input_len + additional_input_len) * sizeof (uint8_t));
    }
    input[20U] = 1U;
    EverCrypt_HMAC_compute_sha1(k_0, k, 20U, input, input_len0);
    EverCrypt_HMAC_compute_sha1(v, k_0, 20U, v, 20U);
    memcpy(k, k_0, 20U * sizeof (uint8_t));
  }
  ctr[0U] = 1U;
  return true;
}

static bool
reseed_sha2_256(
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
  uint8_t *entropy_input = (uint8_t *)alloca(entropy_input_len * sizeof (uint8_t));
  memset(entropy_input, 0U, entropy_input_len * sizeof (uint8_t));
  bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len);
  if (!ok)
  {
    return false;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_len);
  uint8_t
  *seed_material =
    (uint8_t *)alloca((entropy_input_len + additional_input_len) * sizeof (uint8_t));
  memset(seed_material, 0U, (entropy_input_len + additional_input_len) * sizeof (uint8_t));
  memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
  memcpy(seed_material + entropy_input_len,
    additional_input,
    additional_input_len * sizeof (uint8_t));
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == SHA2_256_s)
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
  uint32_t input_len = 33U + entropy_input_len + additional_input_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
  memset(input0, 0U, input_len * sizeof (uint8_t));
  uint8_t *k_ = input0;
  memcpy(k_, v, 32U * sizeof (uint8_t));
  if (entropy_input_len + additional_input_len != 0U)
  {
    memcpy(input0 + 33U,
      seed_material,
      (entropy_input_len + additional_input_len) * sizeof (uint8_t));
  }
  input0[32U] = 0U;
  EverCrypt_HMAC_compute_sha2_256(k_, k, 32U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_256(v, k_, 32U, v, 32U);
  memcpy(k, k_, 32U * sizeof (uint8_t));
  if (entropy_input_len + additional_input_len != 0U)
  {
    uint32_t input_len0 = 33U + entropy_input_len + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
    memset(input, 0U, input_len0 * sizeof (uint8_t));
    uint8_t *k_0 = input;
    memcpy(k_0, v, 32U * sizeof (uint8_t));
    if (entropy_input_len + additional_input_len != 0U)
    {
      memcpy(input + 33U,
        seed_material,
        (entropy_input_len + additional_input_len) * sizeof (uint8_t));
    }
    input[32U] = 1U;
    EverCrypt_HMAC_compute_sha2_256(k_0, k, 32U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_256(v, k_0, 32U, v, 32U);
    memcpy(k, k_0, 32U * sizeof (uint8_t));
  }
  ctr[0U] = 1U;
  return true;
}

static bool
reseed_sha2_384(
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
  uint8_t *entropy_input = (uint8_t *)alloca(entropy_input_len * sizeof (uint8_t));
  memset(entropy_input, 0U, entropy_input_len * sizeof (uint8_t));
  bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len);
  if (!ok)
  {
    return false;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_len);
  uint8_t
  *seed_material =
    (uint8_t *)alloca((entropy_input_len + additional_input_len) * sizeof (uint8_t));
  memset(seed_material, 0U, (entropy_input_len + additional_input_len) * sizeof (uint8_t));
  memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
  memcpy(seed_material + entropy_input_len,
    additional_input,
    additional_input_len * sizeof (uint8_t));
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == SHA2_384_s)
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
  uint32_t input_len = 49U + entropy_input_len + additional_input_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
  memset(input0, 0U, input_len * sizeof (uint8_t));
  uint8_t *k_ = input0;
  memcpy(k_, v, 48U * sizeof (uint8_t));
  if (entropy_input_len + additional_input_len != 0U)
  {
    memcpy(input0 + 49U,
      seed_material,
      (entropy_input_len + additional_input_len) * sizeof (uint8_t));
  }
  input0[48U] = 0U;
  EverCrypt_HMAC_compute_sha2_384(k_, k, 48U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_384(v, k_, 48U, v, 48U);
  memcpy(k, k_, 48U * sizeof (uint8_t));
  if (entropy_input_len + additional_input_len != 0U)
  {
    uint32_t input_len0 = 49U + entropy_input_len + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
    memset(input, 0U, input_len0 * sizeof (uint8_t));
    uint8_t *k_0 = input;
    memcpy(k_0, v, 48U * sizeof (uint8_t));
    if (entropy_input_len + additional_input_len != 0U)
    {
      memcpy(input + 49U,
        seed_material,
        (entropy_input_len + additional_input_len) * sizeof (uint8_t));
    }
    input[48U] = 1U;
    EverCrypt_HMAC_compute_sha2_384(k_0, k, 48U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_384(v, k_0, 48U, v, 48U);
    memcpy(k, k_0, 48U * sizeof (uint8_t));
  }
  ctr[0U] = 1U;
  return true;
}

static bool
reseed_sha2_512(
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
  uint8_t *entropy_input = (uint8_t *)alloca(entropy_input_len * sizeof (uint8_t));
  memset(entropy_input, 0U, entropy_input_len * sizeof (uint8_t));
  bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len);
  if (!ok)
  {
    return false;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_len);
  uint8_t
  *seed_material =
    (uint8_t *)alloca((entropy_input_len + additional_input_len) * sizeof (uint8_t));
  memset(seed_material, 0U, (entropy_input_len + additional_input_len) * sizeof (uint8_t));
  memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
  memcpy(seed_material + entropy_input_len,
    additional_input,
    additional_input_len * sizeof (uint8_t));
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == SHA2_512_s)
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
  uint32_t input_len = 65U + entropy_input_len + additional_input_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
  memset(input0, 0U, input_len * sizeof (uint8_t));
  uint8_t *k_ = input0;
  memcpy(k_, v, 64U * sizeof (uint8_t));
  if (entropy_input_len + additional_input_len != 0U)
  {
    memcpy(input0 + 65U,
      seed_material,
      (entropy_input_len + additional_input_len) * sizeof (uint8_t));
  }
  input0[64U] = 0U;
  EverCrypt_HMAC_compute_sha2_512(k_, k, 64U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_512(v, k_, 64U, v, 64U);
  memcpy(k, k_, 64U * sizeof (uint8_t));
  if (entropy_input_len + additional_input_len != 0U)
  {
    uint32_t input_len0 = 65U + entropy_input_len + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
    memset(input, 0U, input_len0 * sizeof (uint8_t));
    uint8_t *k_0 = input;
    memcpy(k_0, v, 64U * sizeof (uint8_t));
    if (entropy_input_len + additional_input_len != 0U)
    {
      memcpy(input + 65U,
        seed_material,
        (entropy_input_len + additional_input_len) * sizeof (uint8_t));
    }
    input[64U] = 1U;
    EverCrypt_HMAC_compute_sha2_512(k_0, k, 64U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_512(v, k_0, 64U, v, 64U);
    memcpy(k, k_0, 64U * sizeof (uint8_t));
  }
  ctr[0U] = 1U;
  return true;
}

static bool
generate_sha1(
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
  bool ok0;
  if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
  {
    ok0 = false;
  }
  else
  {
    uint32_t entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA1);
    KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len);
    uint8_t *entropy_input = (uint8_t *)alloca(entropy_input_len * sizeof (uint8_t));
    memset(entropy_input, 0U, entropy_input_len * sizeof (uint8_t));
    bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len);
    bool result;
    if (!ok)
    {
      result = false;
    }
    else
    {
      EverCrypt_DRBG_state_s st_s = *st;
      KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_len);
      uint8_t
      *seed_material =
        (uint8_t *)alloca((entropy_input_len + additional_input_len) * sizeof (uint8_t));
      memset(seed_material, 0U, (entropy_input_len + additional_input_len) * sizeof (uint8_t));
      memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
      memcpy(seed_material + entropy_input_len,
        additional_input,
        additional_input_len * sizeof (uint8_t));
      Hacl_HMAC_DRBG_state scrut;
      if (st_s.tag == SHA1_s)
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
      uint32_t input_len = 21U + entropy_input_len + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
      memset(input0, 0U, input_len * sizeof (uint8_t));
      uint8_t *k_ = input0;
      memcpy(k_, v, 20U * sizeof (uint8_t));
      if (entropy_input_len + additional_input_len != 0U)
      {
        memcpy(input0 + 21U,
          seed_material,
          (entropy_input_len + additional_input_len) * sizeof (uint8_t));
      }
      input0[20U] = 0U;
      EverCrypt_HMAC_compute_sha1(k_, k, 20U, input0, input_len);
      EverCrypt_HMAC_compute_sha1(v, k_, 20U, v, 20U);
      memcpy(k, k_, 20U * sizeof (uint8_t));
      if (entropy_input_len + additional_input_len != 0U)
      {
        uint32_t input_len0 = 21U + entropy_input_len + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
        memset(input, 0U, input_len0 * sizeof (uint8_t));
        uint8_t *k_0 = input;
        memcpy(k_0, v, 20U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_len != 0U)
        {
          memcpy(input + 21U,
            seed_material,
            (entropy_input_len + additional_input_len) * sizeof (uint8_t));
        }
        input[20U] = 1U;
        EverCrypt_HMAC_compute_sha1(k_0, k, 20U, input, input_len0);
        EverCrypt_HMAC_compute_sha1(v, k_0, 20U, v, 20U);
        memcpy(k, k_0, 20U * sizeof (uint8_t));
      }
      ctr[0U] = 1U;
      result = true;
    }
    ok0 = result;
  }
  if (!ok0)
  {
    return false;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  Hacl_HMAC_DRBG_state ite;
  if (st_s.tag == SHA1_s)
  {
    ite = st_s.case_SHA1_s;
  }
  else
  {
    ite = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  if (ite.reseed_counter[0U] > Hacl_HMAC_DRBG_reseed_interval)
  {
    return false;
  }
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == SHA1_s)
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
  if (additional_input_len > 0U)
  {
    uint32_t input_len = 21U + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
    uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
    memset(input0, 0U, input_len * sizeof (uint8_t));
    uint8_t *k_ = input0;
    memcpy(k_, v, 20U * sizeof (uint8_t));
    if (additional_input_len != 0U)
    {
      memcpy(input0 + 21U, additional_input, additional_input_len * sizeof (uint8_t));
    }
    input0[20U] = 0U;
    EverCrypt_HMAC_compute_sha1(k_, k, 20U, input0, input_len);
    EverCrypt_HMAC_compute_sha1(v, k_, 20U, v, 20U);
    memcpy(k, k_, 20U * sizeof (uint8_t));
    if (additional_input_len != 0U)
    {
      uint32_t input_len0 = 21U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
      uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
      memset(input, 0U, input_len0 * sizeof (uint8_t));
      uint8_t *k_0 = input;
      memcpy(k_0, v, 20U * sizeof (uint8_t));
      if (additional_input_len != 0U)
      {
        memcpy(input + 21U, additional_input, additional_input_len * sizeof (uint8_t));
      }
      input[20U] = 1U;
      EverCrypt_HMAC_compute_sha1(k_0, k, 20U, input, input_len0);
      EverCrypt_HMAC_compute_sha1(v, k_0, 20U, v, 20U);
      memcpy(k, k_0, 20U * sizeof (uint8_t));
    }
  }
  uint8_t *output1 = output;
  uint32_t max = n / 20U;
  uint8_t *out = output1;
  for (uint32_t i = 0U; i < max; i++)
  {
    EverCrypt_HMAC_compute_sha1(v, k, 20U, v, 20U);
    memcpy(out + i * 20U, v, 20U * sizeof (uint8_t));
  }
  if (max * 20U < n)
  {
    uint8_t *block = output1 + max * 20U;
    EverCrypt_HMAC_compute_sha1(v, k, 20U, v, 20U);
    memcpy(block, v, (n - max * 20U) * sizeof (uint8_t));
  }
  uint32_t input_len = 21U + additional_input_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
  memset(input0, 0U, input_len * sizeof (uint8_t));
  uint8_t *k_ = input0;
  memcpy(k_, v, 20U * sizeof (uint8_t));
  if (additional_input_len != 0U)
  {
    memcpy(input0 + 21U, additional_input, additional_input_len * sizeof (uint8_t));
  }
  input0[20U] = 0U;
  EverCrypt_HMAC_compute_sha1(k_, k, 20U, input0, input_len);
  EverCrypt_HMAC_compute_sha1(v, k_, 20U, v, 20U);
  memcpy(k, k_, 20U * sizeof (uint8_t));
  if (additional_input_len != 0U)
  {
    uint32_t input_len0 = 21U + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
    memset(input, 0U, input_len0 * sizeof (uint8_t));
    uint8_t *k_0 = input;
    memcpy(k_0, v, 20U * sizeof (uint8_t));
    if (additional_input_len != 0U)
    {
      memcpy(input + 21U, additional_input, additional_input_len * sizeof (uint8_t));
    }
    input[20U] = 1U;
    EverCrypt_HMAC_compute_sha1(k_0, k, 20U, input, input_len0);
    EverCrypt_HMAC_compute_sha1(v, k_0, 20U, v, 20U);
    memcpy(k, k_0, 20U * sizeof (uint8_t));
  }
  uint32_t old_ctr = ctr[0U];
  ctr[0U] = old_ctr + 1U;
  return true;
}

static bool
generate_sha2_256(
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
  bool ok0;
  if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
  {
    ok0 = false;
  }
  else
  {
    uint32_t entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_256);
    KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len);
    uint8_t *entropy_input = (uint8_t *)alloca(entropy_input_len * sizeof (uint8_t));
    memset(entropy_input, 0U, entropy_input_len * sizeof (uint8_t));
    bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len);
    bool result;
    if (!ok)
    {
      result = false;
    }
    else
    {
      EverCrypt_DRBG_state_s st_s = *st;
      KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_len);
      uint8_t
      *seed_material =
        (uint8_t *)alloca((entropy_input_len + additional_input_len) * sizeof (uint8_t));
      memset(seed_material, 0U, (entropy_input_len + additional_input_len) * sizeof (uint8_t));
      memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
      memcpy(seed_material + entropy_input_len,
        additional_input,
        additional_input_len * sizeof (uint8_t));
      Hacl_HMAC_DRBG_state scrut;
      if (st_s.tag == SHA2_256_s)
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
      uint32_t input_len = 33U + entropy_input_len + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
      memset(input0, 0U, input_len * sizeof (uint8_t));
      uint8_t *k_ = input0;
      memcpy(k_, v, 32U * sizeof (uint8_t));
      if (entropy_input_len + additional_input_len != 0U)
      {
        memcpy(input0 + 33U,
          seed_material,
          (entropy_input_len + additional_input_len) * sizeof (uint8_t));
      }
      input0[32U] = 0U;
      EverCrypt_HMAC_compute_sha2_256(k_, k, 32U, input0, input_len);
      EverCrypt_HMAC_compute_sha2_256(v, k_, 32U, v, 32U);
      memcpy(k, k_, 32U * sizeof (uint8_t));
      if (entropy_input_len + additional_input_len != 0U)
      {
        uint32_t input_len0 = 33U + entropy_input_len + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
        memset(input, 0U, input_len0 * sizeof (uint8_t));
        uint8_t *k_0 = input;
        memcpy(k_0, v, 32U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_len != 0U)
        {
          memcpy(input + 33U,
            seed_material,
            (entropy_input_len + additional_input_len) * sizeof (uint8_t));
        }
        input[32U] = 1U;
        EverCrypt_HMAC_compute_sha2_256(k_0, k, 32U, input, input_len0);
        EverCrypt_HMAC_compute_sha2_256(v, k_0, 32U, v, 32U);
        memcpy(k, k_0, 32U * sizeof (uint8_t));
      }
      ctr[0U] = 1U;
      result = true;
    }
    ok0 = result;
  }
  if (!ok0)
  {
    return false;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  Hacl_HMAC_DRBG_state ite;
  if (st_s.tag == SHA2_256_s)
  {
    ite = st_s.case_SHA2_256_s;
  }
  else
  {
    ite = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  if (ite.reseed_counter[0U] > Hacl_HMAC_DRBG_reseed_interval)
  {
    return false;
  }
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == SHA2_256_s)
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
  if (additional_input_len > 0U)
  {
    uint32_t input_len = 33U + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
    uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
    memset(input0, 0U, input_len * sizeof (uint8_t));
    uint8_t *k_ = input0;
    memcpy(k_, v, 32U * sizeof (uint8_t));
    if (additional_input_len != 0U)
    {
      memcpy(input0 + 33U, additional_input, additional_input_len * sizeof (uint8_t));
    }
    input0[32U] = 0U;
    EverCrypt_HMAC_compute_sha2_256(k_, k, 32U, input0, input_len);
    EverCrypt_HMAC_compute_sha2_256(v, k_, 32U, v, 32U);
    memcpy(k, k_, 32U * sizeof (uint8_t));
    if (additional_input_len != 0U)
    {
      uint32_t input_len0 = 33U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
      uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
      memset(input, 0U, input_len0 * sizeof (uint8_t));
      uint8_t *k_0 = input;
      memcpy(k_0, v, 32U * sizeof (uint8_t));
      if (additional_input_len != 0U)
      {
        memcpy(input + 33U, additional_input, additional_input_len * sizeof (uint8_t));
      }
      input[32U] = 1U;
      EverCrypt_HMAC_compute_sha2_256(k_0, k, 32U, input, input_len0);
      EverCrypt_HMAC_compute_sha2_256(v, k_0, 32U, v, 32U);
      memcpy(k, k_0, 32U * sizeof (uint8_t));
    }
  }
  uint8_t *output1 = output;
  uint32_t max = n / 32U;
  uint8_t *out = output1;
  for (uint32_t i = 0U; i < max; i++)
  {
    EverCrypt_HMAC_compute_sha2_256(v, k, 32U, v, 32U);
    memcpy(out + i * 32U, v, 32U * sizeof (uint8_t));
  }
  if (max * 32U < n)
  {
    uint8_t *block = output1 + max * 32U;
    EverCrypt_HMAC_compute_sha2_256(v, k, 32U, v, 32U);
    memcpy(block, v, (n - max * 32U) * sizeof (uint8_t));
  }
  uint32_t input_len = 33U + additional_input_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
  memset(input0, 0U, input_len * sizeof (uint8_t));
  uint8_t *k_ = input0;
  memcpy(k_, v, 32U * sizeof (uint8_t));
  if (additional_input_len != 0U)
  {
    memcpy(input0 + 33U, additional_input, additional_input_len * sizeof (uint8_t));
  }
  input0[32U] = 0U;
  EverCrypt_HMAC_compute_sha2_256(k_, k, 32U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_256(v, k_, 32U, v, 32U);
  memcpy(k, k_, 32U * sizeof (uint8_t));
  if (additional_input_len != 0U)
  {
    uint32_t input_len0 = 33U + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
    memset(input, 0U, input_len0 * sizeof (uint8_t));
    uint8_t *k_0 = input;
    memcpy(k_0, v, 32U * sizeof (uint8_t));
    if (additional_input_len != 0U)
    {
      memcpy(input + 33U, additional_input, additional_input_len * sizeof (uint8_t));
    }
    input[32U] = 1U;
    EverCrypt_HMAC_compute_sha2_256(k_0, k, 32U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_256(v, k_0, 32U, v, 32U);
    memcpy(k, k_0, 32U * sizeof (uint8_t));
  }
  uint32_t old_ctr = ctr[0U];
  ctr[0U] = old_ctr + 1U;
  return true;
}

static bool
generate_sha2_384(
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
  bool ok0;
  if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
  {
    ok0 = false;
  }
  else
  {
    uint32_t entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_384);
    KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len);
    uint8_t *entropy_input = (uint8_t *)alloca(entropy_input_len * sizeof (uint8_t));
    memset(entropy_input, 0U, entropy_input_len * sizeof (uint8_t));
    bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len);
    bool result;
    if (!ok)
    {
      result = false;
    }
    else
    {
      EverCrypt_DRBG_state_s st_s = *st;
      KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_len);
      uint8_t
      *seed_material =
        (uint8_t *)alloca((entropy_input_len + additional_input_len) * sizeof (uint8_t));
      memset(seed_material, 0U, (entropy_input_len + additional_input_len) * sizeof (uint8_t));
      memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
      memcpy(seed_material + entropy_input_len,
        additional_input,
        additional_input_len * sizeof (uint8_t));
      Hacl_HMAC_DRBG_state scrut;
      if (st_s.tag == SHA2_384_s)
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
      uint32_t input_len = 49U + entropy_input_len + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
      memset(input0, 0U, input_len * sizeof (uint8_t));
      uint8_t *k_ = input0;
      memcpy(k_, v, 48U * sizeof (uint8_t));
      if (entropy_input_len + additional_input_len != 0U)
      {
        memcpy(input0 + 49U,
          seed_material,
          (entropy_input_len + additional_input_len) * sizeof (uint8_t));
      }
      input0[48U] = 0U;
      EverCrypt_HMAC_compute_sha2_384(k_, k, 48U, input0, input_len);
      EverCrypt_HMAC_compute_sha2_384(v, k_, 48U, v, 48U);
      memcpy(k, k_, 48U * sizeof (uint8_t));
      if (entropy_input_len + additional_input_len != 0U)
      {
        uint32_t input_len0 = 49U + entropy_input_len + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
        memset(input, 0U, input_len0 * sizeof (uint8_t));
        uint8_t *k_0 = input;
        memcpy(k_0, v, 48U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_len != 0U)
        {
          memcpy(input + 49U,
            seed_material,
            (entropy_input_len + additional_input_len) * sizeof (uint8_t));
        }
        input[48U] = 1U;
        EverCrypt_HMAC_compute_sha2_384(k_0, k, 48U, input, input_len0);
        EverCrypt_HMAC_compute_sha2_384(v, k_0, 48U, v, 48U);
        memcpy(k, k_0, 48U * sizeof (uint8_t));
      }
      ctr[0U] = 1U;
      result = true;
    }
    ok0 = result;
  }
  if (!ok0)
  {
    return false;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  Hacl_HMAC_DRBG_state ite;
  if (st_s.tag == SHA2_384_s)
  {
    ite = st_s.case_SHA2_384_s;
  }
  else
  {
    ite = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  if (ite.reseed_counter[0U] > Hacl_HMAC_DRBG_reseed_interval)
  {
    return false;
  }
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == SHA2_384_s)
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
  if (additional_input_len > 0U)
  {
    uint32_t input_len = 49U + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
    uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
    memset(input0, 0U, input_len * sizeof (uint8_t));
    uint8_t *k_ = input0;
    memcpy(k_, v, 48U * sizeof (uint8_t));
    if (additional_input_len != 0U)
    {
      memcpy(input0 + 49U, additional_input, additional_input_len * sizeof (uint8_t));
    }
    input0[48U] = 0U;
    EverCrypt_HMAC_compute_sha2_384(k_, k, 48U, input0, input_len);
    EverCrypt_HMAC_compute_sha2_384(v, k_, 48U, v, 48U);
    memcpy(k, k_, 48U * sizeof (uint8_t));
    if (additional_input_len != 0U)
    {
      uint32_t input_len0 = 49U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
      uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
      memset(input, 0U, input_len0 * sizeof (uint8_t));
      uint8_t *k_0 = input;
      memcpy(k_0, v, 48U * sizeof (uint8_t));
      if (additional_input_len != 0U)
      {
        memcpy(input + 49U, additional_input, additional_input_len * sizeof (uint8_t));
      }
      input[48U] = 1U;
      EverCrypt_HMAC_compute_sha2_384(k_0, k, 48U, input, input_len0);
      EverCrypt_HMAC_compute_sha2_384(v, k_0, 48U, v, 48U);
      memcpy(k, k_0, 48U * sizeof (uint8_t));
    }
  }
  uint8_t *output1 = output;
  uint32_t max = n / 48U;
  uint8_t *out = output1;
  for (uint32_t i = 0U; i < max; i++)
  {
    EverCrypt_HMAC_compute_sha2_384(v, k, 48U, v, 48U);
    memcpy(out + i * 48U, v, 48U * sizeof (uint8_t));
  }
  if (max * 48U < n)
  {
    uint8_t *block = output1 + max * 48U;
    EverCrypt_HMAC_compute_sha2_384(v, k, 48U, v, 48U);
    memcpy(block, v, (n - max * 48U) * sizeof (uint8_t));
  }
  uint32_t input_len = 49U + additional_input_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
  memset(input0, 0U, input_len * sizeof (uint8_t));
  uint8_t *k_ = input0;
  memcpy(k_, v, 48U * sizeof (uint8_t));
  if (additional_input_len != 0U)
  {
    memcpy(input0 + 49U, additional_input, additional_input_len * sizeof (uint8_t));
  }
  input0[48U] = 0U;
  EverCrypt_HMAC_compute_sha2_384(k_, k, 48U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_384(v, k_, 48U, v, 48U);
  memcpy(k, k_, 48U * sizeof (uint8_t));
  if (additional_input_len != 0U)
  {
    uint32_t input_len0 = 49U + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
    memset(input, 0U, input_len0 * sizeof (uint8_t));
    uint8_t *k_0 = input;
    memcpy(k_0, v, 48U * sizeof (uint8_t));
    if (additional_input_len != 0U)
    {
      memcpy(input + 49U, additional_input, additional_input_len * sizeof (uint8_t));
    }
    input[48U] = 1U;
    EverCrypt_HMAC_compute_sha2_384(k_0, k, 48U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_384(v, k_0, 48U, v, 48U);
    memcpy(k, k_0, 48U * sizeof (uint8_t));
  }
  uint32_t old_ctr = ctr[0U];
  ctr[0U] = old_ctr + 1U;
  return true;
}

static bool
generate_sha2_512(
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
  bool ok0;
  if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
  {
    ok0 = false;
  }
  else
  {
    uint32_t entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_512);
    KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len);
    uint8_t *entropy_input = (uint8_t *)alloca(entropy_input_len * sizeof (uint8_t));
    memset(entropy_input, 0U, entropy_input_len * sizeof (uint8_t));
    bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len);
    bool result;
    if (!ok)
    {
      result = false;
    }
    else
    {
      EverCrypt_DRBG_state_s st_s = *st;
      KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_len);
      uint8_t
      *seed_material =
        (uint8_t *)alloca((entropy_input_len + additional_input_len) * sizeof (uint8_t));
      memset(seed_material, 0U, (entropy_input_len + additional_input_len) * sizeof (uint8_t));
      memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
      memcpy(seed_material + entropy_input_len,
        additional_input,
        additional_input_len * sizeof (uint8_t));
      Hacl_HMAC_DRBG_state scrut;
      if (st_s.tag == SHA2_512_s)
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
      uint32_t input_len = 65U + entropy_input_len + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
      uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
      memset(input0, 0U, input_len * sizeof (uint8_t));
      uint8_t *k_ = input0;
      memcpy(k_, v, 64U * sizeof (uint8_t));
      if (entropy_input_len + additional_input_len != 0U)
      {
        memcpy(input0 + 65U,
          seed_material,
          (entropy_input_len + additional_input_len) * sizeof (uint8_t));
      }
      input0[64U] = 0U;
      EverCrypt_HMAC_compute_sha2_512(k_, k, 64U, input0, input_len);
      EverCrypt_HMAC_compute_sha2_512(v, k_, 64U, v, 64U);
      memcpy(k, k_, 64U * sizeof (uint8_t));
      if (entropy_input_len + additional_input_len != 0U)
      {
        uint32_t input_len0 = 65U + entropy_input_len + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
        uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
        memset(input, 0U, input_len0 * sizeof (uint8_t));
        uint8_t *k_0 = input;
        memcpy(k_0, v, 64U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_len != 0U)
        {
          memcpy(input + 65U,
            seed_material,
            (entropy_input_len + additional_input_len) * sizeof (uint8_t));
        }
        input[64U] = 1U;
        EverCrypt_HMAC_compute_sha2_512(k_0, k, 64U, input, input_len0);
        EverCrypt_HMAC_compute_sha2_512(v, k_0, 64U, v, 64U);
        memcpy(k, k_0, 64U * sizeof (uint8_t));
      }
      ctr[0U] = 1U;
      result = true;
    }
    ok0 = result;
  }
  if (!ok0)
  {
    return false;
  }
  EverCrypt_DRBG_state_s st_s = *st;
  Hacl_HMAC_DRBG_state ite;
  if (st_s.tag == SHA2_512_s)
  {
    ite = st_s.case_SHA2_512_s;
  }
  else
  {
    ite = KRML_EABORT(Hacl_HMAC_DRBG_state, "unreachable (pattern matches are exhaustive in F*)");
  }
  if (ite.reseed_counter[0U] > Hacl_HMAC_DRBG_reseed_interval)
  {
    return false;
  }
  Hacl_HMAC_DRBG_state scrut;
  if (st_s.tag == SHA2_512_s)
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
  if (additional_input_len > 0U)
  {
    uint32_t input_len = 65U + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
    uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
    memset(input0, 0U, input_len * sizeof (uint8_t));
    uint8_t *k_ = input0;
    memcpy(k_, v, 64U * sizeof (uint8_t));
    if (additional_input_len != 0U)
    {
      memcpy(input0 + 65U, additional_input, additional_input_len * sizeof (uint8_t));
    }
    input0[64U] = 0U;
    EverCrypt_HMAC_compute_sha2_512(k_, k, 64U, input0, input_len);
    EverCrypt_HMAC_compute_sha2_512(v, k_, 64U, v, 64U);
    memcpy(k, k_, 64U * sizeof (uint8_t));
    if (additional_input_len != 0U)
    {
      uint32_t input_len0 = 65U + additional_input_len;
      KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
      uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
      memset(input, 0U, input_len0 * sizeof (uint8_t));
      uint8_t *k_0 = input;
      memcpy(k_0, v, 64U * sizeof (uint8_t));
      if (additional_input_len != 0U)
      {
        memcpy(input + 65U, additional_input, additional_input_len * sizeof (uint8_t));
      }
      input[64U] = 1U;
      EverCrypt_HMAC_compute_sha2_512(k_0, k, 64U, input, input_len0);
      EverCrypt_HMAC_compute_sha2_512(v, k_0, 64U, v, 64U);
      memcpy(k, k_0, 64U * sizeof (uint8_t));
    }
  }
  uint8_t *output1 = output;
  uint32_t max = n / 64U;
  uint8_t *out = output1;
  for (uint32_t i = 0U; i < max; i++)
  {
    EverCrypt_HMAC_compute_sha2_512(v, k, 64U, v, 64U);
    memcpy(out + i * 64U, v, 64U * sizeof (uint8_t));
  }
  if (max * 64U < n)
  {
    uint8_t *block = output1 + max * 64U;
    EverCrypt_HMAC_compute_sha2_512(v, k, 64U, v, 64U);
    memcpy(block, v, (n - max * 64U) * sizeof (uint8_t));
  }
  uint32_t input_len = 65U + additional_input_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
  uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
  memset(input0, 0U, input_len * sizeof (uint8_t));
  uint8_t *k_ = input0;
  memcpy(k_, v, 64U * sizeof (uint8_t));
  if (additional_input_len != 0U)
  {
    memcpy(input0 + 65U, additional_input, additional_input_len * sizeof (uint8_t));
  }
  input0[64U] = 0U;
  EverCrypt_HMAC_compute_sha2_512(k_, k, 64U, input0, input_len);
  EverCrypt_HMAC_compute_sha2_512(v, k_, 64U, v, 64U);
  memcpy(k, k_, 64U * sizeof (uint8_t));
  if (additional_input_len != 0U)
  {
    uint32_t input_len0 = 65U + additional_input_len;
    KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
    uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
    memset(input, 0U, input_len0 * sizeof (uint8_t));
    uint8_t *k_0 = input;
    memcpy(k_0, v, 64U * sizeof (uint8_t));
    if (additional_input_len != 0U)
    {
      memcpy(input + 65U, additional_input, additional_input_len * sizeof (uint8_t));
    }
    input[64U] = 1U;
    EverCrypt_HMAC_compute_sha2_512(k_0, k, 64U, input, input_len0);
    EverCrypt_HMAC_compute_sha2_512(v, k_0, 64U, v, 64U);
    memcpy(k, k_0, 64U * sizeof (uint8_t));
  }
  uint32_t old_ctr = ctr[0U];
  ctr[0U] = old_ctr + 1U;
  return true;
}

static void uninstantiate_sha1(EverCrypt_DRBG_state_s *st)
{
  EverCrypt_DRBG_state_s st_s = *st;
  Hacl_HMAC_DRBG_state s;
  if (st_s.tag == SHA1_s)
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
  Lib_Memzero0_memzero(k, 20U, uint8_t, void *);
  Lib_Memzero0_memzero(v, 20U, uint8_t, void *);
  ctr[0U] = 0U;
  KRML_HOST_FREE(k);
  KRML_HOST_FREE(v);
  KRML_HOST_FREE(ctr);
  KRML_HOST_FREE(st);
}

static void uninstantiate_sha2_256(EverCrypt_DRBG_state_s *st)
{
  EverCrypt_DRBG_state_s st_s = *st;
  Hacl_HMAC_DRBG_state s;
  if (st_s.tag == SHA2_256_s)
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
  Lib_Memzero0_memzero(k, 32U, uint8_t, void *);
  Lib_Memzero0_memzero(v, 32U, uint8_t, void *);
  ctr[0U] = 0U;
  KRML_HOST_FREE(k);
  KRML_HOST_FREE(v);
  KRML_HOST_FREE(ctr);
  KRML_HOST_FREE(st);
}

static void uninstantiate_sha2_384(EverCrypt_DRBG_state_s *st)
{
  EverCrypt_DRBG_state_s st_s = *st;
  Hacl_HMAC_DRBG_state s;
  if (st_s.tag == SHA2_384_s)
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
  Lib_Memzero0_memzero(k, 48U, uint8_t, void *);
  Lib_Memzero0_memzero(v, 48U, uint8_t, void *);
  ctr[0U] = 0U;
  KRML_HOST_FREE(k);
  KRML_HOST_FREE(v);
  KRML_HOST_FREE(ctr);
  KRML_HOST_FREE(st);
}

static void uninstantiate_sha2_512(EverCrypt_DRBG_state_s *st)
{
  EverCrypt_DRBG_state_s st_s = *st;
  Hacl_HMAC_DRBG_state s;
  if (st_s.tag == SHA2_512_s)
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
  Lib_Memzero0_memzero(k, 64U, uint8_t, void *);
  Lib_Memzero0_memzero(v, 64U, uint8_t, void *);
  ctr[0U] = 0U;
  KRML_HOST_FREE(k);
  KRML_HOST_FREE(v);
  KRML_HOST_FREE(ctr);
  KRML_HOST_FREE(st);
}

/**
Instantiate the DRBG.

@param st Pointer to DRBG state.
@param personalization_string Pointer to `personalization_string_len` bytes of memory where personalization string is read from.
@param personalization_string_len Length of personalization string.

@return True if and only if instantiation was successful.
*/
bool
EverCrypt_DRBG_instantiate(
  EverCrypt_DRBG_state_s *st,
  uint8_t *personalization_string,
  uint32_t personalization_string_len
)
{
  EverCrypt_DRBG_state_s scrut = *st;
  if (scrut.tag == SHA1_s)
  {
    return instantiate_sha1(st, personalization_string, personalization_string_len);
  }
  if (scrut.tag == SHA2_256_s)
  {
    return instantiate_sha2_256(st, personalization_string, personalization_string_len);
  }
  if (scrut.tag == SHA2_384_s)
  {
    return instantiate_sha2_384(st, personalization_string, personalization_string_len);
  }
  if (scrut.tag == SHA2_512_s)
  {
    return instantiate_sha2_512(st, personalization_string, personalization_string_len);
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

/**
Reseed the DRBG.

@param st Pointer to DRBG state.
@param additional_input_input Pointer to `additional_input_input_len` bytes of memory where additional input is read from.
@param additional_input_input_len Length of additional input.

@return True if and only if reseed was successful.
*/
bool
EverCrypt_DRBG_reseed(
  EverCrypt_DRBG_state_s *st,
  uint8_t *additional_input,
  uint32_t additional_input_len
)
{
  EverCrypt_DRBG_state_s scrut = *st;
  if (scrut.tag == SHA1_s)
  {
    return reseed_sha1(st, additional_input, additional_input_len);
  }
  if (scrut.tag == SHA2_256_s)
  {
    return reseed_sha2_256(st, additional_input, additional_input_len);
  }
  if (scrut.tag == SHA2_384_s)
  {
    return reseed_sha2_384(st, additional_input, additional_input_len);
  }
  if (scrut.tag == SHA2_512_s)
  {
    return reseed_sha2_512(st, additional_input, additional_input_len);
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

/**
Generate output.

@param output Pointer to `n` bytes of memory where random output is written to.
@param st Pointer to DRBG state.
@param n Length of desired output.
@param additional_input_input Pointer to `additional_input_input_len` bytes of memory where additional input is read from.
@param additional_input_input_len Length of additional input.

@return True if and only if generate was successful.
*/
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
  if (scrut.tag == SHA1_s)
  {
    return generate_sha1(output, st, n, additional_input, additional_input_len);
  }
  if (scrut.tag == SHA2_256_s)
  {
    return generate_sha2_256(output, st, n, additional_input, additional_input_len);
  }
  if (scrut.tag == SHA2_384_s)
  {
    return generate_sha2_384(output, st, n, additional_input, additional_input_len);
  }
  if (scrut.tag == SHA2_512_s)
  {
    return generate_sha2_512(output, st, n, additional_input, additional_input_len);
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

/**
Uninstantiate and free the DRBG.

@param st Pointer to DRBG state.
*/
void EverCrypt_DRBG_uninstantiate(EverCrypt_DRBG_state_s *st)
{
  EverCrypt_DRBG_state_s scrut = *st;
  if (scrut.tag == SHA1_s)
  {
    uninstantiate_sha1(st);
    return;
  }
  if (scrut.tag == SHA2_256_s)
  {
    uninstantiate_sha2_256(st);
    return;
  }
  if (scrut.tag == SHA2_384_s)
  {
    uninstantiate_sha2_384(st);
    return;
  }
  if (scrut.tag == SHA2_512_s)
  {
    uninstantiate_sha2_512(st);
    return;
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

