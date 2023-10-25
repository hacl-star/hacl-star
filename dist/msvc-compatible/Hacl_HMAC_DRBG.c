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


#include "Hacl_HMAC_DRBG.h"

uint32_t Hacl_HMAC_DRBG_reseed_interval = 1024U;

uint32_t Hacl_HMAC_DRBG_max_output_length = 65536U;

uint32_t Hacl_HMAC_DRBG_max_length = 65536U;

uint32_t Hacl_HMAC_DRBG_max_personalization_string_length = 65536U;

uint32_t Hacl_HMAC_DRBG_max_additional_input_length = 65536U;

/**
Return the minimal entropy input length of the desired hash function.

@param a Hash algorithm to use.
*/
uint32_t Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_hash_alg a)
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

bool
Hacl_HMAC_DRBG_uu___is_State(Spec_Hash_Definitions_hash_alg a, Hacl_HMAC_DRBG_state projectee)
{
  KRML_MAYBE_UNUSED_VAR(a);
  KRML_MAYBE_UNUSED_VAR(projectee);
  return true;
}

/**
Create a DRBG state.

@param a Hash algorithm to use. The possible instantiations are ...
  * `Spec_Hash_Definitions_SHA2_256`,
  * `Spec_Hash_Definitions_SHA2_384`,
  * `Spec_Hash_Definitions_SHA2_512`, and
  * `Spec_Hash_Definitions_SHA1`.
*/
Hacl_HMAC_DRBG_state Hacl_HMAC_DRBG_create_in(Spec_Hash_Definitions_hash_alg a)
{
  uint8_t *k;
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        uint8_t *buf = (uint8_t *)KRML_HOST_CALLOC(20U, sizeof (uint8_t));
        k = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        uint8_t *buf = (uint8_t *)KRML_HOST_CALLOC(32U, sizeof (uint8_t));
        k = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        uint8_t *buf = (uint8_t *)KRML_HOST_CALLOC(48U, sizeof (uint8_t));
        k = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        uint8_t *buf = (uint8_t *)KRML_HOST_CALLOC(64U, sizeof (uint8_t));
        k = buf;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint8_t *v;
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        uint8_t *buf = (uint8_t *)KRML_HOST_CALLOC(20U, sizeof (uint8_t));
        v = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        uint8_t *buf = (uint8_t *)KRML_HOST_CALLOC(32U, sizeof (uint8_t));
        v = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        uint8_t *buf = (uint8_t *)KRML_HOST_CALLOC(48U, sizeof (uint8_t));
        v = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        uint8_t *buf = (uint8_t *)KRML_HOST_CALLOC(64U, sizeof (uint8_t));
        v = buf;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t *ctr = (uint32_t *)KRML_HOST_MALLOC(sizeof (uint32_t));
  ctr[0U] = 1U;
  return ((Hacl_HMAC_DRBG_state){ .k = k, .v = v, .reseed_counter = ctr });
}

/**
Instantiate the DRBG.

@param a Hash algorithm to use. (Value must match the value used in `Hacl_HMAC_DRBG_create_in`.)
@param st Pointer to DRBG state.
@param entropy_input_len Length of entropy input.
@param entropy_input Pointer to `entropy_input_len` bytes of memory where entropy input is read from.
@param nonce_len Length of nonce.
@param nonce Pointer to `nonce_len` bytes of memory where nonce is read from.
@param personalization_string_len length of personalization string.
@param personalization_string Pointer to `personalization_string_len` bytes of memory where personalization string is read from.
*/
void
Hacl_HMAC_DRBG_instantiate(
  Spec_Hash_Definitions_hash_alg a,
  Hacl_HMAC_DRBG_state st,
  uint32_t entropy_input_len,
  uint8_t *entropy_input,
  uint32_t nonce_len,
  uint8_t *nonce,
  uint32_t personalization_string_len,
  uint8_t *personalization_string
)
{
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t),
          entropy_input_len + nonce_len + personalization_string_len);
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
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
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
        Hacl_HMAC_compute_sha1(k_, k, 20U, input0, input_len);
        Hacl_HMAC_compute_sha1(v, k_, 20U, v, 20U);
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
          Hacl_HMAC_compute_sha1(k_0, k, 20U, input, input_len0);
          Hacl_HMAC_compute_sha1(v, k_0, 20U, v, 20U);
          memcpy(k, k_0, 20U * sizeof (uint8_t));
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t),
          entropy_input_len + nonce_len + personalization_string_len);
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
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
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
        Hacl_HMAC_compute_sha2_256(k_, k, 32U, input0, input_len);
        Hacl_HMAC_compute_sha2_256(v, k_, 32U, v, 32U);
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
          Hacl_HMAC_compute_sha2_256(k_0, k, 32U, input, input_len0);
          Hacl_HMAC_compute_sha2_256(v, k_0, 32U, v, 32U);
          memcpy(k, k_0, 32U * sizeof (uint8_t));
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t),
          entropy_input_len + nonce_len + personalization_string_len);
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
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
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
        Hacl_HMAC_compute_sha2_384(k_, k, 48U, input0, input_len);
        Hacl_HMAC_compute_sha2_384(v, k_, 48U, v, 48U);
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
          Hacl_HMAC_compute_sha2_384(k_0, k, 48U, input, input_len0);
          Hacl_HMAC_compute_sha2_384(v, k_0, 48U, v, 48U);
          memcpy(k, k_0, 48U * sizeof (uint8_t));
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t),
          entropy_input_len + nonce_len + personalization_string_len);
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
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
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
        Hacl_HMAC_compute_sha2_512(k_, k, 64U, input0, input_len);
        Hacl_HMAC_compute_sha2_512(v, k_, 64U, v, 64U);
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
          Hacl_HMAC_compute_sha2_512(k_0, k, 64U, input, input_len0);
          Hacl_HMAC_compute_sha2_512(v, k_0, 64U, v, 64U);
          memcpy(k, k_0, 64U * sizeof (uint8_t));
        }
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

/**
Reseed the DRBG.

@param a Hash algorithm to use. (Value must match the value used in `Hacl_HMAC_DRBG_create_in`.)
@param st Pointer to DRBG state.
@param entropy_input_len Length of entropy input.
@param entropy_input Pointer to `entropy_input_len` bytes of memory where entropy input is read from.
@param additional_input_input_len Length of additional input.
@param additional_input_input Pointer to `additional_input_input_len` bytes of memory where additional input is read from.
*/
void
Hacl_HMAC_DRBG_reseed(
  Spec_Hash_Definitions_hash_alg a,
  Hacl_HMAC_DRBG_state st,
  uint32_t entropy_input_len,
  uint8_t *entropy_input,
  uint32_t additional_input_input_len,
  uint8_t *additional_input_input
)
{
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_input_len);
        uint8_t
        *seed_material =
          (uint8_t *)alloca((entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        memset(seed_material,
          0U,
          (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
        memcpy(seed_material + entropy_input_len,
          additional_input_input,
          additional_input_input_len * sizeof (uint8_t));
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
        uint32_t input_len = 21U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, 20U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != 0U)
        {
          memcpy(input0 + 21U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        }
        input0[20U] = 0U;
        Hacl_HMAC_compute_sha1(k_, k, 20U, input0, input_len);
        Hacl_HMAC_compute_sha1(v, k_, 20U, v, 20U);
        memcpy(k, k_, 20U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != 0U)
        {
          uint32_t input_len0 = 21U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, 20U * sizeof (uint8_t));
          if (entropy_input_len + additional_input_input_len != 0U)
          {
            memcpy(input + 21U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
          }
          input[20U] = 1U;
          Hacl_HMAC_compute_sha1(k_0, k, 20U, input, input_len0);
          Hacl_HMAC_compute_sha1(v, k_0, 20U, v, 20U);
          memcpy(k, k_0, 20U * sizeof (uint8_t));
        }
        ctr[0U] = 1U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_input_len);
        uint8_t
        *seed_material =
          (uint8_t *)alloca((entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        memset(seed_material,
          0U,
          (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
        memcpy(seed_material + entropy_input_len,
          additional_input_input,
          additional_input_input_len * sizeof (uint8_t));
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
        uint32_t input_len = 33U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, 32U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != 0U)
        {
          memcpy(input0 + 33U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        }
        input0[32U] = 0U;
        Hacl_HMAC_compute_sha2_256(k_, k, 32U, input0, input_len);
        Hacl_HMAC_compute_sha2_256(v, k_, 32U, v, 32U);
        memcpy(k, k_, 32U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != 0U)
        {
          uint32_t input_len0 = 33U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, 32U * sizeof (uint8_t));
          if (entropy_input_len + additional_input_input_len != 0U)
          {
            memcpy(input + 33U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
          }
          input[32U] = 1U;
          Hacl_HMAC_compute_sha2_256(k_0, k, 32U, input, input_len0);
          Hacl_HMAC_compute_sha2_256(v, k_0, 32U, v, 32U);
          memcpy(k, k_0, 32U * sizeof (uint8_t));
        }
        ctr[0U] = 1U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_input_len);
        uint8_t
        *seed_material =
          (uint8_t *)alloca((entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        memset(seed_material,
          0U,
          (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
        memcpy(seed_material + entropy_input_len,
          additional_input_input,
          additional_input_input_len * sizeof (uint8_t));
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
        uint32_t input_len = 49U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, 48U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != 0U)
        {
          memcpy(input0 + 49U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        }
        input0[48U] = 0U;
        Hacl_HMAC_compute_sha2_384(k_, k, 48U, input0, input_len);
        Hacl_HMAC_compute_sha2_384(v, k_, 48U, v, 48U);
        memcpy(k, k_, 48U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != 0U)
        {
          uint32_t input_len0 = 49U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, 48U * sizeof (uint8_t));
          if (entropy_input_len + additional_input_input_len != 0U)
          {
            memcpy(input + 49U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
          }
          input[48U] = 1U;
          Hacl_HMAC_compute_sha2_384(k_0, k, 48U, input, input_len0);
          Hacl_HMAC_compute_sha2_384(v, k_0, 48U, v, 48U);
          memcpy(k, k_0, 48U * sizeof (uint8_t));
        }
        ctr[0U] = 1U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_input_len);
        uint8_t
        *seed_material =
          (uint8_t *)alloca((entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        memset(seed_material,
          0U,
          (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
        memcpy(seed_material + entropy_input_len,
          additional_input_input,
          additional_input_input_len * sizeof (uint8_t));
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
        uint32_t input_len = 65U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = (uint8_t *)alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, 64U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != 0U)
        {
          memcpy(input0 + 65U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        }
        input0[64U] = 0U;
        Hacl_HMAC_compute_sha2_512(k_, k, 64U, input0, input_len);
        Hacl_HMAC_compute_sha2_512(v, k_, 64U, v, 64U);
        memcpy(k, k_, 64U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != 0U)
        {
          uint32_t input_len0 = 65U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = (uint8_t *)alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, 64U * sizeof (uint8_t));
          if (entropy_input_len + additional_input_input_len != 0U)
          {
            memcpy(input + 65U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
          }
          input[64U] = 1U;
          Hacl_HMAC_compute_sha2_512(k_0, k, 64U, input, input_len0);
          Hacl_HMAC_compute_sha2_512(v, k_0, 64U, v, 64U);
          memcpy(k, k_0, 64U * sizeof (uint8_t));
        }
        ctr[0U] = 1U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

/**
Generate output.

@param a Hash algorithm to use. (Value must match the value used in `create_in`.)
@param output Pointer to `n` bytes of memory where random output is written to.
@param st Pointer to DRBG state.
@param n Length of desired output.
@param additional_input_input_len Length of additional input.
@param additional_input_input Pointer to `additional_input_input_len` bytes of memory where additional input is read from.
*/
bool
Hacl_HMAC_DRBG_generate(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *output,
  Hacl_HMAC_DRBG_state st,
  uint32_t n,
  uint32_t additional_input_len,
  uint8_t *additional_input
)
{
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        if (st.reseed_counter[0U] > Hacl_HMAC_DRBG_reseed_interval)
        {
          return false;
        }
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
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
          Hacl_HMAC_compute_sha1(k_, k, 20U, input0, input_len);
          Hacl_HMAC_compute_sha1(v, k_, 20U, v, 20U);
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
            Hacl_HMAC_compute_sha1(k_0, k, 20U, input, input_len0);
            Hacl_HMAC_compute_sha1(v, k_0, 20U, v, 20U);
            memcpy(k, k_0, 20U * sizeof (uint8_t));
          }
        }
        uint8_t *output1 = output;
        uint32_t max = n / 20U;
        uint8_t *out = output1;
        for (uint32_t i = 0U; i < max; i++)
        {
          Hacl_HMAC_compute_sha1(v, k, 20U, v, 20U);
          memcpy(out + i * 20U, v, 20U * sizeof (uint8_t));
        }
        if (max * 20U < n)
        {
          uint8_t *block = output1 + max * 20U;
          Hacl_HMAC_compute_sha1(v, k, 20U, v, 20U);
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
        Hacl_HMAC_compute_sha1(k_, k, 20U, input0, input_len);
        Hacl_HMAC_compute_sha1(v, k_, 20U, v, 20U);
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
          Hacl_HMAC_compute_sha1(k_0, k, 20U, input, input_len0);
          Hacl_HMAC_compute_sha1(v, k_0, 20U, v, 20U);
          memcpy(k, k_0, 20U * sizeof (uint8_t));
        }
        uint32_t old_ctr = ctr[0U];
        ctr[0U] = old_ctr + 1U;
        return true;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        if (st.reseed_counter[0U] > Hacl_HMAC_DRBG_reseed_interval)
        {
          return false;
        }
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
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
          Hacl_HMAC_compute_sha2_256(k_, k, 32U, input0, input_len);
          Hacl_HMAC_compute_sha2_256(v, k_, 32U, v, 32U);
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
            Hacl_HMAC_compute_sha2_256(k_0, k, 32U, input, input_len0);
            Hacl_HMAC_compute_sha2_256(v, k_0, 32U, v, 32U);
            memcpy(k, k_0, 32U * sizeof (uint8_t));
          }
        }
        uint8_t *output1 = output;
        uint32_t max = n / 32U;
        uint8_t *out = output1;
        for (uint32_t i = 0U; i < max; i++)
        {
          Hacl_HMAC_compute_sha2_256(v, k, 32U, v, 32U);
          memcpy(out + i * 32U, v, 32U * sizeof (uint8_t));
        }
        if (max * 32U < n)
        {
          uint8_t *block = output1 + max * 32U;
          Hacl_HMAC_compute_sha2_256(v, k, 32U, v, 32U);
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
        Hacl_HMAC_compute_sha2_256(k_, k, 32U, input0, input_len);
        Hacl_HMAC_compute_sha2_256(v, k_, 32U, v, 32U);
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
          Hacl_HMAC_compute_sha2_256(k_0, k, 32U, input, input_len0);
          Hacl_HMAC_compute_sha2_256(v, k_0, 32U, v, 32U);
          memcpy(k, k_0, 32U * sizeof (uint8_t));
        }
        uint32_t old_ctr = ctr[0U];
        ctr[0U] = old_ctr + 1U;
        return true;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        if (st.reseed_counter[0U] > Hacl_HMAC_DRBG_reseed_interval)
        {
          return false;
        }
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
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
          Hacl_HMAC_compute_sha2_384(k_, k, 48U, input0, input_len);
          Hacl_HMAC_compute_sha2_384(v, k_, 48U, v, 48U);
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
            Hacl_HMAC_compute_sha2_384(k_0, k, 48U, input, input_len0);
            Hacl_HMAC_compute_sha2_384(v, k_0, 48U, v, 48U);
            memcpy(k, k_0, 48U * sizeof (uint8_t));
          }
        }
        uint8_t *output1 = output;
        uint32_t max = n / 48U;
        uint8_t *out = output1;
        for (uint32_t i = 0U; i < max; i++)
        {
          Hacl_HMAC_compute_sha2_384(v, k, 48U, v, 48U);
          memcpy(out + i * 48U, v, 48U * sizeof (uint8_t));
        }
        if (max * 48U < n)
        {
          uint8_t *block = output1 + max * 48U;
          Hacl_HMAC_compute_sha2_384(v, k, 48U, v, 48U);
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
        Hacl_HMAC_compute_sha2_384(k_, k, 48U, input0, input_len);
        Hacl_HMAC_compute_sha2_384(v, k_, 48U, v, 48U);
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
          Hacl_HMAC_compute_sha2_384(k_0, k, 48U, input, input_len0);
          Hacl_HMAC_compute_sha2_384(v, k_0, 48U, v, 48U);
          memcpy(k, k_0, 48U * sizeof (uint8_t));
        }
        uint32_t old_ctr = ctr[0U];
        ctr[0U] = old_ctr + 1U;
        return true;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        if (st.reseed_counter[0U] > Hacl_HMAC_DRBG_reseed_interval)
        {
          return false;
        }
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
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
          Hacl_HMAC_compute_sha2_512(k_, k, 64U, input0, input_len);
          Hacl_HMAC_compute_sha2_512(v, k_, 64U, v, 64U);
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
            Hacl_HMAC_compute_sha2_512(k_0, k, 64U, input, input_len0);
            Hacl_HMAC_compute_sha2_512(v, k_0, 64U, v, 64U);
            memcpy(k, k_0, 64U * sizeof (uint8_t));
          }
        }
        uint8_t *output1 = output;
        uint32_t max = n / 64U;
        uint8_t *out = output1;
        for (uint32_t i = 0U; i < max; i++)
        {
          Hacl_HMAC_compute_sha2_512(v, k, 64U, v, 64U);
          memcpy(out + i * 64U, v, 64U * sizeof (uint8_t));
        }
        if (max * 64U < n)
        {
          uint8_t *block = output1 + max * 64U;
          Hacl_HMAC_compute_sha2_512(v, k, 64U, v, 64U);
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
        Hacl_HMAC_compute_sha2_512(k_, k, 64U, input0, input_len);
        Hacl_HMAC_compute_sha2_512(v, k_, 64U, v, 64U);
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
          Hacl_HMAC_compute_sha2_512(k_0, k, 64U, input, input_len0);
          Hacl_HMAC_compute_sha2_512(v, k_0, 64U, v, 64U);
          memcpy(k, k_0, 64U * sizeof (uint8_t));
        }
        uint32_t old_ctr = ctr[0U];
        ctr[0U] = old_ctr + 1U;
        return true;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

void Hacl_HMAC_DRBG_free(Spec_Hash_Definitions_hash_alg uu___, Hacl_HMAC_DRBG_state s)
{
  KRML_MAYBE_UNUSED_VAR(uu___);
  uint8_t *k = s.k;
  uint8_t *v = s.v;
  uint32_t *ctr = s.reseed_counter;
  KRML_HOST_FREE(k);
  KRML_HOST_FREE(v);
  KRML_HOST_FREE(ctr);
}

