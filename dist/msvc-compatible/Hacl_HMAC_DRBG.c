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


#include "Hacl_HMAC_DRBG.h"

uint32_t Hacl_HMAC_DRBG_reseed_interval = (uint32_t)1024U;

uint32_t Hacl_HMAC_DRBG_max_output_length = (uint32_t)65536U;

uint32_t Hacl_HMAC_DRBG_max_length = (uint32_t)65536U;

uint32_t Hacl_HMAC_DRBG_max_personalization_string_length = (uint32_t)65536U;

uint32_t Hacl_HMAC_DRBG_max_additional_input_length = (uint32_t)65536U;

uint32_t Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_hash_alg a)
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

bool
Hacl_HMAC_DRBG_uu___is_State(Spec_Hash_Definitions_hash_alg a, Hacl_HMAC_DRBG_state projectee)
{
  return true;
}

uint8_t
*Hacl_HMAC_DRBG___proj__State__item__k(
  Spec_Hash_Definitions_hash_alg a,
  Hacl_HMAC_DRBG_state projectee
)
{
  return projectee.k;
}

uint8_t
*Hacl_HMAC_DRBG___proj__State__item__v(
  Spec_Hash_Definitions_hash_alg a,
  Hacl_HMAC_DRBG_state projectee
)
{
  return projectee.v;
}

uint32_t
*Hacl_HMAC_DRBG___proj__State__item__reseed_counter(
  Spec_Hash_Definitions_hash_alg a,
  Hacl_HMAC_DRBG_state projectee
)
{
  return projectee.reseed_counter;
}

Hacl_HMAC_DRBG_state Hacl_HMAC_DRBG_create_in(Spec_Hash_Definitions_hash_alg a)
{
  uint8_t *k1;
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        uint8_t *buf = KRML_HOST_CALLOC((uint32_t)20U, sizeof (uint8_t));
        k1 = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        uint8_t *buf = KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
        k1 = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        uint8_t *buf = KRML_HOST_CALLOC((uint32_t)48U, sizeof (uint8_t));
        k1 = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        uint8_t *buf = KRML_HOST_CALLOC((uint32_t)64U, sizeof (uint8_t));
        k1 = buf;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint8_t *v1;
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        uint8_t *buf = KRML_HOST_CALLOC((uint32_t)20U, sizeof (uint8_t));
        v1 = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        uint8_t *buf = KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
        v1 = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        uint8_t *buf = KRML_HOST_CALLOC((uint32_t)48U, sizeof (uint8_t));
        v1 = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        uint8_t *buf = KRML_HOST_CALLOC((uint32_t)64U, sizeof (uint8_t));
        v1 = buf;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t *ctr = KRML_HOST_MALLOC(sizeof (uint32_t));
  ctr[0U] = (uint32_t)1U;
  return ((Hacl_HMAC_DRBG_state){ .k = k1, .v = v1, .reseed_counter = ctr });
}

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
          alloca((entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
        memset(seed_material,
          0U,
          (entropy_input_len + nonce_len + personalization_string_len) * sizeof (seed_material[0U]));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
        memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof (nonce[0U]));
        memcpy(seed_material + entropy_input_len + nonce_len,
          personalization_string,
          personalization_string_len * sizeof (personalization_string[0U]));
        uint8_t *k1 = st.k;
        uint8_t *v1 = st.v;
        uint32_t *ctr = st.reseed_counter;
        memset(k1, 0U, (uint32_t)20U * sizeof (k1[0U]));
        memset(v1, (uint8_t)1U, (uint32_t)20U * sizeof (v1[0U]));
        ctr[0U] = (uint32_t)1U;
        uint32_t
        input_len = (uint32_t)21U + entropy_input_len + nonce_len + personalization_string_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v1, (uint32_t)20U * sizeof (v1[0U]));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)21U,
            seed_material,
            (entropy_input_len + nonce_len + personalization_string_len)
            * sizeof (seed_material[0U]));
        }
        input0[20U] = (uint8_t)0U;
        Hacl_HMAC_legacy_compute_sha1(k_, k1, (uint32_t)20U, input0, input_len);
        Hacl_HMAC_legacy_compute_sha1(v1, k_, (uint32_t)20U, v1, (uint32_t)20U);
        memcpy(k1, k_, (uint32_t)20U * sizeof (k_[0U]));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          uint32_t
          input_len0 = (uint32_t)21U + entropy_input_len + nonce_len + personalization_string_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v1, (uint32_t)20U * sizeof (v1[0U]));
          if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)21U,
              seed_material,
              (entropy_input_len + nonce_len + personalization_string_len)
              * sizeof (seed_material[0U]));
          }
          input[20U] = (uint8_t)1U;
          Hacl_HMAC_legacy_compute_sha1(k_0, k1, (uint32_t)20U, input, input_len0);
          Hacl_HMAC_legacy_compute_sha1(v1, k_0, (uint32_t)20U, v1, (uint32_t)20U);
          memcpy(k1, k_0, (uint32_t)20U * sizeof (k_0[0U]));
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t),
          entropy_input_len + nonce_len + personalization_string_len);
        uint8_t
        *seed_material =
          alloca((entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
        memset(seed_material,
          0U,
          (entropy_input_len + nonce_len + personalization_string_len) * sizeof (seed_material[0U]));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
        memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof (nonce[0U]));
        memcpy(seed_material + entropy_input_len + nonce_len,
          personalization_string,
          personalization_string_len * sizeof (personalization_string[0U]));
        uint8_t *k1 = st.k;
        uint8_t *v1 = st.v;
        uint32_t *ctr = st.reseed_counter;
        memset(k1, 0U, (uint32_t)32U * sizeof (k1[0U]));
        memset(v1, (uint8_t)1U, (uint32_t)32U * sizeof (v1[0U]));
        ctr[0U] = (uint32_t)1U;
        uint32_t
        input_len = (uint32_t)33U + entropy_input_len + nonce_len + personalization_string_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v1, (uint32_t)32U * sizeof (v1[0U]));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)33U,
            seed_material,
            (entropy_input_len + nonce_len + personalization_string_len)
            * sizeof (seed_material[0U]));
        }
        input0[32U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_256(k_, k1, (uint32_t)32U, input0, input_len);
        Hacl_HMAC_compute_sha2_256(v1, k_, (uint32_t)32U, v1, (uint32_t)32U);
        memcpy(k1, k_, (uint32_t)32U * sizeof (k_[0U]));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          uint32_t
          input_len0 = (uint32_t)33U + entropy_input_len + nonce_len + personalization_string_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v1, (uint32_t)32U * sizeof (v1[0U]));
          if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)33U,
              seed_material,
              (entropy_input_len + nonce_len + personalization_string_len)
              * sizeof (seed_material[0U]));
          }
          input[32U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_256(k_0, k1, (uint32_t)32U, input, input_len0);
          Hacl_HMAC_compute_sha2_256(v1, k_0, (uint32_t)32U, v1, (uint32_t)32U);
          memcpy(k1, k_0, (uint32_t)32U * sizeof (k_0[0U]));
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t),
          entropy_input_len + nonce_len + personalization_string_len);
        uint8_t
        *seed_material =
          alloca((entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
        memset(seed_material,
          0U,
          (entropy_input_len + nonce_len + personalization_string_len) * sizeof (seed_material[0U]));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
        memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof (nonce[0U]));
        memcpy(seed_material + entropy_input_len + nonce_len,
          personalization_string,
          personalization_string_len * sizeof (personalization_string[0U]));
        uint8_t *k1 = st.k;
        uint8_t *v1 = st.v;
        uint32_t *ctr = st.reseed_counter;
        memset(k1, 0U, (uint32_t)48U * sizeof (k1[0U]));
        memset(v1, (uint8_t)1U, (uint32_t)48U * sizeof (v1[0U]));
        ctr[0U] = (uint32_t)1U;
        uint32_t
        input_len = (uint32_t)49U + entropy_input_len + nonce_len + personalization_string_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v1, (uint32_t)48U * sizeof (v1[0U]));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)49U,
            seed_material,
            (entropy_input_len + nonce_len + personalization_string_len)
            * sizeof (seed_material[0U]));
        }
        input0[48U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_384(k_, k1, (uint32_t)48U, input0, input_len);
        Hacl_HMAC_compute_sha2_384(v1, k_, (uint32_t)48U, v1, (uint32_t)48U);
        memcpy(k1, k_, (uint32_t)48U * sizeof (k_[0U]));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          uint32_t
          input_len0 = (uint32_t)49U + entropy_input_len + nonce_len + personalization_string_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v1, (uint32_t)48U * sizeof (v1[0U]));
          if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)49U,
              seed_material,
              (entropy_input_len + nonce_len + personalization_string_len)
              * sizeof (seed_material[0U]));
          }
          input[48U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_384(k_0, k1, (uint32_t)48U, input, input_len0);
          Hacl_HMAC_compute_sha2_384(v1, k_0, (uint32_t)48U, v1, (uint32_t)48U);
          memcpy(k1, k_0, (uint32_t)48U * sizeof (k_0[0U]));
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t),
          entropy_input_len + nonce_len + personalization_string_len);
        uint8_t
        *seed_material =
          alloca((entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
        memset(seed_material,
          0U,
          (entropy_input_len + nonce_len + personalization_string_len) * sizeof (seed_material[0U]));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
        memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof (nonce[0U]));
        memcpy(seed_material + entropy_input_len + nonce_len,
          personalization_string,
          personalization_string_len * sizeof (personalization_string[0U]));
        uint8_t *k1 = st.k;
        uint8_t *v1 = st.v;
        uint32_t *ctr = st.reseed_counter;
        memset(k1, 0U, (uint32_t)64U * sizeof (k1[0U]));
        memset(v1, (uint8_t)1U, (uint32_t)64U * sizeof (v1[0U]));
        ctr[0U] = (uint32_t)1U;
        uint32_t
        input_len = (uint32_t)65U + entropy_input_len + nonce_len + personalization_string_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v1, (uint32_t)64U * sizeof (v1[0U]));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)65U,
            seed_material,
            (entropy_input_len + nonce_len + personalization_string_len)
            * sizeof (seed_material[0U]));
        }
        input0[64U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_512(k_, k1, (uint32_t)64U, input0, input_len);
        Hacl_HMAC_compute_sha2_512(v1, k_, (uint32_t)64U, v1, (uint32_t)64U);
        memcpy(k1, k_, (uint32_t)64U * sizeof (k_[0U]));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          uint32_t
          input_len0 = (uint32_t)65U + entropy_input_len + nonce_len + personalization_string_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v1, (uint32_t)64U * sizeof (v1[0U]));
          if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)65U,
              seed_material,
              (entropy_input_len + nonce_len + personalization_string_len)
              * sizeof (seed_material[0U]));
          }
          input[64U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_512(k_0, k1, (uint32_t)64U, input, input_len0);
          Hacl_HMAC_compute_sha2_512(v1, k_0, (uint32_t)64U, v1, (uint32_t)64U);
          memcpy(k1, k_0, (uint32_t)64U * sizeof (k_0[0U]));
        }
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

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
        *seed_material = alloca((entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        memset(seed_material,
          0U,
          (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
        memcpy(seed_material + entropy_input_len,
          additional_input_input,
          additional_input_input_len * sizeof (additional_input_input[0U]));
        Hacl_HMAC_DRBG_state uu____0 = st;
        uint8_t *k1 = uu____0.k;
        uint8_t *v1 = uu____0.v;
        uint32_t *ctr = uu____0.reseed_counter;
        uint32_t input_len = (uint32_t)21U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v1, (uint32_t)20U * sizeof (v1[0U]));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)21U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
        }
        input0[20U] = (uint8_t)0U;
        Hacl_HMAC_legacy_compute_sha1(k_, k1, (uint32_t)20U, input0, input_len);
        Hacl_HMAC_legacy_compute_sha1(v1, k_, (uint32_t)20U, v1, (uint32_t)20U);
        memcpy(k1, k_, (uint32_t)20U * sizeof (k_[0U]));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)21U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v1, (uint32_t)20U * sizeof (v1[0U]));
          if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)21U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
          }
          input[20U] = (uint8_t)1U;
          Hacl_HMAC_legacy_compute_sha1(k_0, k1, (uint32_t)20U, input, input_len0);
          Hacl_HMAC_legacy_compute_sha1(v1, k_0, (uint32_t)20U, v1, (uint32_t)20U);
          memcpy(k1, k_0, (uint32_t)20U * sizeof (k_0[0U]));
        }
        ctr[0U] = (uint32_t)1U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_input_len);
        uint8_t
        *seed_material = alloca((entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        memset(seed_material,
          0U,
          (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
        memcpy(seed_material + entropy_input_len,
          additional_input_input,
          additional_input_input_len * sizeof (additional_input_input[0U]));
        Hacl_HMAC_DRBG_state uu____1 = st;
        uint8_t *k1 = uu____1.k;
        uint8_t *v1 = uu____1.v;
        uint32_t *ctr = uu____1.reseed_counter;
        uint32_t input_len = (uint32_t)33U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v1, (uint32_t)32U * sizeof (v1[0U]));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)33U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
        }
        input0[32U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_256(k_, k1, (uint32_t)32U, input0, input_len);
        Hacl_HMAC_compute_sha2_256(v1, k_, (uint32_t)32U, v1, (uint32_t)32U);
        memcpy(k1, k_, (uint32_t)32U * sizeof (k_[0U]));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)33U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v1, (uint32_t)32U * sizeof (v1[0U]));
          if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)33U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
          }
          input[32U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_256(k_0, k1, (uint32_t)32U, input, input_len0);
          Hacl_HMAC_compute_sha2_256(v1, k_0, (uint32_t)32U, v1, (uint32_t)32U);
          memcpy(k1, k_0, (uint32_t)32U * sizeof (k_0[0U]));
        }
        ctr[0U] = (uint32_t)1U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_input_len);
        uint8_t
        *seed_material = alloca((entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        memset(seed_material,
          0U,
          (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
        memcpy(seed_material + entropy_input_len,
          additional_input_input,
          additional_input_input_len * sizeof (additional_input_input[0U]));
        Hacl_HMAC_DRBG_state uu____2 = st;
        uint8_t *k1 = uu____2.k;
        uint8_t *v1 = uu____2.v;
        uint32_t *ctr = uu____2.reseed_counter;
        uint32_t input_len = (uint32_t)49U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v1, (uint32_t)48U * sizeof (v1[0U]));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)49U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
        }
        input0[48U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_384(k_, k1, (uint32_t)48U, input0, input_len);
        Hacl_HMAC_compute_sha2_384(v1, k_, (uint32_t)48U, v1, (uint32_t)48U);
        memcpy(k1, k_, (uint32_t)48U * sizeof (k_[0U]));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)49U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v1, (uint32_t)48U * sizeof (v1[0U]));
          if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)49U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
          }
          input[48U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_384(k_0, k1, (uint32_t)48U, input, input_len0);
          Hacl_HMAC_compute_sha2_384(v1, k_0, (uint32_t)48U, v1, (uint32_t)48U);
          memcpy(k1, k_0, (uint32_t)48U * sizeof (k_0[0U]));
        }
        ctr[0U] = (uint32_t)1U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_input_len);
        uint8_t
        *seed_material = alloca((entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        memset(seed_material,
          0U,
          (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
        memcpy(seed_material + entropy_input_len,
          additional_input_input,
          additional_input_input_len * sizeof (additional_input_input[0U]));
        Hacl_HMAC_DRBG_state uu____3 = st;
        uint8_t *k1 = uu____3.k;
        uint8_t *v1 = uu____3.v;
        uint32_t *ctr = uu____3.reseed_counter;
        uint32_t input_len = (uint32_t)65U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v1, (uint32_t)64U * sizeof (v1[0U]));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)65U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
        }
        input0[64U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_512(k_, k1, (uint32_t)64U, input0, input_len);
        Hacl_HMAC_compute_sha2_512(v1, k_, (uint32_t)64U, v1, (uint32_t)64U);
        memcpy(k1, k_, (uint32_t)64U * sizeof (k_[0U]));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)65U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v1, (uint32_t)64U * sizeof (v1[0U]));
          if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)65U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
          }
          input[64U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_512(k_0, k1, (uint32_t)64U, input, input_len0);
          Hacl_HMAC_compute_sha2_512(v1, k_0, (uint32_t)64U, v1, (uint32_t)64U);
          memcpy(k1, k_0, (uint32_t)64U * sizeof (k_0[0U]));
        }
        ctr[0U] = (uint32_t)1U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

bool
Hacl_HMAC_DRBG_generate(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *output,
  Hacl_HMAC_DRBG_state st,
  uint32_t n1,
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
        uint8_t *k1 = st.k;
        uint8_t *v1 = st.v;
        uint32_t *ctr = st.reseed_counter;
        if (additional_input_len > (uint32_t)0U)
        {
          uint32_t input_len = (uint32_t)21U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
          uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
          memset(input0, 0U, input_len * sizeof (input0[0U]));
          uint8_t *k_ = input0;
          memcpy(k_, v1, (uint32_t)20U * sizeof (v1[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input0 + (uint32_t)21U,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
          input0[20U] = (uint8_t)0U;
          Hacl_HMAC_legacy_compute_sha1(k_, k1, (uint32_t)20U, input0, input_len);
          Hacl_HMAC_legacy_compute_sha1(v1, k_, (uint32_t)20U, v1, (uint32_t)20U);
          memcpy(k1, k_, (uint32_t)20U * sizeof (k_[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            uint32_t input_len0 = (uint32_t)21U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
            uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
            memset(input, 0U, input_len0 * sizeof (input[0U]));
            uint8_t *k_0 = input;
            memcpy(k_0, v1, (uint32_t)20U * sizeof (v1[0U]));
            if (additional_input_len != (uint32_t)0U)
            {
              memcpy(input + (uint32_t)21U,
                additional_input,
                additional_input_len * sizeof (additional_input[0U]));
            }
            input[20U] = (uint8_t)1U;
            Hacl_HMAC_legacy_compute_sha1(k_0, k1, (uint32_t)20U, input, input_len0);
            Hacl_HMAC_legacy_compute_sha1(v1, k_0, (uint32_t)20U, v1, (uint32_t)20U);
            memcpy(k1, k_0, (uint32_t)20U * sizeof (k_0[0U]));
          }
        }
        uint8_t *output1 = output;
        uint32_t max1 = n1 / (uint32_t)20U;
        uint8_t *out = output1;
        for (uint32_t i = (uint32_t)0U; i < max1; i++)
        {
          Hacl_HMAC_legacy_compute_sha1(v1, k1, (uint32_t)20U, v1, (uint32_t)20U);
          memcpy(out + i * (uint32_t)20U, v1, (uint32_t)20U * sizeof (v1[0U]));
        }
        if (max1 * (uint32_t)20U < n1)
        {
          uint8_t *block = output1 + max1 * (uint32_t)20U;
          Hacl_HMAC_legacy_compute_sha1(v1, k1, (uint32_t)20U, v1, (uint32_t)20U);
          memcpy(block, v1, (n1 - max1 * (uint32_t)20U) * sizeof (v1[0U]));
        }
        uint32_t input_len = (uint32_t)21U + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v1, (uint32_t)20U * sizeof (v1[0U]));
        if (additional_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)21U,
            additional_input,
            additional_input_len * sizeof (additional_input[0U]));
        }
        input0[20U] = (uint8_t)0U;
        Hacl_HMAC_legacy_compute_sha1(k_, k1, (uint32_t)20U, input0, input_len);
        Hacl_HMAC_legacy_compute_sha1(v1, k_, (uint32_t)20U, v1, (uint32_t)20U);
        memcpy(k1, k_, (uint32_t)20U * sizeof (k_[0U]));
        if (additional_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)21U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v1, (uint32_t)20U * sizeof (v1[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)21U,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
          input[20U] = (uint8_t)1U;
          Hacl_HMAC_legacy_compute_sha1(k_0, k1, (uint32_t)20U, input, input_len0);
          Hacl_HMAC_legacy_compute_sha1(v1, k_0, (uint32_t)20U, v1, (uint32_t)20U);
          memcpy(k1, k_0, (uint32_t)20U * sizeof (k_0[0U]));
        }
        uint32_t old_ctr = ctr[0U];
        ctr[0U] = old_ctr + (uint32_t)1U;
        return true;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        if (st.reseed_counter[0U] > Hacl_HMAC_DRBG_reseed_interval)
        {
          return false;
        }
        uint8_t *k1 = st.k;
        uint8_t *v1 = st.v;
        uint32_t *ctr = st.reseed_counter;
        if (additional_input_len > (uint32_t)0U)
        {
          uint32_t input_len = (uint32_t)33U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
          uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
          memset(input0, 0U, input_len * sizeof (input0[0U]));
          uint8_t *k_ = input0;
          memcpy(k_, v1, (uint32_t)32U * sizeof (v1[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input0 + (uint32_t)33U,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
          input0[32U] = (uint8_t)0U;
          Hacl_HMAC_compute_sha2_256(k_, k1, (uint32_t)32U, input0, input_len);
          Hacl_HMAC_compute_sha2_256(v1, k_, (uint32_t)32U, v1, (uint32_t)32U);
          memcpy(k1, k_, (uint32_t)32U * sizeof (k_[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            uint32_t input_len0 = (uint32_t)33U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
            uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
            memset(input, 0U, input_len0 * sizeof (input[0U]));
            uint8_t *k_0 = input;
            memcpy(k_0, v1, (uint32_t)32U * sizeof (v1[0U]));
            if (additional_input_len != (uint32_t)0U)
            {
              memcpy(input + (uint32_t)33U,
                additional_input,
                additional_input_len * sizeof (additional_input[0U]));
            }
            input[32U] = (uint8_t)1U;
            Hacl_HMAC_compute_sha2_256(k_0, k1, (uint32_t)32U, input, input_len0);
            Hacl_HMAC_compute_sha2_256(v1, k_0, (uint32_t)32U, v1, (uint32_t)32U);
            memcpy(k1, k_0, (uint32_t)32U * sizeof (k_0[0U]));
          }
        }
        uint8_t *output1 = output;
        uint32_t max1 = n1 / (uint32_t)32U;
        uint8_t *out = output1;
        for (uint32_t i = (uint32_t)0U; i < max1; i++)
        {
          Hacl_HMAC_compute_sha2_256(v1, k1, (uint32_t)32U, v1, (uint32_t)32U);
          memcpy(out + i * (uint32_t)32U, v1, (uint32_t)32U * sizeof (v1[0U]));
        }
        if (max1 * (uint32_t)32U < n1)
        {
          uint8_t *block = output1 + max1 * (uint32_t)32U;
          Hacl_HMAC_compute_sha2_256(v1, k1, (uint32_t)32U, v1, (uint32_t)32U);
          memcpy(block, v1, (n1 - max1 * (uint32_t)32U) * sizeof (v1[0U]));
        }
        uint32_t input_len = (uint32_t)33U + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v1, (uint32_t)32U * sizeof (v1[0U]));
        if (additional_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)33U,
            additional_input,
            additional_input_len * sizeof (additional_input[0U]));
        }
        input0[32U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_256(k_, k1, (uint32_t)32U, input0, input_len);
        Hacl_HMAC_compute_sha2_256(v1, k_, (uint32_t)32U, v1, (uint32_t)32U);
        memcpy(k1, k_, (uint32_t)32U * sizeof (k_[0U]));
        if (additional_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)33U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v1, (uint32_t)32U * sizeof (v1[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)33U,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
          input[32U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_256(k_0, k1, (uint32_t)32U, input, input_len0);
          Hacl_HMAC_compute_sha2_256(v1, k_0, (uint32_t)32U, v1, (uint32_t)32U);
          memcpy(k1, k_0, (uint32_t)32U * sizeof (k_0[0U]));
        }
        uint32_t old_ctr = ctr[0U];
        ctr[0U] = old_ctr + (uint32_t)1U;
        return true;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        if (st.reseed_counter[0U] > Hacl_HMAC_DRBG_reseed_interval)
        {
          return false;
        }
        uint8_t *k1 = st.k;
        uint8_t *v1 = st.v;
        uint32_t *ctr = st.reseed_counter;
        if (additional_input_len > (uint32_t)0U)
        {
          uint32_t input_len = (uint32_t)49U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
          uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
          memset(input0, 0U, input_len * sizeof (input0[0U]));
          uint8_t *k_ = input0;
          memcpy(k_, v1, (uint32_t)48U * sizeof (v1[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input0 + (uint32_t)49U,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
          input0[48U] = (uint8_t)0U;
          Hacl_HMAC_compute_sha2_384(k_, k1, (uint32_t)48U, input0, input_len);
          Hacl_HMAC_compute_sha2_384(v1, k_, (uint32_t)48U, v1, (uint32_t)48U);
          memcpy(k1, k_, (uint32_t)48U * sizeof (k_[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            uint32_t input_len0 = (uint32_t)49U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
            uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
            memset(input, 0U, input_len0 * sizeof (input[0U]));
            uint8_t *k_0 = input;
            memcpy(k_0, v1, (uint32_t)48U * sizeof (v1[0U]));
            if (additional_input_len != (uint32_t)0U)
            {
              memcpy(input + (uint32_t)49U,
                additional_input,
                additional_input_len * sizeof (additional_input[0U]));
            }
            input[48U] = (uint8_t)1U;
            Hacl_HMAC_compute_sha2_384(k_0, k1, (uint32_t)48U, input, input_len0);
            Hacl_HMAC_compute_sha2_384(v1, k_0, (uint32_t)48U, v1, (uint32_t)48U);
            memcpy(k1, k_0, (uint32_t)48U * sizeof (k_0[0U]));
          }
        }
        uint8_t *output1 = output;
        uint32_t max1 = n1 / (uint32_t)48U;
        uint8_t *out = output1;
        for (uint32_t i = (uint32_t)0U; i < max1; i++)
        {
          Hacl_HMAC_compute_sha2_384(v1, k1, (uint32_t)48U, v1, (uint32_t)48U);
          memcpy(out + i * (uint32_t)48U, v1, (uint32_t)48U * sizeof (v1[0U]));
        }
        if (max1 * (uint32_t)48U < n1)
        {
          uint8_t *block = output1 + max1 * (uint32_t)48U;
          Hacl_HMAC_compute_sha2_384(v1, k1, (uint32_t)48U, v1, (uint32_t)48U);
          memcpy(block, v1, (n1 - max1 * (uint32_t)48U) * sizeof (v1[0U]));
        }
        uint32_t input_len = (uint32_t)49U + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v1, (uint32_t)48U * sizeof (v1[0U]));
        if (additional_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)49U,
            additional_input,
            additional_input_len * sizeof (additional_input[0U]));
        }
        input0[48U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_384(k_, k1, (uint32_t)48U, input0, input_len);
        Hacl_HMAC_compute_sha2_384(v1, k_, (uint32_t)48U, v1, (uint32_t)48U);
        memcpy(k1, k_, (uint32_t)48U * sizeof (k_[0U]));
        if (additional_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)49U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v1, (uint32_t)48U * sizeof (v1[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)49U,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
          input[48U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_384(k_0, k1, (uint32_t)48U, input, input_len0);
          Hacl_HMAC_compute_sha2_384(v1, k_0, (uint32_t)48U, v1, (uint32_t)48U);
          memcpy(k1, k_0, (uint32_t)48U * sizeof (k_0[0U]));
        }
        uint32_t old_ctr = ctr[0U];
        ctr[0U] = old_ctr + (uint32_t)1U;
        return true;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        if (st.reseed_counter[0U] > Hacl_HMAC_DRBG_reseed_interval)
        {
          return false;
        }
        uint8_t *k1 = st.k;
        uint8_t *v1 = st.v;
        uint32_t *ctr = st.reseed_counter;
        if (additional_input_len > (uint32_t)0U)
        {
          uint32_t input_len = (uint32_t)65U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
          uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
          memset(input0, 0U, input_len * sizeof (input0[0U]));
          uint8_t *k_ = input0;
          memcpy(k_, v1, (uint32_t)64U * sizeof (v1[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input0 + (uint32_t)65U,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
          input0[64U] = (uint8_t)0U;
          Hacl_HMAC_compute_sha2_512(k_, k1, (uint32_t)64U, input0, input_len);
          Hacl_HMAC_compute_sha2_512(v1, k_, (uint32_t)64U, v1, (uint32_t)64U);
          memcpy(k1, k_, (uint32_t)64U * sizeof (k_[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            uint32_t input_len0 = (uint32_t)65U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
            uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
            memset(input, 0U, input_len0 * sizeof (input[0U]));
            uint8_t *k_0 = input;
            memcpy(k_0, v1, (uint32_t)64U * sizeof (v1[0U]));
            if (additional_input_len != (uint32_t)0U)
            {
              memcpy(input + (uint32_t)65U,
                additional_input,
                additional_input_len * sizeof (additional_input[0U]));
            }
            input[64U] = (uint8_t)1U;
            Hacl_HMAC_compute_sha2_512(k_0, k1, (uint32_t)64U, input, input_len0);
            Hacl_HMAC_compute_sha2_512(v1, k_0, (uint32_t)64U, v1, (uint32_t)64U);
            memcpy(k1, k_0, (uint32_t)64U * sizeof (k_0[0U]));
          }
        }
        uint8_t *output1 = output;
        uint32_t max1 = n1 / (uint32_t)64U;
        uint8_t *out = output1;
        for (uint32_t i = (uint32_t)0U; i < max1; i++)
        {
          Hacl_HMAC_compute_sha2_512(v1, k1, (uint32_t)64U, v1, (uint32_t)64U);
          memcpy(out + i * (uint32_t)64U, v1, (uint32_t)64U * sizeof (v1[0U]));
        }
        if (max1 * (uint32_t)64U < n1)
        {
          uint8_t *block = output1 + max1 * (uint32_t)64U;
          Hacl_HMAC_compute_sha2_512(v1, k1, (uint32_t)64U, v1, (uint32_t)64U);
          memcpy(block, v1, (n1 - max1 * (uint32_t)64U) * sizeof (v1[0U]));
        }
        uint32_t input_len = (uint32_t)65U + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v1, (uint32_t)64U * sizeof (v1[0U]));
        if (additional_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)65U,
            additional_input,
            additional_input_len * sizeof (additional_input[0U]));
        }
        input0[64U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_512(k_, k1, (uint32_t)64U, input0, input_len);
        Hacl_HMAC_compute_sha2_512(v1, k_, (uint32_t)64U, v1, (uint32_t)64U);
        memcpy(k1, k_, (uint32_t)64U * sizeof (k_[0U]));
        if (additional_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)65U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v1, (uint32_t)64U * sizeof (v1[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)65U,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
          input[64U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_512(k_0, k1, (uint32_t)64U, input, input_len0);
          Hacl_HMAC_compute_sha2_512(v1, k_0, (uint32_t)64U, v1, (uint32_t)64U);
          memcpy(k1, k_0, (uint32_t)64U * sizeof (k_0[0U]));
        }
        uint32_t old_ctr = ctr[0U];
        ctr[0U] = old_ctr + (uint32_t)1U;
        return true;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

