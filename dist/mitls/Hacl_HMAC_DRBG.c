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
  uint8_t *k;
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        uint8_t *buf = KRML_HOST_CALLOC((uint32_t)20U, sizeof (uint8_t));
        k = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        uint8_t *buf = KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
        k = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        uint8_t *buf = KRML_HOST_CALLOC((uint32_t)48U, sizeof (uint8_t));
        k = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        uint8_t *buf = KRML_HOST_CALLOC((uint32_t)64U, sizeof (uint8_t));
        k = buf;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint8_t *v;
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        uint8_t *buf = KRML_HOST_CALLOC((uint32_t)20U, sizeof (uint8_t));
        v = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        uint8_t *buf = KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
        v = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        uint8_t *buf = KRML_HOST_CALLOC((uint32_t)48U, sizeof (uint8_t));
        v = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        uint8_t *buf = KRML_HOST_CALLOC((uint32_t)64U, sizeof (uint8_t));
        v = buf;
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
  return ((Hacl_HMAC_DRBG_state){ .k = k, .v = v, .reseed_counter = ctr });
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
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
        memset(k, 0U, (uint32_t)20U * sizeof (k[0U]));
        memset(v, (uint8_t)1U, (uint32_t)20U * sizeof (v[0U]));
        ctr[0U] = (uint32_t)1U;
        uint32_t
        input_len = (uint32_t)21U + entropy_input_len + nonce_len + personalization_string_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)20U * sizeof (v[0U]));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)21U,
            seed_material,
            (entropy_input_len + nonce_len + personalization_string_len)
            * sizeof (seed_material[0U]));
        }
        input0[20U] = (uint8_t)0U;
        Hacl_HMAC_legacy_compute_sha1(k_, k, (uint32_t)20U, input0, input_len);
        Hacl_HMAC_legacy_compute_sha1(v, k_, (uint32_t)20U, v, (uint32_t)20U);
        memcpy(k, k_, (uint32_t)20U * sizeof (k_[0U]));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          uint32_t
          input_len0 = (uint32_t)21U + entropy_input_len + nonce_len + personalization_string_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)20U * sizeof (v[0U]));
          if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)21U,
              seed_material,
              (entropy_input_len + nonce_len + personalization_string_len)
              * sizeof (seed_material[0U]));
          }
          input[20U] = (uint8_t)1U;
          Hacl_HMAC_legacy_compute_sha1(k_0, k, (uint32_t)20U, input, input_len0);
          Hacl_HMAC_legacy_compute_sha1(v, k_0, (uint32_t)20U, v, (uint32_t)20U);
          memcpy(k, k_0, (uint32_t)20U * sizeof (k_0[0U]));
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
        uint8_t *uu____6;
        if (seed_material == NULL)
        {
          uu____6 = NULL;
        }
        else
        {
          uu____6 = seed_material;
        }
        bool uu____7 = entropy_input == NULL;
        if (!(uu____7 || uu____6 == NULL))
        {
          memcpy(uu____6, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
        }
        uint8_t *uu____8;
        if (seed_material == NULL)
        {
          uu____8 = NULL;
        }
        else
        {
          uu____8 = seed_material + entropy_input_len;
        }
        bool uu____9 = nonce == NULL;
        if (!(uu____9 || uu____8 == NULL))
        {
          memcpy(uu____8, nonce, nonce_len * sizeof (nonce[0U]));
        }
        uint8_t *uu____10;
        if (seed_material == NULL)
        {
          uu____10 = NULL;
        }
        else
        {
          uu____10 = seed_material + entropy_input_len + nonce_len;
        }
        bool uu____11 = personalization_string == NULL;
        if (!(uu____11 || uu____10 == NULL))
        {
          memcpy(uu____10,
            personalization_string,
            personalization_string_len * sizeof (personalization_string[0U]));
        }
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
        memset(k, 0U, (uint32_t)32U * sizeof (k[0U]));
        memset(v, (uint8_t)1U, (uint32_t)32U * sizeof (v[0U]));
        ctr[0U] = (uint32_t)1U;
        uint32_t
        input_len = (uint32_t)33U + entropy_input_len + nonce_len + personalization_string_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)32U * sizeof (v[0U]));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)33U,
            seed_material,
            (entropy_input_len + nonce_len + personalization_string_len)
            * sizeof (seed_material[0U]));
        }
        input0[32U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_256(k_, k, (uint32_t)32U, input0, input_len);
        Hacl_HMAC_compute_sha2_256(v, k_, (uint32_t)32U, v, (uint32_t)32U);
        memcpy(k, k_, (uint32_t)32U * sizeof (k_[0U]));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          uint32_t
          input_len0 = (uint32_t)33U + entropy_input_len + nonce_len + personalization_string_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)32U * sizeof (v[0U]));
          if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)33U,
              seed_material,
              (entropy_input_len + nonce_len + personalization_string_len)
              * sizeof (seed_material[0U]));
          }
          input[32U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_256(k_0, k, (uint32_t)32U, input, input_len0);
          Hacl_HMAC_compute_sha2_256(v, k_0, (uint32_t)32U, v, (uint32_t)32U);
          memcpy(k, k_0, (uint32_t)32U * sizeof (k_0[0U]));
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
        uint8_t *uu____12;
        if (seed_material == NULL)
        {
          uu____12 = NULL;
        }
        else
        {
          uu____12 = seed_material;
        }
        bool uu____13 = entropy_input == NULL;
        if (!(uu____13 || uu____12 == NULL))
        {
          memcpy(uu____12, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
        }
        uint8_t *uu____14;
        if (seed_material == NULL)
        {
          uu____14 = NULL;
        }
        else
        {
          uu____14 = seed_material + entropy_input_len;
        }
        bool uu____15 = nonce == NULL;
        if (!(uu____15 || uu____14 == NULL))
        {
          memcpy(uu____14, nonce, nonce_len * sizeof (nonce[0U]));
        }
        uint8_t *uu____16;
        if (seed_material == NULL)
        {
          uu____16 = NULL;
        }
        else
        {
          uu____16 = seed_material + entropy_input_len + nonce_len;
        }
        bool uu____17 = personalization_string == NULL;
        if (!(uu____17 || uu____16 == NULL))
        {
          memcpy(uu____16,
            personalization_string,
            personalization_string_len * sizeof (personalization_string[0U]));
        }
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
        memset(k, 0U, (uint32_t)48U * sizeof (k[0U]));
        memset(v, (uint8_t)1U, (uint32_t)48U * sizeof (v[0U]));
        ctr[0U] = (uint32_t)1U;
        uint32_t
        input_len = (uint32_t)49U + entropy_input_len + nonce_len + personalization_string_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)48U * sizeof (v[0U]));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)49U,
            seed_material,
            (entropy_input_len + nonce_len + personalization_string_len)
            * sizeof (seed_material[0U]));
        }
        input0[48U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_384(k_, k, (uint32_t)48U, input0, input_len);
        Hacl_HMAC_compute_sha2_384(v, k_, (uint32_t)48U, v, (uint32_t)48U);
        memcpy(k, k_, (uint32_t)48U * sizeof (k_[0U]));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          uint32_t
          input_len0 = (uint32_t)49U + entropy_input_len + nonce_len + personalization_string_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)48U * sizeof (v[0U]));
          if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)49U,
              seed_material,
              (entropy_input_len + nonce_len + personalization_string_len)
              * sizeof (seed_material[0U]));
          }
          input[48U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_384(k_0, k, (uint32_t)48U, input, input_len0);
          Hacl_HMAC_compute_sha2_384(v, k_0, (uint32_t)48U, v, (uint32_t)48U);
          memcpy(k, k_0, (uint32_t)48U * sizeof (k_0[0U]));
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
        uint8_t *uu____18;
        if (seed_material == NULL)
        {
          uu____18 = NULL;
        }
        else
        {
          uu____18 = seed_material;
        }
        bool uu____19 = entropy_input == NULL;
        if (!(uu____19 || uu____18 == NULL))
        {
          memcpy(uu____18, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
        }
        uint8_t *uu____20;
        if (seed_material == NULL)
        {
          uu____20 = NULL;
        }
        else
        {
          uu____20 = seed_material + entropy_input_len;
        }
        bool uu____21 = nonce == NULL;
        if (!(uu____21 || uu____20 == NULL))
        {
          memcpy(uu____20, nonce, nonce_len * sizeof (nonce[0U]));
        }
        uint8_t *uu____22;
        if (seed_material == NULL)
        {
          uu____22 = NULL;
        }
        else
        {
          uu____22 = seed_material + entropy_input_len + nonce_len;
        }
        bool uu____23 = personalization_string == NULL;
        if (!(uu____23 || uu____22 == NULL))
        {
          memcpy(uu____22,
            personalization_string,
            personalization_string_len * sizeof (personalization_string[0U]));
        }
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
        memset(k, 0U, (uint32_t)64U * sizeof (k[0U]));
        memset(v, (uint8_t)1U, (uint32_t)64U * sizeof (v[0U]));
        ctr[0U] = (uint32_t)1U;
        uint32_t
        input_len = (uint32_t)65U + entropy_input_len + nonce_len + personalization_string_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)64U * sizeof (v[0U]));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)65U,
            seed_material,
            (entropy_input_len + nonce_len + personalization_string_len)
            * sizeof (seed_material[0U]));
        }
        input0[64U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_512(k_, k, (uint32_t)64U, input0, input_len);
        Hacl_HMAC_compute_sha2_512(v, k_, (uint32_t)64U, v, (uint32_t)64U);
        memcpy(k, k_, (uint32_t)64U * sizeof (k_[0U]));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          uint32_t
          input_len0 = (uint32_t)65U + entropy_input_len + nonce_len + personalization_string_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)64U * sizeof (v[0U]));
          if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)65U,
              seed_material,
              (entropy_input_len + nonce_len + personalization_string_len)
              * sizeof (seed_material[0U]));
          }
          input[64U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_512(k_0, k, (uint32_t)64U, input, input_len0);
          Hacl_HMAC_compute_sha2_512(v, k_0, (uint32_t)64U, v, (uint32_t)64U);
          memcpy(k, k_0, (uint32_t)64U * sizeof (k_0[0U]));
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
        uint8_t *uu____0;
        if (seed_material == NULL)
        {
          uu____0 = NULL;
        }
        else
        {
          uu____0 = seed_material + entropy_input_len;
        }
        bool uu____1 = additional_input_input == NULL;
        if (!(uu____1 || uu____0 == NULL))
        {
          memcpy(uu____0,
            additional_input_input,
            additional_input_input_len * sizeof (additional_input_input[0U]));
        }
        Hacl_HMAC_DRBG_state uu____2 = st;
        uint8_t *k = uu____2.k;
        uint8_t *v = uu____2.v;
        uint32_t *ctr = uu____2.reseed_counter;
        uint32_t input_len = (uint32_t)21U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)20U * sizeof (v[0U]));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)21U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
        }
        input0[20U] = (uint8_t)0U;
        Hacl_HMAC_legacy_compute_sha1(k_, k, (uint32_t)20U, input0, input_len);
        Hacl_HMAC_legacy_compute_sha1(v, k_, (uint32_t)20U, v, (uint32_t)20U);
        memcpy(k, k_, (uint32_t)20U * sizeof (k_[0U]));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)21U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)20U * sizeof (v[0U]));
          if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)21U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
          }
          input[20U] = (uint8_t)1U;
          Hacl_HMAC_legacy_compute_sha1(k_0, k, (uint32_t)20U, input, input_len0);
          Hacl_HMAC_legacy_compute_sha1(v, k_0, (uint32_t)20U, v, (uint32_t)20U);
          memcpy(k, k_0, (uint32_t)20U * sizeof (k_0[0U]));
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
        uint8_t *uu____3;
        if (seed_material == NULL)
        {
          uu____3 = NULL;
        }
        else
        {
          uu____3 = seed_material + entropy_input_len;
        }
        bool uu____4 = additional_input_input == NULL;
        if (!(uu____4 || uu____3 == NULL))
        {
          memcpy(uu____3,
            additional_input_input,
            additional_input_input_len * sizeof (additional_input_input[0U]));
        }
        Hacl_HMAC_DRBG_state uu____5 = st;
        uint8_t *k = uu____5.k;
        uint8_t *v = uu____5.v;
        uint32_t *ctr = uu____5.reseed_counter;
        uint32_t input_len = (uint32_t)33U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)32U * sizeof (v[0U]));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)33U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
        }
        input0[32U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_256(k_, k, (uint32_t)32U, input0, input_len);
        Hacl_HMAC_compute_sha2_256(v, k_, (uint32_t)32U, v, (uint32_t)32U);
        memcpy(k, k_, (uint32_t)32U * sizeof (k_[0U]));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)33U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)32U * sizeof (v[0U]));
          if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)33U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
          }
          input[32U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_256(k_0, k, (uint32_t)32U, input, input_len0);
          Hacl_HMAC_compute_sha2_256(v, k_0, (uint32_t)32U, v, (uint32_t)32U);
          memcpy(k, k_0, (uint32_t)32U * sizeof (k_0[0U]));
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
        uint8_t *uu____6;
        if (seed_material == NULL)
        {
          uu____6 = NULL;
        }
        else
        {
          uu____6 = seed_material + entropy_input_len;
        }
        bool uu____7 = additional_input_input == NULL;
        if (!(uu____7 || uu____6 == NULL))
        {
          memcpy(uu____6,
            additional_input_input,
            additional_input_input_len * sizeof (additional_input_input[0U]));
        }
        Hacl_HMAC_DRBG_state uu____8 = st;
        uint8_t *k = uu____8.k;
        uint8_t *v = uu____8.v;
        uint32_t *ctr = uu____8.reseed_counter;
        uint32_t input_len = (uint32_t)49U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)48U * sizeof (v[0U]));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)49U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
        }
        input0[48U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_384(k_, k, (uint32_t)48U, input0, input_len);
        Hacl_HMAC_compute_sha2_384(v, k_, (uint32_t)48U, v, (uint32_t)48U);
        memcpy(k, k_, (uint32_t)48U * sizeof (k_[0U]));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)49U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)48U * sizeof (v[0U]));
          if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)49U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
          }
          input[48U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_384(k_0, k, (uint32_t)48U, input, input_len0);
          Hacl_HMAC_compute_sha2_384(v, k_0, (uint32_t)48U, v, (uint32_t)48U);
          memcpy(k, k_0, (uint32_t)48U * sizeof (k_0[0U]));
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
        uint8_t *uu____9;
        if (seed_material == NULL)
        {
          uu____9 = NULL;
        }
        else
        {
          uu____9 = seed_material + entropy_input_len;
        }
        bool uu____10 = additional_input_input == NULL;
        if (!(uu____10 || uu____9 == NULL))
        {
          memcpy(uu____9,
            additional_input_input,
            additional_input_input_len * sizeof (additional_input_input[0U]));
        }
        Hacl_HMAC_DRBG_state uu____11 = st;
        uint8_t *k = uu____11.k;
        uint8_t *v = uu____11.v;
        uint32_t *ctr = uu____11.reseed_counter;
        uint32_t input_len = (uint32_t)65U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)64U * sizeof (v[0U]));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)65U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
        }
        input0[64U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_512(k_, k, (uint32_t)64U, input0, input_len);
        Hacl_HMAC_compute_sha2_512(v, k_, (uint32_t)64U, v, (uint32_t)64U);
        memcpy(k, k_, (uint32_t)64U * sizeof (k_[0U]));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)65U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)64U * sizeof (v[0U]));
          if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)65U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
          }
          input[64U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_512(k_0, k, (uint32_t)64U, input, input_len0);
          Hacl_HMAC_compute_sha2_512(v, k_0, (uint32_t)64U, v, (uint32_t)64U);
          memcpy(k, k_0, (uint32_t)64U * sizeof (k_0[0U]));
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
        if (additional_input_len > (uint32_t)0U)
        {
          uint32_t input_len = (uint32_t)21U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
          uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
          memset(input0, 0U, input_len * sizeof (input0[0U]));
          uint8_t *k_ = input0;
          memcpy(k_, v, (uint32_t)20U * sizeof (v[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input0 + (uint32_t)21U,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
          input0[20U] = (uint8_t)0U;
          Hacl_HMAC_legacy_compute_sha1(k_, k, (uint32_t)20U, input0, input_len);
          Hacl_HMAC_legacy_compute_sha1(v, k_, (uint32_t)20U, v, (uint32_t)20U);
          memcpy(k, k_, (uint32_t)20U * sizeof (k_[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            uint32_t input_len0 = (uint32_t)21U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
            uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
            memset(input, 0U, input_len0 * sizeof (input[0U]));
            uint8_t *k_0 = input;
            memcpy(k_0, v, (uint32_t)20U * sizeof (v[0U]));
            if (additional_input_len != (uint32_t)0U)
            {
              memcpy(input + (uint32_t)21U,
                additional_input,
                additional_input_len * sizeof (additional_input[0U]));
            }
            input[20U] = (uint8_t)1U;
            Hacl_HMAC_legacy_compute_sha1(k_0, k, (uint32_t)20U, input, input_len0);
            Hacl_HMAC_legacy_compute_sha1(v, k_0, (uint32_t)20U, v, (uint32_t)20U);
            memcpy(k, k_0, (uint32_t)20U * sizeof (k_0[0U]));
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
          Hacl_HMAC_legacy_compute_sha1(v, k, (uint32_t)20U, v, (uint32_t)20U);
          memcpy(out + i * (uint32_t)20U, v, (uint32_t)20U * sizeof (v[0U]));
        }
        if (max * (uint32_t)20U < n)
        {
          uint8_t *block = output1 + max * (uint32_t)20U;
          Hacl_HMAC_legacy_compute_sha1(v, k, (uint32_t)20U, v, (uint32_t)20U);
          memcpy(block, v, (n - max * (uint32_t)20U) * sizeof (v[0U]));
        }
        uint32_t input_len = (uint32_t)21U + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)20U * sizeof (v[0U]));
        if (additional_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)21U,
            additional_input,
            additional_input_len * sizeof (additional_input[0U]));
        }
        input0[20U] = (uint8_t)0U;
        Hacl_HMAC_legacy_compute_sha1(k_, k, (uint32_t)20U, input0, input_len);
        Hacl_HMAC_legacy_compute_sha1(v, k_, (uint32_t)20U, v, (uint32_t)20U);
        memcpy(k, k_, (uint32_t)20U * sizeof (k_[0U]));
        if (additional_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)21U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)20U * sizeof (v[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)21U,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
          input[20U] = (uint8_t)1U;
          Hacl_HMAC_legacy_compute_sha1(k_0, k, (uint32_t)20U, input, input_len0);
          Hacl_HMAC_legacy_compute_sha1(v, k_0, (uint32_t)20U, v, (uint32_t)20U);
          memcpy(k, k_0, (uint32_t)20U * sizeof (k_0[0U]));
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
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
        if (additional_input_len > (uint32_t)0U)
        {
          uint32_t input_len = (uint32_t)33U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
          uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
          memset(input0, 0U, input_len * sizeof (input0[0U]));
          uint8_t *k_ = input0;
          memcpy(k_, v, (uint32_t)32U * sizeof (v[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input0 + (uint32_t)33U,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
          input0[32U] = (uint8_t)0U;
          Hacl_HMAC_compute_sha2_256(k_, k, (uint32_t)32U, input0, input_len);
          Hacl_HMAC_compute_sha2_256(v, k_, (uint32_t)32U, v, (uint32_t)32U);
          memcpy(k, k_, (uint32_t)32U * sizeof (k_[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            uint32_t input_len0 = (uint32_t)33U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
            uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
            memset(input, 0U, input_len0 * sizeof (input[0U]));
            uint8_t *k_0 = input;
            memcpy(k_0, v, (uint32_t)32U * sizeof (v[0U]));
            if (additional_input_len != (uint32_t)0U)
            {
              memcpy(input + (uint32_t)33U,
                additional_input,
                additional_input_len * sizeof (additional_input[0U]));
            }
            input[32U] = (uint8_t)1U;
            Hacl_HMAC_compute_sha2_256(k_0, k, (uint32_t)32U, input, input_len0);
            Hacl_HMAC_compute_sha2_256(v, k_0, (uint32_t)32U, v, (uint32_t)32U);
            memcpy(k, k_0, (uint32_t)32U * sizeof (k_0[0U]));
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
          Hacl_HMAC_compute_sha2_256(v, k, (uint32_t)32U, v, (uint32_t)32U);
          memcpy(out + i * (uint32_t)32U, v, (uint32_t)32U * sizeof (v[0U]));
        }
        if (max * (uint32_t)32U < n)
        {
          uint8_t *block = output1 + max * (uint32_t)32U;
          Hacl_HMAC_compute_sha2_256(v, k, (uint32_t)32U, v, (uint32_t)32U);
          memcpy(block, v, (n - max * (uint32_t)32U) * sizeof (v[0U]));
        }
        uint32_t input_len = (uint32_t)33U + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)32U * sizeof (v[0U]));
        if (additional_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)33U,
            additional_input,
            additional_input_len * sizeof (additional_input[0U]));
        }
        input0[32U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_256(k_, k, (uint32_t)32U, input0, input_len);
        Hacl_HMAC_compute_sha2_256(v, k_, (uint32_t)32U, v, (uint32_t)32U);
        memcpy(k, k_, (uint32_t)32U * sizeof (k_[0U]));
        if (additional_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)33U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)32U * sizeof (v[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)33U,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
          input[32U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_256(k_0, k, (uint32_t)32U, input, input_len0);
          Hacl_HMAC_compute_sha2_256(v, k_0, (uint32_t)32U, v, (uint32_t)32U);
          memcpy(k, k_0, (uint32_t)32U * sizeof (k_0[0U]));
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
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
        if (additional_input_len > (uint32_t)0U)
        {
          uint32_t input_len = (uint32_t)49U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
          uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
          memset(input0, 0U, input_len * sizeof (input0[0U]));
          uint8_t *k_ = input0;
          memcpy(k_, v, (uint32_t)48U * sizeof (v[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input0 + (uint32_t)49U,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
          input0[48U] = (uint8_t)0U;
          Hacl_HMAC_compute_sha2_384(k_, k, (uint32_t)48U, input0, input_len);
          Hacl_HMAC_compute_sha2_384(v, k_, (uint32_t)48U, v, (uint32_t)48U);
          memcpy(k, k_, (uint32_t)48U * sizeof (k_[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            uint32_t input_len0 = (uint32_t)49U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
            uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
            memset(input, 0U, input_len0 * sizeof (input[0U]));
            uint8_t *k_0 = input;
            memcpy(k_0, v, (uint32_t)48U * sizeof (v[0U]));
            if (additional_input_len != (uint32_t)0U)
            {
              memcpy(input + (uint32_t)49U,
                additional_input,
                additional_input_len * sizeof (additional_input[0U]));
            }
            input[48U] = (uint8_t)1U;
            Hacl_HMAC_compute_sha2_384(k_0, k, (uint32_t)48U, input, input_len0);
            Hacl_HMAC_compute_sha2_384(v, k_0, (uint32_t)48U, v, (uint32_t)48U);
            memcpy(k, k_0, (uint32_t)48U * sizeof (k_0[0U]));
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
          Hacl_HMAC_compute_sha2_384(v, k, (uint32_t)48U, v, (uint32_t)48U);
          memcpy(out + i * (uint32_t)48U, v, (uint32_t)48U * sizeof (v[0U]));
        }
        if (max * (uint32_t)48U < n)
        {
          uint8_t *block = output1 + max * (uint32_t)48U;
          Hacl_HMAC_compute_sha2_384(v, k, (uint32_t)48U, v, (uint32_t)48U);
          memcpy(block, v, (n - max * (uint32_t)48U) * sizeof (v[0U]));
        }
        uint32_t input_len = (uint32_t)49U + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)48U * sizeof (v[0U]));
        if (additional_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)49U,
            additional_input,
            additional_input_len * sizeof (additional_input[0U]));
        }
        input0[48U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_384(k_, k, (uint32_t)48U, input0, input_len);
        Hacl_HMAC_compute_sha2_384(v, k_, (uint32_t)48U, v, (uint32_t)48U);
        memcpy(k, k_, (uint32_t)48U * sizeof (k_[0U]));
        if (additional_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)49U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)48U * sizeof (v[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)49U,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
          input[48U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_384(k_0, k, (uint32_t)48U, input, input_len0);
          Hacl_HMAC_compute_sha2_384(v, k_0, (uint32_t)48U, v, (uint32_t)48U);
          memcpy(k, k_0, (uint32_t)48U * sizeof (k_0[0U]));
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
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
        if (additional_input_len > (uint32_t)0U)
        {
          uint32_t input_len = (uint32_t)65U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
          uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
          memset(input0, 0U, input_len * sizeof (input0[0U]));
          uint8_t *k_ = input0;
          memcpy(k_, v, (uint32_t)64U * sizeof (v[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input0 + (uint32_t)65U,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
          input0[64U] = (uint8_t)0U;
          Hacl_HMAC_compute_sha2_512(k_, k, (uint32_t)64U, input0, input_len);
          Hacl_HMAC_compute_sha2_512(v, k_, (uint32_t)64U, v, (uint32_t)64U);
          memcpy(k, k_, (uint32_t)64U * sizeof (k_[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            uint32_t input_len0 = (uint32_t)65U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
            uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
            memset(input, 0U, input_len0 * sizeof (input[0U]));
            uint8_t *k_0 = input;
            memcpy(k_0, v, (uint32_t)64U * sizeof (v[0U]));
            if (additional_input_len != (uint32_t)0U)
            {
              memcpy(input + (uint32_t)65U,
                additional_input,
                additional_input_len * sizeof (additional_input[0U]));
            }
            input[64U] = (uint8_t)1U;
            Hacl_HMAC_compute_sha2_512(k_0, k, (uint32_t)64U, input, input_len0);
            Hacl_HMAC_compute_sha2_512(v, k_0, (uint32_t)64U, v, (uint32_t)64U);
            memcpy(k, k_0, (uint32_t)64U * sizeof (k_0[0U]));
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
          Hacl_HMAC_compute_sha2_512(v, k, (uint32_t)64U, v, (uint32_t)64U);
          memcpy(out + i * (uint32_t)64U, v, (uint32_t)64U * sizeof (v[0U]));
        }
        if (max * (uint32_t)64U < n)
        {
          uint8_t *block = output1 + max * (uint32_t)64U;
          Hacl_HMAC_compute_sha2_512(v, k, (uint32_t)64U, v, (uint32_t)64U);
          memcpy(block, v, (n - max * (uint32_t)64U) * sizeof (v[0U]));
        }
        uint32_t input_len = (uint32_t)65U + additional_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t *input0 = alloca(input_len * sizeof (uint8_t));
        memset(input0, 0U, input_len * sizeof (input0[0U]));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)64U * sizeof (v[0U]));
        if (additional_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)65U,
            additional_input,
            additional_input_len * sizeof (additional_input[0U]));
        }
        input0[64U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_512(k_, k, (uint32_t)64U, input0, input_len);
        Hacl_HMAC_compute_sha2_512(v, k_, (uint32_t)64U, v, (uint32_t)64U);
        memcpy(k, k_, (uint32_t)64U * sizeof (k_[0U]));
        if (additional_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)65U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t *input = alloca(input_len0 * sizeof (uint8_t));
          memset(input, 0U, input_len0 * sizeof (input[0U]));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)64U * sizeof (v[0U]));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)65U,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
          input[64U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_512(k_0, k, (uint32_t)64U, input, input_len0);
          Hacl_HMAC_compute_sha2_512(v, k_0, (uint32_t)64U, v, (uint32_t)64U);
          memcpy(k, k_0, (uint32_t)64U * sizeof (k_0[0U]));
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

