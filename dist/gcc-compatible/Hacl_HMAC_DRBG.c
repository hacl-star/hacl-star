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
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
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
              (entropy_input_len + nonce_len + personalization_string_len)
              * sizeof (seed_material[0U]));
          }
        }
        input0[20U] = (uint8_t)0U;
        Hacl_HMAC_legacy_compute_sha1(k_, k, (uint32_t)20U, input0, input_len);
        Hacl_HMAC_legacy_compute_sha1(v, k_, (uint32_t)20U, v, (uint32_t)20U);
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
                (entropy_input_len + nonce_len + personalization_string_len)
                * sizeof (seed_material[0U]));
            }
          }
          input[20U] = (uint8_t)1U;
          Hacl_HMAC_legacy_compute_sha1(k_0, k, (uint32_t)20U, input, input_len0);
          Hacl_HMAC_legacy_compute_sha1(v, k_0, (uint32_t)20U, v, (uint32_t)20U);
          bool uu____13 = k_0 == NULL;
          if (!(uu____13 || k == NULL))
          {
            memcpy(k, k_0, (uint32_t)20U * sizeof (k_0[0U]));
          }
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t),
          entropy_input_len + nonce_len + personalization_string_len);
        uint8_t seed_material[entropy_input_len + nonce_len + personalization_string_len];
        memset(seed_material,
          0U,
          (entropy_input_len + nonce_len + personalization_string_len) * sizeof (seed_material[0U]));
        uint8_t *uu____14;
        if (seed_material == NULL)
        {
          uu____14 = NULL;
        }
        else
        {
          uu____14 = seed_material;
        }
        bool uu____15 = entropy_input == NULL;
        if (!(uu____15 || uu____14 == NULL))
        {
          memcpy(uu____14, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
        }
        uint8_t *uu____16;
        if (seed_material == NULL)
        {
          uu____16 = NULL;
        }
        else
        {
          uu____16 = seed_material + entropy_input_len;
        }
        bool uu____17 = nonce == NULL;
        if (!(uu____17 || uu____16 == NULL))
        {
          memcpy(uu____16, nonce, nonce_len * sizeof (nonce[0U]));
        }
        uint8_t *uu____18;
        if (seed_material == NULL)
        {
          uu____18 = NULL;
        }
        else
        {
          uu____18 = seed_material + entropy_input_len + nonce_len;
        }
        bool uu____19 = personalization_string == NULL;
        if (!(uu____19 || uu____18 == NULL))
        {
          memcpy(uu____18,
            personalization_string,
            personalization_string_len * sizeof (personalization_string[0U]));
        }
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
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
        bool uu____20 = v == NULL;
        if (!(uu____20 || k_ == NULL))
        {
          memcpy(k_, v, (uint32_t)32U * sizeof (v[0U]));
        }
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          uint8_t *uu____21;
          if (input0 == NULL)
          {
            uu____21 = NULL;
          }
          else
          {
            uu____21 = input0 + (uint32_t)33U;
          }
          bool uu____22 = seed_material == NULL;
          if (!(uu____22 || uu____21 == NULL))
          {
            memcpy(uu____21,
              seed_material,
              (entropy_input_len + nonce_len + personalization_string_len)
              * sizeof (seed_material[0U]));
          }
        }
        input0[32U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_256(k_, k, (uint32_t)32U, input0, input_len);
        Hacl_HMAC_compute_sha2_256(v, k_, (uint32_t)32U, v, (uint32_t)32U);
        bool uu____23 = k_ == NULL;
        if (!(uu____23 || k == NULL))
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
          bool uu____24 = v == NULL;
          if (!(uu____24 || k_0 == NULL))
          {
            memcpy(k_0, v, (uint32_t)32U * sizeof (v[0U]));
          }
          if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
          {
            uint8_t *uu____25;
            if (input == NULL)
            {
              uu____25 = NULL;
            }
            else
            {
              uu____25 = input + (uint32_t)33U;
            }
            bool uu____26 = seed_material == NULL;
            if (!(uu____26 || uu____25 == NULL))
            {
              memcpy(uu____25,
                seed_material,
                (entropy_input_len + nonce_len + personalization_string_len)
                * sizeof (seed_material[0U]));
            }
          }
          input[32U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_256(k_0, k, (uint32_t)32U, input, input_len0);
          Hacl_HMAC_compute_sha2_256(v, k_0, (uint32_t)32U, v, (uint32_t)32U);
          bool uu____27 = k_0 == NULL;
          if (!(uu____27 || k == NULL))
          {
            memcpy(k, k_0, (uint32_t)32U * sizeof (k_0[0U]));
          }
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t),
          entropy_input_len + nonce_len + personalization_string_len);
        uint8_t seed_material[entropy_input_len + nonce_len + personalization_string_len];
        memset(seed_material,
          0U,
          (entropy_input_len + nonce_len + personalization_string_len) * sizeof (seed_material[0U]));
        uint8_t *uu____28;
        if (seed_material == NULL)
        {
          uu____28 = NULL;
        }
        else
        {
          uu____28 = seed_material;
        }
        bool uu____29 = entropy_input == NULL;
        if (!(uu____29 || uu____28 == NULL))
        {
          memcpy(uu____28, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
        }
        uint8_t *uu____30;
        if (seed_material == NULL)
        {
          uu____30 = NULL;
        }
        else
        {
          uu____30 = seed_material + entropy_input_len;
        }
        bool uu____31 = nonce == NULL;
        if (!(uu____31 || uu____30 == NULL))
        {
          memcpy(uu____30, nonce, nonce_len * sizeof (nonce[0U]));
        }
        uint8_t *uu____32;
        if (seed_material == NULL)
        {
          uu____32 = NULL;
        }
        else
        {
          uu____32 = seed_material + entropy_input_len + nonce_len;
        }
        bool uu____33 = personalization_string == NULL;
        if (!(uu____33 || uu____32 == NULL))
        {
          memcpy(uu____32,
            personalization_string,
            personalization_string_len * sizeof (personalization_string[0U]));
        }
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
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
        bool uu____34 = v == NULL;
        if (!(uu____34 || k_ == NULL))
        {
          memcpy(k_, v, (uint32_t)48U * sizeof (v[0U]));
        }
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          uint8_t *uu____35;
          if (input0 == NULL)
          {
            uu____35 = NULL;
          }
          else
          {
            uu____35 = input0 + (uint32_t)49U;
          }
          bool uu____36 = seed_material == NULL;
          if (!(uu____36 || uu____35 == NULL))
          {
            memcpy(uu____35,
              seed_material,
              (entropy_input_len + nonce_len + personalization_string_len)
              * sizeof (seed_material[0U]));
          }
        }
        input0[48U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_384(k_, k, (uint32_t)48U, input0, input_len);
        Hacl_HMAC_compute_sha2_384(v, k_, (uint32_t)48U, v, (uint32_t)48U);
        bool uu____37 = k_ == NULL;
        if (!(uu____37 || k == NULL))
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
          bool uu____38 = v == NULL;
          if (!(uu____38 || k_0 == NULL))
          {
            memcpy(k_0, v, (uint32_t)48U * sizeof (v[0U]));
          }
          if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
          {
            uint8_t *uu____39;
            if (input == NULL)
            {
              uu____39 = NULL;
            }
            else
            {
              uu____39 = input + (uint32_t)49U;
            }
            bool uu____40 = seed_material == NULL;
            if (!(uu____40 || uu____39 == NULL))
            {
              memcpy(uu____39,
                seed_material,
                (entropy_input_len + nonce_len + personalization_string_len)
                * sizeof (seed_material[0U]));
            }
          }
          input[48U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_384(k_0, k, (uint32_t)48U, input, input_len0);
          Hacl_HMAC_compute_sha2_384(v, k_0, (uint32_t)48U, v, (uint32_t)48U);
          bool uu____41 = k_0 == NULL;
          if (!(uu____41 || k == NULL))
          {
            memcpy(k, k_0, (uint32_t)48U * sizeof (k_0[0U]));
          }
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t),
          entropy_input_len + nonce_len + personalization_string_len);
        uint8_t seed_material[entropy_input_len + nonce_len + personalization_string_len];
        memset(seed_material,
          0U,
          (entropy_input_len + nonce_len + personalization_string_len) * sizeof (seed_material[0U]));
        uint8_t *uu____42;
        if (seed_material == NULL)
        {
          uu____42 = NULL;
        }
        else
        {
          uu____42 = seed_material;
        }
        bool uu____43 = entropy_input == NULL;
        if (!(uu____43 || uu____42 == NULL))
        {
          memcpy(uu____42, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
        }
        uint8_t *uu____44;
        if (seed_material == NULL)
        {
          uu____44 = NULL;
        }
        else
        {
          uu____44 = seed_material + entropy_input_len;
        }
        bool uu____45 = nonce == NULL;
        if (!(uu____45 || uu____44 == NULL))
        {
          memcpy(uu____44, nonce, nonce_len * sizeof (nonce[0U]));
        }
        uint8_t *uu____46;
        if (seed_material == NULL)
        {
          uu____46 = NULL;
        }
        else
        {
          uu____46 = seed_material + entropy_input_len + nonce_len;
        }
        bool uu____47 = personalization_string == NULL;
        if (!(uu____47 || uu____46 == NULL))
        {
          memcpy(uu____46,
            personalization_string,
            personalization_string_len * sizeof (personalization_string[0U]));
        }
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
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
        bool uu____48 = v == NULL;
        if (!(uu____48 || k_ == NULL))
        {
          memcpy(k_, v, (uint32_t)64U * sizeof (v[0U]));
        }
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          uint8_t *uu____49;
          if (input0 == NULL)
          {
            uu____49 = NULL;
          }
          else
          {
            uu____49 = input0 + (uint32_t)65U;
          }
          bool uu____50 = seed_material == NULL;
          if (!(uu____50 || uu____49 == NULL))
          {
            memcpy(uu____49,
              seed_material,
              (entropy_input_len + nonce_len + personalization_string_len)
              * sizeof (seed_material[0U]));
          }
        }
        input0[64U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_512(k_, k, (uint32_t)64U, input0, input_len);
        Hacl_HMAC_compute_sha2_512(v, k_, (uint32_t)64U, v, (uint32_t)64U);
        bool uu____51 = k_ == NULL;
        if (!(uu____51 || k == NULL))
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
          bool uu____52 = v == NULL;
          if (!(uu____52 || k_0 == NULL))
          {
            memcpy(k_0, v, (uint32_t)64U * sizeof (v[0U]));
          }
          if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
          {
            uint8_t *uu____53;
            if (input == NULL)
            {
              uu____53 = NULL;
            }
            else
            {
              uu____53 = input + (uint32_t)65U;
            }
            bool uu____54 = seed_material == NULL;
            if (!(uu____54 || uu____53 == NULL))
            {
              memcpy(uu____53,
                seed_material,
                (entropy_input_len + nonce_len + personalization_string_len)
                * sizeof (seed_material[0U]));
            }
          }
          input[64U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_512(k_0, k, (uint32_t)64U, input, input_len0);
          Hacl_HMAC_compute_sha2_512(v, k_0, (uint32_t)64U, v, (uint32_t)64U);
          bool uu____55 = k_0 == NULL;
          if (!(uu____55 || k == NULL))
          {
            memcpy(k, k_0, (uint32_t)64U * sizeof (k_0[0U]));
          }
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
        uint8_t seed_material[entropy_input_len + additional_input_input_len];
        memset(seed_material,
          0U,
          (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
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
        bool uu____3 = additional_input_input == NULL;
        if (!(uu____3 || uu____2 == NULL))
        {
          memcpy(uu____2,
            additional_input_input,
            additional_input_input_len * sizeof (additional_input_input[0U]));
        }
        Hacl_HMAC_DRBG_state uu____4 = st;
        uint8_t *k = uu____4.k;
        uint8_t *v = uu____4.v;
        uint32_t *ctr = uu____4.reseed_counter;
        uint32_t input_len = (uint32_t)21U + entropy_input_len + additional_input_input_len;
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
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
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
              (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
          }
        }
        input0[20U] = (uint8_t)0U;
        Hacl_HMAC_legacy_compute_sha1(k_, k, (uint32_t)20U, input0, input_len);
        Hacl_HMAC_legacy_compute_sha1(v, k_, (uint32_t)20U, v, (uint32_t)20U);
        bool uu____8 = k_ == NULL;
        if (!(uu____8 || k == NULL))
        {
          memcpy(k, k_, (uint32_t)20U * sizeof (k_[0U]));
        }
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)21U + entropy_input_len + additional_input_input_len;
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
          if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
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
                (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
            }
          }
          input[20U] = (uint8_t)1U;
          Hacl_HMAC_legacy_compute_sha1(k_0, k, (uint32_t)20U, input, input_len0);
          Hacl_HMAC_legacy_compute_sha1(v, k_0, (uint32_t)20U, v, (uint32_t)20U);
          bool uu____12 = k_0 == NULL;
          if (!(uu____12 || k == NULL))
          {
            memcpy(k, k_0, (uint32_t)20U * sizeof (k_0[0U]));
          }
        }
        ctr[0U] = (uint32_t)1U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_input_len);
        uint8_t seed_material[entropy_input_len + additional_input_input_len];
        memset(seed_material,
          0U,
          (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
        uint8_t *uu____13;
        if (seed_material == NULL)
        {
          uu____13 = NULL;
        }
        else
        {
          uu____13 = seed_material;
        }
        bool uu____14 = entropy_input == NULL;
        if (!(uu____14 || uu____13 == NULL))
        {
          memcpy(uu____13, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
        }
        uint8_t *uu____15;
        if (seed_material == NULL)
        {
          uu____15 = NULL;
        }
        else
        {
          uu____15 = seed_material + entropy_input_len;
        }
        bool uu____16 = additional_input_input == NULL;
        if (!(uu____16 || uu____15 == NULL))
        {
          memcpy(uu____15,
            additional_input_input,
            additional_input_input_len * sizeof (additional_input_input[0U]));
        }
        Hacl_HMAC_DRBG_state uu____17 = st;
        uint8_t *k = uu____17.k;
        uint8_t *v = uu____17.v;
        uint32_t *ctr = uu____17.reseed_counter;
        uint32_t input_len = (uint32_t)33U + entropy_input_len + additional_input_input_len;
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
        bool uu____18 = v == NULL;
        if (!(uu____18 || k_ == NULL))
        {
          memcpy(k_, v, (uint32_t)32U * sizeof (v[0U]));
        }
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          uint8_t *uu____19;
          if (input0 == NULL)
          {
            uu____19 = NULL;
          }
          else
          {
            uu____19 = input0 + (uint32_t)33U;
          }
          bool uu____20 = seed_material == NULL;
          if (!(uu____20 || uu____19 == NULL))
          {
            memcpy(uu____19,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
          }
        }
        input0[32U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_256(k_, k, (uint32_t)32U, input0, input_len);
        Hacl_HMAC_compute_sha2_256(v, k_, (uint32_t)32U, v, (uint32_t)32U);
        bool uu____21 = k_ == NULL;
        if (!(uu____21 || k == NULL))
        {
          memcpy(k, k_, (uint32_t)32U * sizeof (k_[0U]));
        }
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)33U + entropy_input_len + additional_input_input_len;
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
          bool uu____22 = v == NULL;
          if (!(uu____22 || k_0 == NULL))
          {
            memcpy(k_0, v, (uint32_t)32U * sizeof (v[0U]));
          }
          if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
          {
            uint8_t *uu____23;
            if (input == NULL)
            {
              uu____23 = NULL;
            }
            else
            {
              uu____23 = input + (uint32_t)33U;
            }
            bool uu____24 = seed_material == NULL;
            if (!(uu____24 || uu____23 == NULL))
            {
              memcpy(uu____23,
                seed_material,
                (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
            }
          }
          input[32U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_256(k_0, k, (uint32_t)32U, input, input_len0);
          Hacl_HMAC_compute_sha2_256(v, k_0, (uint32_t)32U, v, (uint32_t)32U);
          bool uu____25 = k_0 == NULL;
          if (!(uu____25 || k == NULL))
          {
            memcpy(k, k_0, (uint32_t)32U * sizeof (k_0[0U]));
          }
        }
        ctr[0U] = (uint32_t)1U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_input_len);
        uint8_t seed_material[entropy_input_len + additional_input_input_len];
        memset(seed_material,
          0U,
          (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
        uint8_t *uu____26;
        if (seed_material == NULL)
        {
          uu____26 = NULL;
        }
        else
        {
          uu____26 = seed_material;
        }
        bool uu____27 = entropy_input == NULL;
        if (!(uu____27 || uu____26 == NULL))
        {
          memcpy(uu____26, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
        }
        uint8_t *uu____28;
        if (seed_material == NULL)
        {
          uu____28 = NULL;
        }
        else
        {
          uu____28 = seed_material + entropy_input_len;
        }
        bool uu____29 = additional_input_input == NULL;
        if (!(uu____29 || uu____28 == NULL))
        {
          memcpy(uu____28,
            additional_input_input,
            additional_input_input_len * sizeof (additional_input_input[0U]));
        }
        Hacl_HMAC_DRBG_state uu____30 = st;
        uint8_t *k = uu____30.k;
        uint8_t *v = uu____30.v;
        uint32_t *ctr = uu____30.reseed_counter;
        uint32_t input_len = (uint32_t)49U + entropy_input_len + additional_input_input_len;
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
        bool uu____31 = v == NULL;
        if (!(uu____31 || k_ == NULL))
        {
          memcpy(k_, v, (uint32_t)48U * sizeof (v[0U]));
        }
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          uint8_t *uu____32;
          if (input0 == NULL)
          {
            uu____32 = NULL;
          }
          else
          {
            uu____32 = input0 + (uint32_t)49U;
          }
          bool uu____33 = seed_material == NULL;
          if (!(uu____33 || uu____32 == NULL))
          {
            memcpy(uu____32,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
          }
        }
        input0[48U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_384(k_, k, (uint32_t)48U, input0, input_len);
        Hacl_HMAC_compute_sha2_384(v, k_, (uint32_t)48U, v, (uint32_t)48U);
        bool uu____34 = k_ == NULL;
        if (!(uu____34 || k == NULL))
        {
          memcpy(k, k_, (uint32_t)48U * sizeof (k_[0U]));
        }
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)49U + entropy_input_len + additional_input_input_len;
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
          bool uu____35 = v == NULL;
          if (!(uu____35 || k_0 == NULL))
          {
            memcpy(k_0, v, (uint32_t)48U * sizeof (v[0U]));
          }
          if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
          {
            uint8_t *uu____36;
            if (input == NULL)
            {
              uu____36 = NULL;
            }
            else
            {
              uu____36 = input + (uint32_t)49U;
            }
            bool uu____37 = seed_material == NULL;
            if (!(uu____37 || uu____36 == NULL))
            {
              memcpy(uu____36,
                seed_material,
                (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
            }
          }
          input[48U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_384(k_0, k, (uint32_t)48U, input, input_len0);
          Hacl_HMAC_compute_sha2_384(v, k_0, (uint32_t)48U, v, (uint32_t)48U);
          bool uu____38 = k_0 == NULL;
          if (!(uu____38 || k == NULL))
          {
            memcpy(k, k_0, (uint32_t)48U * sizeof (k_0[0U]));
          }
        }
        ctr[0U] = (uint32_t)1U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_input_len);
        uint8_t seed_material[entropy_input_len + additional_input_input_len];
        memset(seed_material,
          0U,
          (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
        uint8_t *uu____39;
        if (seed_material == NULL)
        {
          uu____39 = NULL;
        }
        else
        {
          uu____39 = seed_material;
        }
        bool uu____40 = entropy_input == NULL;
        if (!(uu____40 || uu____39 == NULL))
        {
          memcpy(uu____39, entropy_input, entropy_input_len * sizeof (entropy_input[0U]));
        }
        uint8_t *uu____41;
        if (seed_material == NULL)
        {
          uu____41 = NULL;
        }
        else
        {
          uu____41 = seed_material + entropy_input_len;
        }
        bool uu____42 = additional_input_input == NULL;
        if (!(uu____42 || uu____41 == NULL))
        {
          memcpy(uu____41,
            additional_input_input,
            additional_input_input_len * sizeof (additional_input_input[0U]));
        }
        Hacl_HMAC_DRBG_state uu____43 = st;
        uint8_t *k = uu____43.k;
        uint8_t *v = uu____43.v;
        uint32_t *ctr = uu____43.reseed_counter;
        uint32_t input_len = (uint32_t)65U + entropy_input_len + additional_input_input_len;
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
        bool uu____44 = v == NULL;
        if (!(uu____44 || k_ == NULL))
        {
          memcpy(k_, v, (uint32_t)64U * sizeof (v[0U]));
        }
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          uint8_t *uu____45;
          if (input0 == NULL)
          {
            uu____45 = NULL;
          }
          else
          {
            uu____45 = input0 + (uint32_t)65U;
          }
          bool uu____46 = seed_material == NULL;
          if (!(uu____46 || uu____45 == NULL))
          {
            memcpy(uu____45,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
          }
        }
        input0[64U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_512(k_, k, (uint32_t)64U, input0, input_len);
        Hacl_HMAC_compute_sha2_512(v, k_, (uint32_t)64U, v, (uint32_t)64U);
        bool uu____47 = k_ == NULL;
        if (!(uu____47 || k == NULL))
        {
          memcpy(k, k_, (uint32_t)64U * sizeof (k_[0U]));
        }
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)65U + entropy_input_len + additional_input_input_len;
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
          bool uu____48 = v == NULL;
          if (!(uu____48 || k_0 == NULL))
          {
            memcpy(k_0, v, (uint32_t)64U * sizeof (v[0U]));
          }
          if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
          {
            uint8_t *uu____49;
            if (input == NULL)
            {
              uu____49 = NULL;
            }
            else
            {
              uu____49 = input + (uint32_t)65U;
            }
            bool uu____50 = seed_material == NULL;
            if (!(uu____50 || uu____49 == NULL))
            {
              memcpy(uu____49,
                seed_material,
                (entropy_input_len + additional_input_input_len) * sizeof (seed_material[0U]));
            }
          }
          input[64U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_512(k_0, k, (uint32_t)64U, input, input_len0);
          Hacl_HMAC_compute_sha2_512(v, k_0, (uint32_t)64U, v, (uint32_t)64U);
          bool uu____51 = k_0 == NULL;
          if (!(uu____51 || k == NULL))
          {
            memcpy(k, k_0, (uint32_t)64U * sizeof (k_0[0U]));
          }
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
          bool uu____0 = v == NULL;
          if (!(uu____0 || k_ == NULL))
          {
            memcpy(k_, v, (uint32_t)20U * sizeof (v[0U]));
          }
          if (additional_input_len != (uint32_t)0U)
          {
            uint8_t *uu____1;
            if (input0 == NULL)
            {
              uu____1 = NULL;
            }
            else
            {
              uu____1 = input0 + (uint32_t)21U;
            }
            bool uu____2 = additional_input == NULL;
            if (!(uu____2 || uu____1 == NULL))
            {
              memcpy(uu____1,
                additional_input,
                additional_input_len * sizeof (additional_input[0U]));
            }
          }
          input0[20U] = (uint8_t)0U;
          Hacl_HMAC_legacy_compute_sha1(k_, k, (uint32_t)20U, input0, input_len);
          Hacl_HMAC_legacy_compute_sha1(v, k_, (uint32_t)20U, v, (uint32_t)20U);
          bool uu____3 = k_ == NULL;
          if (!(uu____3 || k == NULL))
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
            bool uu____4 = v == NULL;
            if (!(uu____4 || k_0 == NULL))
            {
              memcpy(k_0, v, (uint32_t)20U * sizeof (v[0U]));
            }
            if (additional_input_len != (uint32_t)0U)
            {
              uint8_t *uu____5;
              if (input == NULL)
              {
                uu____5 = NULL;
              }
              else
              {
                uu____5 = input + (uint32_t)21U;
              }
              bool uu____6 = additional_input == NULL;
              if (!(uu____6 || uu____5 == NULL))
              {
                memcpy(uu____5,
                  additional_input,
                  additional_input_len * sizeof (additional_input[0U]));
              }
            }
            input[20U] = (uint8_t)1U;
            Hacl_HMAC_legacy_compute_sha1(k_0, k, (uint32_t)20U, input, input_len0);
            Hacl_HMAC_legacy_compute_sha1(v, k_0, (uint32_t)20U, v, (uint32_t)20U);
            bool uu____7 = k_0 == NULL;
            if (!(uu____7 || k == NULL))
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
          Hacl_HMAC_legacy_compute_sha1(v, k, (uint32_t)20U, v, (uint32_t)20U);
          uint8_t *uu____8;
          if (out == NULL)
          {
            uu____8 = NULL;
          }
          else
          {
            uu____8 = out + i * (uint32_t)20U;
          }
          bool uu____9 = v == NULL;
          if (!(uu____9 || uu____8 == NULL))
          {
            memcpy(uu____8, v, (uint32_t)20U * sizeof (v[0U]));
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
          Hacl_HMAC_legacy_compute_sha1(v, k, (uint32_t)20U, v, (uint32_t)20U);
          uint8_t *uu____10;
          if (v == NULL)
          {
            uu____10 = NULL;
          }
          else
          {
            uu____10 = v;
          }
          bool uu____11 = uu____10 == NULL;
          if (!(uu____11 || block == NULL))
          {
            memcpy(block, uu____10, (n - max * (uint32_t)20U) * sizeof (uu____10[0U]));
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
        bool uu____12 = v == NULL;
        if (!(uu____12 || k_ == NULL))
        {
          memcpy(k_, v, (uint32_t)20U * sizeof (v[0U]));
        }
        if (additional_input_len != (uint32_t)0U)
        {
          uint8_t *uu____13;
          if (input0 == NULL)
          {
            uu____13 = NULL;
          }
          else
          {
            uu____13 = input0 + (uint32_t)21U;
          }
          bool uu____14 = additional_input == NULL;
          if (!(uu____14 || uu____13 == NULL))
          {
            memcpy(uu____13,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
        }
        input0[20U] = (uint8_t)0U;
        Hacl_HMAC_legacy_compute_sha1(k_, k, (uint32_t)20U, input0, input_len);
        Hacl_HMAC_legacy_compute_sha1(v, k_, (uint32_t)20U, v, (uint32_t)20U);
        bool uu____15 = k_ == NULL;
        if (!(uu____15 || k == NULL))
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
          bool uu____16 = v == NULL;
          if (!(uu____16 || k_0 == NULL))
          {
            memcpy(k_0, v, (uint32_t)20U * sizeof (v[0U]));
          }
          if (additional_input_len != (uint32_t)0U)
          {
            uint8_t *uu____17;
            if (input == NULL)
            {
              uu____17 = NULL;
            }
            else
            {
              uu____17 = input + (uint32_t)21U;
            }
            bool uu____18 = additional_input == NULL;
            if (!(uu____18 || uu____17 == NULL))
            {
              memcpy(uu____17,
                additional_input,
                additional_input_len * sizeof (additional_input[0U]));
            }
          }
          input[20U] = (uint8_t)1U;
          Hacl_HMAC_legacy_compute_sha1(k_0, k, (uint32_t)20U, input, input_len0);
          Hacl_HMAC_legacy_compute_sha1(v, k_0, (uint32_t)20U, v, (uint32_t)20U);
          bool uu____19 = k_0 == NULL;
          if (!(uu____19 || k == NULL))
          {
            memcpy(k, k_0, (uint32_t)20U * sizeof (k_0[0U]));
          }
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
          bool uu____20 = v == NULL;
          if (!(uu____20 || k_ == NULL))
          {
            memcpy(k_, v, (uint32_t)32U * sizeof (v[0U]));
          }
          if (additional_input_len != (uint32_t)0U)
          {
            uint8_t *uu____21;
            if (input0 == NULL)
            {
              uu____21 = NULL;
            }
            else
            {
              uu____21 = input0 + (uint32_t)33U;
            }
            bool uu____22 = additional_input == NULL;
            if (!(uu____22 || uu____21 == NULL))
            {
              memcpy(uu____21,
                additional_input,
                additional_input_len * sizeof (additional_input[0U]));
            }
          }
          input0[32U] = (uint8_t)0U;
          Hacl_HMAC_compute_sha2_256(k_, k, (uint32_t)32U, input0, input_len);
          Hacl_HMAC_compute_sha2_256(v, k_, (uint32_t)32U, v, (uint32_t)32U);
          bool uu____23 = k_ == NULL;
          if (!(uu____23 || k == NULL))
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
            bool uu____24 = v == NULL;
            if (!(uu____24 || k_0 == NULL))
            {
              memcpy(k_0, v, (uint32_t)32U * sizeof (v[0U]));
            }
            if (additional_input_len != (uint32_t)0U)
            {
              uint8_t *uu____25;
              if (input == NULL)
              {
                uu____25 = NULL;
              }
              else
              {
                uu____25 = input + (uint32_t)33U;
              }
              bool uu____26 = additional_input == NULL;
              if (!(uu____26 || uu____25 == NULL))
              {
                memcpy(uu____25,
                  additional_input,
                  additional_input_len * sizeof (additional_input[0U]));
              }
            }
            input[32U] = (uint8_t)1U;
            Hacl_HMAC_compute_sha2_256(k_0, k, (uint32_t)32U, input, input_len0);
            Hacl_HMAC_compute_sha2_256(v, k_0, (uint32_t)32U, v, (uint32_t)32U);
            bool uu____27 = k_0 == NULL;
            if (!(uu____27 || k == NULL))
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
          Hacl_HMAC_compute_sha2_256(v, k, (uint32_t)32U, v, (uint32_t)32U);
          uint8_t *uu____28;
          if (out == NULL)
          {
            uu____28 = NULL;
          }
          else
          {
            uu____28 = out + i * (uint32_t)32U;
          }
          bool uu____29 = v == NULL;
          if (!(uu____29 || uu____28 == NULL))
          {
            memcpy(uu____28, v, (uint32_t)32U * sizeof (v[0U]));
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
          Hacl_HMAC_compute_sha2_256(v, k, (uint32_t)32U, v, (uint32_t)32U);
          uint8_t *uu____30;
          if (v == NULL)
          {
            uu____30 = NULL;
          }
          else
          {
            uu____30 = v;
          }
          bool uu____31 = uu____30 == NULL;
          if (!(uu____31 || block == NULL))
          {
            memcpy(block, uu____30, (n - max * (uint32_t)32U) * sizeof (uu____30[0U]));
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
        bool uu____32 = v == NULL;
        if (!(uu____32 || k_ == NULL))
        {
          memcpy(k_, v, (uint32_t)32U * sizeof (v[0U]));
        }
        if (additional_input_len != (uint32_t)0U)
        {
          uint8_t *uu____33;
          if (input0 == NULL)
          {
            uu____33 = NULL;
          }
          else
          {
            uu____33 = input0 + (uint32_t)33U;
          }
          bool uu____34 = additional_input == NULL;
          if (!(uu____34 || uu____33 == NULL))
          {
            memcpy(uu____33,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
        }
        input0[32U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_256(k_, k, (uint32_t)32U, input0, input_len);
        Hacl_HMAC_compute_sha2_256(v, k_, (uint32_t)32U, v, (uint32_t)32U);
        bool uu____35 = k_ == NULL;
        if (!(uu____35 || k == NULL))
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
          bool uu____36 = v == NULL;
          if (!(uu____36 || k_0 == NULL))
          {
            memcpy(k_0, v, (uint32_t)32U * sizeof (v[0U]));
          }
          if (additional_input_len != (uint32_t)0U)
          {
            uint8_t *uu____37;
            if (input == NULL)
            {
              uu____37 = NULL;
            }
            else
            {
              uu____37 = input + (uint32_t)33U;
            }
            bool uu____38 = additional_input == NULL;
            if (!(uu____38 || uu____37 == NULL))
            {
              memcpy(uu____37,
                additional_input,
                additional_input_len * sizeof (additional_input[0U]));
            }
          }
          input[32U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_256(k_0, k, (uint32_t)32U, input, input_len0);
          Hacl_HMAC_compute_sha2_256(v, k_0, (uint32_t)32U, v, (uint32_t)32U);
          bool uu____39 = k_0 == NULL;
          if (!(uu____39 || k == NULL))
          {
            memcpy(k, k_0, (uint32_t)32U * sizeof (k_0[0U]));
          }
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
          bool uu____40 = v == NULL;
          if (!(uu____40 || k_ == NULL))
          {
            memcpy(k_, v, (uint32_t)48U * sizeof (v[0U]));
          }
          if (additional_input_len != (uint32_t)0U)
          {
            uint8_t *uu____41;
            if (input0 == NULL)
            {
              uu____41 = NULL;
            }
            else
            {
              uu____41 = input0 + (uint32_t)49U;
            }
            bool uu____42 = additional_input == NULL;
            if (!(uu____42 || uu____41 == NULL))
            {
              memcpy(uu____41,
                additional_input,
                additional_input_len * sizeof (additional_input[0U]));
            }
          }
          input0[48U] = (uint8_t)0U;
          Hacl_HMAC_compute_sha2_384(k_, k, (uint32_t)48U, input0, input_len);
          Hacl_HMAC_compute_sha2_384(v, k_, (uint32_t)48U, v, (uint32_t)48U);
          bool uu____43 = k_ == NULL;
          if (!(uu____43 || k == NULL))
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
            bool uu____44 = v == NULL;
            if (!(uu____44 || k_0 == NULL))
            {
              memcpy(k_0, v, (uint32_t)48U * sizeof (v[0U]));
            }
            if (additional_input_len != (uint32_t)0U)
            {
              uint8_t *uu____45;
              if (input == NULL)
              {
                uu____45 = NULL;
              }
              else
              {
                uu____45 = input + (uint32_t)49U;
              }
              bool uu____46 = additional_input == NULL;
              if (!(uu____46 || uu____45 == NULL))
              {
                memcpy(uu____45,
                  additional_input,
                  additional_input_len * sizeof (additional_input[0U]));
              }
            }
            input[48U] = (uint8_t)1U;
            Hacl_HMAC_compute_sha2_384(k_0, k, (uint32_t)48U, input, input_len0);
            Hacl_HMAC_compute_sha2_384(v, k_0, (uint32_t)48U, v, (uint32_t)48U);
            bool uu____47 = k_0 == NULL;
            if (!(uu____47 || k == NULL))
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
          Hacl_HMAC_compute_sha2_384(v, k, (uint32_t)48U, v, (uint32_t)48U);
          uint8_t *uu____48;
          if (out == NULL)
          {
            uu____48 = NULL;
          }
          else
          {
            uu____48 = out + i * (uint32_t)48U;
          }
          bool uu____49 = v == NULL;
          if (!(uu____49 || uu____48 == NULL))
          {
            memcpy(uu____48, v, (uint32_t)48U * sizeof (v[0U]));
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
          Hacl_HMAC_compute_sha2_384(v, k, (uint32_t)48U, v, (uint32_t)48U);
          uint8_t *uu____50;
          if (v == NULL)
          {
            uu____50 = NULL;
          }
          else
          {
            uu____50 = v;
          }
          bool uu____51 = uu____50 == NULL;
          if (!(uu____51 || block == NULL))
          {
            memcpy(block, uu____50, (n - max * (uint32_t)48U) * sizeof (uu____50[0U]));
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
        bool uu____52 = v == NULL;
        if (!(uu____52 || k_ == NULL))
        {
          memcpy(k_, v, (uint32_t)48U * sizeof (v[0U]));
        }
        if (additional_input_len != (uint32_t)0U)
        {
          uint8_t *uu____53;
          if (input0 == NULL)
          {
            uu____53 = NULL;
          }
          else
          {
            uu____53 = input0 + (uint32_t)49U;
          }
          bool uu____54 = additional_input == NULL;
          if (!(uu____54 || uu____53 == NULL))
          {
            memcpy(uu____53,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
        }
        input0[48U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_384(k_, k, (uint32_t)48U, input0, input_len);
        Hacl_HMAC_compute_sha2_384(v, k_, (uint32_t)48U, v, (uint32_t)48U);
        bool uu____55 = k_ == NULL;
        if (!(uu____55 || k == NULL))
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
          bool uu____56 = v == NULL;
          if (!(uu____56 || k_0 == NULL))
          {
            memcpy(k_0, v, (uint32_t)48U * sizeof (v[0U]));
          }
          if (additional_input_len != (uint32_t)0U)
          {
            uint8_t *uu____57;
            if (input == NULL)
            {
              uu____57 = NULL;
            }
            else
            {
              uu____57 = input + (uint32_t)49U;
            }
            bool uu____58 = additional_input == NULL;
            if (!(uu____58 || uu____57 == NULL))
            {
              memcpy(uu____57,
                additional_input,
                additional_input_len * sizeof (additional_input[0U]));
            }
          }
          input[48U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_384(k_0, k, (uint32_t)48U, input, input_len0);
          Hacl_HMAC_compute_sha2_384(v, k_0, (uint32_t)48U, v, (uint32_t)48U);
          bool uu____59 = k_0 == NULL;
          if (!(uu____59 || k == NULL))
          {
            memcpy(k, k_0, (uint32_t)48U * sizeof (k_0[0U]));
          }
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
          bool uu____60 = v == NULL;
          if (!(uu____60 || k_ == NULL))
          {
            memcpy(k_, v, (uint32_t)64U * sizeof (v[0U]));
          }
          if (additional_input_len != (uint32_t)0U)
          {
            uint8_t *uu____61;
            if (input0 == NULL)
            {
              uu____61 = NULL;
            }
            else
            {
              uu____61 = input0 + (uint32_t)65U;
            }
            bool uu____62 = additional_input == NULL;
            if (!(uu____62 || uu____61 == NULL))
            {
              memcpy(uu____61,
                additional_input,
                additional_input_len * sizeof (additional_input[0U]));
            }
          }
          input0[64U] = (uint8_t)0U;
          Hacl_HMAC_compute_sha2_512(k_, k, (uint32_t)64U, input0, input_len);
          Hacl_HMAC_compute_sha2_512(v, k_, (uint32_t)64U, v, (uint32_t)64U);
          bool uu____63 = k_ == NULL;
          if (!(uu____63 || k == NULL))
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
            bool uu____64 = v == NULL;
            if (!(uu____64 || k_0 == NULL))
            {
              memcpy(k_0, v, (uint32_t)64U * sizeof (v[0U]));
            }
            if (additional_input_len != (uint32_t)0U)
            {
              uint8_t *uu____65;
              if (input == NULL)
              {
                uu____65 = NULL;
              }
              else
              {
                uu____65 = input + (uint32_t)65U;
              }
              bool uu____66 = additional_input == NULL;
              if (!(uu____66 || uu____65 == NULL))
              {
                memcpy(uu____65,
                  additional_input,
                  additional_input_len * sizeof (additional_input[0U]));
              }
            }
            input[64U] = (uint8_t)1U;
            Hacl_HMAC_compute_sha2_512(k_0, k, (uint32_t)64U, input, input_len0);
            Hacl_HMAC_compute_sha2_512(v, k_0, (uint32_t)64U, v, (uint32_t)64U);
            bool uu____67 = k_0 == NULL;
            if (!(uu____67 || k == NULL))
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
          Hacl_HMAC_compute_sha2_512(v, k, (uint32_t)64U, v, (uint32_t)64U);
          uint8_t *uu____68;
          if (out == NULL)
          {
            uu____68 = NULL;
          }
          else
          {
            uu____68 = out + i * (uint32_t)64U;
          }
          bool uu____69 = v == NULL;
          if (!(uu____69 || uu____68 == NULL))
          {
            memcpy(uu____68, v, (uint32_t)64U * sizeof (v[0U]));
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
          Hacl_HMAC_compute_sha2_512(v, k, (uint32_t)64U, v, (uint32_t)64U);
          uint8_t *uu____70;
          if (v == NULL)
          {
            uu____70 = NULL;
          }
          else
          {
            uu____70 = v;
          }
          bool uu____71 = uu____70 == NULL;
          if (!(uu____71 || block == NULL))
          {
            memcpy(block, uu____70, (n - max * (uint32_t)64U) * sizeof (uu____70[0U]));
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
        bool uu____72 = v == NULL;
        if (!(uu____72 || k_ == NULL))
        {
          memcpy(k_, v, (uint32_t)64U * sizeof (v[0U]));
        }
        if (additional_input_len != (uint32_t)0U)
        {
          uint8_t *uu____73;
          if (input0 == NULL)
          {
            uu____73 = NULL;
          }
          else
          {
            uu____73 = input0 + (uint32_t)65U;
          }
          bool uu____74 = additional_input == NULL;
          if (!(uu____74 || uu____73 == NULL))
          {
            memcpy(uu____73,
              additional_input,
              additional_input_len * sizeof (additional_input[0U]));
          }
        }
        input0[64U] = (uint8_t)0U;
        Hacl_HMAC_compute_sha2_512(k_, k, (uint32_t)64U, input0, input_len);
        Hacl_HMAC_compute_sha2_512(v, k_, (uint32_t)64U, v, (uint32_t)64U);
        bool uu____75 = k_ == NULL;
        if (!(uu____75 || k == NULL))
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
          bool uu____76 = v == NULL;
          if (!(uu____76 || k_0 == NULL))
          {
            memcpy(k_0, v, (uint32_t)64U * sizeof (v[0U]));
          }
          if (additional_input_len != (uint32_t)0U)
          {
            uint8_t *uu____77;
            if (input == NULL)
            {
              uu____77 = NULL;
            }
            else
            {
              uu____77 = input + (uint32_t)65U;
            }
            bool uu____78 = additional_input == NULL;
            if (!(uu____78 || uu____77 == NULL))
            {
              memcpy(uu____77,
                additional_input,
                additional_input_len * sizeof (additional_input[0U]));
            }
          }
          input[64U] = (uint8_t)1U;
          Hacl_HMAC_compute_sha2_512(k_0, k, (uint32_t)64U, input, input_len0);
          Hacl_HMAC_compute_sha2_512(v, k_0, (uint32_t)64U, v, (uint32_t)64U);
          bool uu____79 = k_0 == NULL;
          if (!(uu____79 || k == NULL))
          {
            memcpy(k, k_0, (uint32_t)64U * sizeof (k_0[0U]));
          }
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

