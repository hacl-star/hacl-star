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

u32 Hacl_HMAC_DRBG_reseed_interval = (u32)1024U;

u32 Hacl_HMAC_DRBG_max_output_length = (u32)65536U;

u32 Hacl_HMAC_DRBG_max_length = (u32)65536U;

u32 Hacl_HMAC_DRBG_max_personalization_string_length = (u32)65536U;

u32 Hacl_HMAC_DRBG_max_additional_input_length = (u32)65536U;

u32 Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_hash_alg a)
{
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        return (u32)16U;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        return (u32)32U;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        return (u32)32U;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        return (u32)32U;
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

u8
*Hacl_HMAC_DRBG___proj__State__item__k(
  Spec_Hash_Definitions_hash_alg a,
  Hacl_HMAC_DRBG_state projectee
)
{
  return projectee.k;
}

u8
*Hacl_HMAC_DRBG___proj__State__item__v(
  Spec_Hash_Definitions_hash_alg a,
  Hacl_HMAC_DRBG_state projectee
)
{
  return projectee.v;
}

u32
*Hacl_HMAC_DRBG___proj__State__item__reseed_counter(
  Spec_Hash_Definitions_hash_alg a,
  Hacl_HMAC_DRBG_state projectee
)
{
  return projectee.reseed_counter;
}

Hacl_HMAC_DRBG_state Hacl_HMAC_DRBG_create_in(Spec_Hash_Definitions_hash_alg a)
{
  u8 *k;
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        u8 *buf = KRML_HOST_CALLOC((u32)20U, sizeof (u8));
        k = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        u8 *buf = KRML_HOST_CALLOC((u32)32U, sizeof (u8));
        k = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        u8 *buf = KRML_HOST_CALLOC((u32)48U, sizeof (u8));
        k = buf;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        u8 *buf = KRML_HOST_CALLOC((u32)64U, sizeof (u8));
        k = buf;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  {
    u8 *v;
    switch (a)
    {
      case Spec_Hash_Definitions_SHA1:
        {
          u8 *buf = KRML_HOST_CALLOC((u32)20U, sizeof (u8));
          v = buf;
          break;
        }
      case Spec_Hash_Definitions_SHA2_256:
        {
          u8 *buf = KRML_HOST_CALLOC((u32)32U, sizeof (u8));
          v = buf;
          break;
        }
      case Spec_Hash_Definitions_SHA2_384:
        {
          u8 *buf = KRML_HOST_CALLOC((u32)48U, sizeof (u8));
          v = buf;
          break;
        }
      case Spec_Hash_Definitions_SHA2_512:
        {
          u8 *buf = KRML_HOST_CALLOC((u32)64U, sizeof (u8));
          v = buf;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    {
      u32 *ctr = KRML_HOST_MALLOC(sizeof (u32));
      ctr[0U] = (u32)1U;
      return ((Hacl_HMAC_DRBG_state){ .k = k, .v = v, .reseed_counter = ctr });
    }
  }
}

void
Hacl_HMAC_DRBG_instantiate(
  Spec_Hash_Definitions_hash_alg a,
  Hacl_HMAC_DRBG_state st,
  u32 entropy_input_len,
  u8 *entropy_input,
  u32 nonce_len,
  u8 *nonce,
  u32 personalization_string_len,
  u8 *personalization_string
)
{
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        KRML_CHECK_SIZE(sizeof (u8), entropy_input_len + nonce_len + personalization_string_len);
        {
          u8 seed_material[entropy_input_len + nonce_len + personalization_string_len];
          memset(seed_material,
            0U,
            (entropy_input_len + nonce_len + personalization_string_len) * sizeof (u8));
          {
            u8 *k;
            u8 *v;
            u32 *ctr;
            memcpy(seed_material, entropy_input, entropy_input_len * sizeof (u8));
            memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof (u8));
            memcpy(seed_material + entropy_input_len + nonce_len,
              personalization_string,
              personalization_string_len * sizeof (u8));
            k = st.k;
            v = st.v;
            ctr = st.reseed_counter;
            memset(k, 0U, (u32)20U * sizeof (u8));
            memset(v, (u8)1U, (u32)20U * sizeof (u8));
            ctr[0U] = (u32)1U;
            {
              u32 input_len = (u32)21U + entropy_input_len + nonce_len + personalization_string_len;
              KRML_CHECK_SIZE(sizeof (u8), input_len);
              {
                u8 input0[input_len];
                memset(input0, 0U, input_len * sizeof (u8));
                {
                  u8 *k_ = input0;
                  memcpy(k_, v, (u32)20U * sizeof (u8));
                  if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                    memcpy(input0 + (u32)21U,
                      seed_material,
                      (entropy_input_len + nonce_len + personalization_string_len) * sizeof (u8));
                  input0[20U] = (u8)0U;
                  Hacl_HMAC_legacy_compute_sha1(k_, k, (u32)20U, input0, input_len);
                  Hacl_HMAC_legacy_compute_sha1(v, k_, (u32)20U, v, (u32)20U);
                  memcpy(k, k_, (u32)20U * sizeof (u8));
                  if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                  {
                    u32
                    input_len0 =
                      (u32)21U
                      + entropy_input_len + nonce_len + personalization_string_len;
                    KRML_CHECK_SIZE(sizeof (u8), input_len0);
                    {
                      u8 input[input_len0];
                      memset(input, 0U, input_len0 * sizeof (u8));
                      {
                        u8 *k_0 = input;
                        memcpy(k_0, v, (u32)20U * sizeof (u8));
                        if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                          memcpy(input + (u32)21U,
                            seed_material,
                            (entropy_input_len + nonce_len + personalization_string_len)
                            * sizeof (u8));
                        input[20U] = (u8)1U;
                        Hacl_HMAC_legacy_compute_sha1(k_0, k, (u32)20U, input, input_len0);
                        Hacl_HMAC_legacy_compute_sha1(v, k_0, (u32)20U, v, (u32)20U);
                        memcpy(k, k_0, (u32)20U * sizeof (u8));
                      }
                    }
                  }
                }
              }
            }
          }
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        KRML_CHECK_SIZE(sizeof (u8), entropy_input_len + nonce_len + personalization_string_len);
        {
          u8 seed_material[entropy_input_len + nonce_len + personalization_string_len];
          memset(seed_material,
            0U,
            (entropy_input_len + nonce_len + personalization_string_len) * sizeof (u8));
          {
            u8 *k;
            u8 *v;
            u32 *ctr;
            memcpy(seed_material, entropy_input, entropy_input_len * sizeof (u8));
            memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof (u8));
            memcpy(seed_material + entropy_input_len + nonce_len,
              personalization_string,
              personalization_string_len * sizeof (u8));
            k = st.k;
            v = st.v;
            ctr = st.reseed_counter;
            memset(k, 0U, (u32)32U * sizeof (u8));
            memset(v, (u8)1U, (u32)32U * sizeof (u8));
            ctr[0U] = (u32)1U;
            {
              u32 input_len = (u32)33U + entropy_input_len + nonce_len + personalization_string_len;
              KRML_CHECK_SIZE(sizeof (u8), input_len);
              {
                u8 input0[input_len];
                memset(input0, 0U, input_len * sizeof (u8));
                {
                  u8 *k_ = input0;
                  memcpy(k_, v, (u32)32U * sizeof (u8));
                  if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                    memcpy(input0 + (u32)33U,
                      seed_material,
                      (entropy_input_len + nonce_len + personalization_string_len) * sizeof (u8));
                  input0[32U] = (u8)0U;
                  Hacl_HMAC_compute_sha2_256(k_, k, (u32)32U, input0, input_len);
                  Hacl_HMAC_compute_sha2_256(v, k_, (u32)32U, v, (u32)32U);
                  memcpy(k, k_, (u32)32U * sizeof (u8));
                  if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                  {
                    u32
                    input_len0 =
                      (u32)33U
                      + entropy_input_len + nonce_len + personalization_string_len;
                    KRML_CHECK_SIZE(sizeof (u8), input_len0);
                    {
                      u8 input[input_len0];
                      memset(input, 0U, input_len0 * sizeof (u8));
                      {
                        u8 *k_0 = input;
                        memcpy(k_0, v, (u32)32U * sizeof (u8));
                        if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                          memcpy(input + (u32)33U,
                            seed_material,
                            (entropy_input_len + nonce_len + personalization_string_len)
                            * sizeof (u8));
                        input[32U] = (u8)1U;
                        Hacl_HMAC_compute_sha2_256(k_0, k, (u32)32U, input, input_len0);
                        Hacl_HMAC_compute_sha2_256(v, k_0, (u32)32U, v, (u32)32U);
                        memcpy(k, k_0, (u32)32U * sizeof (u8));
                      }
                    }
                  }
                }
              }
            }
          }
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        KRML_CHECK_SIZE(sizeof (u8), entropy_input_len + nonce_len + personalization_string_len);
        {
          u8 seed_material[entropy_input_len + nonce_len + personalization_string_len];
          memset(seed_material,
            0U,
            (entropy_input_len + nonce_len + personalization_string_len) * sizeof (u8));
          {
            u8 *k;
            u8 *v;
            u32 *ctr;
            memcpy(seed_material, entropy_input, entropy_input_len * sizeof (u8));
            memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof (u8));
            memcpy(seed_material + entropy_input_len + nonce_len,
              personalization_string,
              personalization_string_len * sizeof (u8));
            k = st.k;
            v = st.v;
            ctr = st.reseed_counter;
            memset(k, 0U, (u32)48U * sizeof (u8));
            memset(v, (u8)1U, (u32)48U * sizeof (u8));
            ctr[0U] = (u32)1U;
            {
              u32 input_len = (u32)49U + entropy_input_len + nonce_len + personalization_string_len;
              KRML_CHECK_SIZE(sizeof (u8), input_len);
              {
                u8 input0[input_len];
                memset(input0, 0U, input_len * sizeof (u8));
                {
                  u8 *k_ = input0;
                  memcpy(k_, v, (u32)48U * sizeof (u8));
                  if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                    memcpy(input0 + (u32)49U,
                      seed_material,
                      (entropy_input_len + nonce_len + personalization_string_len) * sizeof (u8));
                  input0[48U] = (u8)0U;
                  Hacl_HMAC_compute_sha2_384(k_, k, (u32)48U, input0, input_len);
                  Hacl_HMAC_compute_sha2_384(v, k_, (u32)48U, v, (u32)48U);
                  memcpy(k, k_, (u32)48U * sizeof (u8));
                  if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                  {
                    u32
                    input_len0 =
                      (u32)49U
                      + entropy_input_len + nonce_len + personalization_string_len;
                    KRML_CHECK_SIZE(sizeof (u8), input_len0);
                    {
                      u8 input[input_len0];
                      memset(input, 0U, input_len0 * sizeof (u8));
                      {
                        u8 *k_0 = input;
                        memcpy(k_0, v, (u32)48U * sizeof (u8));
                        if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                          memcpy(input + (u32)49U,
                            seed_material,
                            (entropy_input_len + nonce_len + personalization_string_len)
                            * sizeof (u8));
                        input[48U] = (u8)1U;
                        Hacl_HMAC_compute_sha2_384(k_0, k, (u32)48U, input, input_len0);
                        Hacl_HMAC_compute_sha2_384(v, k_0, (u32)48U, v, (u32)48U);
                        memcpy(k, k_0, (u32)48U * sizeof (u8));
                      }
                    }
                  }
                }
              }
            }
          }
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        KRML_CHECK_SIZE(sizeof (u8), entropy_input_len + nonce_len + personalization_string_len);
        {
          u8 seed_material[entropy_input_len + nonce_len + personalization_string_len];
          memset(seed_material,
            0U,
            (entropy_input_len + nonce_len + personalization_string_len) * sizeof (u8));
          {
            u8 *k;
            u8 *v;
            u32 *ctr;
            memcpy(seed_material, entropy_input, entropy_input_len * sizeof (u8));
            memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof (u8));
            memcpy(seed_material + entropy_input_len + nonce_len,
              personalization_string,
              personalization_string_len * sizeof (u8));
            k = st.k;
            v = st.v;
            ctr = st.reseed_counter;
            memset(k, 0U, (u32)64U * sizeof (u8));
            memset(v, (u8)1U, (u32)64U * sizeof (u8));
            ctr[0U] = (u32)1U;
            {
              u32 input_len = (u32)65U + entropy_input_len + nonce_len + personalization_string_len;
              KRML_CHECK_SIZE(sizeof (u8), input_len);
              {
                u8 input0[input_len];
                memset(input0, 0U, input_len * sizeof (u8));
                {
                  u8 *k_ = input0;
                  memcpy(k_, v, (u32)64U * sizeof (u8));
                  if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                    memcpy(input0 + (u32)65U,
                      seed_material,
                      (entropy_input_len + nonce_len + personalization_string_len) * sizeof (u8));
                  input0[64U] = (u8)0U;
                  Hacl_HMAC_compute_sha2_512(k_, k, (u32)64U, input0, input_len);
                  Hacl_HMAC_compute_sha2_512(v, k_, (u32)64U, v, (u32)64U);
                  memcpy(k, k_, (u32)64U * sizeof (u8));
                  if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                  {
                    u32
                    input_len0 =
                      (u32)65U
                      + entropy_input_len + nonce_len + personalization_string_len;
                    KRML_CHECK_SIZE(sizeof (u8), input_len0);
                    {
                      u8 input[input_len0];
                      memset(input, 0U, input_len0 * sizeof (u8));
                      {
                        u8 *k_0 = input;
                        memcpy(k_0, v, (u32)64U * sizeof (u8));
                        if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                          memcpy(input + (u32)65U,
                            seed_material,
                            (entropy_input_len + nonce_len + personalization_string_len)
                            * sizeof (u8));
                        input[64U] = (u8)1U;
                        Hacl_HMAC_compute_sha2_512(k_0, k, (u32)64U, input, input_len0);
                        Hacl_HMAC_compute_sha2_512(v, k_0, (u32)64U, v, (u32)64U);
                        memcpy(k, k_0, (u32)64U * sizeof (u8));
                      }
                    }
                  }
                }
              }
            }
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
  u32 entropy_input_len,
  u8 *entropy_input,
  u32 additional_input_input_len,
  u8 *additional_input_input
)
{
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        KRML_CHECK_SIZE(sizeof (u8), entropy_input_len + additional_input_input_len);
        {
          u8 seed_material[entropy_input_len + additional_input_input_len];
          memset(seed_material, 0U, (entropy_input_len + additional_input_input_len) * sizeof (u8));
          {
            Hacl_HMAC_DRBG_state uu____0;
            u8 *k;
            u8 *v;
            u32 *ctr;
            memcpy(seed_material, entropy_input, entropy_input_len * sizeof (u8));
            memcpy(seed_material + entropy_input_len,
              additional_input_input,
              additional_input_input_len * sizeof (u8));
            uu____0 = st;
            k = uu____0.k;
            v = uu____0.v;
            ctr = uu____0.reseed_counter;
            {
              u32 input_len = (u32)21U + entropy_input_len + additional_input_input_len;
              KRML_CHECK_SIZE(sizeof (u8), input_len);
              {
                u8 input0[input_len];
                memset(input0, 0U, input_len * sizeof (u8));
                {
                  u8 *k_ = input0;
                  memcpy(k_, v, (u32)20U * sizeof (u8));
                  if (entropy_input_len + additional_input_input_len != (u32)0U)
                    memcpy(input0 + (u32)21U,
                      seed_material,
                      (entropy_input_len + additional_input_input_len) * sizeof (u8));
                  input0[20U] = (u8)0U;
                  Hacl_HMAC_legacy_compute_sha1(k_, k, (u32)20U, input0, input_len);
                  Hacl_HMAC_legacy_compute_sha1(v, k_, (u32)20U, v, (u32)20U);
                  memcpy(k, k_, (u32)20U * sizeof (u8));
                  if (entropy_input_len + additional_input_input_len != (u32)0U)
                  {
                    u32 input_len0 = (u32)21U + entropy_input_len + additional_input_input_len;
                    KRML_CHECK_SIZE(sizeof (u8), input_len0);
                    {
                      u8 input[input_len0];
                      memset(input, 0U, input_len0 * sizeof (u8));
                      {
                        u8 *k_0 = input;
                        memcpy(k_0, v, (u32)20U * sizeof (u8));
                        if (entropy_input_len + additional_input_input_len != (u32)0U)
                          memcpy(input + (u32)21U,
                            seed_material,
                            (entropy_input_len + additional_input_input_len) * sizeof (u8));
                        input[20U] = (u8)1U;
                        Hacl_HMAC_legacy_compute_sha1(k_0, k, (u32)20U, input, input_len0);
                        Hacl_HMAC_legacy_compute_sha1(v, k_0, (u32)20U, v, (u32)20U);
                        memcpy(k, k_0, (u32)20U * sizeof (u8));
                      }
                    }
                  }
                  ctr[0U] = (u32)1U;
                }
              }
            }
          }
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        KRML_CHECK_SIZE(sizeof (u8), entropy_input_len + additional_input_input_len);
        {
          u8 seed_material[entropy_input_len + additional_input_input_len];
          memset(seed_material, 0U, (entropy_input_len + additional_input_input_len) * sizeof (u8));
          {
            Hacl_HMAC_DRBG_state uu____1;
            u8 *k;
            u8 *v;
            u32 *ctr;
            memcpy(seed_material, entropy_input, entropy_input_len * sizeof (u8));
            memcpy(seed_material + entropy_input_len,
              additional_input_input,
              additional_input_input_len * sizeof (u8));
            uu____1 = st;
            k = uu____1.k;
            v = uu____1.v;
            ctr = uu____1.reseed_counter;
            {
              u32 input_len = (u32)33U + entropy_input_len + additional_input_input_len;
              KRML_CHECK_SIZE(sizeof (u8), input_len);
              {
                u8 input0[input_len];
                memset(input0, 0U, input_len * sizeof (u8));
                {
                  u8 *k_ = input0;
                  memcpy(k_, v, (u32)32U * sizeof (u8));
                  if (entropy_input_len + additional_input_input_len != (u32)0U)
                    memcpy(input0 + (u32)33U,
                      seed_material,
                      (entropy_input_len + additional_input_input_len) * sizeof (u8));
                  input0[32U] = (u8)0U;
                  Hacl_HMAC_compute_sha2_256(k_, k, (u32)32U, input0, input_len);
                  Hacl_HMAC_compute_sha2_256(v, k_, (u32)32U, v, (u32)32U);
                  memcpy(k, k_, (u32)32U * sizeof (u8));
                  if (entropy_input_len + additional_input_input_len != (u32)0U)
                  {
                    u32 input_len0 = (u32)33U + entropy_input_len + additional_input_input_len;
                    KRML_CHECK_SIZE(sizeof (u8), input_len0);
                    {
                      u8 input[input_len0];
                      memset(input, 0U, input_len0 * sizeof (u8));
                      {
                        u8 *k_0 = input;
                        memcpy(k_0, v, (u32)32U * sizeof (u8));
                        if (entropy_input_len + additional_input_input_len != (u32)0U)
                          memcpy(input + (u32)33U,
                            seed_material,
                            (entropy_input_len + additional_input_input_len) * sizeof (u8));
                        input[32U] = (u8)1U;
                        Hacl_HMAC_compute_sha2_256(k_0, k, (u32)32U, input, input_len0);
                        Hacl_HMAC_compute_sha2_256(v, k_0, (u32)32U, v, (u32)32U);
                        memcpy(k, k_0, (u32)32U * sizeof (u8));
                      }
                    }
                  }
                  ctr[0U] = (u32)1U;
                }
              }
            }
          }
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        KRML_CHECK_SIZE(sizeof (u8), entropy_input_len + additional_input_input_len);
        {
          u8 seed_material[entropy_input_len + additional_input_input_len];
          memset(seed_material, 0U, (entropy_input_len + additional_input_input_len) * sizeof (u8));
          {
            Hacl_HMAC_DRBG_state uu____2;
            u8 *k;
            u8 *v;
            u32 *ctr;
            memcpy(seed_material, entropy_input, entropy_input_len * sizeof (u8));
            memcpy(seed_material + entropy_input_len,
              additional_input_input,
              additional_input_input_len * sizeof (u8));
            uu____2 = st;
            k = uu____2.k;
            v = uu____2.v;
            ctr = uu____2.reseed_counter;
            {
              u32 input_len = (u32)49U + entropy_input_len + additional_input_input_len;
              KRML_CHECK_SIZE(sizeof (u8), input_len);
              {
                u8 input0[input_len];
                memset(input0, 0U, input_len * sizeof (u8));
                {
                  u8 *k_ = input0;
                  memcpy(k_, v, (u32)48U * sizeof (u8));
                  if (entropy_input_len + additional_input_input_len != (u32)0U)
                    memcpy(input0 + (u32)49U,
                      seed_material,
                      (entropy_input_len + additional_input_input_len) * sizeof (u8));
                  input0[48U] = (u8)0U;
                  Hacl_HMAC_compute_sha2_384(k_, k, (u32)48U, input0, input_len);
                  Hacl_HMAC_compute_sha2_384(v, k_, (u32)48U, v, (u32)48U);
                  memcpy(k, k_, (u32)48U * sizeof (u8));
                  if (entropy_input_len + additional_input_input_len != (u32)0U)
                  {
                    u32 input_len0 = (u32)49U + entropy_input_len + additional_input_input_len;
                    KRML_CHECK_SIZE(sizeof (u8), input_len0);
                    {
                      u8 input[input_len0];
                      memset(input, 0U, input_len0 * sizeof (u8));
                      {
                        u8 *k_0 = input;
                        memcpy(k_0, v, (u32)48U * sizeof (u8));
                        if (entropy_input_len + additional_input_input_len != (u32)0U)
                          memcpy(input + (u32)49U,
                            seed_material,
                            (entropy_input_len + additional_input_input_len) * sizeof (u8));
                        input[48U] = (u8)1U;
                        Hacl_HMAC_compute_sha2_384(k_0, k, (u32)48U, input, input_len0);
                        Hacl_HMAC_compute_sha2_384(v, k_0, (u32)48U, v, (u32)48U);
                        memcpy(k, k_0, (u32)48U * sizeof (u8));
                      }
                    }
                  }
                  ctr[0U] = (u32)1U;
                }
              }
            }
          }
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        KRML_CHECK_SIZE(sizeof (u8), entropy_input_len + additional_input_input_len);
        {
          u8 seed_material[entropy_input_len + additional_input_input_len];
          memset(seed_material, 0U, (entropy_input_len + additional_input_input_len) * sizeof (u8));
          {
            Hacl_HMAC_DRBG_state uu____3;
            u8 *k;
            u8 *v;
            u32 *ctr;
            memcpy(seed_material, entropy_input, entropy_input_len * sizeof (u8));
            memcpy(seed_material + entropy_input_len,
              additional_input_input,
              additional_input_input_len * sizeof (u8));
            uu____3 = st;
            k = uu____3.k;
            v = uu____3.v;
            ctr = uu____3.reseed_counter;
            {
              u32 input_len = (u32)65U + entropy_input_len + additional_input_input_len;
              KRML_CHECK_SIZE(sizeof (u8), input_len);
              {
                u8 input0[input_len];
                memset(input0, 0U, input_len * sizeof (u8));
                {
                  u8 *k_ = input0;
                  memcpy(k_, v, (u32)64U * sizeof (u8));
                  if (entropy_input_len + additional_input_input_len != (u32)0U)
                    memcpy(input0 + (u32)65U,
                      seed_material,
                      (entropy_input_len + additional_input_input_len) * sizeof (u8));
                  input0[64U] = (u8)0U;
                  Hacl_HMAC_compute_sha2_512(k_, k, (u32)64U, input0, input_len);
                  Hacl_HMAC_compute_sha2_512(v, k_, (u32)64U, v, (u32)64U);
                  memcpy(k, k_, (u32)64U * sizeof (u8));
                  if (entropy_input_len + additional_input_input_len != (u32)0U)
                  {
                    u32 input_len0 = (u32)65U + entropy_input_len + additional_input_input_len;
                    KRML_CHECK_SIZE(sizeof (u8), input_len0);
                    {
                      u8 input[input_len0];
                      memset(input, 0U, input_len0 * sizeof (u8));
                      {
                        u8 *k_0 = input;
                        memcpy(k_0, v, (u32)64U * sizeof (u8));
                        if (entropy_input_len + additional_input_input_len != (u32)0U)
                          memcpy(input + (u32)65U,
                            seed_material,
                            (entropy_input_len + additional_input_input_len) * sizeof (u8));
                        input[64U] = (u8)1U;
                        Hacl_HMAC_compute_sha2_512(k_0, k, (u32)64U, input, input_len0);
                        Hacl_HMAC_compute_sha2_512(v, k_0, (u32)64U, v, (u32)64U);
                        memcpy(k, k_0, (u32)64U * sizeof (u8));
                      }
                    }
                  }
                  ctr[0U] = (u32)1U;
                }
              }
            }
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

bool
Hacl_HMAC_DRBG_generate(
  Spec_Hash_Definitions_hash_alg a,
  u8 *output,
  Hacl_HMAC_DRBG_state st,
  u32 n,
  u32 additional_input_len,
  u8 *additional_input
)
{
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        if (st.reseed_counter[0U] > Hacl_HMAC_DRBG_reseed_interval)
          return false;
        {
          u8 *k = st.k;
          u8 *v = st.v;
          u32 *ctr = st.reseed_counter;
          if (additional_input_len > (u32)0U)
          {
            u32 input_len = (u32)21U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (u8), input_len);
            {
              u8 input0[input_len];
              memset(input0, 0U, input_len * sizeof (u8));
              {
                u8 *k_ = input0;
                memcpy(k_, v, (u32)20U * sizeof (u8));
                if (additional_input_len != (u32)0U)
                  memcpy(input0 + (u32)21U, additional_input, additional_input_len * sizeof (u8));
                input0[20U] = (u8)0U;
                Hacl_HMAC_legacy_compute_sha1(k_, k, (u32)20U, input0, input_len);
                Hacl_HMAC_legacy_compute_sha1(v, k_, (u32)20U, v, (u32)20U);
                memcpy(k, k_, (u32)20U * sizeof (u8));
                if (additional_input_len != (u32)0U)
                {
                  u32 input_len0 = (u32)21U + additional_input_len;
                  KRML_CHECK_SIZE(sizeof (u8), input_len0);
                  {
                    u8 input[input_len0];
                    memset(input, 0U, input_len0 * sizeof (u8));
                    {
                      u8 *k_0 = input;
                      memcpy(k_0, v, (u32)20U * sizeof (u8));
                      if (additional_input_len != (u32)0U)
                        memcpy(input + (u32)21U,
                          additional_input,
                          additional_input_len * sizeof (u8));
                      input[20U] = (u8)1U;
                      Hacl_HMAC_legacy_compute_sha1(k_0, k, (u32)20U, input, input_len0);
                      Hacl_HMAC_legacy_compute_sha1(v, k_0, (u32)20U, v, (u32)20U);
                      memcpy(k, k_0, (u32)20U * sizeof (u8));
                    }
                  }
                }
              }
            }
          }
          {
            u8 *output1 = output;
            u32 max = n / (u32)20U;
            u8 *out = output1;
            {
              u32 i;
              for (i = (u32)0U; i < max; i++)
              {
                Hacl_HMAC_legacy_compute_sha1(v, k, (u32)20U, v, (u32)20U);
                memcpy(out + i * (u32)20U, v, (u32)20U * sizeof (u8));
              }
            }
            if (max * (u32)20U < n)
            {
              u8 *block = output1 + max * (u32)20U;
              Hacl_HMAC_legacy_compute_sha1(v, k, (u32)20U, v, (u32)20U);
              memcpy(block, v, (n - max * (u32)20U) * sizeof (u8));
            }
            {
              u32 input_len = (u32)21U + additional_input_len;
              KRML_CHECK_SIZE(sizeof (u8), input_len);
              {
                u8 input0[input_len];
                memset(input0, 0U, input_len * sizeof (u8));
                {
                  u8 *k_ = input0;
                  memcpy(k_, v, (u32)20U * sizeof (u8));
                  if (additional_input_len != (u32)0U)
                    memcpy(input0 + (u32)21U, additional_input, additional_input_len * sizeof (u8));
                  input0[20U] = (u8)0U;
                  Hacl_HMAC_legacy_compute_sha1(k_, k, (u32)20U, input0, input_len);
                  Hacl_HMAC_legacy_compute_sha1(v, k_, (u32)20U, v, (u32)20U);
                  memcpy(k, k_, (u32)20U * sizeof (u8));
                  if (additional_input_len != (u32)0U)
                  {
                    u32 input_len0 = (u32)21U + additional_input_len;
                    KRML_CHECK_SIZE(sizeof (u8), input_len0);
                    {
                      u8 input[input_len0];
                      memset(input, 0U, input_len0 * sizeof (u8));
                      {
                        u8 *k_0 = input;
                        memcpy(k_0, v, (u32)20U * sizeof (u8));
                        if (additional_input_len != (u32)0U)
                          memcpy(input + (u32)21U,
                            additional_input,
                            additional_input_len * sizeof (u8));
                        input[20U] = (u8)1U;
                        Hacl_HMAC_legacy_compute_sha1(k_0, k, (u32)20U, input, input_len0);
                        Hacl_HMAC_legacy_compute_sha1(v, k_0, (u32)20U, v, (u32)20U);
                        memcpy(k, k_0, (u32)20U * sizeof (u8));
                      }
                    }
                  }
                  {
                    u32 old_ctr = ctr[0U];
                    ctr[0U] = old_ctr + (u32)1U;
                    return true;
                  }
                }
              }
            }
          }
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        if (st.reseed_counter[0U] > Hacl_HMAC_DRBG_reseed_interval)
          return false;
        {
          u8 *k = st.k;
          u8 *v = st.v;
          u32 *ctr = st.reseed_counter;
          if (additional_input_len > (u32)0U)
          {
            u32 input_len = (u32)33U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (u8), input_len);
            {
              u8 input0[input_len];
              memset(input0, 0U, input_len * sizeof (u8));
              {
                u8 *k_ = input0;
                memcpy(k_, v, (u32)32U * sizeof (u8));
                if (additional_input_len != (u32)0U)
                  memcpy(input0 + (u32)33U, additional_input, additional_input_len * sizeof (u8));
                input0[32U] = (u8)0U;
                Hacl_HMAC_compute_sha2_256(k_, k, (u32)32U, input0, input_len);
                Hacl_HMAC_compute_sha2_256(v, k_, (u32)32U, v, (u32)32U);
                memcpy(k, k_, (u32)32U * sizeof (u8));
                if (additional_input_len != (u32)0U)
                {
                  u32 input_len0 = (u32)33U + additional_input_len;
                  KRML_CHECK_SIZE(sizeof (u8), input_len0);
                  {
                    u8 input[input_len0];
                    memset(input, 0U, input_len0 * sizeof (u8));
                    {
                      u8 *k_0 = input;
                      memcpy(k_0, v, (u32)32U * sizeof (u8));
                      if (additional_input_len != (u32)0U)
                        memcpy(input + (u32)33U,
                          additional_input,
                          additional_input_len * sizeof (u8));
                      input[32U] = (u8)1U;
                      Hacl_HMAC_compute_sha2_256(k_0, k, (u32)32U, input, input_len0);
                      Hacl_HMAC_compute_sha2_256(v, k_0, (u32)32U, v, (u32)32U);
                      memcpy(k, k_0, (u32)32U * sizeof (u8));
                    }
                  }
                }
              }
            }
          }
          {
            u8 *output1 = output;
            u32 max = n / (u32)32U;
            u8 *out = output1;
            {
              u32 i;
              for (i = (u32)0U; i < max; i++)
              {
                Hacl_HMAC_compute_sha2_256(v, k, (u32)32U, v, (u32)32U);
                memcpy(out + i * (u32)32U, v, (u32)32U * sizeof (u8));
              }
            }
            if (max * (u32)32U < n)
            {
              u8 *block = output1 + max * (u32)32U;
              Hacl_HMAC_compute_sha2_256(v, k, (u32)32U, v, (u32)32U);
              memcpy(block, v, (n - max * (u32)32U) * sizeof (u8));
            }
            {
              u32 input_len = (u32)33U + additional_input_len;
              KRML_CHECK_SIZE(sizeof (u8), input_len);
              {
                u8 input0[input_len];
                memset(input0, 0U, input_len * sizeof (u8));
                {
                  u8 *k_ = input0;
                  memcpy(k_, v, (u32)32U * sizeof (u8));
                  if (additional_input_len != (u32)0U)
                    memcpy(input0 + (u32)33U, additional_input, additional_input_len * sizeof (u8));
                  input0[32U] = (u8)0U;
                  Hacl_HMAC_compute_sha2_256(k_, k, (u32)32U, input0, input_len);
                  Hacl_HMAC_compute_sha2_256(v, k_, (u32)32U, v, (u32)32U);
                  memcpy(k, k_, (u32)32U * sizeof (u8));
                  if (additional_input_len != (u32)0U)
                  {
                    u32 input_len0 = (u32)33U + additional_input_len;
                    KRML_CHECK_SIZE(sizeof (u8), input_len0);
                    {
                      u8 input[input_len0];
                      memset(input, 0U, input_len0 * sizeof (u8));
                      {
                        u8 *k_0 = input;
                        memcpy(k_0, v, (u32)32U * sizeof (u8));
                        if (additional_input_len != (u32)0U)
                          memcpy(input + (u32)33U,
                            additional_input,
                            additional_input_len * sizeof (u8));
                        input[32U] = (u8)1U;
                        Hacl_HMAC_compute_sha2_256(k_0, k, (u32)32U, input, input_len0);
                        Hacl_HMAC_compute_sha2_256(v, k_0, (u32)32U, v, (u32)32U);
                        memcpy(k, k_0, (u32)32U * sizeof (u8));
                      }
                    }
                  }
                  {
                    u32 old_ctr = ctr[0U];
                    ctr[0U] = old_ctr + (u32)1U;
                    return true;
                  }
                }
              }
            }
          }
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        if (st.reseed_counter[0U] > Hacl_HMAC_DRBG_reseed_interval)
          return false;
        {
          u8 *k = st.k;
          u8 *v = st.v;
          u32 *ctr = st.reseed_counter;
          if (additional_input_len > (u32)0U)
          {
            u32 input_len = (u32)49U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (u8), input_len);
            {
              u8 input0[input_len];
              memset(input0, 0U, input_len * sizeof (u8));
              {
                u8 *k_ = input0;
                memcpy(k_, v, (u32)48U * sizeof (u8));
                if (additional_input_len != (u32)0U)
                  memcpy(input0 + (u32)49U, additional_input, additional_input_len * sizeof (u8));
                input0[48U] = (u8)0U;
                Hacl_HMAC_compute_sha2_384(k_, k, (u32)48U, input0, input_len);
                Hacl_HMAC_compute_sha2_384(v, k_, (u32)48U, v, (u32)48U);
                memcpy(k, k_, (u32)48U * sizeof (u8));
                if (additional_input_len != (u32)0U)
                {
                  u32 input_len0 = (u32)49U + additional_input_len;
                  KRML_CHECK_SIZE(sizeof (u8), input_len0);
                  {
                    u8 input[input_len0];
                    memset(input, 0U, input_len0 * sizeof (u8));
                    {
                      u8 *k_0 = input;
                      memcpy(k_0, v, (u32)48U * sizeof (u8));
                      if (additional_input_len != (u32)0U)
                        memcpy(input + (u32)49U,
                          additional_input,
                          additional_input_len * sizeof (u8));
                      input[48U] = (u8)1U;
                      Hacl_HMAC_compute_sha2_384(k_0, k, (u32)48U, input, input_len0);
                      Hacl_HMAC_compute_sha2_384(v, k_0, (u32)48U, v, (u32)48U);
                      memcpy(k, k_0, (u32)48U * sizeof (u8));
                    }
                  }
                }
              }
            }
          }
          {
            u8 *output1 = output;
            u32 max = n / (u32)48U;
            u8 *out = output1;
            {
              u32 i;
              for (i = (u32)0U; i < max; i++)
              {
                Hacl_HMAC_compute_sha2_384(v, k, (u32)48U, v, (u32)48U);
                memcpy(out + i * (u32)48U, v, (u32)48U * sizeof (u8));
              }
            }
            if (max * (u32)48U < n)
            {
              u8 *block = output1 + max * (u32)48U;
              Hacl_HMAC_compute_sha2_384(v, k, (u32)48U, v, (u32)48U);
              memcpy(block, v, (n - max * (u32)48U) * sizeof (u8));
            }
            {
              u32 input_len = (u32)49U + additional_input_len;
              KRML_CHECK_SIZE(sizeof (u8), input_len);
              {
                u8 input0[input_len];
                memset(input0, 0U, input_len * sizeof (u8));
                {
                  u8 *k_ = input0;
                  memcpy(k_, v, (u32)48U * sizeof (u8));
                  if (additional_input_len != (u32)0U)
                    memcpy(input0 + (u32)49U, additional_input, additional_input_len * sizeof (u8));
                  input0[48U] = (u8)0U;
                  Hacl_HMAC_compute_sha2_384(k_, k, (u32)48U, input0, input_len);
                  Hacl_HMAC_compute_sha2_384(v, k_, (u32)48U, v, (u32)48U);
                  memcpy(k, k_, (u32)48U * sizeof (u8));
                  if (additional_input_len != (u32)0U)
                  {
                    u32 input_len0 = (u32)49U + additional_input_len;
                    KRML_CHECK_SIZE(sizeof (u8), input_len0);
                    {
                      u8 input[input_len0];
                      memset(input, 0U, input_len0 * sizeof (u8));
                      {
                        u8 *k_0 = input;
                        memcpy(k_0, v, (u32)48U * sizeof (u8));
                        if (additional_input_len != (u32)0U)
                          memcpy(input + (u32)49U,
                            additional_input,
                            additional_input_len * sizeof (u8));
                        input[48U] = (u8)1U;
                        Hacl_HMAC_compute_sha2_384(k_0, k, (u32)48U, input, input_len0);
                        Hacl_HMAC_compute_sha2_384(v, k_0, (u32)48U, v, (u32)48U);
                        memcpy(k, k_0, (u32)48U * sizeof (u8));
                      }
                    }
                  }
                  {
                    u32 old_ctr = ctr[0U];
                    ctr[0U] = old_ctr + (u32)1U;
                    return true;
                  }
                }
              }
            }
          }
        }
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        if (st.reseed_counter[0U] > Hacl_HMAC_DRBG_reseed_interval)
          return false;
        {
          u8 *k = st.k;
          u8 *v = st.v;
          u32 *ctr = st.reseed_counter;
          if (additional_input_len > (u32)0U)
          {
            u32 input_len = (u32)65U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (u8), input_len);
            {
              u8 input0[input_len];
              memset(input0, 0U, input_len * sizeof (u8));
              {
                u8 *k_ = input0;
                memcpy(k_, v, (u32)64U * sizeof (u8));
                if (additional_input_len != (u32)0U)
                  memcpy(input0 + (u32)65U, additional_input, additional_input_len * sizeof (u8));
                input0[64U] = (u8)0U;
                Hacl_HMAC_compute_sha2_512(k_, k, (u32)64U, input0, input_len);
                Hacl_HMAC_compute_sha2_512(v, k_, (u32)64U, v, (u32)64U);
                memcpy(k, k_, (u32)64U * sizeof (u8));
                if (additional_input_len != (u32)0U)
                {
                  u32 input_len0 = (u32)65U + additional_input_len;
                  KRML_CHECK_SIZE(sizeof (u8), input_len0);
                  {
                    u8 input[input_len0];
                    memset(input, 0U, input_len0 * sizeof (u8));
                    {
                      u8 *k_0 = input;
                      memcpy(k_0, v, (u32)64U * sizeof (u8));
                      if (additional_input_len != (u32)0U)
                        memcpy(input + (u32)65U,
                          additional_input,
                          additional_input_len * sizeof (u8));
                      input[64U] = (u8)1U;
                      Hacl_HMAC_compute_sha2_512(k_0, k, (u32)64U, input, input_len0);
                      Hacl_HMAC_compute_sha2_512(v, k_0, (u32)64U, v, (u32)64U);
                      memcpy(k, k_0, (u32)64U * sizeof (u8));
                    }
                  }
                }
              }
            }
          }
          {
            u8 *output1 = output;
            u32 max = n / (u32)64U;
            u8 *out = output1;
            {
              u32 i;
              for (i = (u32)0U; i < max; i++)
              {
                Hacl_HMAC_compute_sha2_512(v, k, (u32)64U, v, (u32)64U);
                memcpy(out + i * (u32)64U, v, (u32)64U * sizeof (u8));
              }
            }
            if (max * (u32)64U < n)
            {
              u8 *block = output1 + max * (u32)64U;
              Hacl_HMAC_compute_sha2_512(v, k, (u32)64U, v, (u32)64U);
              memcpy(block, v, (n - max * (u32)64U) * sizeof (u8));
            }
            {
              u32 input_len = (u32)65U + additional_input_len;
              KRML_CHECK_SIZE(sizeof (u8), input_len);
              {
                u8 input0[input_len];
                memset(input0, 0U, input_len * sizeof (u8));
                {
                  u8 *k_ = input0;
                  memcpy(k_, v, (u32)64U * sizeof (u8));
                  if (additional_input_len != (u32)0U)
                    memcpy(input0 + (u32)65U, additional_input, additional_input_len * sizeof (u8));
                  input0[64U] = (u8)0U;
                  Hacl_HMAC_compute_sha2_512(k_, k, (u32)64U, input0, input_len);
                  Hacl_HMAC_compute_sha2_512(v, k_, (u32)64U, v, (u32)64U);
                  memcpy(k, k_, (u32)64U * sizeof (u8));
                  if (additional_input_len != (u32)0U)
                  {
                    u32 input_len0 = (u32)65U + additional_input_len;
                    KRML_CHECK_SIZE(sizeof (u8), input_len0);
                    {
                      u8 input[input_len0];
                      memset(input, 0U, input_len0 * sizeof (u8));
                      {
                        u8 *k_0 = input;
                        memcpy(k_0, v, (u32)64U * sizeof (u8));
                        if (additional_input_len != (u32)0U)
                          memcpy(input + (u32)65U,
                            additional_input,
                            additional_input_len * sizeof (u8));
                        input[64U] = (u8)1U;
                        Hacl_HMAC_compute_sha2_512(k_0, k, (u32)64U, input, input_len0);
                        Hacl_HMAC_compute_sha2_512(v, k_0, (u32)64U, v, (u32)64U);
                        memcpy(k, k_0, (u32)64U * sizeof (u8));
                      }
                    }
                  }
                  {
                    u32 old_ctr = ctr[0U];
                    ctr[0U] = old_ctr + (u32)1U;
                    return true;
                  }
                }
              }
            }
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

