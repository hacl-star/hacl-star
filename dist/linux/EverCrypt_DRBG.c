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

u32 EverCrypt_DRBG_reseed_interval = (u32)1024U;

u32 EverCrypt_DRBG_max_output_length = (u32)65536U;

u32 EverCrypt_DRBG_max_length = (u32)65536U;

u32 EverCrypt_DRBG_max_personalization_string_length = (u32)65536U;

u32 EverCrypt_DRBG_max_additional_input_length = (u32)65536U;

u32 EverCrypt_DRBG_min_length(Spec_Hash_Definitions_hash_alg a)
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
  else
  {
    return false;
  }
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
EverCrypt_DRBG_uu___is_SHA2_256_s(
  Spec_Hash_Definitions_hash_alg uu____239,
  EverCrypt_DRBG_state_s projectee
)
{
  if (projectee.tag == EverCrypt_DRBG_SHA2_256_s)
  {
    return true;
  }
  else
  {
    return false;
  }
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
EverCrypt_DRBG_uu___is_SHA2_384_s(
  Spec_Hash_Definitions_hash_alg uu____314,
  EverCrypt_DRBG_state_s projectee
)
{
  if (projectee.tag == EverCrypt_DRBG_SHA2_384_s)
  {
    return true;
  }
  else
  {
    return false;
  }
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
EverCrypt_DRBG_uu___is_SHA2_512_s(
  Spec_Hash_Definitions_hash_alg uu____389,
  EverCrypt_DRBG_state_s projectee
)
{
  if (projectee.tag == EverCrypt_DRBG_SHA2_512_s)
  {
    return true;
  }
  else
  {
    return false;
  }
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
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

EverCrypt_DRBG_state_s *EverCrypt_DRBG_create(Spec_Hash_Definitions_hash_alg a)
{
  EverCrypt_DRBG_state_s st;
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        u8 *k1 = KRML_HOST_CALLOC((u32)20U, sizeof (u8));
        u8 *v1 = KRML_HOST_CALLOC((u32)20U, sizeof (u8));
        u32 *ctr = KRML_HOST_MALLOC(sizeof (u32));
        ctr[0U] = (u32)1U;
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
        u8 *k1 = KRML_HOST_CALLOC((u32)32U, sizeof (u8));
        u8 *v1 = KRML_HOST_CALLOC((u32)32U, sizeof (u8));
        u32 *ctr = KRML_HOST_MALLOC(sizeof (u32));
        ctr[0U] = (u32)1U;
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
        u8 *k1 = KRML_HOST_CALLOC((u32)48U, sizeof (u8));
        u8 *v1 = KRML_HOST_CALLOC((u32)48U, sizeof (u8));
        u32 *ctr = KRML_HOST_MALLOC(sizeof (u32));
        ctr[0U] = (u32)1U;
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
        u8 *k1 = KRML_HOST_CALLOC((u32)64U, sizeof (u8));
        u8 *v1 = KRML_HOST_CALLOC((u32)64U, sizeof (u8));
        u32 *ctr = KRML_HOST_MALLOC(sizeof (u32));
        ctr[0U] = (u32)1U;
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
  KRML_CHECK_SIZE(sizeof (EverCrypt_DRBG_state_s), (u32)1U);
  {
    EverCrypt_DRBG_state_s *buf = KRML_HOST_MALLOC(sizeof (EverCrypt_DRBG_state_s));
    buf[0U] = st;
    return buf;
  }
}

bool
EverCrypt_DRBG_instantiate_sha1(
  EverCrypt_DRBG_state_s *st,
  u8 *personalization_string,
  u32 personalization_string_len
)
{
  if (personalization_string_len > Hacl_HMAC_DRBG_max_personalization_string_length)
  {
    return false;
  }
  else
  {
    u32 entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA1);
    u32 nonce_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA1) / (u32)2U;
    u32 min_entropy = entropy_input_len + nonce_len;
    KRML_CHECK_SIZE(sizeof (u8), min_entropy);
    {
      u8 entropy[min_entropy];
      memset(entropy, 0U, min_entropy * sizeof entropy[0U]);
      {
        bool ok = Lib_RandomBuffer_System_randombytes(entropy, min_entropy);
        if (!ok)
        {
          return false;
        }
        else
        {
          u8 *entropy_input = entropy;
          u8 *nonce = entropy + entropy_input_len;
          EverCrypt_DRBG_state_s st_s = *st;
          KRML_CHECK_SIZE(sizeof (u8), entropy_input_len + nonce_len + personalization_string_len);
          {
            u8 seed_material[entropy_input_len + nonce_len + personalization_string_len];
            memset(seed_material,
              0U,
              (entropy_input_len + nonce_len + personalization_string_len)
              * sizeof seed_material[0U]);
            memcpy(seed_material, entropy_input, entropy_input_len * sizeof entropy_input[0U]);
            memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof nonce[0U]);
            memcpy(seed_material + entropy_input_len + nonce_len,
              personalization_string,
              personalization_string_len * sizeof personalization_string[0U]);
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
              {
                u8 *k1 = scrut.k;
                u8 *v1 = scrut.v;
                u32 *ctr = scrut.reseed_counter;
                memset(k1, 0U, (u32)20U * sizeof k1[0U]);
                memset(v1, (u8)1U, (u32)20U * sizeof v1[0U]);
                ctr[0U] = (u32)1U;
                {
                  u32
                  input_len = (u32)21U + entropy_input_len + nonce_len + personalization_string_len;
                  KRML_CHECK_SIZE(sizeof (u8), input_len);
                  {
                    u8 input0[input_len];
                    memset(input0, 0U, input_len * sizeof input0[0U]);
                    {
                      u8 *k_ = input0;
                      memcpy(k_, v1, (u32)20U * sizeof v1[0U]);
                      if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                      {
                        memcpy(input0 + (u32)21U,
                          seed_material,
                          (entropy_input_len + nonce_len + personalization_string_len)
                          * sizeof seed_material[0U]);
                      }
                      input0[20U] = (u8)0U;
                      EverCrypt_HMAC_compute_sha1(k_, k1, (u32)20U, input0, input_len);
                      EverCrypt_HMAC_compute_sha1(v1, k_, (u32)20U, v1, (u32)20U);
                      memcpy(k1, k_, (u32)20U * sizeof k_[0U]);
                      if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                      {
                        u32
                        input_len0 =
                          (u32)21U
                          + entropy_input_len + nonce_len + personalization_string_len;
                        KRML_CHECK_SIZE(sizeof (u8), input_len0);
                        {
                          u8 input[input_len0];
                          memset(input, 0U, input_len0 * sizeof input[0U]);
                          {
                            u8 *k_0 = input;
                            memcpy(k_0, v1, (u32)20U * sizeof v1[0U]);
                            if
                            (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                            {
                              memcpy(input + (u32)21U,
                                seed_material,
                                (entropy_input_len + nonce_len + personalization_string_len)
                                * sizeof seed_material[0U]);
                            }
                            input[20U] = (u8)1U;
                            EverCrypt_HMAC_compute_sha1(k_0, k1, (u32)20U, input, input_len0);
                            EverCrypt_HMAC_compute_sha1(v1, k_0, (u32)20U, v1, (u32)20U);
                            memcpy(k1, k_0, (u32)20U * sizeof k_0[0U]);
                          }
                        }
                      }
                      return true;
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

bool
EverCrypt_DRBG_instantiate_sha2_256(
  EverCrypt_DRBG_state_s *st,
  u8 *personalization_string,
  u32 personalization_string_len
)
{
  if (personalization_string_len > Hacl_HMAC_DRBG_max_personalization_string_length)
  {
    return false;
  }
  else
  {
    u32 entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_256);
    u32 nonce_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_256) / (u32)2U;
    u32 min_entropy = entropy_input_len + nonce_len;
    KRML_CHECK_SIZE(sizeof (u8), min_entropy);
    {
      u8 entropy[min_entropy];
      memset(entropy, 0U, min_entropy * sizeof entropy[0U]);
      {
        bool ok = Lib_RandomBuffer_System_randombytes(entropy, min_entropy);
        if (!ok)
        {
          return false;
        }
        else
        {
          u8 *entropy_input = entropy;
          u8 *nonce = entropy + entropy_input_len;
          EverCrypt_DRBG_state_s st_s = *st;
          KRML_CHECK_SIZE(sizeof (u8), entropy_input_len + nonce_len + personalization_string_len);
          {
            u8 seed_material[entropy_input_len + nonce_len + personalization_string_len];
            memset(seed_material,
              0U,
              (entropy_input_len + nonce_len + personalization_string_len)
              * sizeof seed_material[0U]);
            memcpy(seed_material, entropy_input, entropy_input_len * sizeof entropy_input[0U]);
            memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof nonce[0U]);
            memcpy(seed_material + entropy_input_len + nonce_len,
              personalization_string,
              personalization_string_len * sizeof personalization_string[0U]);
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
              {
                u8 *k1 = scrut.k;
                u8 *v1 = scrut.v;
                u32 *ctr = scrut.reseed_counter;
                memset(k1, 0U, (u32)32U * sizeof k1[0U]);
                memset(v1, (u8)1U, (u32)32U * sizeof v1[0U]);
                ctr[0U] = (u32)1U;
                {
                  u32
                  input_len = (u32)33U + entropy_input_len + nonce_len + personalization_string_len;
                  KRML_CHECK_SIZE(sizeof (u8), input_len);
                  {
                    u8 input0[input_len];
                    memset(input0, 0U, input_len * sizeof input0[0U]);
                    {
                      u8 *k_ = input0;
                      memcpy(k_, v1, (u32)32U * sizeof v1[0U]);
                      if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                      {
                        memcpy(input0 + (u32)33U,
                          seed_material,
                          (entropy_input_len + nonce_len + personalization_string_len)
                          * sizeof seed_material[0U]);
                      }
                      input0[32U] = (u8)0U;
                      EverCrypt_HMAC_compute_sha2_256(k_, k1, (u32)32U, input0, input_len);
                      EverCrypt_HMAC_compute_sha2_256(v1, k_, (u32)32U, v1, (u32)32U);
                      memcpy(k1, k_, (u32)32U * sizeof k_[0U]);
                      if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                      {
                        u32
                        input_len0 =
                          (u32)33U
                          + entropy_input_len + nonce_len + personalization_string_len;
                        KRML_CHECK_SIZE(sizeof (u8), input_len0);
                        {
                          u8 input[input_len0];
                          memset(input, 0U, input_len0 * sizeof input[0U]);
                          {
                            u8 *k_0 = input;
                            memcpy(k_0, v1, (u32)32U * sizeof v1[0U]);
                            if
                            (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                            {
                              memcpy(input + (u32)33U,
                                seed_material,
                                (entropy_input_len + nonce_len + personalization_string_len)
                                * sizeof seed_material[0U]);
                            }
                            input[32U] = (u8)1U;
                            EverCrypt_HMAC_compute_sha2_256(k_0, k1, (u32)32U, input, input_len0);
                            EverCrypt_HMAC_compute_sha2_256(v1, k_0, (u32)32U, v1, (u32)32U);
                            memcpy(k1, k_0, (u32)32U * sizeof k_0[0U]);
                          }
                        }
                      }
                      return true;
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

bool
EverCrypt_DRBG_instantiate_sha2_384(
  EverCrypt_DRBG_state_s *st,
  u8 *personalization_string,
  u32 personalization_string_len
)
{
  if (personalization_string_len > Hacl_HMAC_DRBG_max_personalization_string_length)
  {
    return false;
  }
  else
  {
    u32 entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_384);
    u32 nonce_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_384) / (u32)2U;
    u32 min_entropy = entropy_input_len + nonce_len;
    KRML_CHECK_SIZE(sizeof (u8), min_entropy);
    {
      u8 entropy[min_entropy];
      memset(entropy, 0U, min_entropy * sizeof entropy[0U]);
      {
        bool ok = Lib_RandomBuffer_System_randombytes(entropy, min_entropy);
        if (!ok)
        {
          return false;
        }
        else
        {
          u8 *entropy_input = entropy;
          u8 *nonce = entropy + entropy_input_len;
          EverCrypt_DRBG_state_s st_s = *st;
          KRML_CHECK_SIZE(sizeof (u8), entropy_input_len + nonce_len + personalization_string_len);
          {
            u8 seed_material[entropy_input_len + nonce_len + personalization_string_len];
            memset(seed_material,
              0U,
              (entropy_input_len + nonce_len + personalization_string_len)
              * sizeof seed_material[0U]);
            memcpy(seed_material, entropy_input, entropy_input_len * sizeof entropy_input[0U]);
            memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof nonce[0U]);
            memcpy(seed_material + entropy_input_len + nonce_len,
              personalization_string,
              personalization_string_len * sizeof personalization_string[0U]);
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
              {
                u8 *k1 = scrut.k;
                u8 *v1 = scrut.v;
                u32 *ctr = scrut.reseed_counter;
                memset(k1, 0U, (u32)48U * sizeof k1[0U]);
                memset(v1, (u8)1U, (u32)48U * sizeof v1[0U]);
                ctr[0U] = (u32)1U;
                {
                  u32
                  input_len = (u32)49U + entropy_input_len + nonce_len + personalization_string_len;
                  KRML_CHECK_SIZE(sizeof (u8), input_len);
                  {
                    u8 input0[input_len];
                    memset(input0, 0U, input_len * sizeof input0[0U]);
                    {
                      u8 *k_ = input0;
                      memcpy(k_, v1, (u32)48U * sizeof v1[0U]);
                      if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                      {
                        memcpy(input0 + (u32)49U,
                          seed_material,
                          (entropy_input_len + nonce_len + personalization_string_len)
                          * sizeof seed_material[0U]);
                      }
                      input0[48U] = (u8)0U;
                      EverCrypt_HMAC_compute_sha2_384(k_, k1, (u32)48U, input0, input_len);
                      EverCrypt_HMAC_compute_sha2_384(v1, k_, (u32)48U, v1, (u32)48U);
                      memcpy(k1, k_, (u32)48U * sizeof k_[0U]);
                      if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                      {
                        u32
                        input_len0 =
                          (u32)49U
                          + entropy_input_len + nonce_len + personalization_string_len;
                        KRML_CHECK_SIZE(sizeof (u8), input_len0);
                        {
                          u8 input[input_len0];
                          memset(input, 0U, input_len0 * sizeof input[0U]);
                          {
                            u8 *k_0 = input;
                            memcpy(k_0, v1, (u32)48U * sizeof v1[0U]);
                            if
                            (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                            {
                              memcpy(input + (u32)49U,
                                seed_material,
                                (entropy_input_len + nonce_len + personalization_string_len)
                                * sizeof seed_material[0U]);
                            }
                            input[48U] = (u8)1U;
                            EverCrypt_HMAC_compute_sha2_384(k_0, k1, (u32)48U, input, input_len0);
                            EverCrypt_HMAC_compute_sha2_384(v1, k_0, (u32)48U, v1, (u32)48U);
                            memcpy(k1, k_0, (u32)48U * sizeof k_0[0U]);
                          }
                        }
                      }
                      return true;
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

bool
EverCrypt_DRBG_instantiate_sha2_512(
  EverCrypt_DRBG_state_s *st,
  u8 *personalization_string,
  u32 personalization_string_len
)
{
  if (personalization_string_len > Hacl_HMAC_DRBG_max_personalization_string_length)
  {
    return false;
  }
  else
  {
    u32 entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_512);
    u32 nonce_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_512) / (u32)2U;
    u32 min_entropy = entropy_input_len + nonce_len;
    KRML_CHECK_SIZE(sizeof (u8), min_entropy);
    {
      u8 entropy[min_entropy];
      memset(entropy, 0U, min_entropy * sizeof entropy[0U]);
      {
        bool ok = Lib_RandomBuffer_System_randombytes(entropy, min_entropy);
        if (!ok)
        {
          return false;
        }
        else
        {
          u8 *entropy_input = entropy;
          u8 *nonce = entropy + entropy_input_len;
          EverCrypt_DRBG_state_s st_s = *st;
          KRML_CHECK_SIZE(sizeof (u8), entropy_input_len + nonce_len + personalization_string_len);
          {
            u8 seed_material[entropy_input_len + nonce_len + personalization_string_len];
            memset(seed_material,
              0U,
              (entropy_input_len + nonce_len + personalization_string_len)
              * sizeof seed_material[0U]);
            memcpy(seed_material, entropy_input, entropy_input_len * sizeof entropy_input[0U]);
            memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof nonce[0U]);
            memcpy(seed_material + entropy_input_len + nonce_len,
              personalization_string,
              personalization_string_len * sizeof personalization_string[0U]);
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
              {
                u8 *k1 = scrut.k;
                u8 *v1 = scrut.v;
                u32 *ctr = scrut.reseed_counter;
                memset(k1, 0U, (u32)64U * sizeof k1[0U]);
                memset(v1, (u8)1U, (u32)64U * sizeof v1[0U]);
                ctr[0U] = (u32)1U;
                {
                  u32
                  input_len = (u32)65U + entropy_input_len + nonce_len + personalization_string_len;
                  KRML_CHECK_SIZE(sizeof (u8), input_len);
                  {
                    u8 input0[input_len];
                    memset(input0, 0U, input_len * sizeof input0[0U]);
                    {
                      u8 *k_ = input0;
                      memcpy(k_, v1, (u32)64U * sizeof v1[0U]);
                      if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                      {
                        memcpy(input0 + (u32)65U,
                          seed_material,
                          (entropy_input_len + nonce_len + personalization_string_len)
                          * sizeof seed_material[0U]);
                      }
                      input0[64U] = (u8)0U;
                      EverCrypt_HMAC_compute_sha2_512(k_, k1, (u32)64U, input0, input_len);
                      EverCrypt_HMAC_compute_sha2_512(v1, k_, (u32)64U, v1, (u32)64U);
                      memcpy(k1, k_, (u32)64U * sizeof k_[0U]);
                      if (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                      {
                        u32
                        input_len0 =
                          (u32)65U
                          + entropy_input_len + nonce_len + personalization_string_len;
                        KRML_CHECK_SIZE(sizeof (u8), input_len0);
                        {
                          u8 input[input_len0];
                          memset(input, 0U, input_len0 * sizeof input[0U]);
                          {
                            u8 *k_0 = input;
                            memcpy(k_0, v1, (u32)64U * sizeof v1[0U]);
                            if
                            (entropy_input_len + nonce_len + personalization_string_len != (u32)0U)
                            {
                              memcpy(input + (u32)65U,
                                seed_material,
                                (entropy_input_len + nonce_len + personalization_string_len)
                                * sizeof seed_material[0U]);
                            }
                            input[64U] = (u8)1U;
                            EverCrypt_HMAC_compute_sha2_512(k_0, k1, (u32)64U, input, input_len0);
                            EverCrypt_HMAC_compute_sha2_512(v1, k_0, (u32)64U, v1, (u32)64U);
                            memcpy(k1, k_0, (u32)64U * sizeof k_0[0U]);
                          }
                        }
                      }
                      return true;
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

bool
EverCrypt_DRBG_reseed_sha1(
  EverCrypt_DRBG_state_s *st,
  u8 *additional_input,
  u32 additional_input_len
)
{
  if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
  {
    return false;
  }
  else
  {
    u32 entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA1);
    KRML_CHECK_SIZE(sizeof (u8), entropy_input_len);
    {
      u8 entropy_input[entropy_input_len];
      memset(entropy_input, 0U, entropy_input_len * sizeof entropy_input[0U]);
      {
        bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len);
        if (!ok)
        {
          return false;
        }
        else
        {
          EverCrypt_DRBG_state_s st_s = *st;
          KRML_CHECK_SIZE(sizeof (u8), entropy_input_len + additional_input_len);
          {
            u8 seed_material[entropy_input_len + additional_input_len];
            memset(seed_material,
              0U,
              (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
            memcpy(seed_material, entropy_input, entropy_input_len * sizeof entropy_input[0U]);
            memcpy(seed_material + entropy_input_len,
              additional_input,
              additional_input_len * sizeof additional_input[0U]);
            {
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
              {
                u8 *k1 = uu____0.k;
                u8 *v1 = uu____0.v;
                u32 *ctr = uu____0.reseed_counter;
                u32 input_len = (u32)21U + entropy_input_len + additional_input_len;
                KRML_CHECK_SIZE(sizeof (u8), input_len);
                {
                  u8 input0[input_len];
                  memset(input0, 0U, input_len * sizeof input0[0U]);
                  {
                    u8 *k_ = input0;
                    memcpy(k_, v1, (u32)20U * sizeof v1[0U]);
                    if (entropy_input_len + additional_input_len != (u32)0U)
                    {
                      memcpy(input0 + (u32)21U,
                        seed_material,
                        (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
                    }
                    input0[20U] = (u8)0U;
                    EverCrypt_HMAC_compute_sha1(k_, k1, (u32)20U, input0, input_len);
                    EverCrypt_HMAC_compute_sha1(v1, k_, (u32)20U, v1, (u32)20U);
                    memcpy(k1, k_, (u32)20U * sizeof k_[0U]);
                    if (entropy_input_len + additional_input_len != (u32)0U)
                    {
                      u32 input_len0 = (u32)21U + entropy_input_len + additional_input_len;
                      KRML_CHECK_SIZE(sizeof (u8), input_len0);
                      {
                        u8 input[input_len0];
                        memset(input, 0U, input_len0 * sizeof input[0U]);
                        {
                          u8 *k_0 = input;
                          memcpy(k_0, v1, (u32)20U * sizeof v1[0U]);
                          if (entropy_input_len + additional_input_len != (u32)0U)
                          {
                            memcpy(input + (u32)21U,
                              seed_material,
                              (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
                          }
                          input[20U] = (u8)1U;
                          EverCrypt_HMAC_compute_sha1(k_0, k1, (u32)20U, input, input_len0);
                          EverCrypt_HMAC_compute_sha1(v1, k_0, (u32)20U, v1, (u32)20U);
                          memcpy(k1, k_0, (u32)20U * sizeof k_0[0U]);
                        }
                      }
                    }
                    ctr[0U] = (u32)1U;
                    return true;
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

bool
EverCrypt_DRBG_reseed_sha2_256(
  EverCrypt_DRBG_state_s *st,
  u8 *additional_input,
  u32 additional_input_len
)
{
  if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
  {
    return false;
  }
  else
  {
    u32 entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_256);
    KRML_CHECK_SIZE(sizeof (u8), entropy_input_len);
    {
      u8 entropy_input[entropy_input_len];
      memset(entropy_input, 0U, entropy_input_len * sizeof entropy_input[0U]);
      {
        bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len);
        if (!ok)
        {
          return false;
        }
        else
        {
          EverCrypt_DRBG_state_s st_s = *st;
          KRML_CHECK_SIZE(sizeof (u8), entropy_input_len + additional_input_len);
          {
            u8 seed_material[entropy_input_len + additional_input_len];
            memset(seed_material,
              0U,
              (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
            memcpy(seed_material, entropy_input, entropy_input_len * sizeof entropy_input[0U]);
            memcpy(seed_material + entropy_input_len,
              additional_input,
              additional_input_len * sizeof additional_input[0U]);
            {
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
              {
                u8 *k1 = uu____0.k;
                u8 *v1 = uu____0.v;
                u32 *ctr = uu____0.reseed_counter;
                u32 input_len = (u32)33U + entropy_input_len + additional_input_len;
                KRML_CHECK_SIZE(sizeof (u8), input_len);
                {
                  u8 input0[input_len];
                  memset(input0, 0U, input_len * sizeof input0[0U]);
                  {
                    u8 *k_ = input0;
                    memcpy(k_, v1, (u32)32U * sizeof v1[0U]);
                    if (entropy_input_len + additional_input_len != (u32)0U)
                    {
                      memcpy(input0 + (u32)33U,
                        seed_material,
                        (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
                    }
                    input0[32U] = (u8)0U;
                    EverCrypt_HMAC_compute_sha2_256(k_, k1, (u32)32U, input0, input_len);
                    EverCrypt_HMAC_compute_sha2_256(v1, k_, (u32)32U, v1, (u32)32U);
                    memcpy(k1, k_, (u32)32U * sizeof k_[0U]);
                    if (entropy_input_len + additional_input_len != (u32)0U)
                    {
                      u32 input_len0 = (u32)33U + entropy_input_len + additional_input_len;
                      KRML_CHECK_SIZE(sizeof (u8), input_len0);
                      {
                        u8 input[input_len0];
                        memset(input, 0U, input_len0 * sizeof input[0U]);
                        {
                          u8 *k_0 = input;
                          memcpy(k_0, v1, (u32)32U * sizeof v1[0U]);
                          if (entropy_input_len + additional_input_len != (u32)0U)
                          {
                            memcpy(input + (u32)33U,
                              seed_material,
                              (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
                          }
                          input[32U] = (u8)1U;
                          EverCrypt_HMAC_compute_sha2_256(k_0, k1, (u32)32U, input, input_len0);
                          EverCrypt_HMAC_compute_sha2_256(v1, k_0, (u32)32U, v1, (u32)32U);
                          memcpy(k1, k_0, (u32)32U * sizeof k_0[0U]);
                        }
                      }
                    }
                    ctr[0U] = (u32)1U;
                    return true;
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

bool
EverCrypt_DRBG_reseed_sha2_384(
  EverCrypt_DRBG_state_s *st,
  u8 *additional_input,
  u32 additional_input_len
)
{
  if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
  {
    return false;
  }
  else
  {
    u32 entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_384);
    KRML_CHECK_SIZE(sizeof (u8), entropy_input_len);
    {
      u8 entropy_input[entropy_input_len];
      memset(entropy_input, 0U, entropy_input_len * sizeof entropy_input[0U]);
      {
        bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len);
        if (!ok)
        {
          return false;
        }
        else
        {
          EverCrypt_DRBG_state_s st_s = *st;
          KRML_CHECK_SIZE(sizeof (u8), entropy_input_len + additional_input_len);
          {
            u8 seed_material[entropy_input_len + additional_input_len];
            memset(seed_material,
              0U,
              (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
            memcpy(seed_material, entropy_input, entropy_input_len * sizeof entropy_input[0U]);
            memcpy(seed_material + entropy_input_len,
              additional_input,
              additional_input_len * sizeof additional_input[0U]);
            {
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
              {
                u8 *k1 = uu____0.k;
                u8 *v1 = uu____0.v;
                u32 *ctr = uu____0.reseed_counter;
                u32 input_len = (u32)49U + entropy_input_len + additional_input_len;
                KRML_CHECK_SIZE(sizeof (u8), input_len);
                {
                  u8 input0[input_len];
                  memset(input0, 0U, input_len * sizeof input0[0U]);
                  {
                    u8 *k_ = input0;
                    memcpy(k_, v1, (u32)48U * sizeof v1[0U]);
                    if (entropy_input_len + additional_input_len != (u32)0U)
                    {
                      memcpy(input0 + (u32)49U,
                        seed_material,
                        (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
                    }
                    input0[48U] = (u8)0U;
                    EverCrypt_HMAC_compute_sha2_384(k_, k1, (u32)48U, input0, input_len);
                    EverCrypt_HMAC_compute_sha2_384(v1, k_, (u32)48U, v1, (u32)48U);
                    memcpy(k1, k_, (u32)48U * sizeof k_[0U]);
                    if (entropy_input_len + additional_input_len != (u32)0U)
                    {
                      u32 input_len0 = (u32)49U + entropy_input_len + additional_input_len;
                      KRML_CHECK_SIZE(sizeof (u8), input_len0);
                      {
                        u8 input[input_len0];
                        memset(input, 0U, input_len0 * sizeof input[0U]);
                        {
                          u8 *k_0 = input;
                          memcpy(k_0, v1, (u32)48U * sizeof v1[0U]);
                          if (entropy_input_len + additional_input_len != (u32)0U)
                          {
                            memcpy(input + (u32)49U,
                              seed_material,
                              (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
                          }
                          input[48U] = (u8)1U;
                          EverCrypt_HMAC_compute_sha2_384(k_0, k1, (u32)48U, input, input_len0);
                          EverCrypt_HMAC_compute_sha2_384(v1, k_0, (u32)48U, v1, (u32)48U);
                          memcpy(k1, k_0, (u32)48U * sizeof k_0[0U]);
                        }
                      }
                    }
                    ctr[0U] = (u32)1U;
                    return true;
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

bool
EverCrypt_DRBG_reseed_sha2_512(
  EverCrypt_DRBG_state_s *st,
  u8 *additional_input,
  u32 additional_input_len
)
{
  if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
  {
    return false;
  }
  else
  {
    u32 entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_512);
    KRML_CHECK_SIZE(sizeof (u8), entropy_input_len);
    {
      u8 entropy_input[entropy_input_len];
      memset(entropy_input, 0U, entropy_input_len * sizeof entropy_input[0U]);
      {
        bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len);
        if (!ok)
        {
          return false;
        }
        else
        {
          EverCrypt_DRBG_state_s st_s = *st;
          KRML_CHECK_SIZE(sizeof (u8), entropy_input_len + additional_input_len);
          {
            u8 seed_material[entropy_input_len + additional_input_len];
            memset(seed_material,
              0U,
              (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
            memcpy(seed_material, entropy_input, entropy_input_len * sizeof entropy_input[0U]);
            memcpy(seed_material + entropy_input_len,
              additional_input,
              additional_input_len * sizeof additional_input[0U]);
            {
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
              {
                u8 *k1 = uu____0.k;
                u8 *v1 = uu____0.v;
                u32 *ctr = uu____0.reseed_counter;
                u32 input_len = (u32)65U + entropy_input_len + additional_input_len;
                KRML_CHECK_SIZE(sizeof (u8), input_len);
                {
                  u8 input0[input_len];
                  memset(input0, 0U, input_len * sizeof input0[0U]);
                  {
                    u8 *k_ = input0;
                    memcpy(k_, v1, (u32)64U * sizeof v1[0U]);
                    if (entropy_input_len + additional_input_len != (u32)0U)
                    {
                      memcpy(input0 + (u32)65U,
                        seed_material,
                        (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
                    }
                    input0[64U] = (u8)0U;
                    EverCrypt_HMAC_compute_sha2_512(k_, k1, (u32)64U, input0, input_len);
                    EverCrypt_HMAC_compute_sha2_512(v1, k_, (u32)64U, v1, (u32)64U);
                    memcpy(k1, k_, (u32)64U * sizeof k_[0U]);
                    if (entropy_input_len + additional_input_len != (u32)0U)
                    {
                      u32 input_len0 = (u32)65U + entropy_input_len + additional_input_len;
                      KRML_CHECK_SIZE(sizeof (u8), input_len0);
                      {
                        u8 input[input_len0];
                        memset(input, 0U, input_len0 * sizeof input[0U]);
                        {
                          u8 *k_0 = input;
                          memcpy(k_0, v1, (u32)64U * sizeof v1[0U]);
                          if (entropy_input_len + additional_input_len != (u32)0U)
                          {
                            memcpy(input + (u32)65U,
                              seed_material,
                              (entropy_input_len + additional_input_len) * sizeof seed_material[0U]);
                          }
                          input[64U] = (u8)1U;
                          EverCrypt_HMAC_compute_sha2_512(k_0, k1, (u32)64U, input, input_len0);
                          EverCrypt_HMAC_compute_sha2_512(v1, k_0, (u32)64U, v1, (u32)64U);
                          memcpy(k1, k_0, (u32)64U * sizeof k_0[0U]);
                        }
                      }
                    }
                    ctr[0U] = (u32)1U;
                    return true;
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

bool
EverCrypt_DRBG_generate_sha1(
  u8 *output,
  EverCrypt_DRBG_state_s *st,
  u32 n1,
  u8 *additional_input,
  u32 additional_input_len
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
  else
  {
    u32 entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA1);
    bool ok0;
    if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
    {
      ok0 = false;
    }
    else
    {
      u32 entropy_input_len1 = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA1);
      KRML_CHECK_SIZE(sizeof (u8), entropy_input_len1);
      {
        u8 entropy_input[entropy_input_len1];
        memset(entropy_input, 0U, entropy_input_len1 * sizeof entropy_input[0U]);
        {
          bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len1);
          bool result;
          if (!ok)
          {
            result = false;
          }
          else
          {
            EverCrypt_DRBG_state_s st_s = *st;
            KRML_CHECK_SIZE(sizeof (u8), entropy_input_len1 + additional_input_len);
            {
              u8 seed_material[entropy_input_len1 + additional_input_len];
              memset(seed_material,
                0U,
                (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
              memcpy(seed_material, entropy_input, entropy_input_len1 * sizeof entropy_input[0U]);
              memcpy(seed_material + entropy_input_len1,
                additional_input,
                additional_input_len * sizeof additional_input[0U]);
              {
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
                {
                  u8 *k1 = uu____0.k;
                  u8 *v1 = uu____0.v;
                  u32 *ctr = uu____0.reseed_counter;
                  u32 input_len = (u32)21U + entropy_input_len1 + additional_input_len;
                  KRML_CHECK_SIZE(sizeof (u8), input_len);
                  {
                    u8 input0[input_len];
                    memset(input0, 0U, input_len * sizeof input0[0U]);
                    {
                      u8 *k_ = input0;
                      memcpy(k_, v1, (u32)20U * sizeof v1[0U]);
                      if (entropy_input_len1 + additional_input_len != (u32)0U)
                      {
                        memcpy(input0 + (u32)21U,
                          seed_material,
                          (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
                      }
                      input0[20U] = (u8)0U;
                      EverCrypt_HMAC_compute_sha1(k_, k1, (u32)20U, input0, input_len);
                      EverCrypt_HMAC_compute_sha1(v1, k_, (u32)20U, v1, (u32)20U);
                      memcpy(k1, k_, (u32)20U * sizeof k_[0U]);
                      if (entropy_input_len1 + additional_input_len != (u32)0U)
                      {
                        u32 input_len0 = (u32)21U + entropy_input_len1 + additional_input_len;
                        KRML_CHECK_SIZE(sizeof (u8), input_len0);
                        {
                          u8 input[input_len0];
                          memset(input, 0U, input_len0 * sizeof input[0U]);
                          {
                            u8 *k_0 = input;
                            memcpy(k_0, v1, (u32)20U * sizeof v1[0U]);
                            if (entropy_input_len1 + additional_input_len != (u32)0U)
                            {
                              memcpy(input + (u32)21U,
                                seed_material,
                                (entropy_input_len1 + additional_input_len)
                                * sizeof seed_material[0U]);
                            }
                            input[20U] = (u8)1U;
                            EverCrypt_HMAC_compute_sha1(k_0, k1, (u32)20U, input, input_len0);
                            EverCrypt_HMAC_compute_sha1(v1, k_0, (u32)20U, v1, (u32)20U);
                            memcpy(k1, k_0, (u32)20U * sizeof k_0[0U]);
                          }
                        }
                      }
                      ctr[0U] = (u32)1U;
                      result = true;
                    }
                  }
                }
              }
            }
          }
          ok0 = result;
        }
      }
    }
    if (!ok0)
    {
      return false;
    }
    else
    {
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
      {
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
          {
            u8 *k1 = scrut.k;
            u8 *v1 = scrut.v;
            u32 *ctr = scrut.reseed_counter;
            if (additional_input_len > (u32)0U)
            {
              u32 input_len = (u32)21U + additional_input_len;
              KRML_CHECK_SIZE(sizeof (u8), input_len);
              {
                u8 input0[input_len];
                memset(input0, 0U, input_len * sizeof input0[0U]);
                {
                  u8 *k_ = input0;
                  memcpy(k_, v1, (u32)20U * sizeof v1[0U]);
                  if (additional_input_len != (u32)0U)
                  {
                    memcpy(input0 + (u32)21U,
                      additional_input,
                      additional_input_len * sizeof additional_input[0U]);
                  }
                  input0[20U] = (u8)0U;
                  EverCrypt_HMAC_compute_sha1(k_, k1, (u32)20U, input0, input_len);
                  EverCrypt_HMAC_compute_sha1(v1, k_, (u32)20U, v1, (u32)20U);
                  memcpy(k1, k_, (u32)20U * sizeof k_[0U]);
                  if (additional_input_len != (u32)0U)
                  {
                    u32 input_len0 = (u32)21U + additional_input_len;
                    KRML_CHECK_SIZE(sizeof (u8), input_len0);
                    {
                      u8 input[input_len0];
                      memset(input, 0U, input_len0 * sizeof input[0U]);
                      {
                        u8 *k_0 = input;
                        memcpy(k_0, v1, (u32)20U * sizeof v1[0U]);
                        if (additional_input_len != (u32)0U)
                        {
                          memcpy(input + (u32)21U,
                            additional_input,
                            additional_input_len * sizeof additional_input[0U]);
                        }
                        input[20U] = (u8)1U;
                        EverCrypt_HMAC_compute_sha1(k_0, k1, (u32)20U, input, input_len0);
                        EverCrypt_HMAC_compute_sha1(v1, k_0, (u32)20U, v1, (u32)20U);
                        memcpy(k1, k_0, (u32)20U * sizeof k_0[0U]);
                      }
                    }
                  }
                }
              }
            }
            {
              u8 *output1 = output;
              u32 max1 = n1 / (u32)20U;
              u8 *out = output1;
              {
                u32 i;
                for (i = (u32)0U; i < max1; i = i + (u32)1U)
                {
                  EverCrypt_HMAC_compute_sha1(v1, k1, (u32)20U, v1, (u32)20U);
                  memcpy(out + i * (u32)20U, v1, (u32)20U * sizeof v1[0U]);
                }
              }
              if (max1 * (u32)20U < n1)
              {
                u8 *block = output1 + max1 * (u32)20U;
                EverCrypt_HMAC_compute_sha1(v1, k1, (u32)20U, v1, (u32)20U);
                memcpy(block, v1, (n1 - max1 * (u32)20U) * sizeof v1[0U]);
              }
              {
                u32 input_len = (u32)21U + additional_input_len;
                KRML_CHECK_SIZE(sizeof (u8), input_len);
                {
                  u8 input0[input_len];
                  memset(input0, 0U, input_len * sizeof input0[0U]);
                  {
                    u8 *k_ = input0;
                    memcpy(k_, v1, (u32)20U * sizeof v1[0U]);
                    if (additional_input_len != (u32)0U)
                    {
                      memcpy(input0 + (u32)21U,
                        additional_input,
                        additional_input_len * sizeof additional_input[0U]);
                    }
                    input0[20U] = (u8)0U;
                    EverCrypt_HMAC_compute_sha1(k_, k1, (u32)20U, input0, input_len);
                    EverCrypt_HMAC_compute_sha1(v1, k_, (u32)20U, v1, (u32)20U);
                    memcpy(k1, k_, (u32)20U * sizeof k_[0U]);
                    if (additional_input_len != (u32)0U)
                    {
                      u32 input_len0 = (u32)21U + additional_input_len;
                      KRML_CHECK_SIZE(sizeof (u8), input_len0);
                      {
                        u8 input[input_len0];
                        memset(input, 0U, input_len0 * sizeof input[0U]);
                        {
                          u8 *k_0 = input;
                          memcpy(k_0, v1, (u32)20U * sizeof v1[0U]);
                          if (additional_input_len != (u32)0U)
                          {
                            memcpy(input + (u32)21U,
                              additional_input,
                              additional_input_len * sizeof additional_input[0U]);
                          }
                          input[20U] = (u8)1U;
                          EverCrypt_HMAC_compute_sha1(k_0, k1, (u32)20U, input, input_len0);
                          EverCrypt_HMAC_compute_sha1(v1, k_0, (u32)20U, v1, (u32)20U);
                          memcpy(k1, k_0, (u32)20U * sizeof k_0[0U]);
                        }
                      }
                    }
                    {
                      u32 old_ctr = ctr[0U];
                      ctr[0U] = old_ctr + (u32)1U;
                      b = true;
                    }
                  }
                }
              }
            }
          }
        }
        return true;
      }
    }
  }
}

bool
EverCrypt_DRBG_generate_sha2_256(
  u8 *output,
  EverCrypt_DRBG_state_s *st,
  u32 n1,
  u8 *additional_input,
  u32 additional_input_len
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
  else
  {
    u32 entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_256);
    bool ok0;
    if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
    {
      ok0 = false;
    }
    else
    {
      u32 entropy_input_len1 = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_256);
      KRML_CHECK_SIZE(sizeof (u8), entropy_input_len1);
      {
        u8 entropy_input[entropy_input_len1];
        memset(entropy_input, 0U, entropy_input_len1 * sizeof entropy_input[0U]);
        {
          bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len1);
          bool result;
          if (!ok)
          {
            result = false;
          }
          else
          {
            EverCrypt_DRBG_state_s st_s = *st;
            KRML_CHECK_SIZE(sizeof (u8), entropy_input_len1 + additional_input_len);
            {
              u8 seed_material[entropy_input_len1 + additional_input_len];
              memset(seed_material,
                0U,
                (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
              memcpy(seed_material, entropy_input, entropy_input_len1 * sizeof entropy_input[0U]);
              memcpy(seed_material + entropy_input_len1,
                additional_input,
                additional_input_len * sizeof additional_input[0U]);
              {
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
                {
                  u8 *k1 = uu____0.k;
                  u8 *v1 = uu____0.v;
                  u32 *ctr = uu____0.reseed_counter;
                  u32 input_len = (u32)33U + entropy_input_len1 + additional_input_len;
                  KRML_CHECK_SIZE(sizeof (u8), input_len);
                  {
                    u8 input0[input_len];
                    memset(input0, 0U, input_len * sizeof input0[0U]);
                    {
                      u8 *k_ = input0;
                      memcpy(k_, v1, (u32)32U * sizeof v1[0U]);
                      if (entropy_input_len1 + additional_input_len != (u32)0U)
                      {
                        memcpy(input0 + (u32)33U,
                          seed_material,
                          (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
                      }
                      input0[32U] = (u8)0U;
                      EverCrypt_HMAC_compute_sha2_256(k_, k1, (u32)32U, input0, input_len);
                      EverCrypt_HMAC_compute_sha2_256(v1, k_, (u32)32U, v1, (u32)32U);
                      memcpy(k1, k_, (u32)32U * sizeof k_[0U]);
                      if (entropy_input_len1 + additional_input_len != (u32)0U)
                      {
                        u32 input_len0 = (u32)33U + entropy_input_len1 + additional_input_len;
                        KRML_CHECK_SIZE(sizeof (u8), input_len0);
                        {
                          u8 input[input_len0];
                          memset(input, 0U, input_len0 * sizeof input[0U]);
                          {
                            u8 *k_0 = input;
                            memcpy(k_0, v1, (u32)32U * sizeof v1[0U]);
                            if (entropy_input_len1 + additional_input_len != (u32)0U)
                            {
                              memcpy(input + (u32)33U,
                                seed_material,
                                (entropy_input_len1 + additional_input_len)
                                * sizeof seed_material[0U]);
                            }
                            input[32U] = (u8)1U;
                            EverCrypt_HMAC_compute_sha2_256(k_0, k1, (u32)32U, input, input_len0);
                            EverCrypt_HMAC_compute_sha2_256(v1, k_0, (u32)32U, v1, (u32)32U);
                            memcpy(k1, k_0, (u32)32U * sizeof k_0[0U]);
                          }
                        }
                      }
                      ctr[0U] = (u32)1U;
                      result = true;
                    }
                  }
                }
              }
            }
          }
          ok0 = result;
        }
      }
    }
    if (!ok0)
    {
      return false;
    }
    else
    {
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
      {
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
          {
            u8 *k1 = scrut.k;
            u8 *v1 = scrut.v;
            u32 *ctr = scrut.reseed_counter;
            if (additional_input_len > (u32)0U)
            {
              u32 input_len = (u32)33U + additional_input_len;
              KRML_CHECK_SIZE(sizeof (u8), input_len);
              {
                u8 input0[input_len];
                memset(input0, 0U, input_len * sizeof input0[0U]);
                {
                  u8 *k_ = input0;
                  memcpy(k_, v1, (u32)32U * sizeof v1[0U]);
                  if (additional_input_len != (u32)0U)
                  {
                    memcpy(input0 + (u32)33U,
                      additional_input,
                      additional_input_len * sizeof additional_input[0U]);
                  }
                  input0[32U] = (u8)0U;
                  EverCrypt_HMAC_compute_sha2_256(k_, k1, (u32)32U, input0, input_len);
                  EverCrypt_HMAC_compute_sha2_256(v1, k_, (u32)32U, v1, (u32)32U);
                  memcpy(k1, k_, (u32)32U * sizeof k_[0U]);
                  if (additional_input_len != (u32)0U)
                  {
                    u32 input_len0 = (u32)33U + additional_input_len;
                    KRML_CHECK_SIZE(sizeof (u8), input_len0);
                    {
                      u8 input[input_len0];
                      memset(input, 0U, input_len0 * sizeof input[0U]);
                      {
                        u8 *k_0 = input;
                        memcpy(k_0, v1, (u32)32U * sizeof v1[0U]);
                        if (additional_input_len != (u32)0U)
                        {
                          memcpy(input + (u32)33U,
                            additional_input,
                            additional_input_len * sizeof additional_input[0U]);
                        }
                        input[32U] = (u8)1U;
                        EverCrypt_HMAC_compute_sha2_256(k_0, k1, (u32)32U, input, input_len0);
                        EverCrypt_HMAC_compute_sha2_256(v1, k_0, (u32)32U, v1, (u32)32U);
                        memcpy(k1, k_0, (u32)32U * sizeof k_0[0U]);
                      }
                    }
                  }
                }
              }
            }
            {
              u8 *output1 = output;
              u32 max1 = n1 / (u32)32U;
              u8 *out = output1;
              {
                u32 i;
                for (i = (u32)0U; i < max1; i = i + (u32)1U)
                {
                  EverCrypt_HMAC_compute_sha2_256(v1, k1, (u32)32U, v1, (u32)32U);
                  memcpy(out + i * (u32)32U, v1, (u32)32U * sizeof v1[0U]);
                }
              }
              if (max1 * (u32)32U < n1)
              {
                u8 *block = output1 + max1 * (u32)32U;
                EverCrypt_HMAC_compute_sha2_256(v1, k1, (u32)32U, v1, (u32)32U);
                memcpy(block, v1, (n1 - max1 * (u32)32U) * sizeof v1[0U]);
              }
              {
                u32 input_len = (u32)33U + additional_input_len;
                KRML_CHECK_SIZE(sizeof (u8), input_len);
                {
                  u8 input0[input_len];
                  memset(input0, 0U, input_len * sizeof input0[0U]);
                  {
                    u8 *k_ = input0;
                    memcpy(k_, v1, (u32)32U * sizeof v1[0U]);
                    if (additional_input_len != (u32)0U)
                    {
                      memcpy(input0 + (u32)33U,
                        additional_input,
                        additional_input_len * sizeof additional_input[0U]);
                    }
                    input0[32U] = (u8)0U;
                    EverCrypt_HMAC_compute_sha2_256(k_, k1, (u32)32U, input0, input_len);
                    EverCrypt_HMAC_compute_sha2_256(v1, k_, (u32)32U, v1, (u32)32U);
                    memcpy(k1, k_, (u32)32U * sizeof k_[0U]);
                    if (additional_input_len != (u32)0U)
                    {
                      u32 input_len0 = (u32)33U + additional_input_len;
                      KRML_CHECK_SIZE(sizeof (u8), input_len0);
                      {
                        u8 input[input_len0];
                        memset(input, 0U, input_len0 * sizeof input[0U]);
                        {
                          u8 *k_0 = input;
                          memcpy(k_0, v1, (u32)32U * sizeof v1[0U]);
                          if (additional_input_len != (u32)0U)
                          {
                            memcpy(input + (u32)33U,
                              additional_input,
                              additional_input_len * sizeof additional_input[0U]);
                          }
                          input[32U] = (u8)1U;
                          EverCrypt_HMAC_compute_sha2_256(k_0, k1, (u32)32U, input, input_len0);
                          EverCrypt_HMAC_compute_sha2_256(v1, k_0, (u32)32U, v1, (u32)32U);
                          memcpy(k1, k_0, (u32)32U * sizeof k_0[0U]);
                        }
                      }
                    }
                    {
                      u32 old_ctr = ctr[0U];
                      ctr[0U] = old_ctr + (u32)1U;
                      b = true;
                    }
                  }
                }
              }
            }
          }
        }
        return true;
      }
    }
  }
}

bool
EverCrypt_DRBG_generate_sha2_384(
  u8 *output,
  EverCrypt_DRBG_state_s *st,
  u32 n1,
  u8 *additional_input,
  u32 additional_input_len
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
  else
  {
    u32 entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_384);
    bool ok0;
    if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
    {
      ok0 = false;
    }
    else
    {
      u32 entropy_input_len1 = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_384);
      KRML_CHECK_SIZE(sizeof (u8), entropy_input_len1);
      {
        u8 entropy_input[entropy_input_len1];
        memset(entropy_input, 0U, entropy_input_len1 * sizeof entropy_input[0U]);
        {
          bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len1);
          bool result;
          if (!ok)
          {
            result = false;
          }
          else
          {
            EverCrypt_DRBG_state_s st_s = *st;
            KRML_CHECK_SIZE(sizeof (u8), entropy_input_len1 + additional_input_len);
            {
              u8 seed_material[entropy_input_len1 + additional_input_len];
              memset(seed_material,
                0U,
                (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
              memcpy(seed_material, entropy_input, entropy_input_len1 * sizeof entropy_input[0U]);
              memcpy(seed_material + entropy_input_len1,
                additional_input,
                additional_input_len * sizeof additional_input[0U]);
              {
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
                {
                  u8 *k1 = uu____0.k;
                  u8 *v1 = uu____0.v;
                  u32 *ctr = uu____0.reseed_counter;
                  u32 input_len = (u32)49U + entropy_input_len1 + additional_input_len;
                  KRML_CHECK_SIZE(sizeof (u8), input_len);
                  {
                    u8 input0[input_len];
                    memset(input0, 0U, input_len * sizeof input0[0U]);
                    {
                      u8 *k_ = input0;
                      memcpy(k_, v1, (u32)48U * sizeof v1[0U]);
                      if (entropy_input_len1 + additional_input_len != (u32)0U)
                      {
                        memcpy(input0 + (u32)49U,
                          seed_material,
                          (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
                      }
                      input0[48U] = (u8)0U;
                      EverCrypt_HMAC_compute_sha2_384(k_, k1, (u32)48U, input0, input_len);
                      EverCrypt_HMAC_compute_sha2_384(v1, k_, (u32)48U, v1, (u32)48U);
                      memcpy(k1, k_, (u32)48U * sizeof k_[0U]);
                      if (entropy_input_len1 + additional_input_len != (u32)0U)
                      {
                        u32 input_len0 = (u32)49U + entropy_input_len1 + additional_input_len;
                        KRML_CHECK_SIZE(sizeof (u8), input_len0);
                        {
                          u8 input[input_len0];
                          memset(input, 0U, input_len0 * sizeof input[0U]);
                          {
                            u8 *k_0 = input;
                            memcpy(k_0, v1, (u32)48U * sizeof v1[0U]);
                            if (entropy_input_len1 + additional_input_len != (u32)0U)
                            {
                              memcpy(input + (u32)49U,
                                seed_material,
                                (entropy_input_len1 + additional_input_len)
                                * sizeof seed_material[0U]);
                            }
                            input[48U] = (u8)1U;
                            EverCrypt_HMAC_compute_sha2_384(k_0, k1, (u32)48U, input, input_len0);
                            EverCrypt_HMAC_compute_sha2_384(v1, k_0, (u32)48U, v1, (u32)48U);
                            memcpy(k1, k_0, (u32)48U * sizeof k_0[0U]);
                          }
                        }
                      }
                      ctr[0U] = (u32)1U;
                      result = true;
                    }
                  }
                }
              }
            }
          }
          ok0 = result;
        }
      }
    }
    if (!ok0)
    {
      return false;
    }
    else
    {
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
      {
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
          {
            u8 *k1 = scrut.k;
            u8 *v1 = scrut.v;
            u32 *ctr = scrut.reseed_counter;
            if (additional_input_len > (u32)0U)
            {
              u32 input_len = (u32)49U + additional_input_len;
              KRML_CHECK_SIZE(sizeof (u8), input_len);
              {
                u8 input0[input_len];
                memset(input0, 0U, input_len * sizeof input0[0U]);
                {
                  u8 *k_ = input0;
                  memcpy(k_, v1, (u32)48U * sizeof v1[0U]);
                  if (additional_input_len != (u32)0U)
                  {
                    memcpy(input0 + (u32)49U,
                      additional_input,
                      additional_input_len * sizeof additional_input[0U]);
                  }
                  input0[48U] = (u8)0U;
                  EverCrypt_HMAC_compute_sha2_384(k_, k1, (u32)48U, input0, input_len);
                  EverCrypt_HMAC_compute_sha2_384(v1, k_, (u32)48U, v1, (u32)48U);
                  memcpy(k1, k_, (u32)48U * sizeof k_[0U]);
                  if (additional_input_len != (u32)0U)
                  {
                    u32 input_len0 = (u32)49U + additional_input_len;
                    KRML_CHECK_SIZE(sizeof (u8), input_len0);
                    {
                      u8 input[input_len0];
                      memset(input, 0U, input_len0 * sizeof input[0U]);
                      {
                        u8 *k_0 = input;
                        memcpy(k_0, v1, (u32)48U * sizeof v1[0U]);
                        if (additional_input_len != (u32)0U)
                        {
                          memcpy(input + (u32)49U,
                            additional_input,
                            additional_input_len * sizeof additional_input[0U]);
                        }
                        input[48U] = (u8)1U;
                        EverCrypt_HMAC_compute_sha2_384(k_0, k1, (u32)48U, input, input_len0);
                        EverCrypt_HMAC_compute_sha2_384(v1, k_0, (u32)48U, v1, (u32)48U);
                        memcpy(k1, k_0, (u32)48U * sizeof k_0[0U]);
                      }
                    }
                  }
                }
              }
            }
            {
              u8 *output1 = output;
              u32 max1 = n1 / (u32)48U;
              u8 *out = output1;
              {
                u32 i;
                for (i = (u32)0U; i < max1; i = i + (u32)1U)
                {
                  EverCrypt_HMAC_compute_sha2_384(v1, k1, (u32)48U, v1, (u32)48U);
                  memcpy(out + i * (u32)48U, v1, (u32)48U * sizeof v1[0U]);
                }
              }
              if (max1 * (u32)48U < n1)
              {
                u8 *block = output1 + max1 * (u32)48U;
                EverCrypt_HMAC_compute_sha2_384(v1, k1, (u32)48U, v1, (u32)48U);
                memcpy(block, v1, (n1 - max1 * (u32)48U) * sizeof v1[0U]);
              }
              {
                u32 input_len = (u32)49U + additional_input_len;
                KRML_CHECK_SIZE(sizeof (u8), input_len);
                {
                  u8 input0[input_len];
                  memset(input0, 0U, input_len * sizeof input0[0U]);
                  {
                    u8 *k_ = input0;
                    memcpy(k_, v1, (u32)48U * sizeof v1[0U]);
                    if (additional_input_len != (u32)0U)
                    {
                      memcpy(input0 + (u32)49U,
                        additional_input,
                        additional_input_len * sizeof additional_input[0U]);
                    }
                    input0[48U] = (u8)0U;
                    EverCrypt_HMAC_compute_sha2_384(k_, k1, (u32)48U, input0, input_len);
                    EverCrypt_HMAC_compute_sha2_384(v1, k_, (u32)48U, v1, (u32)48U);
                    memcpy(k1, k_, (u32)48U * sizeof k_[0U]);
                    if (additional_input_len != (u32)0U)
                    {
                      u32 input_len0 = (u32)49U + additional_input_len;
                      KRML_CHECK_SIZE(sizeof (u8), input_len0);
                      {
                        u8 input[input_len0];
                        memset(input, 0U, input_len0 * sizeof input[0U]);
                        {
                          u8 *k_0 = input;
                          memcpy(k_0, v1, (u32)48U * sizeof v1[0U]);
                          if (additional_input_len != (u32)0U)
                          {
                            memcpy(input + (u32)49U,
                              additional_input,
                              additional_input_len * sizeof additional_input[0U]);
                          }
                          input[48U] = (u8)1U;
                          EverCrypt_HMAC_compute_sha2_384(k_0, k1, (u32)48U, input, input_len0);
                          EverCrypt_HMAC_compute_sha2_384(v1, k_0, (u32)48U, v1, (u32)48U);
                          memcpy(k1, k_0, (u32)48U * sizeof k_0[0U]);
                        }
                      }
                    }
                    {
                      u32 old_ctr = ctr[0U];
                      ctr[0U] = old_ctr + (u32)1U;
                      b = true;
                    }
                  }
                }
              }
            }
          }
        }
        return true;
      }
    }
  }
}

bool
EverCrypt_DRBG_generate_sha2_512(
  u8 *output,
  EverCrypt_DRBG_state_s *st,
  u32 n1,
  u8 *additional_input,
  u32 additional_input_len
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
  else
  {
    u32 entropy_input_len = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_512);
    bool ok0;
    if (additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length)
    {
      ok0 = false;
    }
    else
    {
      u32 entropy_input_len1 = Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_SHA2_512);
      KRML_CHECK_SIZE(sizeof (u8), entropy_input_len1);
      {
        u8 entropy_input[entropy_input_len1];
        memset(entropy_input, 0U, entropy_input_len1 * sizeof entropy_input[0U]);
        {
          bool ok = Lib_RandomBuffer_System_randombytes(entropy_input, entropy_input_len1);
          bool result;
          if (!ok)
          {
            result = false;
          }
          else
          {
            EverCrypt_DRBG_state_s st_s = *st;
            KRML_CHECK_SIZE(sizeof (u8), entropy_input_len1 + additional_input_len);
            {
              u8 seed_material[entropy_input_len1 + additional_input_len];
              memset(seed_material,
                0U,
                (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
              memcpy(seed_material, entropy_input, entropy_input_len1 * sizeof entropy_input[0U]);
              memcpy(seed_material + entropy_input_len1,
                additional_input,
                additional_input_len * sizeof additional_input[0U]);
              {
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
                {
                  u8 *k1 = uu____0.k;
                  u8 *v1 = uu____0.v;
                  u32 *ctr = uu____0.reseed_counter;
                  u32 input_len = (u32)65U + entropy_input_len1 + additional_input_len;
                  KRML_CHECK_SIZE(sizeof (u8), input_len);
                  {
                    u8 input0[input_len];
                    memset(input0, 0U, input_len * sizeof input0[0U]);
                    {
                      u8 *k_ = input0;
                      memcpy(k_, v1, (u32)64U * sizeof v1[0U]);
                      if (entropy_input_len1 + additional_input_len != (u32)0U)
                      {
                        memcpy(input0 + (u32)65U,
                          seed_material,
                          (entropy_input_len1 + additional_input_len) * sizeof seed_material[0U]);
                      }
                      input0[64U] = (u8)0U;
                      EverCrypt_HMAC_compute_sha2_512(k_, k1, (u32)64U, input0, input_len);
                      EverCrypt_HMAC_compute_sha2_512(v1, k_, (u32)64U, v1, (u32)64U);
                      memcpy(k1, k_, (u32)64U * sizeof k_[0U]);
                      if (entropy_input_len1 + additional_input_len != (u32)0U)
                      {
                        u32 input_len0 = (u32)65U + entropy_input_len1 + additional_input_len;
                        KRML_CHECK_SIZE(sizeof (u8), input_len0);
                        {
                          u8 input[input_len0];
                          memset(input, 0U, input_len0 * sizeof input[0U]);
                          {
                            u8 *k_0 = input;
                            memcpy(k_0, v1, (u32)64U * sizeof v1[0U]);
                            if (entropy_input_len1 + additional_input_len != (u32)0U)
                            {
                              memcpy(input + (u32)65U,
                                seed_material,
                                (entropy_input_len1 + additional_input_len)
                                * sizeof seed_material[0U]);
                            }
                            input[64U] = (u8)1U;
                            EverCrypt_HMAC_compute_sha2_512(k_0, k1, (u32)64U, input, input_len0);
                            EverCrypt_HMAC_compute_sha2_512(v1, k_0, (u32)64U, v1, (u32)64U);
                            memcpy(k1, k_0, (u32)64U * sizeof k_0[0U]);
                          }
                        }
                      }
                      ctr[0U] = (u32)1U;
                      result = true;
                    }
                  }
                }
              }
            }
          }
          ok0 = result;
        }
      }
    }
    if (!ok0)
    {
      return false;
    }
    else
    {
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
      {
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
          {
            u8 *k1 = scrut.k;
            u8 *v1 = scrut.v;
            u32 *ctr = scrut.reseed_counter;
            if (additional_input_len > (u32)0U)
            {
              u32 input_len = (u32)65U + additional_input_len;
              KRML_CHECK_SIZE(sizeof (u8), input_len);
              {
                u8 input0[input_len];
                memset(input0, 0U, input_len * sizeof input0[0U]);
                {
                  u8 *k_ = input0;
                  memcpy(k_, v1, (u32)64U * sizeof v1[0U]);
                  if (additional_input_len != (u32)0U)
                  {
                    memcpy(input0 + (u32)65U,
                      additional_input,
                      additional_input_len * sizeof additional_input[0U]);
                  }
                  input0[64U] = (u8)0U;
                  EverCrypt_HMAC_compute_sha2_512(k_, k1, (u32)64U, input0, input_len);
                  EverCrypt_HMAC_compute_sha2_512(v1, k_, (u32)64U, v1, (u32)64U);
                  memcpy(k1, k_, (u32)64U * sizeof k_[0U]);
                  if (additional_input_len != (u32)0U)
                  {
                    u32 input_len0 = (u32)65U + additional_input_len;
                    KRML_CHECK_SIZE(sizeof (u8), input_len0);
                    {
                      u8 input[input_len0];
                      memset(input, 0U, input_len0 * sizeof input[0U]);
                      {
                        u8 *k_0 = input;
                        memcpy(k_0, v1, (u32)64U * sizeof v1[0U]);
                        if (additional_input_len != (u32)0U)
                        {
                          memcpy(input + (u32)65U,
                            additional_input,
                            additional_input_len * sizeof additional_input[0U]);
                        }
                        input[64U] = (u8)1U;
                        EverCrypt_HMAC_compute_sha2_512(k_0, k1, (u32)64U, input, input_len0);
                        EverCrypt_HMAC_compute_sha2_512(v1, k_0, (u32)64U, v1, (u32)64U);
                        memcpy(k1, k_0, (u32)64U * sizeof k_0[0U]);
                      }
                    }
                  }
                }
              }
            }
            {
              u8 *output1 = output;
              u32 max1 = n1 / (u32)64U;
              u8 *out = output1;
              {
                u32 i;
                for (i = (u32)0U; i < max1; i = i + (u32)1U)
                {
                  EverCrypt_HMAC_compute_sha2_512(v1, k1, (u32)64U, v1, (u32)64U);
                  memcpy(out + i * (u32)64U, v1, (u32)64U * sizeof v1[0U]);
                }
              }
              if (max1 * (u32)64U < n1)
              {
                u8 *block = output1 + max1 * (u32)64U;
                EverCrypt_HMAC_compute_sha2_512(v1, k1, (u32)64U, v1, (u32)64U);
                memcpy(block, v1, (n1 - max1 * (u32)64U) * sizeof v1[0U]);
              }
              {
                u32 input_len = (u32)65U + additional_input_len;
                KRML_CHECK_SIZE(sizeof (u8), input_len);
                {
                  u8 input0[input_len];
                  memset(input0, 0U, input_len * sizeof input0[0U]);
                  {
                    u8 *k_ = input0;
                    memcpy(k_, v1, (u32)64U * sizeof v1[0U]);
                    if (additional_input_len != (u32)0U)
                    {
                      memcpy(input0 + (u32)65U,
                        additional_input,
                        additional_input_len * sizeof additional_input[0U]);
                    }
                    input0[64U] = (u8)0U;
                    EverCrypt_HMAC_compute_sha2_512(k_, k1, (u32)64U, input0, input_len);
                    EverCrypt_HMAC_compute_sha2_512(v1, k_, (u32)64U, v1, (u32)64U);
                    memcpy(k1, k_, (u32)64U * sizeof k_[0U]);
                    if (additional_input_len != (u32)0U)
                    {
                      u32 input_len0 = (u32)65U + additional_input_len;
                      KRML_CHECK_SIZE(sizeof (u8), input_len0);
                      {
                        u8 input[input_len0];
                        memset(input, 0U, input_len0 * sizeof input[0U]);
                        {
                          u8 *k_0 = input;
                          memcpy(k_0, v1, (u32)64U * sizeof v1[0U]);
                          if (additional_input_len != (u32)0U)
                          {
                            memcpy(input + (u32)65U,
                              additional_input,
                              additional_input_len * sizeof additional_input[0U]);
                          }
                          input[64U] = (u8)1U;
                          EverCrypt_HMAC_compute_sha2_512(k_0, k1, (u32)64U, input, input_len0);
                          EverCrypt_HMAC_compute_sha2_512(v1, k_0, (u32)64U, v1, (u32)64U);
                          memcpy(k1, k_0, (u32)64U * sizeof k_0[0U]);
                        }
                      }
                    }
                    {
                      u32 old_ctr = ctr[0U];
                      ctr[0U] = old_ctr + (u32)1U;
                      b = true;
                    }
                  }
                }
              }
            }
          }
        }
        return true;
      }
    }
  }
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
  {
    u8 *k1 = s.k;
    u8 *v1 = s.v;
    u32 *ctr = s.reseed_counter;
    Lib_Memzero_clear_words_u8((u32)20U, k1);
    Lib_Memzero_clear_words_u8((u32)20U, v1);
    ctr[0U] = (u32)0U;
    KRML_HOST_FREE(k1);
    KRML_HOST_FREE(v1);
    KRML_HOST_FREE(ctr);
    KRML_HOST_FREE(st);
  }
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
  {
    u8 *k1 = s.k;
    u8 *v1 = s.v;
    u32 *ctr = s.reseed_counter;
    Lib_Memzero_clear_words_u8((u32)32U, k1);
    Lib_Memzero_clear_words_u8((u32)32U, v1);
    ctr[0U] = (u32)0U;
    KRML_HOST_FREE(k1);
    KRML_HOST_FREE(v1);
    KRML_HOST_FREE(ctr);
    KRML_HOST_FREE(st);
  }
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
  {
    u8 *k1 = s.k;
    u8 *v1 = s.v;
    u32 *ctr = s.reseed_counter;
    Lib_Memzero_clear_words_u8((u32)48U, k1);
    Lib_Memzero_clear_words_u8((u32)48U, v1);
    ctr[0U] = (u32)0U;
    KRML_HOST_FREE(k1);
    KRML_HOST_FREE(v1);
    KRML_HOST_FREE(ctr);
    KRML_HOST_FREE(st);
  }
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
  {
    u8 *k1 = s.k;
    u8 *v1 = s.v;
    u32 *ctr = s.reseed_counter;
    Lib_Memzero_clear_words_u8((u32)64U, k1);
    Lib_Memzero_clear_words_u8((u32)64U, v1);
    ctr[0U] = (u32)0U;
    KRML_HOST_FREE(k1);
    KRML_HOST_FREE(v1);
    KRML_HOST_FREE(ctr);
    KRML_HOST_FREE(st);
  }
}

bool
EverCrypt_DRBG_instantiate(
  EverCrypt_DRBG_state_s *st,
  u8 *personalization_string,
  u32 personalization_string_len
)
{
  EverCrypt_DRBG_state_s scrut = *st;
  if (scrut.tag == EverCrypt_DRBG_SHA1_s)
  {
    return EverCrypt_DRBG_instantiate_sha1(st, personalization_string, personalization_string_len);
  }
  else if (scrut.tag == EverCrypt_DRBG_SHA2_256_s)
  {
    return
      EverCrypt_DRBG_instantiate_sha2_256(st,
        personalization_string,
        personalization_string_len);
  }
  else if (scrut.tag == EverCrypt_DRBG_SHA2_384_s)
  {
    return
      EverCrypt_DRBG_instantiate_sha2_384(st,
        personalization_string,
        personalization_string_len);
  }
  else if (scrut.tag == EverCrypt_DRBG_SHA2_512_s)
  {
    return
      EverCrypt_DRBG_instantiate_sha2_512(st,
        personalization_string,
        personalization_string_len);
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
EverCrypt_DRBG_reseed(
  EverCrypt_DRBG_state_s *st,
  u8 *additional_input,
  u32 additional_input_len
)
{
  EverCrypt_DRBG_state_s scrut = *st;
  if (scrut.tag == EverCrypt_DRBG_SHA1_s)
  {
    return EverCrypt_DRBG_reseed_sha1(st, additional_input, additional_input_len);
  }
  else if (scrut.tag == EverCrypt_DRBG_SHA2_256_s)
  {
    return EverCrypt_DRBG_reseed_sha2_256(st, additional_input, additional_input_len);
  }
  else if (scrut.tag == EverCrypt_DRBG_SHA2_384_s)
  {
    return EverCrypt_DRBG_reseed_sha2_384(st, additional_input, additional_input_len);
  }
  else if (scrut.tag == EverCrypt_DRBG_SHA2_512_s)
  {
    return EverCrypt_DRBG_reseed_sha2_512(st, additional_input, additional_input_len);
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
EverCrypt_DRBG_generate(
  u8 *output,
  EverCrypt_DRBG_state_s *st,
  u32 n1,
  u8 *additional_input,
  u32 additional_input_len
)
{
  EverCrypt_DRBG_state_s scrut = *st;
  if (scrut.tag == EverCrypt_DRBG_SHA1_s)
  {
    return EverCrypt_DRBG_generate_sha1(output, st, n1, additional_input, additional_input_len);
  }
  else if (scrut.tag == EverCrypt_DRBG_SHA2_256_s)
  {
    return
      EverCrypt_DRBG_generate_sha2_256(output,
        st,
        n1,
        additional_input,
        additional_input_len);
  }
  else if (scrut.tag == EverCrypt_DRBG_SHA2_384_s)
  {
    return
      EverCrypt_DRBG_generate_sha2_384(output,
        st,
        n1,
        additional_input,
        additional_input_len);
  }
  else if (scrut.tag == EverCrypt_DRBG_SHA2_512_s)
  {
    return
      EverCrypt_DRBG_generate_sha2_512(output,
        st,
        n1,
        additional_input,
        additional_input_len);
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

void EverCrypt_DRBG_uninstantiate(EverCrypt_DRBG_state_s *st)
{
  EverCrypt_DRBG_state_s scrut = *st;
  if (scrut.tag == EverCrypt_DRBG_SHA1_s)
  {
    EverCrypt_DRBG_uninstantiate_sha1(st);
  }
  else if (scrut.tag == EverCrypt_DRBG_SHA2_256_s)
  {
    EverCrypt_DRBG_uninstantiate_sha2_256(st);
  }
  else if (scrut.tag == EverCrypt_DRBG_SHA2_384_s)
  {
    EverCrypt_DRBG_uninstantiate_sha2_384(st);
  }
  else if (scrut.tag == EverCrypt_DRBG_SHA2_512_s)
  {
    EverCrypt_DRBG_uninstantiate_sha2_512(st);
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

