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


#include "Hacl_HPKE_Curve51_CP128_SHA512.h"

#include "internal/Hacl_Spec.h"

u32
Hacl_HPKE_Curve51_CP128_SHA512_setupBaseS(
  u8 *o_pkE,
  Hacl_Impl_HPKE_context_s o_ctx,
  u8 *skE,
  u8 *pkR,
  u32 infolen,
  u8 *info
)
{
  u8 o_shared[32U] = { 0U };
  u8 *o_pkE1 = o_pkE;
  u32 res1;
  u32 res0;
  u32 ite0;
  Hacl_Curve25519_51_secret_to_public(o_pkE1, skE);
  res1 = (u32)0U;
  if (res1 == (u32)0U)
  {
    u8 o_dh[32U] = { 0U };
    u8 zeros[32U] = { 0U };
    Hacl_Curve25519_51_scalarmult(o_dh, skE, pkR);
    {
      u8 res2 = (u8)255U;
      {
        u32 i;
        for (i = (u32)0U; i < (u32)32U; i++)
        {
          u8 uu____0 = FStar_UInt8_eq_mask(o_dh[i], zeros[i]);
          res2 = uu____0 & res2;
        }
      }
      {
        u8 z = res2;
        u32 res;
        if (z == (u8)255U)
          res = (u32)1U;
        else
          res = (u32)0U;
        {
          u32 res20 = res;
          if (res20 == (u32)0U)
          {
            u8 o_kemcontext[64U] = { 0U };
            u8 *uu____1 = o_kemcontext;
            u32 sw0;
            switch
            (
              Spec_Agile_HPKE_kem_dh_of_cs((
                  (Spec_Agile_HPKE_ciphersuite){
                    .fst = Spec_Agile_DH_DH_Curve25519,
                    .snd = Spec_Hash_Definitions_SHA2_256,
                    .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
                    .f3 = Spec_Hash_Definitions_SHA2_512
                  }
                ))
            )
            {
              case Spec_Agile_DH_DH_Curve25519:
                {
                  sw0 = (u32)32U;
                  break;
                }
              case Spec_Agile_DH_DH_P256:
                {
                  sw0 = (u32)65U;
                  break;
                }
              default:
                {
                  KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                  KRML_HOST_EXIT(253U);
                }
            }
            memcpy(uu____1, o_pkE, sw0 * sizeof (u8));
            {
              u32 sw1;
              switch
              (
                Spec_Agile_HPKE_kem_dh_of_cs((
                    (Spec_Agile_HPKE_ciphersuite){
                      .fst = Spec_Agile_DH_DH_Curve25519,
                      .snd = Spec_Hash_Definitions_SHA2_256,
                      .thd = {
                        .tag = Spec_Agile_HPKE_Seal,
                        .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                      },
                      .f3 = Spec_Hash_Definitions_SHA2_512
                    }
                  ))
              )
              {
                case Spec_Agile_DH_DH_Curve25519:
                  {
                    sw1 = (u32)32U;
                    break;
                  }
                case Spec_Agile_DH_DH_P256:
                  {
                    sw1 = (u32)65U;
                    break;
                  }
                default:
                  {
                    KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                    KRML_HOST_EXIT(253U);
                  }
              }
              {
                u8 *o_pkRm = o_kemcontext + sw1;
                u8 *o_pkR = o_pkRm;
                u32 sw2;
                switch
                (
                  Spec_Agile_HPKE_kem_dh_of_cs((
                      (Spec_Agile_HPKE_ciphersuite){
                        .fst = Spec_Agile_DH_DH_Curve25519,
                        .snd = Spec_Hash_Definitions_SHA2_256,
                        .thd = {
                          .tag = Spec_Agile_HPKE_Seal,
                          .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                        },
                        .f3 = Spec_Hash_Definitions_SHA2_512
                      }
                    ))
                )
                {
                  case Spec_Agile_DH_DH_Curve25519:
                    {
                      sw2 = (u32)32U;
                      break;
                    }
                  case Spec_Agile_DH_DH_P256:
                    {
                      sw2 = (u32)64U;
                      break;
                    }
                  default:
                    {
                      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                      KRML_HOST_EXIT(253U);
                    }
                }
                memcpy(o_pkR, pkR, sw2 * sizeof (u8));
                {
                  u8 *o_dhm = o_dh;
                  u8 o_eae_prk[32U] = { 0U };
                  u8 suite_id_kem[5U] = { 0U };
                  u8 *uu____2 = suite_id_kem;
                  uu____2[0U] = (u8)0x4bU;
                  uu____2[1U] = (u8)0x45U;
                  uu____2[2U] = (u8)0x4dU;
                  {
                    u8 *uu____3 = suite_id_kem + (u32)3U;
                    uu____3[0U] = (u8)0U;
                    uu____3[1U] = (u8)32U;
                    {
                      u8 *empty = suite_id_kem;
                      u8
                      label_eae_prk[7U] =
                        {
                          (u8)0x65U, (u8)0x61U, (u8)0x65U, (u8)0x5fU, (u8)0x70U, (u8)0x72U,
                          (u8)0x6bU
                        };
                      u32 len = (u32)7U + (u32)5U + (u32)7U + (u32)32U;
                      KRML_CHECK_SIZE(sizeof (u8), len);
                      {
                        u8 tmp0[len];
                        memset(tmp0, 0U, len * sizeof (u8));
                        {
                          u8 *uu____4 = tmp0;
                          uu____4[0U] = (u8)0x48U;
                          uu____4[1U] = (u8)0x50U;
                          uu____4[2U] = (u8)0x4bU;
                          uu____4[3U] = (u8)0x45U;
                          uu____4[4U] = (u8)0x2dU;
                          uu____4[5U] = (u8)0x76U;
                          uu____4[6U] = (u8)0x31U;
                          memcpy(tmp0 + (u32)7U, suite_id_kem, (u32)5U * sizeof (u8));
                          memcpy(tmp0 + (u32)7U + (u32)5U, label_eae_prk, (u32)7U * sizeof (u8));
                          memcpy(tmp0 + (u32)7U + (u32)5U + (u32)7U, o_dhm, (u32)32U * sizeof (u8));
                          Hacl_HKDF_extract_sha2_256(o_eae_prk, empty, (u32)0U, tmp0, len);
                          {
                            u8
                            label_shared_secret[13U] =
                              {
                                (u8)0x73U, (u8)0x68U, (u8)0x61U, (u8)0x72U, (u8)0x65U, (u8)0x64U,
                                (u8)0x5fU, (u8)0x73U, (u8)0x65U, (u8)0x63U, (u8)0x72U, (u8)0x65U,
                                (u8)0x74U
                              };
                            u32 sw3;
                            switch
                            (
                              Spec_Agile_HPKE_kem_dh_of_cs((
                                  (Spec_Agile_HPKE_ciphersuite){
                                    .fst = Spec_Agile_DH_DH_Curve25519,
                                    .snd = Spec_Hash_Definitions_SHA2_256,
                                    .thd = {
                                      .tag = Spec_Agile_HPKE_Seal,
                                      .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                    },
                                    .f3 = Spec_Hash_Definitions_SHA2_512
                                  }
                                ))
                            )
                            {
                              case Spec_Agile_DH_DH_Curve25519:
                                {
                                  sw3 = (u32)64U;
                                  break;
                                }
                              case Spec_Agile_DH_DH_P256:
                                {
                                  sw3 = (u32)130U;
                                  break;
                                }
                              default:
                                {
                                  KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                    __FILE__,
                                    __LINE__);
                                  KRML_HOST_EXIT(253U);
                                }
                            }
                            {
                              u32 len0 = (u32)9U + (u32)5U + (u32)13U + sw3;
                              KRML_CHECK_SIZE(sizeof (u8), len0);
                              {
                                u8 tmp[len0];
                                memset(tmp, 0U, len0 * sizeof (u8));
                                {
                                  u8 *uu____5 = tmp;
                                  u8 *uu____6 = uu____5;
                                  u32 sw4;
                                  switch
                                  (
                                    Spec_Agile_HPKE_kem_hash_of_cs((
                                        (Spec_Agile_HPKE_ciphersuite){
                                          .fst = Spec_Agile_DH_DH_Curve25519,
                                          .snd = Spec_Hash_Definitions_SHA2_256,
                                          .thd = {
                                            .tag = Spec_Agile_HPKE_Seal,
                                            .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                          },
                                          .f3 = Spec_Hash_Definitions_SHA2_512
                                        }
                                      ))
                                  )
                                  {
                                    case Spec_Hash_Definitions_SHA2_256:
                                      {
                                        sw4 = (u32)32U;
                                        break;
                                      }
                                    default:
                                      {
                                        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                          __FILE__,
                                          __LINE__);
                                        KRML_HOST_EXIT(253U);
                                      }
                                  }
                                  store32_be(uu____6, sw4);
                                  memcpy(uu____5, uu____5 + (u32)2U, (u32)2U * sizeof (u8));
                                  {
                                    u8 *uu____7 = tmp + (u32)2U;
                                    uu____7[0U] = (u8)0x48U;
                                    uu____7[1U] = (u8)0x50U;
                                    uu____7[2U] = (u8)0x4bU;
                                    uu____7[3U] = (u8)0x45U;
                                    uu____7[4U] = (u8)0x2dU;
                                    uu____7[5U] = (u8)0x76U;
                                    uu____7[6U] = (u8)0x31U;
                                    memcpy(tmp + (u32)9U, suite_id_kem, (u32)5U * sizeof (u8));
                                    memcpy(tmp + (u32)9U + (u32)5U,
                                      label_shared_secret,
                                      (u32)13U * sizeof (u8));
                                    {
                                      u8 *uu____8 = tmp + (u32)9U + (u32)5U + (u32)13U;
                                      u32 sw5;
                                      switch
                                      (
                                        Spec_Agile_HPKE_kem_dh_of_cs((
                                            (Spec_Agile_HPKE_ciphersuite){
                                              .fst = Spec_Agile_DH_DH_Curve25519,
                                              .snd = Spec_Hash_Definitions_SHA2_256,
                                              .thd = {
                                                .tag = Spec_Agile_HPKE_Seal,
                                                .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                              },
                                              .f3 = Spec_Hash_Definitions_SHA2_512
                                            }
                                          ))
                                      )
                                      {
                                        case Spec_Agile_DH_DH_Curve25519:
                                          {
                                            sw5 = (u32)64U;
                                            break;
                                          }
                                        case Spec_Agile_DH_DH_P256:
                                          {
                                            sw5 = (u32)130U;
                                            break;
                                          }
                                        default:
                                          {
                                            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                              __FILE__,
                                              __LINE__);
                                            KRML_HOST_EXIT(253U);
                                          }
                                      }
                                      memcpy(uu____8, o_kemcontext, sw5 * sizeof (u8));
                                      {
                                        u32 sw6;
                                        switch
                                        (
                                          Spec_Agile_HPKE_kem_hash_of_cs((
                                              (Spec_Agile_HPKE_ciphersuite){
                                                .fst = Spec_Agile_DH_DH_Curve25519,
                                                .snd = Spec_Hash_Definitions_SHA2_256,
                                                .thd = {
                                                  .tag = Spec_Agile_HPKE_Seal,
                                                  .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                },
                                                .f3 = Spec_Hash_Definitions_SHA2_512
                                              }
                                            ))
                                        )
                                        {
                                          case Spec_Hash_Definitions_SHA2_256:
                                            {
                                              sw6 = (u32)32U;
                                              break;
                                            }
                                          default:
                                            {
                                              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                __FILE__,
                                                __LINE__);
                                              KRML_HOST_EXIT(253U);
                                            }
                                        }
                                        {
                                          u32 sw;
                                          switch
                                          (
                                            Spec_Agile_HPKE_kem_hash_of_cs((
                                                (Spec_Agile_HPKE_ciphersuite){
                                                  .fst = Spec_Agile_DH_DH_Curve25519,
                                                  .snd = Spec_Hash_Definitions_SHA2_256,
                                                  .thd = {
                                                    .tag = Spec_Agile_HPKE_Seal,
                                                    .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                  },
                                                  .f3 = Spec_Hash_Definitions_SHA2_512
                                                }
                                              ))
                                          )
                                          {
                                            case Spec_Hash_Definitions_SHA2_256:
                                              {
                                                sw = (u32)32U;
                                                break;
                                              }
                                            default:
                                              {
                                                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                  __FILE__,
                                                  __LINE__);
                                                KRML_HOST_EXIT(253U);
                                              }
                                          }
                                          Hacl_HKDF_expand_sha2_256(o_shared,
                                            o_eae_prk,
                                            sw6,
                                            tmp,
                                            len0,
                                            sw);
                                          res0 = (u32)0U;
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
                  }
                }
              }
            }
          }
          else
            res0 = (u32)1U;
        }
      }
    }
  }
  else
    res0 = (u32)1U;
  if (res0 == (u32)0U)
  {
    u8 o_context[129U] = { 0U };
    u8 o_secret[64U] = { 0U };
    u8 suite_id[10U] = { 0U };
    u8 *uu____9 = suite_id;
    uu____9[0U] = (u8)0x48U;
    uu____9[1U] = (u8)0x50U;
    uu____9[2U] = (u8)0x4bU;
    uu____9[3U] = (u8)0x45U;
    {
      u8 *uu____10 = suite_id + (u32)4U;
      uu____10[0U] = (u8)0U;
      uu____10[1U] = (u8)32U;
      {
        u8 *uu____11 = suite_id + (u32)6U;
        uu____11[0U] = (u8)0U;
        uu____11[1U] = (u8)3U;
        {
          u8 *uu____12 = suite_id + (u32)8U;
          uu____12[0U] = (u8)0U;
          uu____12[1U] = (u8)3U;
          {
            u8
            label_psk_id_hash[11U] =
              {
                (u8)0x70U, (u8)0x73U, (u8)0x6bU, (u8)0x5fU, (u8)0x69U, (u8)0x64U, (u8)0x5fU,
                (u8)0x68U, (u8)0x61U, (u8)0x73U, (u8)0x68U
              };
            u8 o_psk_id_hash[64U] = { 0U };
            u8 *empty = suite_id;
            u32 len0 = (u32)7U + (u32)10U + (u32)11U + (u32)0U;
            KRML_CHECK_SIZE(sizeof (u8), len0);
            {
              u8 tmp0[len0];
              memset(tmp0, 0U, len0 * sizeof (u8));
              {
                u8 *uu____13 = tmp0;
                uu____13[0U] = (u8)0x48U;
                uu____13[1U] = (u8)0x50U;
                uu____13[2U] = (u8)0x4bU;
                uu____13[3U] = (u8)0x45U;
                uu____13[4U] = (u8)0x2dU;
                uu____13[5U] = (u8)0x76U;
                uu____13[6U] = (u8)0x31U;
                memcpy(tmp0 + (u32)7U, suite_id, (u32)10U * sizeof (u8));
                memcpy(tmp0 + (u32)7U + (u32)10U, label_psk_id_hash, (u32)11U * sizeof (u8));
                memcpy(tmp0 + (u32)7U + (u32)10U + (u32)11U, empty, (u32)0U * sizeof (u8));
                Hacl_HKDF_extract_sha2_512(o_psk_id_hash, empty, (u32)0U, tmp0, len0);
                {
                  u8
                  label_info_hash[9U] =
                    {
                      (u8)0x69U, (u8)0x6eU, (u8)0x66U, (u8)0x6fU, (u8)0x5fU, (u8)0x68U, (u8)0x61U,
                      (u8)0x73U, (u8)0x68U
                    };
                  u8 o_info_hash[64U] = { 0U };
                  u32 len1 = (u32)7U + (u32)10U + (u32)9U + infolen;
                  KRML_CHECK_SIZE(sizeof (u8), len1);
                  {
                    u8 tmp1[len1];
                    memset(tmp1, 0U, len1 * sizeof (u8));
                    {
                      u8 *uu____14 = tmp1;
                      uu____14[0U] = (u8)0x48U;
                      uu____14[1U] = (u8)0x50U;
                      uu____14[2U] = (u8)0x4bU;
                      uu____14[3U] = (u8)0x45U;
                      uu____14[4U] = (u8)0x2dU;
                      uu____14[5U] = (u8)0x76U;
                      uu____14[6U] = (u8)0x31U;
                      memcpy(tmp1 + (u32)7U, suite_id, (u32)10U * sizeof (u8));
                      memcpy(tmp1 + (u32)7U + (u32)10U, label_info_hash, (u32)9U * sizeof (u8));
                      memcpy(tmp1 + (u32)7U + (u32)10U + (u32)9U, info, infolen * sizeof (u8));
                      Hacl_HKDF_extract_sha2_512(o_info_hash, empty, (u32)0U, tmp1, len1);
                      o_context[0U] = (u8)0U;
                      {
                        u8 *uu____15 = o_context + (u32)1U;
                        u32 sw0;
                        switch
                        (
                          Spec_Agile_HPKE_hash_of_cs((
                              (Spec_Agile_HPKE_ciphersuite){
                                .fst = Spec_Agile_DH_DH_Curve25519,
                                .snd = Spec_Hash_Definitions_SHA2_256,
                                .thd = {
                                  .tag = Spec_Agile_HPKE_Seal,
                                  .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                },
                                .f3 = Spec_Hash_Definitions_SHA2_512
                              }
                            ))
                        )
                        {
                          case Spec_Hash_Definitions_SHA2_256:
                            {
                              sw0 = (u32)32U;
                              break;
                            }
                          case Spec_Hash_Definitions_SHA2_384:
                            {
                              sw0 = (u32)48U;
                              break;
                            }
                          case Spec_Hash_Definitions_SHA2_512:
                            {
                              sw0 = (u32)64U;
                              break;
                            }
                          default:
                            {
                              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                __FILE__,
                                __LINE__);
                              KRML_HOST_EXIT(253U);
                            }
                        }
                        memcpy(uu____15, o_psk_id_hash, sw0 * sizeof (u8));
                        {
                          u32 sw1;
                          switch
                          (
                            Spec_Agile_HPKE_hash_of_cs((
                                (Spec_Agile_HPKE_ciphersuite){
                                  .fst = Spec_Agile_DH_DH_Curve25519,
                                  .snd = Spec_Hash_Definitions_SHA2_256,
                                  .thd = {
                                    .tag = Spec_Agile_HPKE_Seal,
                                    .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                  },
                                  .f3 = Spec_Hash_Definitions_SHA2_512
                                }
                              ))
                          )
                          {
                            case Spec_Hash_Definitions_SHA2_256:
                              {
                                sw1 = (u32)33U;
                                break;
                              }
                            case Spec_Hash_Definitions_SHA2_384:
                              {
                                sw1 = (u32)49U;
                                break;
                              }
                            case Spec_Hash_Definitions_SHA2_512:
                              {
                                sw1 = (u32)65U;
                                break;
                              }
                            default:
                              {
                                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                  __FILE__,
                                  __LINE__);
                                KRML_HOST_EXIT(253U);
                              }
                          }
                          {
                            u8 *uu____16 = o_context + sw1;
                            u32 sw2;
                            switch
                            (
                              Spec_Agile_HPKE_hash_of_cs((
                                  (Spec_Agile_HPKE_ciphersuite){
                                    .fst = Spec_Agile_DH_DH_Curve25519,
                                    .snd = Spec_Hash_Definitions_SHA2_256,
                                    .thd = {
                                      .tag = Spec_Agile_HPKE_Seal,
                                      .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                    },
                                    .f3 = Spec_Hash_Definitions_SHA2_512
                                  }
                                ))
                            )
                            {
                              case Spec_Hash_Definitions_SHA2_256:
                                {
                                  sw2 = (u32)32U;
                                  break;
                                }
                              case Spec_Hash_Definitions_SHA2_384:
                                {
                                  sw2 = (u32)48U;
                                  break;
                                }
                              case Spec_Hash_Definitions_SHA2_512:
                                {
                                  sw2 = (u32)64U;
                                  break;
                                }
                              default:
                                {
                                  KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                    __FILE__,
                                    __LINE__);
                                  KRML_HOST_EXIT(253U);
                                }
                            }
                            memcpy(uu____16, o_info_hash, sw2 * sizeof (u8));
                            {
                              u8
                              label_secret[6U] =
                                { (u8)0x73U, (u8)0x65U, (u8)0x63U, (u8)0x72U, (u8)0x65U, (u8)0x74U };
                              u32 len = (u32)7U + (u32)10U + (u32)6U + (u32)0U;
                              KRML_CHECK_SIZE(sizeof (u8), len);
                              {
                                u8 tmp2[len];
                                memset(tmp2, 0U, len * sizeof (u8));
                                {
                                  u8 *uu____17 = tmp2;
                                  uu____17[0U] = (u8)0x48U;
                                  uu____17[1U] = (u8)0x50U;
                                  uu____17[2U] = (u8)0x4bU;
                                  uu____17[3U] = (u8)0x45U;
                                  uu____17[4U] = (u8)0x2dU;
                                  uu____17[5U] = (u8)0x76U;
                                  uu____17[6U] = (u8)0x31U;
                                  memcpy(tmp2 + (u32)7U, suite_id, (u32)10U * sizeof (u8));
                                  memcpy(tmp2 + (u32)7U + (u32)10U,
                                    label_secret,
                                    (u32)6U * sizeof (u8));
                                  memcpy(tmp2 + (u32)7U + (u32)10U + (u32)6U,
                                    empty,
                                    (u32)0U * sizeof (u8));
                                  {
                                    u32 sw3;
                                    switch
                                    (
                                      Spec_Agile_HPKE_kem_hash_of_cs((
                                          (Spec_Agile_HPKE_ciphersuite){
                                            .fst = Spec_Agile_DH_DH_Curve25519,
                                            .snd = Spec_Hash_Definitions_SHA2_256,
                                            .thd = {
                                              .tag = Spec_Agile_HPKE_Seal,
                                              .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                            },
                                            .f3 = Spec_Hash_Definitions_SHA2_512
                                          }
                                        ))
                                    )
                                    {
                                      case Spec_Hash_Definitions_SHA2_256:
                                        {
                                          sw3 = (u32)32U;
                                          break;
                                        }
                                      default:
                                        {
                                          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                            __FILE__,
                                            __LINE__);
                                          KRML_HOST_EXIT(253U);
                                        }
                                    }
                                    Hacl_HKDF_extract_sha2_512(o_secret, o_shared, sw3, tmp2, len);
                                    {
                                      u8 label_exp[3U] = { (u8)0x65U, (u8)0x78U, (u8)0x70U };
                                      u32 sw4;
                                      switch
                                      (
                                        Spec_Agile_HPKE_hash_of_cs((
                                            (Spec_Agile_HPKE_ciphersuite){
                                              .fst = Spec_Agile_DH_DH_Curve25519,
                                              .snd = Spec_Hash_Definitions_SHA2_256,
                                              .thd = {
                                                .tag = Spec_Agile_HPKE_Seal,
                                                .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                              },
                                              .f3 = Spec_Hash_Definitions_SHA2_512
                                            }
                                          ))
                                      )
                                      {
                                        case Spec_Hash_Definitions_SHA2_256:
                                          {
                                            sw4 = (u32)65U;
                                            break;
                                          }
                                        case Spec_Hash_Definitions_SHA2_384:
                                          {
                                            sw4 = (u32)97U;
                                            break;
                                          }
                                        case Spec_Hash_Definitions_SHA2_512:
                                          {
                                            sw4 = (u32)129U;
                                            break;
                                          }
                                        default:
                                          {
                                            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                              __FILE__,
                                              __LINE__);
                                            KRML_HOST_EXIT(253U);
                                          }
                                      }
                                      {
                                        u32 len2 = (u32)9U + (u32)10U + (u32)3U + sw4;
                                        KRML_CHECK_SIZE(sizeof (u8), len2);
                                        {
                                          u8 tmp3[len2];
                                          memset(tmp3, 0U, len2 * sizeof (u8));
                                          {
                                            u8 *uu____18 = tmp3;
                                            u8 *uu____19 = uu____18;
                                            u32 sw5;
                                            switch
                                            (
                                              Spec_Agile_HPKE_hash_of_cs((
                                                  (Spec_Agile_HPKE_ciphersuite){
                                                    .fst = Spec_Agile_DH_DH_Curve25519,
                                                    .snd = Spec_Hash_Definitions_SHA2_256,
                                                    .thd = {
                                                      .tag = Spec_Agile_HPKE_Seal,
                                                      .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                    },
                                                    .f3 = Spec_Hash_Definitions_SHA2_512
                                                  }
                                                ))
                                            )
                                            {
                                              case Spec_Hash_Definitions_SHA2_256:
                                                {
                                                  sw5 = (u32)32U;
                                                  break;
                                                }
                                              case Spec_Hash_Definitions_SHA2_384:
                                                {
                                                  sw5 = (u32)48U;
                                                  break;
                                                }
                                              case Spec_Hash_Definitions_SHA2_512:
                                                {
                                                  sw5 = (u32)64U;
                                                  break;
                                                }
                                              default:
                                                {
                                                  KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                    __FILE__,
                                                    __LINE__);
                                                  KRML_HOST_EXIT(253U);
                                                }
                                            }
                                            store32_be(uu____19, sw5);
                                            memcpy(uu____18,
                                              uu____18 + (u32)2U,
                                              (u32)2U * sizeof (u8));
                                            {
                                              u8 *uu____20 = tmp3 + (u32)2U;
                                              uu____20[0U] = (u8)0x48U;
                                              uu____20[1U] = (u8)0x50U;
                                              uu____20[2U] = (u8)0x4bU;
                                              uu____20[3U] = (u8)0x45U;
                                              uu____20[4U] = (u8)0x2dU;
                                              uu____20[5U] = (u8)0x76U;
                                              uu____20[6U] = (u8)0x31U;
                                              memcpy(tmp3 + (u32)9U,
                                                suite_id,
                                                (u32)10U * sizeof (u8));
                                              memcpy(tmp3 + (u32)9U + (u32)10U,
                                                label_exp,
                                                (u32)3U * sizeof (u8));
                                              {
                                                u8 *uu____21 = tmp3 + (u32)9U + (u32)10U + (u32)3U;
                                                u32 sw6;
                                                switch
                                                (
                                                  Spec_Agile_HPKE_hash_of_cs((
                                                      (Spec_Agile_HPKE_ciphersuite){
                                                        .fst = Spec_Agile_DH_DH_Curve25519,
                                                        .snd = Spec_Hash_Definitions_SHA2_256,
                                                        .thd = {
                                                          .tag = Spec_Agile_HPKE_Seal,
                                                          .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                        },
                                                        .f3 = Spec_Hash_Definitions_SHA2_512
                                                      }
                                                    ))
                                                )
                                                {
                                                  case Spec_Hash_Definitions_SHA2_256:
                                                    {
                                                      sw6 = (u32)65U;
                                                      break;
                                                    }
                                                  case Spec_Hash_Definitions_SHA2_384:
                                                    {
                                                      sw6 = (u32)97U;
                                                      break;
                                                    }
                                                  case Spec_Hash_Definitions_SHA2_512:
                                                    {
                                                      sw6 = (u32)129U;
                                                      break;
                                                    }
                                                  default:
                                                    {
                                                      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                        __FILE__,
                                                        __LINE__);
                                                      KRML_HOST_EXIT(253U);
                                                    }
                                                }
                                                memcpy(uu____21, o_context, sw6 * sizeof (u8));
                                                {
                                                  u32 sw7;
                                                  switch
                                                  (
                                                    Spec_Agile_HPKE_hash_of_cs((
                                                        (Spec_Agile_HPKE_ciphersuite){
                                                          .fst = Spec_Agile_DH_DH_Curve25519,
                                                          .snd = Spec_Hash_Definitions_SHA2_256,
                                                          .thd = {
                                                            .tag = Spec_Agile_HPKE_Seal,
                                                            .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                          },
                                                          .f3 = Spec_Hash_Definitions_SHA2_512
                                                        }
                                                      ))
                                                  )
                                                  {
                                                    case Spec_Hash_Definitions_SHA2_256:
                                                      {
                                                        sw7 = (u32)32U;
                                                        break;
                                                      }
                                                    case Spec_Hash_Definitions_SHA2_384:
                                                      {
                                                        sw7 = (u32)48U;
                                                        break;
                                                      }
                                                    case Spec_Hash_Definitions_SHA2_512:
                                                      {
                                                        sw7 = (u32)64U;
                                                        break;
                                                      }
                                                    default:
                                                      {
                                                        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                          __FILE__,
                                                          __LINE__);
                                                        KRML_HOST_EXIT(253U);
                                                      }
                                                  }
                                                  {
                                                    u32 sw8;
                                                    switch
                                                    (
                                                      Spec_Agile_HPKE_hash_of_cs((
                                                          (Spec_Agile_HPKE_ciphersuite){
                                                            .fst = Spec_Agile_DH_DH_Curve25519,
                                                            .snd = Spec_Hash_Definitions_SHA2_256,
                                                            .thd = {
                                                              .tag = Spec_Agile_HPKE_Seal,
                                                              .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                            },
                                                            .f3 = Spec_Hash_Definitions_SHA2_512
                                                          }
                                                        ))
                                                    )
                                                    {
                                                      case Spec_Hash_Definitions_SHA2_256:
                                                        {
                                                          sw8 = (u32)32U;
                                                          break;
                                                        }
                                                      case Spec_Hash_Definitions_SHA2_384:
                                                        {
                                                          sw8 = (u32)48U;
                                                          break;
                                                        }
                                                      case Spec_Hash_Definitions_SHA2_512:
                                                        {
                                                          sw8 = (u32)64U;
                                                          break;
                                                        }
                                                      default:
                                                        {
                                                          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                            __FILE__,
                                                            __LINE__);
                                                          KRML_HOST_EXIT(253U);
                                                        }
                                                    }
                                                    Hacl_HKDF_expand_sha2_512(o_ctx.ctx_exporter,
                                                      o_secret,
                                                      sw7,
                                                      tmp3,
                                                      len2,
                                                      sw8);
                                                    {
                                                      Spec_Agile_HPKE_aead
                                                      scrut0 =
                                                        Spec_Agile_HPKE_aead_of_cs((
                                                            (Spec_Agile_HPKE_ciphersuite){
                                                              .fst = Spec_Agile_DH_DH_Curve25519,
                                                              .snd = Spec_Hash_Definitions_SHA2_256,
                                                              .thd = {
                                                                .tag = Spec_Agile_HPKE_Seal,
                                                                .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                              },
                                                              .f3 = Spec_Hash_Definitions_SHA2_512
                                                            }
                                                          ));
                                                      if (scrut0.tag == Spec_Agile_HPKE_ExportOnly)
                                                        o_ctx.ctx_seq[0U] = (u64)0U;
                                                      else
                                                      {
                                                        u8
                                                        label_key[3U] =
                                                          { (u8)0x6bU, (u8)0x65U, (u8)0x79U };
                                                        u32 sw9;
                                                        switch
                                                        (
                                                          Spec_Agile_HPKE_hash_of_cs((
                                                              (Spec_Agile_HPKE_ciphersuite){
                                                                .fst = Spec_Agile_DH_DH_Curve25519,
                                                                .snd = Spec_Hash_Definitions_SHA2_256,
                                                                .thd = {
                                                                  .tag = Spec_Agile_HPKE_Seal,
                                                                  .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                },
                                                                .f3 = Spec_Hash_Definitions_SHA2_512
                                                              }
                                                            ))
                                                        )
                                                        {
                                                          case Spec_Hash_Definitions_SHA2_256:
                                                            {
                                                              sw9 = (u32)65U;
                                                              break;
                                                            }
                                                          case Spec_Hash_Definitions_SHA2_384:
                                                            {
                                                              sw9 = (u32)97U;
                                                              break;
                                                            }
                                                          case Spec_Hash_Definitions_SHA2_512:
                                                            {
                                                              sw9 = (u32)129U;
                                                              break;
                                                            }
                                                          default:
                                                            {
                                                              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                __FILE__,
                                                                __LINE__);
                                                              KRML_HOST_EXIT(253U);
                                                            }
                                                        }
                                                        {
                                                          u32
                                                          len3 = (u32)9U + (u32)10U + (u32)3U + sw9;
                                                          KRML_CHECK_SIZE(sizeof (u8), len3);
                                                          {
                                                            u8 tmp4[len3];
                                                            memset(tmp4, 0U, len3 * sizeof (u8));
                                                            {
                                                              u8 *uu____22 = tmp4;
                                                              u8 *uu____23 = uu____22;
                                                              Spec_Agile_HPKE_aead
                                                              scrut1 =
                                                                Spec_Agile_HPKE_aead_of_cs((
                                                                    (Spec_Agile_HPKE_ciphersuite){
                                                                      .fst = Spec_Agile_DH_DH_Curve25519,
                                                                      .snd = Spec_Hash_Definitions_SHA2_256,
                                                                      .thd = {
                                                                        .tag = Spec_Agile_HPKE_Seal,
                                                                        .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                      },
                                                                      .f3 = Spec_Hash_Definitions_SHA2_512
                                                                    }
                                                                  ));
                                                              u32 ite1;
                                                              if
                                                              (
                                                                scrut1.tag
                                                                == Spec_Agile_HPKE_ExportOnly
                                                              )
                                                                ite1 = (u32)0U;
                                                              else if
                                                              (
                                                                scrut1.tag
                                                                == Spec_Agile_HPKE_Seal
                                                                &&
                                                                  scrut1.alg
                                                                  == Spec_Agile_AEAD_AES128_GCM
                                                              )
                                                                ite1 = (u32)16U;
                                                              else if
                                                              (
                                                                scrut1.tag
                                                                == Spec_Agile_HPKE_Seal
                                                                &&
                                                                  scrut1.alg
                                                                  == Spec_Agile_AEAD_AES256_GCM
                                                              )
                                                                ite1 = (u32)32U;
                                                              else if
                                                              (
                                                                scrut1.tag
                                                                == Spec_Agile_HPKE_Seal
                                                                &&
                                                                  scrut1.alg
                                                                  ==
                                                                    Spec_Agile_AEAD_CHACHA20_POLY1305
                                                              )
                                                                ite1 = (u32)32U;
                                                              else
                                                                ite1 =
                                                                  KRML_EABORT(u32,
                                                                    "unreachable (pattern matches are exhaustive in F*)");
                                                              store32_be(uu____23, ite1);
                                                              memcpy(uu____22,
                                                                uu____22 + (u32)2U,
                                                                (u32)2U * sizeof (u8));
                                                              {
                                                                u8 *uu____24 = tmp4 + (u32)2U;
                                                                uu____24[0U] = (u8)0x48U;
                                                                uu____24[1U] = (u8)0x50U;
                                                                uu____24[2U] = (u8)0x4bU;
                                                                uu____24[3U] = (u8)0x45U;
                                                                uu____24[4U] = (u8)0x2dU;
                                                                uu____24[5U] = (u8)0x76U;
                                                                uu____24[6U] = (u8)0x31U;
                                                                memcpy(tmp4 + (u32)9U,
                                                                  suite_id,
                                                                  (u32)10U * sizeof (u8));
                                                                memcpy(tmp4 + (u32)9U + (u32)10U,
                                                                  label_key,
                                                                  (u32)3U * sizeof (u8));
                                                                {
                                                                  u8
                                                                  *uu____25 =
                                                                    tmp4
                                                                    + (u32)9U + (u32)10U + (u32)3U;
                                                                  u32 sw10;
                                                                  switch
                                                                  (
                                                                    Spec_Agile_HPKE_hash_of_cs((
                                                                        (Spec_Agile_HPKE_ciphersuite){
                                                                          .fst = Spec_Agile_DH_DH_Curve25519,
                                                                          .snd = Spec_Hash_Definitions_SHA2_256,
                                                                          .thd = {
                                                                            .tag = Spec_Agile_HPKE_Seal,
                                                                            .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                          },
                                                                          .f3 = Spec_Hash_Definitions_SHA2_512
                                                                        }
                                                                      ))
                                                                  )
                                                                  {
                                                                    case
                                                                    Spec_Hash_Definitions_SHA2_256:
                                                                      {
                                                                        sw10 = (u32)65U;
                                                                        break;
                                                                      }
                                                                    case
                                                                    Spec_Hash_Definitions_SHA2_384:
                                                                      {
                                                                        sw10 = (u32)97U;
                                                                        break;
                                                                      }
                                                                    case
                                                                    Spec_Hash_Definitions_SHA2_512:
                                                                      {
                                                                        sw10 = (u32)129U;
                                                                        break;
                                                                      }
                                                                    default:
                                                                      {
                                                                        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                          __FILE__,
                                                                          __LINE__);
                                                                        KRML_HOST_EXIT(253U);
                                                                      }
                                                                  }
                                                                  memcpy(uu____25,
                                                                    o_context,
                                                                    sw10 * sizeof (u8));
                                                                  {
                                                                    u32 sw11;
                                                                    switch
                                                                    (
                                                                      Spec_Agile_HPKE_hash_of_cs((
                                                                          (Spec_Agile_HPKE_ciphersuite){
                                                                            .fst = Spec_Agile_DH_DH_Curve25519,
                                                                            .snd = Spec_Hash_Definitions_SHA2_256,
                                                                            .thd = {
                                                                              .tag = Spec_Agile_HPKE_Seal,
                                                                              .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                            },
                                                                            .f3 = Spec_Hash_Definitions_SHA2_512
                                                                          }
                                                                        ))
                                                                    )
                                                                    {
                                                                      case
                                                                      Spec_Hash_Definitions_SHA2_256:
                                                                        {
                                                                          sw11 = (u32)32U;
                                                                          break;
                                                                        }
                                                                      case
                                                                      Spec_Hash_Definitions_SHA2_384:
                                                                        {
                                                                          sw11 = (u32)48U;
                                                                          break;
                                                                        }
                                                                      case
                                                                      Spec_Hash_Definitions_SHA2_512:
                                                                        {
                                                                          sw11 = (u32)64U;
                                                                          break;
                                                                        }
                                                                      default:
                                                                        {
                                                                          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                            __FILE__,
                                                                            __LINE__);
                                                                          KRML_HOST_EXIT(253U);
                                                                        }
                                                                    }
                                                                    {
                                                                      Spec_Agile_HPKE_aead
                                                                      scrut2 =
                                                                        Spec_Agile_HPKE_aead_of_cs((
                                                                            (Spec_Agile_HPKE_ciphersuite){
                                                                              .fst = Spec_Agile_DH_DH_Curve25519,
                                                                              .snd = Spec_Hash_Definitions_SHA2_256,
                                                                              .thd = {
                                                                                .tag = Spec_Agile_HPKE_Seal,
                                                                                .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                              },
                                                                              .f3 = Spec_Hash_Definitions_SHA2_512
                                                                            }
                                                                          ));
                                                                      u32 ite2;
                                                                      if
                                                                      (
                                                                        scrut2.tag
                                                                        ==
                                                                          Spec_Agile_HPKE_ExportOnly
                                                                      )
                                                                        ite2 = (u32)0U;
                                                                      else if
                                                                      (
                                                                        scrut2.tag
                                                                        == Spec_Agile_HPKE_Seal
                                                                        &&
                                                                          scrut2.alg
                                                                          ==
                                                                            Spec_Agile_AEAD_AES128_GCM
                                                                      )
                                                                        ite2 = (u32)16U;
                                                                      else if
                                                                      (
                                                                        scrut2.tag
                                                                        == Spec_Agile_HPKE_Seal
                                                                        &&
                                                                          scrut2.alg
                                                                          ==
                                                                            Spec_Agile_AEAD_AES256_GCM
                                                                      )
                                                                        ite2 = (u32)32U;
                                                                      else if
                                                                      (
                                                                        scrut2.tag
                                                                        == Spec_Agile_HPKE_Seal
                                                                        &&
                                                                          scrut2.alg
                                                                          ==
                                                                            Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                      )
                                                                        ite2 = (u32)32U;
                                                                      else
                                                                        ite2 =
                                                                          KRML_EABORT(u32,
                                                                            "unreachable (pattern matches are exhaustive in F*)");
                                                                      Hacl_HKDF_expand_sha2_512(o_ctx.ctx_key,
                                                                        o_secret,
                                                                        sw11,
                                                                        tmp4,
                                                                        len3,
                                                                        ite2);
                                                                      {
                                                                        u8
                                                                        label_base_nonce[10U] =
                                                                          {
                                                                            (u8)0x62U, (u8)0x61U,
                                                                            (u8)0x73U, (u8)0x65U,
                                                                            (u8)0x5fU, (u8)0x6eU,
                                                                            (u8)0x6fU, (u8)0x6eU,
                                                                            (u8)0x63U, (u8)0x65U
                                                                          };
                                                                        u32 sw12;
                                                                        switch
                                                                        (
                                                                          Spec_Agile_HPKE_hash_of_cs((
                                                                              (Spec_Agile_HPKE_ciphersuite){
                                                                                .fst = Spec_Agile_DH_DH_Curve25519,
                                                                                .snd = Spec_Hash_Definitions_SHA2_256,
                                                                                .thd = {
                                                                                  .tag = Spec_Agile_HPKE_Seal,
                                                                                  .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                                },
                                                                                .f3 = Spec_Hash_Definitions_SHA2_512
                                                                              }
                                                                            ))
                                                                        )
                                                                        {
                                                                          case
                                                                          Spec_Hash_Definitions_SHA2_256:
                                                                            {
                                                                              sw12 = (u32)65U;
                                                                              break;
                                                                            }
                                                                          case
                                                                          Spec_Hash_Definitions_SHA2_384:
                                                                            {
                                                                              sw12 = (u32)97U;
                                                                              break;
                                                                            }
                                                                          case
                                                                          Spec_Hash_Definitions_SHA2_512:
                                                                            {
                                                                              sw12 = (u32)129U;
                                                                              break;
                                                                            }
                                                                          default:
                                                                            {
                                                                              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                __FILE__,
                                                                                __LINE__);
                                                                              KRML_HOST_EXIT(253U);
                                                                            }
                                                                        }
                                                                        {
                                                                          u32
                                                                          len4 =
                                                                            (u32)9U
                                                                            + (u32)10U
                                                                            + (u32)10U
                                                                            + sw12;
                                                                          KRML_CHECK_SIZE(sizeof (
                                                                              u8
                                                                            ),
                                                                            len4);
                                                                          {
                                                                            u8 tmp[len4];
                                                                            memset(tmp,
                                                                              0U,
                                                                              len4 * sizeof (u8));
                                                                            {
                                                                              u8 *uu____26 = tmp;
                                                                              u8
                                                                              *uu____27 = uu____26;
                                                                              Spec_Agile_HPKE_aead
                                                                              scrut3 =
                                                                                Spec_Agile_HPKE_aead_of_cs((
                                                                                    (Spec_Agile_HPKE_ciphersuite){
                                                                                      .fst = Spec_Agile_DH_DH_Curve25519,
                                                                                      .snd = Spec_Hash_Definitions_SHA2_256,
                                                                                      .thd = {
                                                                                        .tag = Spec_Agile_HPKE_Seal,
                                                                                        .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                                      },
                                                                                      .f3 = Spec_Hash_Definitions_SHA2_512
                                                                                    }
                                                                                  ));
                                                                              u32 ite3;
                                                                              if
                                                                              (
                                                                                scrut3.tag
                                                                                ==
                                                                                  Spec_Agile_HPKE_ExportOnly
                                                                              )
                                                                                ite3 = (u32)0U;
                                                                              else if
                                                                              (
                                                                                scrut3.tag
                                                                                ==
                                                                                  Spec_Agile_HPKE_Seal
                                                                              )
                                                                                ite3 = (u32)12U;
                                                                              else
                                                                                ite3 =
                                                                                  KRML_EABORT(u32,
                                                                                    "unreachable (pattern matches are exhaustive in F*)");
                                                                              store32_be(uu____27,
                                                                                ite3);
                                                                              memcpy(uu____26,
                                                                                uu____26 + (u32)2U,
                                                                                (u32)2U
                                                                                * sizeof (u8));
                                                                              {
                                                                                u8
                                                                                *uu____28 =
                                                                                  tmp
                                                                                  + (u32)2U;
                                                                                uu____28[0U] =
                                                                                  (u8)0x48U;
                                                                                uu____28[1U] =
                                                                                  (u8)0x50U;
                                                                                uu____28[2U] =
                                                                                  (u8)0x4bU;
                                                                                uu____28[3U] =
                                                                                  (u8)0x45U;
                                                                                uu____28[4U] =
                                                                                  (u8)0x2dU;
                                                                                uu____28[5U] =
                                                                                  (u8)0x76U;
                                                                                uu____28[6U] =
                                                                                  (u8)0x31U;
                                                                                memcpy(tmp + (u32)9U,
                                                                                  suite_id,
                                                                                  (u32)10U
                                                                                  * sizeof (u8));
                                                                                memcpy(tmp
                                                                                  +
                                                                                    (u32)9U
                                                                                    + (u32)10U,
                                                                                  label_base_nonce,
                                                                                  (u32)10U
                                                                                  * sizeof (u8));
                                                                                {
                                                                                  u8
                                                                                  *uu____29 =
                                                                                    tmp
                                                                                    +
                                                                                      (u32)9U
                                                                                      + (u32)10U
                                                                                      + (u32)10U;
                                                                                  u32 sw;
                                                                                  switch
                                                                                  (
                                                                                    Spec_Agile_HPKE_hash_of_cs((
                                                                                        (Spec_Agile_HPKE_ciphersuite){
                                                                                          .fst = Spec_Agile_DH_DH_Curve25519,
                                                                                          .snd = Spec_Hash_Definitions_SHA2_256,
                                                                                          .thd = {
                                                                                            .tag = Spec_Agile_HPKE_Seal,
                                                                                            .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                                          },
                                                                                          .f3 = Spec_Hash_Definitions_SHA2_512
                                                                                        }
                                                                                      ))
                                                                                  )
                                                                                  {
                                                                                    case
                                                                                    Spec_Hash_Definitions_SHA2_256:
                                                                                      {
                                                                                        sw =
                                                                                          (u32)65U;
                                                                                        break;
                                                                                      }
                                                                                    case
                                                                                    Spec_Hash_Definitions_SHA2_384:
                                                                                      {
                                                                                        sw =
                                                                                          (u32)97U;
                                                                                        break;
                                                                                      }
                                                                                    case
                                                                                    Spec_Hash_Definitions_SHA2_512:
                                                                                      {
                                                                                        sw =
                                                                                          (u32)129U;
                                                                                        break;
                                                                                      }
                                                                                    default:
                                                                                      {
                                                                                        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                          __FILE__,
                                                                                          __LINE__);
                                                                                        KRML_HOST_EXIT(253U);
                                                                                      }
                                                                                  }
                                                                                  memcpy(uu____29,
                                                                                    o_context,
                                                                                    sw * sizeof (u8));
                                                                                  {
                                                                                    u32 sw13;
                                                                                    switch
                                                                                    (
                                                                                      Spec_Agile_HPKE_hash_of_cs((
                                                                                          (Spec_Agile_HPKE_ciphersuite){
                                                                                            .fst = Spec_Agile_DH_DH_Curve25519,
                                                                                            .snd = Spec_Hash_Definitions_SHA2_256,
                                                                                            .thd = {
                                                                                              .tag = Spec_Agile_HPKE_Seal,
                                                                                              .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                                            },
                                                                                            .f3 = Spec_Hash_Definitions_SHA2_512
                                                                                          }
                                                                                        ))
                                                                                    )
                                                                                    {
                                                                                      case
                                                                                      Spec_Hash_Definitions_SHA2_256:
                                                                                        {
                                                                                          sw13 =
                                                                                            (u32)32U;
                                                                                          break;
                                                                                        }
                                                                                      case
                                                                                      Spec_Hash_Definitions_SHA2_384:
                                                                                        {
                                                                                          sw13 =
                                                                                            (u32)48U;
                                                                                          break;
                                                                                        }
                                                                                      case
                                                                                      Spec_Hash_Definitions_SHA2_512:
                                                                                        {
                                                                                          sw13 =
                                                                                            (u32)64U;
                                                                                          break;
                                                                                        }
                                                                                      default:
                                                                                        {
                                                                                          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                            __FILE__,
                                                                                            __LINE__);
                                                                                          KRML_HOST_EXIT(253U);
                                                                                        }
                                                                                    }
                                                                                    {
                                                                                      Spec_Agile_HPKE_aead
                                                                                      scrut =
                                                                                        Spec_Agile_HPKE_aead_of_cs((
                                                                                            (Spec_Agile_HPKE_ciphersuite){
                                                                                              .fst = Spec_Agile_DH_DH_Curve25519,
                                                                                              .snd = Spec_Hash_Definitions_SHA2_256,
                                                                                              .thd = {
                                                                                                .tag = Spec_Agile_HPKE_Seal,
                                                                                                .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                                              },
                                                                                              .f3 = Spec_Hash_Definitions_SHA2_512
                                                                                            }
                                                                                          ));
                                                                                      u32 ite;
                                                                                      if
                                                                                      (
                                                                                        scrut.tag
                                                                                        ==
                                                                                          Spec_Agile_HPKE_ExportOnly
                                                                                      )
                                                                                        ite =
                                                                                          (u32)0U;
                                                                                      else if
                                                                                      (
                                                                                        scrut.tag
                                                                                        ==
                                                                                          Spec_Agile_HPKE_Seal
                                                                                      )
                                                                                        ite =
                                                                                          (u32)12U;
                                                                                      else
                                                                                        ite =
                                                                                          KRML_EABORT(u32,
                                                                                            "unreachable (pattern matches are exhaustive in F*)");
                                                                                      Hacl_HKDF_expand_sha2_512(o_ctx.ctx_nonce,
                                                                                        o_secret,
                                                                                        sw13,
                                                                                        tmp,
                                                                                        len4,
                                                                                        ite);
                                                                                      o_ctx.ctx_seq[0U]
                                                                                      = (u64)0U;
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
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                      ite0 = res0;
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
        }
      }
    }
  }
  else
    ite0 = res0;
  return ite0;
}

u32
Hacl_HPKE_Curve51_CP128_SHA512_setupBaseR(
  Hacl_Impl_HPKE_context_s o_ctx,
  u8 *enc,
  u8 *skR,
  u32 infolen,
  u8 *info
)
{
  u8 pkR[32U] = { 0U };
  u32 res1;
  u32 ite0;
  Hacl_Curve25519_51_secret_to_public(pkR, skR);
  res1 = (u32)0U;
  if (res1 == (u32)0U)
  {
    u8 shared[32U] = { 0U };
    u8 *pkE = enc;
    u8 dh[32U] = { 0U };
    u8 zeros[32U] = { 0U };
    Hacl_Curve25519_51_scalarmult(dh, skR, pkE);
    {
      u8 res0 = (u8)255U;
      {
        u32 i;
        for (i = (u32)0U; i < (u32)32U; i++)
        {
          u8 uu____0 = FStar_UInt8_eq_mask(dh[i], zeros[i]);
          res0 = uu____0 & res0;
        }
      }
      {
        u8 z = res0;
        u32 res;
        if (z == (u8)255U)
          res = (u32)1U;
        else
          res = (u32)0U;
        {
          u32 res11 = res;
          u32 res2;
          if (res11 == (u32)0U)
          {
            u8 kemcontext[64U] = { 0U };
            u32 sw0;
            switch
            (
              Spec_Agile_HPKE_kem_dh_of_cs((
                  (Spec_Agile_HPKE_ciphersuite){
                    .fst = Spec_Agile_DH_DH_Curve25519,
                    .snd = Spec_Hash_Definitions_SHA2_256,
                    .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
                    .f3 = Spec_Hash_Definitions_SHA2_512
                  }
                ))
            )
            {
              case Spec_Agile_DH_DH_Curve25519:
                {
                  sw0 = (u32)32U;
                  break;
                }
              case Spec_Agile_DH_DH_P256:
                {
                  sw0 = (u32)65U;
                  break;
                }
              default:
                {
                  KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                  KRML_HOST_EXIT(253U);
                }
            }
            {
              u8 *pkRm = kemcontext + sw0;
              u8 *pkR1 = pkRm;
              Hacl_Curve25519_51_secret_to_public(pkR1, skR);
              {
                u32 res20 = (u32)0U;
                if (res20 == (u32)0U)
                {
                  u8 *uu____1 = kemcontext;
                  u32 sw1;
                  switch
                  (
                    Spec_Agile_HPKE_kem_dh_of_cs((
                        (Spec_Agile_HPKE_ciphersuite){
                          .fst = Spec_Agile_DH_DH_Curve25519,
                          .snd = Spec_Hash_Definitions_SHA2_256,
                          .thd = {
                            .tag = Spec_Agile_HPKE_Seal,
                            .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                          },
                          .f3 = Spec_Hash_Definitions_SHA2_512
                        }
                      ))
                  )
                  {
                    case Spec_Agile_DH_DH_Curve25519:
                      {
                        sw1 = (u32)32U;
                        break;
                      }
                    case Spec_Agile_DH_DH_P256:
                      {
                        sw1 = (u32)65U;
                        break;
                      }
                    default:
                      {
                        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                          __FILE__,
                          __LINE__);
                        KRML_HOST_EXIT(253U);
                      }
                  }
                  memcpy(uu____1, enc, sw1 * sizeof (u8));
                  {
                    u8 *dhm = dh;
                    u8 o_eae_prk[32U] = { 0U };
                    u8 suite_id_kem[5U] = { 0U };
                    u8 *uu____2 = suite_id_kem;
                    uu____2[0U] = (u8)0x4bU;
                    uu____2[1U] = (u8)0x45U;
                    uu____2[2U] = (u8)0x4dU;
                    {
                      u8 *uu____3 = suite_id_kem + (u32)3U;
                      uu____3[0U] = (u8)0U;
                      uu____3[1U] = (u8)32U;
                      {
                        u8 *empty = suite_id_kem;
                        u8
                        label_eae_prk[7U] =
                          {
                            (u8)0x65U, (u8)0x61U, (u8)0x65U, (u8)0x5fU, (u8)0x70U, (u8)0x72U,
                            (u8)0x6bU
                          };
                        u32 len = (u32)7U + (u32)5U + (u32)7U + (u32)32U;
                        KRML_CHECK_SIZE(sizeof (u8), len);
                        {
                          u8 tmp0[len];
                          memset(tmp0, 0U, len * sizeof (u8));
                          {
                            u8 *uu____4 = tmp0;
                            uu____4[0U] = (u8)0x48U;
                            uu____4[1U] = (u8)0x50U;
                            uu____4[2U] = (u8)0x4bU;
                            uu____4[3U] = (u8)0x45U;
                            uu____4[4U] = (u8)0x2dU;
                            uu____4[5U] = (u8)0x76U;
                            uu____4[6U] = (u8)0x31U;
                            memcpy(tmp0 + (u32)7U, suite_id_kem, (u32)5U * sizeof (u8));
                            memcpy(tmp0 + (u32)7U + (u32)5U, label_eae_prk, (u32)7U * sizeof (u8));
                            memcpy(tmp0 + (u32)7U + (u32)5U + (u32)7U, dhm, (u32)32U * sizeof (u8));
                            Hacl_HKDF_extract_sha2_256(o_eae_prk, empty, (u32)0U, tmp0, len);
                            {
                              u8
                              label_shared_secret[13U] =
                                {
                                  (u8)0x73U, (u8)0x68U, (u8)0x61U, (u8)0x72U, (u8)0x65U, (u8)0x64U,
                                  (u8)0x5fU, (u8)0x73U, (u8)0x65U, (u8)0x63U, (u8)0x72U, (u8)0x65U,
                                  (u8)0x74U
                                };
                              u32 sw2;
                              switch
                              (
                                Spec_Agile_HPKE_kem_dh_of_cs((
                                    (Spec_Agile_HPKE_ciphersuite){
                                      .fst = Spec_Agile_DH_DH_Curve25519,
                                      .snd = Spec_Hash_Definitions_SHA2_256,
                                      .thd = {
                                        .tag = Spec_Agile_HPKE_Seal,
                                        .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                      },
                                      .f3 = Spec_Hash_Definitions_SHA2_512
                                    }
                                  ))
                              )
                              {
                                case Spec_Agile_DH_DH_Curve25519:
                                  {
                                    sw2 = (u32)64U;
                                    break;
                                  }
                                case Spec_Agile_DH_DH_P256:
                                  {
                                    sw2 = (u32)130U;
                                    break;
                                  }
                                default:
                                  {
                                    KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                      __FILE__,
                                      __LINE__);
                                    KRML_HOST_EXIT(253U);
                                  }
                              }
                              {
                                u32 len0 = (u32)9U + (u32)5U + (u32)13U + sw2;
                                KRML_CHECK_SIZE(sizeof (u8), len0);
                                {
                                  u8 tmp[len0];
                                  memset(tmp, 0U, len0 * sizeof (u8));
                                  {
                                    u8 *uu____5 = tmp;
                                    u8 *uu____6 = uu____5;
                                    u32 sw3;
                                    switch
                                    (
                                      Spec_Agile_HPKE_kem_hash_of_cs((
                                          (Spec_Agile_HPKE_ciphersuite){
                                            .fst = Spec_Agile_DH_DH_Curve25519,
                                            .snd = Spec_Hash_Definitions_SHA2_256,
                                            .thd = {
                                              .tag = Spec_Agile_HPKE_Seal,
                                              .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                            },
                                            .f3 = Spec_Hash_Definitions_SHA2_512
                                          }
                                        ))
                                    )
                                    {
                                      case Spec_Hash_Definitions_SHA2_256:
                                        {
                                          sw3 = (u32)32U;
                                          break;
                                        }
                                      default:
                                        {
                                          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                            __FILE__,
                                            __LINE__);
                                          KRML_HOST_EXIT(253U);
                                        }
                                    }
                                    store32_be(uu____6, sw3);
                                    memcpy(uu____5, uu____5 + (u32)2U, (u32)2U * sizeof (u8));
                                    {
                                      u8 *uu____7 = tmp + (u32)2U;
                                      uu____7[0U] = (u8)0x48U;
                                      uu____7[1U] = (u8)0x50U;
                                      uu____7[2U] = (u8)0x4bU;
                                      uu____7[3U] = (u8)0x45U;
                                      uu____7[4U] = (u8)0x2dU;
                                      uu____7[5U] = (u8)0x76U;
                                      uu____7[6U] = (u8)0x31U;
                                      memcpy(tmp + (u32)9U, suite_id_kem, (u32)5U * sizeof (u8));
                                      memcpy(tmp + (u32)9U + (u32)5U,
                                        label_shared_secret,
                                        (u32)13U * sizeof (u8));
                                      {
                                        u8 *uu____8 = tmp + (u32)9U + (u32)5U + (u32)13U;
                                        u32 sw4;
                                        switch
                                        (
                                          Spec_Agile_HPKE_kem_dh_of_cs((
                                              (Spec_Agile_HPKE_ciphersuite){
                                                .fst = Spec_Agile_DH_DH_Curve25519,
                                                .snd = Spec_Hash_Definitions_SHA2_256,
                                                .thd = {
                                                  .tag = Spec_Agile_HPKE_Seal,
                                                  .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                },
                                                .f3 = Spec_Hash_Definitions_SHA2_512
                                              }
                                            ))
                                        )
                                        {
                                          case Spec_Agile_DH_DH_Curve25519:
                                            {
                                              sw4 = (u32)64U;
                                              break;
                                            }
                                          case Spec_Agile_DH_DH_P256:
                                            {
                                              sw4 = (u32)130U;
                                              break;
                                            }
                                          default:
                                            {
                                              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                __FILE__,
                                                __LINE__);
                                              KRML_HOST_EXIT(253U);
                                            }
                                        }
                                        memcpy(uu____8, kemcontext, sw4 * sizeof (u8));
                                        {
                                          u32 sw5;
                                          switch
                                          (
                                            Spec_Agile_HPKE_kem_hash_of_cs((
                                                (Spec_Agile_HPKE_ciphersuite){
                                                  .fst = Spec_Agile_DH_DH_Curve25519,
                                                  .snd = Spec_Hash_Definitions_SHA2_256,
                                                  .thd = {
                                                    .tag = Spec_Agile_HPKE_Seal,
                                                    .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                  },
                                                  .f3 = Spec_Hash_Definitions_SHA2_512
                                                }
                                              ))
                                          )
                                          {
                                            case Spec_Hash_Definitions_SHA2_256:
                                              {
                                                sw5 = (u32)32U;
                                                break;
                                              }
                                            default:
                                              {
                                                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                  __FILE__,
                                                  __LINE__);
                                                KRML_HOST_EXIT(253U);
                                              }
                                          }
                                          {
                                            u32 sw;
                                            switch
                                            (
                                              Spec_Agile_HPKE_kem_hash_of_cs((
                                                  (Spec_Agile_HPKE_ciphersuite){
                                                    .fst = Spec_Agile_DH_DH_Curve25519,
                                                    .snd = Spec_Hash_Definitions_SHA2_256,
                                                    .thd = {
                                                      .tag = Spec_Agile_HPKE_Seal,
                                                      .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                    },
                                                    .f3 = Spec_Hash_Definitions_SHA2_512
                                                  }
                                                ))
                                            )
                                            {
                                              case Spec_Hash_Definitions_SHA2_256:
                                                {
                                                  sw = (u32)32U;
                                                  break;
                                                }
                                              default:
                                                {
                                                  KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                    __FILE__,
                                                    __LINE__);
                                                  KRML_HOST_EXIT(253U);
                                                }
                                            }
                                            Hacl_HKDF_expand_sha2_256(shared,
                                              o_eae_prk,
                                              sw5,
                                              tmp,
                                              len0,
                                              sw);
                                            res2 = (u32)0U;
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
                    }
                  }
                }
                else
                  res2 = (u32)1U;
              }
            }
          }
          else
            res2 = (u32)1U;
          if (res2 == (u32)0U)
          {
            u8 o_context[129U] = { 0U };
            u8 o_secret[64U] = { 0U };
            u8 suite_id[10U] = { 0U };
            u8 *uu____9 = suite_id;
            uu____9[0U] = (u8)0x48U;
            uu____9[1U] = (u8)0x50U;
            uu____9[2U] = (u8)0x4bU;
            uu____9[3U] = (u8)0x45U;
            {
              u8 *uu____10 = suite_id + (u32)4U;
              uu____10[0U] = (u8)0U;
              uu____10[1U] = (u8)32U;
              {
                u8 *uu____11 = suite_id + (u32)6U;
                uu____11[0U] = (u8)0U;
                uu____11[1U] = (u8)3U;
                {
                  u8 *uu____12 = suite_id + (u32)8U;
                  uu____12[0U] = (u8)0U;
                  uu____12[1U] = (u8)3U;
                  {
                    u8
                    label_psk_id_hash[11U] =
                      {
                        (u8)0x70U, (u8)0x73U, (u8)0x6bU, (u8)0x5fU, (u8)0x69U, (u8)0x64U, (u8)0x5fU,
                        (u8)0x68U, (u8)0x61U, (u8)0x73U, (u8)0x68U
                      };
                    u8 o_psk_id_hash[64U] = { 0U };
                    u8 *empty = suite_id;
                    u32 len0 = (u32)7U + (u32)10U + (u32)11U + (u32)0U;
                    KRML_CHECK_SIZE(sizeof (u8), len0);
                    {
                      u8 tmp0[len0];
                      memset(tmp0, 0U, len0 * sizeof (u8));
                      {
                        u8 *uu____13 = tmp0;
                        uu____13[0U] = (u8)0x48U;
                        uu____13[1U] = (u8)0x50U;
                        uu____13[2U] = (u8)0x4bU;
                        uu____13[3U] = (u8)0x45U;
                        uu____13[4U] = (u8)0x2dU;
                        uu____13[5U] = (u8)0x76U;
                        uu____13[6U] = (u8)0x31U;
                        memcpy(tmp0 + (u32)7U, suite_id, (u32)10U * sizeof (u8));
                        memcpy(tmp0 + (u32)7U + (u32)10U,
                          label_psk_id_hash,
                          (u32)11U * sizeof (u8));
                        memcpy(tmp0 + (u32)7U + (u32)10U + (u32)11U, empty, (u32)0U * sizeof (u8));
                        Hacl_HKDF_extract_sha2_512(o_psk_id_hash, empty, (u32)0U, tmp0, len0);
                        {
                          u8
                          label_info_hash[9U] =
                            {
                              (u8)0x69U, (u8)0x6eU, (u8)0x66U, (u8)0x6fU, (u8)0x5fU, (u8)0x68U,
                              (u8)0x61U, (u8)0x73U, (u8)0x68U
                            };
                          u8 o_info_hash[64U] = { 0U };
                          u32 len1 = (u32)7U + (u32)10U + (u32)9U + infolen;
                          KRML_CHECK_SIZE(sizeof (u8), len1);
                          {
                            u8 tmp1[len1];
                            memset(tmp1, 0U, len1 * sizeof (u8));
                            {
                              u8 *uu____14 = tmp1;
                              uu____14[0U] = (u8)0x48U;
                              uu____14[1U] = (u8)0x50U;
                              uu____14[2U] = (u8)0x4bU;
                              uu____14[3U] = (u8)0x45U;
                              uu____14[4U] = (u8)0x2dU;
                              uu____14[5U] = (u8)0x76U;
                              uu____14[6U] = (u8)0x31U;
                              memcpy(tmp1 + (u32)7U, suite_id, (u32)10U * sizeof (u8));
                              memcpy(tmp1 + (u32)7U + (u32)10U,
                                label_info_hash,
                                (u32)9U * sizeof (u8));
                              memcpy(tmp1 + (u32)7U + (u32)10U + (u32)9U,
                                info,
                                infolen * sizeof (u8));
                              Hacl_HKDF_extract_sha2_512(o_info_hash, empty, (u32)0U, tmp1, len1);
                              o_context[0U] = (u8)0U;
                              {
                                u8 *uu____15 = o_context + (u32)1U;
                                u32 sw0;
                                switch
                                (
                                  Spec_Agile_HPKE_hash_of_cs((
                                      (Spec_Agile_HPKE_ciphersuite){
                                        .fst = Spec_Agile_DH_DH_Curve25519,
                                        .snd = Spec_Hash_Definitions_SHA2_256,
                                        .thd = {
                                          .tag = Spec_Agile_HPKE_Seal,
                                          .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                        },
                                        .f3 = Spec_Hash_Definitions_SHA2_512
                                      }
                                    ))
                                )
                                {
                                  case Spec_Hash_Definitions_SHA2_256:
                                    {
                                      sw0 = (u32)32U;
                                      break;
                                    }
                                  case Spec_Hash_Definitions_SHA2_384:
                                    {
                                      sw0 = (u32)48U;
                                      break;
                                    }
                                  case Spec_Hash_Definitions_SHA2_512:
                                    {
                                      sw0 = (u32)64U;
                                      break;
                                    }
                                  default:
                                    {
                                      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                        __FILE__,
                                        __LINE__);
                                      KRML_HOST_EXIT(253U);
                                    }
                                }
                                memcpy(uu____15, o_psk_id_hash, sw0 * sizeof (u8));
                                {
                                  u32 sw1;
                                  switch
                                  (
                                    Spec_Agile_HPKE_hash_of_cs((
                                        (Spec_Agile_HPKE_ciphersuite){
                                          .fst = Spec_Agile_DH_DH_Curve25519,
                                          .snd = Spec_Hash_Definitions_SHA2_256,
                                          .thd = {
                                            .tag = Spec_Agile_HPKE_Seal,
                                            .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                          },
                                          .f3 = Spec_Hash_Definitions_SHA2_512
                                        }
                                      ))
                                  )
                                  {
                                    case Spec_Hash_Definitions_SHA2_256:
                                      {
                                        sw1 = (u32)33U;
                                        break;
                                      }
                                    case Spec_Hash_Definitions_SHA2_384:
                                      {
                                        sw1 = (u32)49U;
                                        break;
                                      }
                                    case Spec_Hash_Definitions_SHA2_512:
                                      {
                                        sw1 = (u32)65U;
                                        break;
                                      }
                                    default:
                                      {
                                        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                          __FILE__,
                                          __LINE__);
                                        KRML_HOST_EXIT(253U);
                                      }
                                  }
                                  {
                                    u8 *uu____16 = o_context + sw1;
                                    u32 sw2;
                                    switch
                                    (
                                      Spec_Agile_HPKE_hash_of_cs((
                                          (Spec_Agile_HPKE_ciphersuite){
                                            .fst = Spec_Agile_DH_DH_Curve25519,
                                            .snd = Spec_Hash_Definitions_SHA2_256,
                                            .thd = {
                                              .tag = Spec_Agile_HPKE_Seal,
                                              .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                            },
                                            .f3 = Spec_Hash_Definitions_SHA2_512
                                          }
                                        ))
                                    )
                                    {
                                      case Spec_Hash_Definitions_SHA2_256:
                                        {
                                          sw2 = (u32)32U;
                                          break;
                                        }
                                      case Spec_Hash_Definitions_SHA2_384:
                                        {
                                          sw2 = (u32)48U;
                                          break;
                                        }
                                      case Spec_Hash_Definitions_SHA2_512:
                                        {
                                          sw2 = (u32)64U;
                                          break;
                                        }
                                      default:
                                        {
                                          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                            __FILE__,
                                            __LINE__);
                                          KRML_HOST_EXIT(253U);
                                        }
                                    }
                                    memcpy(uu____16, o_info_hash, sw2 * sizeof (u8));
                                    {
                                      u8
                                      label_secret[6U] =
                                        {
                                          (u8)0x73U, (u8)0x65U, (u8)0x63U, (u8)0x72U, (u8)0x65U,
                                          (u8)0x74U
                                        };
                                      u32 len = (u32)7U + (u32)10U + (u32)6U + (u32)0U;
                                      KRML_CHECK_SIZE(sizeof (u8), len);
                                      {
                                        u8 tmp2[len];
                                        memset(tmp2, 0U, len * sizeof (u8));
                                        {
                                          u8 *uu____17 = tmp2;
                                          uu____17[0U] = (u8)0x48U;
                                          uu____17[1U] = (u8)0x50U;
                                          uu____17[2U] = (u8)0x4bU;
                                          uu____17[3U] = (u8)0x45U;
                                          uu____17[4U] = (u8)0x2dU;
                                          uu____17[5U] = (u8)0x76U;
                                          uu____17[6U] = (u8)0x31U;
                                          memcpy(tmp2 + (u32)7U, suite_id, (u32)10U * sizeof (u8));
                                          memcpy(tmp2 + (u32)7U + (u32)10U,
                                            label_secret,
                                            (u32)6U * sizeof (u8));
                                          memcpy(tmp2 + (u32)7U + (u32)10U + (u32)6U,
                                            empty,
                                            (u32)0U * sizeof (u8));
                                          {
                                            u32 sw3;
                                            switch
                                            (
                                              Spec_Agile_HPKE_kem_hash_of_cs((
                                                  (Spec_Agile_HPKE_ciphersuite){
                                                    .fst = Spec_Agile_DH_DH_Curve25519,
                                                    .snd = Spec_Hash_Definitions_SHA2_256,
                                                    .thd = {
                                                      .tag = Spec_Agile_HPKE_Seal,
                                                      .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                    },
                                                    .f3 = Spec_Hash_Definitions_SHA2_512
                                                  }
                                                ))
                                            )
                                            {
                                              case Spec_Hash_Definitions_SHA2_256:
                                                {
                                                  sw3 = (u32)32U;
                                                  break;
                                                }
                                              default:
                                                {
                                                  KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                    __FILE__,
                                                    __LINE__);
                                                  KRML_HOST_EXIT(253U);
                                                }
                                            }
                                            Hacl_HKDF_extract_sha2_512(o_secret,
                                              shared,
                                              sw3,
                                              tmp2,
                                              len);
                                            {
                                              u8
                                              label_exp[3U] = { (u8)0x65U, (u8)0x78U, (u8)0x70U };
                                              u32 sw4;
                                              switch
                                              (
                                                Spec_Agile_HPKE_hash_of_cs((
                                                    (Spec_Agile_HPKE_ciphersuite){
                                                      .fst = Spec_Agile_DH_DH_Curve25519,
                                                      .snd = Spec_Hash_Definitions_SHA2_256,
                                                      .thd = {
                                                        .tag = Spec_Agile_HPKE_Seal,
                                                        .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                      },
                                                      .f3 = Spec_Hash_Definitions_SHA2_512
                                                    }
                                                  ))
                                              )
                                              {
                                                case Spec_Hash_Definitions_SHA2_256:
                                                  {
                                                    sw4 = (u32)65U;
                                                    break;
                                                  }
                                                case Spec_Hash_Definitions_SHA2_384:
                                                  {
                                                    sw4 = (u32)97U;
                                                    break;
                                                  }
                                                case Spec_Hash_Definitions_SHA2_512:
                                                  {
                                                    sw4 = (u32)129U;
                                                    break;
                                                  }
                                                default:
                                                  {
                                                    KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                      __FILE__,
                                                      __LINE__);
                                                    KRML_HOST_EXIT(253U);
                                                  }
                                              }
                                              {
                                                u32 len2 = (u32)9U + (u32)10U + (u32)3U + sw4;
                                                KRML_CHECK_SIZE(sizeof (u8), len2);
                                                {
                                                  u8 tmp3[len2];
                                                  memset(tmp3, 0U, len2 * sizeof (u8));
                                                  {
                                                    u8 *uu____18 = tmp3;
                                                    u8 *uu____19 = uu____18;
                                                    u32 sw5;
                                                    switch
                                                    (
                                                      Spec_Agile_HPKE_hash_of_cs((
                                                          (Spec_Agile_HPKE_ciphersuite){
                                                            .fst = Spec_Agile_DH_DH_Curve25519,
                                                            .snd = Spec_Hash_Definitions_SHA2_256,
                                                            .thd = {
                                                              .tag = Spec_Agile_HPKE_Seal,
                                                              .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                            },
                                                            .f3 = Spec_Hash_Definitions_SHA2_512
                                                          }
                                                        ))
                                                    )
                                                    {
                                                      case Spec_Hash_Definitions_SHA2_256:
                                                        {
                                                          sw5 = (u32)32U;
                                                          break;
                                                        }
                                                      case Spec_Hash_Definitions_SHA2_384:
                                                        {
                                                          sw5 = (u32)48U;
                                                          break;
                                                        }
                                                      case Spec_Hash_Definitions_SHA2_512:
                                                        {
                                                          sw5 = (u32)64U;
                                                          break;
                                                        }
                                                      default:
                                                        {
                                                          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                            __FILE__,
                                                            __LINE__);
                                                          KRML_HOST_EXIT(253U);
                                                        }
                                                    }
                                                    store32_be(uu____19, sw5);
                                                    memcpy(uu____18,
                                                      uu____18 + (u32)2U,
                                                      (u32)2U * sizeof (u8));
                                                    {
                                                      u8 *uu____20 = tmp3 + (u32)2U;
                                                      uu____20[0U] = (u8)0x48U;
                                                      uu____20[1U] = (u8)0x50U;
                                                      uu____20[2U] = (u8)0x4bU;
                                                      uu____20[3U] = (u8)0x45U;
                                                      uu____20[4U] = (u8)0x2dU;
                                                      uu____20[5U] = (u8)0x76U;
                                                      uu____20[6U] = (u8)0x31U;
                                                      memcpy(tmp3 + (u32)9U,
                                                        suite_id,
                                                        (u32)10U * sizeof (u8));
                                                      memcpy(tmp3 + (u32)9U + (u32)10U,
                                                        label_exp,
                                                        (u32)3U * sizeof (u8));
                                                      {
                                                        u8
                                                        *uu____21 =
                                                          tmp3
                                                          + (u32)9U + (u32)10U + (u32)3U;
                                                        u32 sw6;
                                                        switch
                                                        (
                                                          Spec_Agile_HPKE_hash_of_cs((
                                                              (Spec_Agile_HPKE_ciphersuite){
                                                                .fst = Spec_Agile_DH_DH_Curve25519,
                                                                .snd = Spec_Hash_Definitions_SHA2_256,
                                                                .thd = {
                                                                  .tag = Spec_Agile_HPKE_Seal,
                                                                  .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                },
                                                                .f3 = Spec_Hash_Definitions_SHA2_512
                                                              }
                                                            ))
                                                        )
                                                        {
                                                          case Spec_Hash_Definitions_SHA2_256:
                                                            {
                                                              sw6 = (u32)65U;
                                                              break;
                                                            }
                                                          case Spec_Hash_Definitions_SHA2_384:
                                                            {
                                                              sw6 = (u32)97U;
                                                              break;
                                                            }
                                                          case Spec_Hash_Definitions_SHA2_512:
                                                            {
                                                              sw6 = (u32)129U;
                                                              break;
                                                            }
                                                          default:
                                                            {
                                                              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                __FILE__,
                                                                __LINE__);
                                                              KRML_HOST_EXIT(253U);
                                                            }
                                                        }
                                                        memcpy(uu____21,
                                                          o_context,
                                                          sw6 * sizeof (u8));
                                                        {
                                                          u32 sw7;
                                                          switch
                                                          (
                                                            Spec_Agile_HPKE_hash_of_cs((
                                                                (Spec_Agile_HPKE_ciphersuite){
                                                                  .fst = Spec_Agile_DH_DH_Curve25519,
                                                                  .snd = Spec_Hash_Definitions_SHA2_256,
                                                                  .thd = {
                                                                    .tag = Spec_Agile_HPKE_Seal,
                                                                    .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                  },
                                                                  .f3 = Spec_Hash_Definitions_SHA2_512
                                                                }
                                                              ))
                                                          )
                                                          {
                                                            case Spec_Hash_Definitions_SHA2_256:
                                                              {
                                                                sw7 = (u32)32U;
                                                                break;
                                                              }
                                                            case Spec_Hash_Definitions_SHA2_384:
                                                              {
                                                                sw7 = (u32)48U;
                                                                break;
                                                              }
                                                            case Spec_Hash_Definitions_SHA2_512:
                                                              {
                                                                sw7 = (u32)64U;
                                                                break;
                                                              }
                                                            default:
                                                              {
                                                                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                  __FILE__,
                                                                  __LINE__);
                                                                KRML_HOST_EXIT(253U);
                                                              }
                                                          }
                                                          {
                                                            u32 sw8;
                                                            switch
                                                            (
                                                              Spec_Agile_HPKE_hash_of_cs((
                                                                  (Spec_Agile_HPKE_ciphersuite){
                                                                    .fst = Spec_Agile_DH_DH_Curve25519,
                                                                    .snd = Spec_Hash_Definitions_SHA2_256,
                                                                    .thd = {
                                                                      .tag = Spec_Agile_HPKE_Seal,
                                                                      .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                    },
                                                                    .f3 = Spec_Hash_Definitions_SHA2_512
                                                                  }
                                                                ))
                                                            )
                                                            {
                                                              case Spec_Hash_Definitions_SHA2_256:
                                                                {
                                                                  sw8 = (u32)32U;
                                                                  break;
                                                                }
                                                              case Spec_Hash_Definitions_SHA2_384:
                                                                {
                                                                  sw8 = (u32)48U;
                                                                  break;
                                                                }
                                                              case Spec_Hash_Definitions_SHA2_512:
                                                                {
                                                                  sw8 = (u32)64U;
                                                                  break;
                                                                }
                                                              default:
                                                                {
                                                                  KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                    __FILE__,
                                                                    __LINE__);
                                                                  KRML_HOST_EXIT(253U);
                                                                }
                                                            }
                                                            Hacl_HKDF_expand_sha2_512(o_ctx.ctx_exporter,
                                                              o_secret,
                                                              sw7,
                                                              tmp3,
                                                              len2,
                                                              sw8);
                                                            {
                                                              Spec_Agile_HPKE_aead
                                                              scrut0 =
                                                                Spec_Agile_HPKE_aead_of_cs((
                                                                    (Spec_Agile_HPKE_ciphersuite){
                                                                      .fst = Spec_Agile_DH_DH_Curve25519,
                                                                      .snd = Spec_Hash_Definitions_SHA2_256,
                                                                      .thd = {
                                                                        .tag = Spec_Agile_HPKE_Seal,
                                                                        .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                      },
                                                                      .f3 = Spec_Hash_Definitions_SHA2_512
                                                                    }
                                                                  ));
                                                              if
                                                              (
                                                                scrut0.tag
                                                                == Spec_Agile_HPKE_ExportOnly
                                                              )
                                                                o_ctx.ctx_seq[0U] = (u64)0U;
                                                              else
                                                              {
                                                                u8
                                                                label_key[3U] =
                                                                  {
                                                                    (u8)0x6bU,
                                                                    (u8)0x65U,
                                                                    (u8)0x79U
                                                                  };
                                                                u32 sw9;
                                                                switch
                                                                (
                                                                  Spec_Agile_HPKE_hash_of_cs((
                                                                      (Spec_Agile_HPKE_ciphersuite){
                                                                        .fst = Spec_Agile_DH_DH_Curve25519,
                                                                        .snd = Spec_Hash_Definitions_SHA2_256,
                                                                        .thd = {
                                                                          .tag = Spec_Agile_HPKE_Seal,
                                                                          .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                        },
                                                                        .f3 = Spec_Hash_Definitions_SHA2_512
                                                                      }
                                                                    ))
                                                                )
                                                                {
                                                                  case
                                                                  Spec_Hash_Definitions_SHA2_256:
                                                                    {
                                                                      sw9 = (u32)65U;
                                                                      break;
                                                                    }
                                                                  case
                                                                  Spec_Hash_Definitions_SHA2_384:
                                                                    {
                                                                      sw9 = (u32)97U;
                                                                      break;
                                                                    }
                                                                  case
                                                                  Spec_Hash_Definitions_SHA2_512:
                                                                    {
                                                                      sw9 = (u32)129U;
                                                                      break;
                                                                    }
                                                                  default:
                                                                    {
                                                                      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                        __FILE__,
                                                                        __LINE__);
                                                                      KRML_HOST_EXIT(253U);
                                                                    }
                                                                }
                                                                {
                                                                  u32
                                                                  len3 =
                                                                    (u32)9U
                                                                    + (u32)10U
                                                                    + (u32)3U
                                                                    + sw9;
                                                                  KRML_CHECK_SIZE(sizeof (u8),
                                                                    len3);
                                                                  {
                                                                    u8 tmp4[len3];
                                                                    memset(tmp4,
                                                                      0U,
                                                                      len3 * sizeof (u8));
                                                                    {
                                                                      u8 *uu____22 = tmp4;
                                                                      u8 *uu____23 = uu____22;
                                                                      Spec_Agile_HPKE_aead
                                                                      scrut1 =
                                                                        Spec_Agile_HPKE_aead_of_cs((
                                                                            (Spec_Agile_HPKE_ciphersuite){
                                                                              .fst = Spec_Agile_DH_DH_Curve25519,
                                                                              .snd = Spec_Hash_Definitions_SHA2_256,
                                                                              .thd = {
                                                                                .tag = Spec_Agile_HPKE_Seal,
                                                                                .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                              },
                                                                              .f3 = Spec_Hash_Definitions_SHA2_512
                                                                            }
                                                                          ));
                                                                      u32 ite1;
                                                                      if
                                                                      (
                                                                        scrut1.tag
                                                                        ==
                                                                          Spec_Agile_HPKE_ExportOnly
                                                                      )
                                                                        ite1 = (u32)0U;
                                                                      else if
                                                                      (
                                                                        scrut1.tag
                                                                        == Spec_Agile_HPKE_Seal
                                                                        &&
                                                                          scrut1.alg
                                                                          ==
                                                                            Spec_Agile_AEAD_AES128_GCM
                                                                      )
                                                                        ite1 = (u32)16U;
                                                                      else if
                                                                      (
                                                                        scrut1.tag
                                                                        == Spec_Agile_HPKE_Seal
                                                                        &&
                                                                          scrut1.alg
                                                                          ==
                                                                            Spec_Agile_AEAD_AES256_GCM
                                                                      )
                                                                        ite1 = (u32)32U;
                                                                      else if
                                                                      (
                                                                        scrut1.tag
                                                                        == Spec_Agile_HPKE_Seal
                                                                        &&
                                                                          scrut1.alg
                                                                          ==
                                                                            Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                      )
                                                                        ite1 = (u32)32U;
                                                                      else
                                                                        ite1 =
                                                                          KRML_EABORT(u32,
                                                                            "unreachable (pattern matches are exhaustive in F*)");
                                                                      store32_be(uu____23, ite1);
                                                                      memcpy(uu____22,
                                                                        uu____22 + (u32)2U,
                                                                        (u32)2U * sizeof (u8));
                                                                      {
                                                                        u8
                                                                        *uu____24 = tmp4 + (u32)2U;
                                                                        uu____24[0U] = (u8)0x48U;
                                                                        uu____24[1U] = (u8)0x50U;
                                                                        uu____24[2U] = (u8)0x4bU;
                                                                        uu____24[3U] = (u8)0x45U;
                                                                        uu____24[4U] = (u8)0x2dU;
                                                                        uu____24[5U] = (u8)0x76U;
                                                                        uu____24[6U] = (u8)0x31U;
                                                                        memcpy(tmp4 + (u32)9U,
                                                                          suite_id,
                                                                          (u32)10U * sizeof (u8));
                                                                        memcpy(tmp4
                                                                          + (u32)9U + (u32)10U,
                                                                          label_key,
                                                                          (u32)3U * sizeof (u8));
                                                                        {
                                                                          u8
                                                                          *uu____25 =
                                                                            tmp4
                                                                            +
                                                                              (u32)9U
                                                                              + (u32)10U
                                                                              + (u32)3U;
                                                                          u32 sw10;
                                                                          switch
                                                                          (
                                                                            Spec_Agile_HPKE_hash_of_cs((
                                                                                (Spec_Agile_HPKE_ciphersuite){
                                                                                  .fst = Spec_Agile_DH_DH_Curve25519,
                                                                                  .snd = Spec_Hash_Definitions_SHA2_256,
                                                                                  .thd = {
                                                                                    .tag = Spec_Agile_HPKE_Seal,
                                                                                    .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                                  },
                                                                                  .f3 = Spec_Hash_Definitions_SHA2_512
                                                                                }
                                                                              ))
                                                                          )
                                                                          {
                                                                            case
                                                                            Spec_Hash_Definitions_SHA2_256:
                                                                              {
                                                                                sw10 = (u32)65U;
                                                                                break;
                                                                              }
                                                                            case
                                                                            Spec_Hash_Definitions_SHA2_384:
                                                                              {
                                                                                sw10 = (u32)97U;
                                                                                break;
                                                                              }
                                                                            case
                                                                            Spec_Hash_Definitions_SHA2_512:
                                                                              {
                                                                                sw10 = (u32)129U;
                                                                                break;
                                                                              }
                                                                            default:
                                                                              {
                                                                                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                  __FILE__,
                                                                                  __LINE__);
                                                                                KRML_HOST_EXIT(253U);
                                                                              }
                                                                          }
                                                                          memcpy(uu____25,
                                                                            o_context,
                                                                            sw10 * sizeof (u8));
                                                                          {
                                                                            u32 sw11;
                                                                            switch
                                                                            (
                                                                              Spec_Agile_HPKE_hash_of_cs((
                                                                                  (Spec_Agile_HPKE_ciphersuite){
                                                                                    .fst = Spec_Agile_DH_DH_Curve25519,
                                                                                    .snd = Spec_Hash_Definitions_SHA2_256,
                                                                                    .thd = {
                                                                                      .tag = Spec_Agile_HPKE_Seal,
                                                                                      .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                                    },
                                                                                    .f3 = Spec_Hash_Definitions_SHA2_512
                                                                                  }
                                                                                ))
                                                                            )
                                                                            {
                                                                              case
                                                                              Spec_Hash_Definitions_SHA2_256:
                                                                                {
                                                                                  sw11 = (u32)32U;
                                                                                  break;
                                                                                }
                                                                              case
                                                                              Spec_Hash_Definitions_SHA2_384:
                                                                                {
                                                                                  sw11 = (u32)48U;
                                                                                  break;
                                                                                }
                                                                              case
                                                                              Spec_Hash_Definitions_SHA2_512:
                                                                                {
                                                                                  sw11 = (u32)64U;
                                                                                  break;
                                                                                }
                                                                              default:
                                                                                {
                                                                                  KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                    __FILE__,
                                                                                    __LINE__);
                                                                                  KRML_HOST_EXIT(253U);
                                                                                }
                                                                            }
                                                                            {
                                                                              Spec_Agile_HPKE_aead
                                                                              scrut2 =
                                                                                Spec_Agile_HPKE_aead_of_cs((
                                                                                    (Spec_Agile_HPKE_ciphersuite){
                                                                                      .fst = Spec_Agile_DH_DH_Curve25519,
                                                                                      .snd = Spec_Hash_Definitions_SHA2_256,
                                                                                      .thd = {
                                                                                        .tag = Spec_Agile_HPKE_Seal,
                                                                                        .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                                      },
                                                                                      .f3 = Spec_Hash_Definitions_SHA2_512
                                                                                    }
                                                                                  ));
                                                                              u32 ite2;
                                                                              if
                                                                              (
                                                                                scrut2.tag
                                                                                ==
                                                                                  Spec_Agile_HPKE_ExportOnly
                                                                              )
                                                                                ite2 = (u32)0U;
                                                                              else if
                                                                              (
                                                                                scrut2.tag
                                                                                ==
                                                                                  Spec_Agile_HPKE_Seal
                                                                                &&
                                                                                  scrut2.alg
                                                                                  ==
                                                                                    Spec_Agile_AEAD_AES128_GCM
                                                                              )
                                                                                ite2 = (u32)16U;
                                                                              else if
                                                                              (
                                                                                scrut2.tag
                                                                                ==
                                                                                  Spec_Agile_HPKE_Seal
                                                                                &&
                                                                                  scrut2.alg
                                                                                  ==
                                                                                    Spec_Agile_AEAD_AES256_GCM
                                                                              )
                                                                                ite2 = (u32)32U;
                                                                              else if
                                                                              (
                                                                                scrut2.tag
                                                                                ==
                                                                                  Spec_Agile_HPKE_Seal
                                                                                &&
                                                                                  scrut2.alg
                                                                                  ==
                                                                                    Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                              )
                                                                                ite2 = (u32)32U;
                                                                              else
                                                                                ite2 =
                                                                                  KRML_EABORT(u32,
                                                                                    "unreachable (pattern matches are exhaustive in F*)");
                                                                              Hacl_HKDF_expand_sha2_512(o_ctx.ctx_key,
                                                                                o_secret,
                                                                                sw11,
                                                                                tmp4,
                                                                                len3,
                                                                                ite2);
                                                                              {
                                                                                u8
                                                                                label_base_nonce[10U] =
                                                                                  {
                                                                                    (u8)0x62U,
                                                                                    (u8)0x61U,
                                                                                    (u8)0x73U,
                                                                                    (u8)0x65U,
                                                                                    (u8)0x5fU,
                                                                                    (u8)0x6eU,
                                                                                    (u8)0x6fU,
                                                                                    (u8)0x6eU,
                                                                                    (u8)0x63U,
                                                                                    (u8)0x65U
                                                                                  };
                                                                                u32 sw12;
                                                                                switch
                                                                                (
                                                                                  Spec_Agile_HPKE_hash_of_cs((
                                                                                      (Spec_Agile_HPKE_ciphersuite){
                                                                                        .fst = Spec_Agile_DH_DH_Curve25519,
                                                                                        .snd = Spec_Hash_Definitions_SHA2_256,
                                                                                        .thd = {
                                                                                          .tag = Spec_Agile_HPKE_Seal,
                                                                                          .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                                        },
                                                                                        .f3 = Spec_Hash_Definitions_SHA2_512
                                                                                      }
                                                                                    ))
                                                                                )
                                                                                {
                                                                                  case
                                                                                  Spec_Hash_Definitions_SHA2_256:
                                                                                    {
                                                                                      sw12 =
                                                                                        (u32)65U;
                                                                                      break;
                                                                                    }
                                                                                  case
                                                                                  Spec_Hash_Definitions_SHA2_384:
                                                                                    {
                                                                                      sw12 =
                                                                                        (u32)97U;
                                                                                      break;
                                                                                    }
                                                                                  case
                                                                                  Spec_Hash_Definitions_SHA2_512:
                                                                                    {
                                                                                      sw12 =
                                                                                        (u32)129U;
                                                                                      break;
                                                                                    }
                                                                                  default:
                                                                                    {
                                                                                      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                        __FILE__,
                                                                                        __LINE__);
                                                                                      KRML_HOST_EXIT(253U);
                                                                                    }
                                                                                }
                                                                                {
                                                                                  u32
                                                                                  len4 =
                                                                                    (u32)9U
                                                                                    + (u32)10U
                                                                                    + (u32)10U
                                                                                    + sw12;
                                                                                  KRML_CHECK_SIZE(sizeof (
                                                                                      u8
                                                                                    ),
                                                                                    len4);
                                                                                  {
                                                                                    u8 tmp[len4];
                                                                                    memset(tmp,
                                                                                      0U,
                                                                                      len4
                                                                                      * sizeof (u8));
                                                                                    {
                                                                                      u8
                                                                                      *uu____26 =
                                                                                        tmp;
                                                                                      u8
                                                                                      *uu____27 =
                                                                                        uu____26;
                                                                                      Spec_Agile_HPKE_aead
                                                                                      scrut3 =
                                                                                        Spec_Agile_HPKE_aead_of_cs((
                                                                                            (Spec_Agile_HPKE_ciphersuite){
                                                                                              .fst = Spec_Agile_DH_DH_Curve25519,
                                                                                              .snd = Spec_Hash_Definitions_SHA2_256,
                                                                                              .thd = {
                                                                                                .tag = Spec_Agile_HPKE_Seal,
                                                                                                .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                                              },
                                                                                              .f3 = Spec_Hash_Definitions_SHA2_512
                                                                                            }
                                                                                          ));
                                                                                      u32 ite3;
                                                                                      if
                                                                                      (
                                                                                        scrut3.tag
                                                                                        ==
                                                                                          Spec_Agile_HPKE_ExportOnly
                                                                                      )
                                                                                        ite3 =
                                                                                          (u32)0U;
                                                                                      else if
                                                                                      (
                                                                                        scrut3.tag
                                                                                        ==
                                                                                          Spec_Agile_HPKE_Seal
                                                                                      )
                                                                                        ite3 =
                                                                                          (u32)12U;
                                                                                      else
                                                                                        ite3 =
                                                                                          KRML_EABORT(u32,
                                                                                            "unreachable (pattern matches are exhaustive in F*)");
                                                                                      store32_be(uu____27,
                                                                                        ite3);
                                                                                      memcpy(uu____26,
                                                                                        uu____26
                                                                                        + (u32)2U,
                                                                                        (u32)2U
                                                                                        *
                                                                                          sizeof (
                                                                                            u8
                                                                                          ));
                                                                                      {
                                                                                        u8
                                                                                        *uu____28 =
                                                                                          tmp
                                                                                          + (u32)2U;
                                                                                        uu____28[0U]
                                                                                        = (u8)0x48U;
                                                                                        uu____28[1U]
                                                                                        = (u8)0x50U;
                                                                                        uu____28[2U]
                                                                                        = (u8)0x4bU;
                                                                                        uu____28[3U]
                                                                                        = (u8)0x45U;
                                                                                        uu____28[4U]
                                                                                        = (u8)0x2dU;
                                                                                        uu____28[5U]
                                                                                        = (u8)0x76U;
                                                                                        uu____28[6U]
                                                                                        = (u8)0x31U;
                                                                                        memcpy(tmp
                                                                                          + (u32)9U,
                                                                                          suite_id,
                                                                                          (u32)10U
                                                                                          *
                                                                                            sizeof (
                                                                                              u8
                                                                                            ));
                                                                                        memcpy(tmp
                                                                                          +
                                                                                            (u32)9U
                                                                                            +
                                                                                              (u32)10U,
                                                                                          label_base_nonce,
                                                                                          (u32)10U
                                                                                          *
                                                                                            sizeof (
                                                                                              u8
                                                                                            ));
                                                                                        {
                                                                                          u8
                                                                                          *uu____29 =
                                                                                            tmp
                                                                                            +
                                                                                              (u32)9U
                                                                                              +
                                                                                                (u32)10U
                                                                                              +
                                                                                                (u32)10U;
                                                                                          u32 sw;
                                                                                          switch
                                                                                          (
                                                                                            Spec_Agile_HPKE_hash_of_cs((
                                                                                                (Spec_Agile_HPKE_ciphersuite){
                                                                                                  .fst = Spec_Agile_DH_DH_Curve25519,
                                                                                                  .snd = Spec_Hash_Definitions_SHA2_256,
                                                                                                  .thd = {
                                                                                                    .tag = Spec_Agile_HPKE_Seal,
                                                                                                    .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                                                  },
                                                                                                  .f3 = Spec_Hash_Definitions_SHA2_512
                                                                                                }
                                                                                              ))
                                                                                          )
                                                                                          {
                                                                                            case
                                                                                            Spec_Hash_Definitions_SHA2_256:
                                                                                              {
                                                                                                sw =
                                                                                                  (u32)65U;
                                                                                                break;
                                                                                              }
                                                                                            case
                                                                                            Spec_Hash_Definitions_SHA2_384:
                                                                                              {
                                                                                                sw =
                                                                                                  (u32)97U;
                                                                                                break;
                                                                                              }
                                                                                            case
                                                                                            Spec_Hash_Definitions_SHA2_512:
                                                                                              {
                                                                                                sw =
                                                                                                  (u32)129U;
                                                                                                break;
                                                                                              }
                                                                                            default:
                                                                                              {
                                                                                                KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                                  __FILE__,
                                                                                                  __LINE__);
                                                                                                KRML_HOST_EXIT(253U);
                                                                                              }
                                                                                          }
                                                                                          memcpy(uu____29,
                                                                                            o_context,
                                                                                            sw
                                                                                            *
                                                                                              sizeof (
                                                                                                u8
                                                                                              ));
                                                                                          {
                                                                                            u32
                                                                                            sw13;
                                                                                            switch
                                                                                            (
                                                                                              Spec_Agile_HPKE_hash_of_cs((
                                                                                                  (Spec_Agile_HPKE_ciphersuite){
                                                                                                    .fst = Spec_Agile_DH_DH_Curve25519,
                                                                                                    .snd = Spec_Hash_Definitions_SHA2_256,
                                                                                                    .thd = {
                                                                                                      .tag = Spec_Agile_HPKE_Seal,
                                                                                                      .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                                                    },
                                                                                                    .f3 = Spec_Hash_Definitions_SHA2_512
                                                                                                  }
                                                                                                ))
                                                                                            )
                                                                                            {
                                                                                              case
                                                                                              Spec_Hash_Definitions_SHA2_256:
                                                                                                {
                                                                                                  sw13
                                                                                                  =
                                                                                                    (u32)32U;
                                                                                                  break;
                                                                                                }
                                                                                              case
                                                                                              Spec_Hash_Definitions_SHA2_384:
                                                                                                {
                                                                                                  sw13
                                                                                                  =
                                                                                                    (u32)48U;
                                                                                                  break;
                                                                                                }
                                                                                              case
                                                                                              Spec_Hash_Definitions_SHA2_512:
                                                                                                {
                                                                                                  sw13
                                                                                                  =
                                                                                                    (u32)64U;
                                                                                                  break;
                                                                                                }
                                                                                              default:
                                                                                                {
                                                                                                  KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                                    __FILE__,
                                                                                                    __LINE__);
                                                                                                  KRML_HOST_EXIT(253U);
                                                                                                }
                                                                                            }
                                                                                            {
                                                                                              Spec_Agile_HPKE_aead
                                                                                              scrut =
                                                                                                Spec_Agile_HPKE_aead_of_cs((
                                                                                                    (Spec_Agile_HPKE_ciphersuite){
                                                                                                      .fst = Spec_Agile_DH_DH_Curve25519,
                                                                                                      .snd = Spec_Hash_Definitions_SHA2_256,
                                                                                                      .thd = {
                                                                                                        .tag = Spec_Agile_HPKE_Seal,
                                                                                                        .alg = Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                                                      },
                                                                                                      .f3 = Spec_Hash_Definitions_SHA2_512
                                                                                                    }
                                                                                                  ));
                                                                                              u32
                                                                                              ite;
                                                                                              if
                                                                                              (
                                                                                                scrut.tag
                                                                                                ==
                                                                                                  Spec_Agile_HPKE_ExportOnly
                                                                                              )
                                                                                                ite
                                                                                                =
                                                                                                  (u32)0U;
                                                                                              else if
                                                                                              (
                                                                                                scrut.tag
                                                                                                ==
                                                                                                  Spec_Agile_HPKE_Seal
                                                                                              )
                                                                                                ite
                                                                                                =
                                                                                                  (u32)12U;
                                                                                              else
                                                                                                ite
                                                                                                =
                                                                                                  KRML_EABORT(u32,
                                                                                                    "unreachable (pattern matches are exhaustive in F*)");
                                                                                              Hacl_HKDF_expand_sha2_512(o_ctx.ctx_nonce,
                                                                                                o_secret,
                                                                                                sw13,
                                                                                                tmp,
                                                                                                len4,
                                                                                                ite);
                                                                                              o_ctx.ctx_seq[0U]
                                                                                              =
                                                                                                (u64)0U;
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
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                              ite0 = (u32)0U;
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
                }
              }
            }
          }
          else
            ite0 = (u32)1U;
        }
      }
    }
  }
  else
    ite0 = (u32)1U;
  return ite0;
}

u32
Hacl_HPKE_Curve51_CP128_SHA512_sealBase(
  u8 *skE,
  u8 *pkR,
  u32 infolen,
  u8 *info,
  u32 aadlen,
  u8 *aad,
  u32 plainlen,
  u8 *plain,
  u8 *o_enc,
  u8 *o_ct
)
{
  u8 ctx_key[32U] = { 0U };
  u8 ctx_nonce[12U] = { 0U };
  u64 ctx_seq = (u64)0U;
  u8 ctx_exporter[64U] = { 0U };
  Hacl_Impl_HPKE_context_s
  o_ctx =
    {
      .ctx_key = ctx_key,
      .ctx_nonce = ctx_nonce,
      .ctx_seq = &ctx_seq,
      .ctx_exporter = ctx_exporter
    };
  u32 res = Hacl_HPKE_Curve51_CP128_SHA512_setupBaseS(o_enc, o_ctx, skE, pkR, infolen, info);
  if (res == (u32)0U)
  {
    u8 nonce[12U] = { 0U };
    u64 s = o_ctx.ctx_seq[0U];
    u8 enc[12U] = { 0U };
    store64_be(enc + (u32)4U, s);
    {
      u32 i;
      for (i = (u32)0U; i < (u32)12U; i++)
      {
        u8 xi = enc[i];
        u8 yi = o_ctx.ctx_nonce[i];
        nonce[i] = xi ^ yi;
      }
    }
    Hacl_Chacha20Poly1305_128_aead_encrypt(o_ctx.ctx_key,
      nonce,
      aadlen,
      aad,
      plainlen,
      plain,
      o_ct,
      o_ct + plainlen);
    {
      u64 s1 = o_ctx.ctx_seq[0U];
      u32 res1;
      if (s1 == (u64)18446744073709551615U)
        res1 = (u32)1U;
      else
      {
        u64 s_ = s1 + (u64)1U;
        o_ctx.ctx_seq[0U] = s_;
        res1 = (u32)0U;
      }
      {
        u32 res10 = res1;
        return res10;
      }
    }
  }
  return (u32)1U;
}

u32
Hacl_HPKE_Curve51_CP128_SHA512_openBase(
  u8 *pkE,
  u8 *skR,
  u32 infolen,
  u8 *info,
  u32 aadlen,
  u8 *aad,
  u32 ctlen,
  u8 *ct,
  u8 *o_pt
)
{
  u8 ctx_key[32U] = { 0U };
  u8 ctx_nonce[12U] = { 0U };
  u64 ctx_seq = (u64)0U;
  u8 ctx_exporter[64U] = { 0U };
  Hacl_Impl_HPKE_context_s
  o_ctx =
    {
      .ctx_key = ctx_key,
      .ctx_nonce = ctx_nonce,
      .ctx_seq = &ctx_seq,
      .ctx_exporter = ctx_exporter
    };
  u32 res = Hacl_HPKE_Curve51_CP128_SHA512_setupBaseR(o_ctx, pkE, skR, infolen, info);
  if (res == (u32)0U)
  {
    u8 nonce[12U] = { 0U };
    u64 s = o_ctx.ctx_seq[0U];
    u8 enc[12U] = { 0U };
    store64_be(enc + (u32)4U, s);
    {
      u32 i;
      for (i = (u32)0U; i < (u32)12U; i++)
      {
        u8 xi = enc[i];
        u8 yi = o_ctx.ctx_nonce[i];
        nonce[i] = xi ^ yi;
      }
    }
    {
      u32
      res1 =
        Hacl_Chacha20Poly1305_128_aead_decrypt(o_ctx.ctx_key,
          nonce,
          aadlen,
          aad,
          ctlen - (u32)16U,
          o_pt,
          ct,
          ct + ctlen - (u32)16U);
      if (res1 == (u32)0U)
      {
        u64 s1 = o_ctx.ctx_seq[0U];
        if (s1 == (u64)18446744073709551615U)
          return (u32)1U;
        {
          u64 s_ = s1 + (u64)1U;
          o_ctx.ctx_seq[0U] = s_;
          return (u32)0U;
        }
      }
      return (u32)1U;
    }
  }
  return (u32)1U;
}

