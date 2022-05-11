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


#include "Hacl_HPKE_P256_CP128_SHA256.h"

#include "internal/Hacl_Spec.h"
#include "internal/Hacl_P256.h"

uint32_t
Hacl_HPKE_P256_CP128_SHA256_setupBaseS(
  uint8_t *o_pkE,
  Hacl_Impl_HPKE_context_s o_ctx,
  uint8_t *skE,
  uint8_t *pkR,
  uint32_t infolen,
  uint8_t *info
)
{
  uint8_t o_shared[32U] = { 0U };
  uint8_t *o_pkE1 = o_pkE + (uint32_t)1U;
  uint64_t tempBuffer[100U] = { 0U };
  uint64_t resultBuffer[12U] = { 0U };
  uint64_t *resultBufferX = resultBuffer;
  uint64_t *resultBufferY = resultBuffer + (uint32_t)4U;
  uint8_t *resultX0 = o_pkE1;
  uint8_t *resultY0 = o_pkE1 + (uint32_t)32U;
  uint64_t flag;
  bool res0;
  uint32_t res1;
  uint32_t res;
  uint32_t ite0;
  Hacl_Impl_P256_Core_secretToPublic(resultBuffer, skE, tempBuffer);
  flag = Hacl_Impl_P256_Core_isPointAtInfinityPrivate(resultBuffer);
  Hacl_Impl_P256_LowLevel_changeEndian(resultBufferX);
  Hacl_Impl_P256_LowLevel_changeEndian(resultBufferY);
  Hacl_Impl_P256_LowLevel_toUint8(resultBufferX, resultX0);
  Hacl_Impl_P256_LowLevel_toUint8(resultBufferY, resultY0);
  res0 = flag == (uint64_t)0U;
  if (res0)
  {
    res1 = (uint32_t)0U;
  }
  else
  {
    res1 = (uint32_t)1U;
  }
  if (res1 == (uint32_t)0U)
  {
    o_pkE[0U] = (uint8_t)4U;
    {
      uint8_t o_dh[64U] = { 0U };
      uint8_t tmp0[64U] = { 0U };
      uint64_t resultBufferFelem[12U] = { 0U };
      uint64_t *resultBufferFelemX = resultBufferFelem;
      uint64_t *resultBufferFelemY = resultBufferFelem + (uint32_t)4U;
      uint8_t *resultX = tmp0;
      uint8_t *resultY = tmp0 + (uint32_t)32U;
      uint64_t publicKeyAsFelem[8U] = { 0U };
      uint64_t *publicKeyFelemX = publicKeyAsFelem;
      uint64_t *publicKeyFelemY = publicKeyAsFelem + (uint32_t)4U;
      uint8_t *pubKeyX = pkR;
      uint8_t *pubKeyY = pkR + (uint32_t)32U;
      Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
      Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
      {
        uint64_t flag0 = Hacl_Impl_P256_DH__ecp256dh_r(resultBufferFelem, publicKeyAsFelem, skE);
        Hacl_Impl_P256_LowLevel_changeEndian(resultBufferFelemX);
        Hacl_Impl_P256_LowLevel_changeEndian(resultBufferFelemY);
        Hacl_Impl_P256_LowLevel_toUint8(resultBufferFelemX, resultX);
        Hacl_Impl_P256_LowLevel_toUint8(resultBufferFelemY, resultY);
        {
          bool res3 = flag0 == (uint64_t)0U;
          memcpy(o_dh, tmp0, (uint32_t)64U * sizeof (uint8_t));
          {
            uint32_t res2;
            if (res3)
            {
              res2 = (uint32_t)0U;
            }
            else
            {
              res2 = (uint32_t)1U;
            }
            if (res2 == (uint32_t)0U)
            {
              uint8_t o_kemcontext[130U] = { 0U };
              uint8_t *uu____0 = o_kemcontext;
              Spec_Agile_HPKE_ciphersuite lit0;
              lit0.fst = Spec_Agile_DH_DH_P256;
              lit0.snd = Spec_Hash_Definitions_SHA2_256;
              lit0.thd.tag = Spec_Agile_HPKE_Seal;
              lit0.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
              lit0.f3 = Spec_Hash_Definitions_SHA2_256;
              {
                uint32_t sw0;
                switch (Spec_Agile_HPKE_kem_dh_of_cs(lit0))
                {
                  case Spec_Agile_DH_DH_Curve25519:
                    {
                      sw0 = (uint32_t)32U;
                      break;
                    }
                  case Spec_Agile_DH_DH_P256:
                    {
                      sw0 = (uint32_t)65U;
                      break;
                    }
                  default:
                    {
                      KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                      KRML_HOST_EXIT(253U);
                    }
                }
                memcpy(uu____0, o_pkE, sw0 * sizeof (uint8_t));
                {
                  Spec_Agile_HPKE_ciphersuite lit1;
                  lit1.fst = Spec_Agile_DH_DH_P256;
                  lit1.snd = Spec_Hash_Definitions_SHA2_256;
                  lit1.thd.tag = Spec_Agile_HPKE_Seal;
                  lit1.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
                  lit1.f3 = Spec_Hash_Definitions_SHA2_256;
                  {
                    uint32_t sw1;
                    switch (Spec_Agile_HPKE_kem_dh_of_cs(lit1))
                    {
                      case Spec_Agile_DH_DH_Curve25519:
                        {
                          sw1 = (uint32_t)32U;
                          break;
                        }
                      case Spec_Agile_DH_DH_P256:
                        {
                          sw1 = (uint32_t)65U;
                          break;
                        }
                      default:
                        {
                          KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                            __FILE__,
                            __LINE__);
                          KRML_HOST_EXIT(253U);
                        }
                    }
                    {
                      uint8_t *o_pkRm = o_kemcontext + sw1;
                      uint8_t *o_pkR = o_pkRm + (uint32_t)1U;
                      Spec_Agile_HPKE_ciphersuite lit2;
                      lit2.fst = Spec_Agile_DH_DH_P256;
                      lit2.snd = Spec_Hash_Definitions_SHA2_256;
                      lit2.thd.tag = Spec_Agile_HPKE_Seal;
                      lit2.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
                      lit2.f3 = Spec_Hash_Definitions_SHA2_256;
                      {
                        uint32_t sw2;
                        switch (Spec_Agile_HPKE_kem_dh_of_cs(lit2))
                        {
                          case Spec_Agile_DH_DH_Curve25519:
                            {
                              sw2 = (uint32_t)32U;
                              break;
                            }
                          case Spec_Agile_DH_DH_P256:
                            {
                              sw2 = (uint32_t)64U;
                              break;
                            }
                          default:
                            {
                              KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                __FILE__,
                                __LINE__);
                              KRML_HOST_EXIT(253U);
                            }
                        }
                        memcpy(o_pkR, pkR, sw2 * sizeof (uint8_t));
                        o_pkRm[0U] = (uint8_t)4U;
                        {
                          uint8_t *o_dhm = o_dh;
                          uint8_t o_eae_prk[32U] = { 0U };
                          uint8_t suite_id_kem[5U] = { 0U };
                          uint8_t *uu____1 = suite_id_kem;
                          uu____1[0U] = (uint8_t)0x4bU;
                          uu____1[1U] = (uint8_t)0x45U;
                          uu____1[2U] = (uint8_t)0x4dU;
                          {
                            uint8_t *uu____2 = suite_id_kem + (uint32_t)3U;
                            uu____2[0U] = (uint8_t)0U;
                            uu____2[1U] = (uint8_t)16U;
                            {
                              uint8_t *empty = suite_id_kem;
                              uint8_t
                              label_eae_prk[7U] =
                                {
                                  (uint8_t)0x65U, (uint8_t)0x61U, (uint8_t)0x65U, (uint8_t)0x5fU,
                                  (uint8_t)0x70U, (uint8_t)0x72U, (uint8_t)0x6bU
                                };
                              uint32_t
                              len = (uint32_t)7U + (uint32_t)5U + (uint32_t)7U + (uint32_t)32U;
                              KRML_CHECK_SIZE(sizeof (uint8_t), len);
                              {
                                uint8_t tmp1[len];
                                memset(tmp1, 0U, len * sizeof (uint8_t));
                                {
                                  uint8_t *uu____3 = tmp1;
                                  uu____3[0U] = (uint8_t)0x48U;
                                  uu____3[1U] = (uint8_t)0x50U;
                                  uu____3[2U] = (uint8_t)0x4bU;
                                  uu____3[3U] = (uint8_t)0x45U;
                                  uu____3[4U] = (uint8_t)0x2dU;
                                  uu____3[5U] = (uint8_t)0x76U;
                                  uu____3[6U] = (uint8_t)0x31U;
                                  memcpy(tmp1 + (uint32_t)7U,
                                    suite_id_kem,
                                    (uint32_t)5U * sizeof (uint8_t));
                                  memcpy(tmp1 + (uint32_t)7U + (uint32_t)5U,
                                    label_eae_prk,
                                    (uint32_t)7U * sizeof (uint8_t));
                                  memcpy(tmp1 + (uint32_t)7U + (uint32_t)5U + (uint32_t)7U,
                                    o_dhm,
                                    (uint32_t)32U * sizeof (uint8_t));
                                  Hacl_HKDF_extract_sha2_256(o_eae_prk,
                                    empty,
                                    (uint32_t)0U,
                                    tmp1,
                                    len);
                                  {
                                    uint8_t
                                    label_shared_secret[13U] =
                                      {
                                        (uint8_t)0x73U, (uint8_t)0x68U, (uint8_t)0x61U,
                                        (uint8_t)0x72U, (uint8_t)0x65U, (uint8_t)0x64U,
                                        (uint8_t)0x5fU, (uint8_t)0x73U, (uint8_t)0x65U,
                                        (uint8_t)0x63U, (uint8_t)0x72U, (uint8_t)0x65U,
                                        (uint8_t)0x74U
                                      };
                                    Spec_Agile_HPKE_ciphersuite lit3;
                                    lit3.fst = Spec_Agile_DH_DH_P256;
                                    lit3.snd = Spec_Hash_Definitions_SHA2_256;
                                    lit3.thd.tag = Spec_Agile_HPKE_Seal;
                                    lit3.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
                                    lit3.f3 = Spec_Hash_Definitions_SHA2_256;
                                    {
                                      uint32_t sw3;
                                      switch (Spec_Agile_HPKE_kem_dh_of_cs(lit3))
                                      {
                                        case Spec_Agile_DH_DH_Curve25519:
                                          {
                                            sw3 = (uint32_t)64U;
                                            break;
                                          }
                                        case Spec_Agile_DH_DH_P256:
                                          {
                                            sw3 = (uint32_t)130U;
                                            break;
                                          }
                                        default:
                                          {
                                            KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                              __FILE__,
                                              __LINE__);
                                            KRML_HOST_EXIT(253U);
                                          }
                                      }
                                      {
                                        uint32_t
                                        len0 = (uint32_t)9U + (uint32_t)5U + (uint32_t)13U + sw3;
                                        KRML_CHECK_SIZE(sizeof (uint8_t), len0);
                                        {
                                          uint8_t tmp[len0];
                                          memset(tmp, 0U, len0 * sizeof (uint8_t));
                                          {
                                            uint8_t *uu____4 = tmp;
                                            uint8_t *uu____5 = uu____4;
                                            Spec_Agile_HPKE_ciphersuite lit4;
                                            lit4.fst = Spec_Agile_DH_DH_P256;
                                            lit4.snd = Spec_Hash_Definitions_SHA2_256;
                                            lit4.thd.tag = Spec_Agile_HPKE_Seal;
                                            lit4.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
                                            lit4.f3 = Spec_Hash_Definitions_SHA2_256;
                                            {
                                              uint32_t sw4;
                                              switch (Spec_Agile_HPKE_kem_hash_of_cs(lit4))
                                              {
                                                case Spec_Hash_Definitions_SHA2_256:
                                                  {
                                                    sw4 = (uint32_t)32U;
                                                    break;
                                                  }
                                                default:
                                                  {
                                                    KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                      __FILE__,
                                                      __LINE__);
                                                    KRML_HOST_EXIT(253U);
                                                  }
                                              }
                                              store32_be(uu____5, sw4);
                                              memcpy(uu____4,
                                                uu____4 + (uint32_t)2U,
                                                (uint32_t)2U * sizeof (uint8_t));
                                              {
                                                uint8_t *uu____6 = tmp + (uint32_t)2U;
                                                uu____6[0U] = (uint8_t)0x48U;
                                                uu____6[1U] = (uint8_t)0x50U;
                                                uu____6[2U] = (uint8_t)0x4bU;
                                                uu____6[3U] = (uint8_t)0x45U;
                                                uu____6[4U] = (uint8_t)0x2dU;
                                                uu____6[5U] = (uint8_t)0x76U;
                                                uu____6[6U] = (uint8_t)0x31U;
                                                memcpy(tmp + (uint32_t)9U,
                                                  suite_id_kem,
                                                  (uint32_t)5U * sizeof (uint8_t));
                                                memcpy(tmp + (uint32_t)9U + (uint32_t)5U,
                                                  label_shared_secret,
                                                  (uint32_t)13U * sizeof (uint8_t));
                                                {
                                                  uint8_t
                                                  *uu____7 =
                                                    tmp
                                                    + (uint32_t)9U + (uint32_t)5U + (uint32_t)13U;
                                                  Spec_Agile_HPKE_ciphersuite lit5;
                                                  lit5.fst = Spec_Agile_DH_DH_P256;
                                                  lit5.snd = Spec_Hash_Definitions_SHA2_256;
                                                  lit5.thd.tag = Spec_Agile_HPKE_Seal;
                                                  lit5.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                  lit5.f3 = Spec_Hash_Definitions_SHA2_256;
                                                  {
                                                    uint32_t sw5;
                                                    switch (Spec_Agile_HPKE_kem_dh_of_cs(lit5))
                                                    {
                                                      case Spec_Agile_DH_DH_Curve25519:
                                                        {
                                                          sw5 = (uint32_t)64U;
                                                          break;
                                                        }
                                                      case Spec_Agile_DH_DH_P256:
                                                        {
                                                          sw5 = (uint32_t)130U;
                                                          break;
                                                        }
                                                      default:
                                                        {
                                                          KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                            __FILE__,
                                                            __LINE__);
                                                          KRML_HOST_EXIT(253U);
                                                        }
                                                    }
                                                    memcpy(uu____7,
                                                      o_kemcontext,
                                                      sw5 * sizeof (uint8_t));
                                                    {
                                                      Spec_Agile_HPKE_ciphersuite lit6;
                                                      lit6.fst = Spec_Agile_DH_DH_P256;
                                                      lit6.snd = Spec_Hash_Definitions_SHA2_256;
                                                      lit6.thd.tag = Spec_Agile_HPKE_Seal;
                                                      lit6.thd.alg =
                                                        Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                      lit6.f3 = Spec_Hash_Definitions_SHA2_256;
                                                      {
                                                        uint32_t sw6;
                                                        switch
                                                        (Spec_Agile_HPKE_kem_hash_of_cs(lit6))
                                                        {
                                                          case Spec_Hash_Definitions_SHA2_256:
                                                            {
                                                              sw6 = (uint32_t)32U;
                                                              break;
                                                            }
                                                          default:
                                                            {
                                                              KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                __FILE__,
                                                                __LINE__);
                                                              KRML_HOST_EXIT(253U);
                                                            }
                                                        }
                                                        {
                                                          Spec_Agile_HPKE_ciphersuite lit;
                                                          lit.fst = Spec_Agile_DH_DH_P256;
                                                          lit.snd = Spec_Hash_Definitions_SHA2_256;
                                                          lit.thd.tag = Spec_Agile_HPKE_Seal;
                                                          lit.thd.alg =
                                                            Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                          lit.f3 = Spec_Hash_Definitions_SHA2_256;
                                                          {
                                                            uint32_t sw;
                                                            switch
                                                            (Spec_Agile_HPKE_kem_hash_of_cs(lit))
                                                            {
                                                              case Spec_Hash_Definitions_SHA2_256:
                                                                {
                                                                  sw = (uint32_t)32U;
                                                                  break;
                                                                }
                                                              default:
                                                                {
                                                                  KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
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
                                                            res = (uint32_t)0U;
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
            {
              res = (uint32_t)1U;
            }
          }
        }
      }
    }
  }
  else
  {
    res = (uint32_t)1U;
  }
  if (res == (uint32_t)0U)
  {
    uint8_t o_context[65U] = { 0U };
    uint8_t o_secret[32U] = { 0U };
    uint8_t suite_id[10U] = { 0U };
    uint8_t *uu____8 = suite_id;
    uu____8[0U] = (uint8_t)0x48U;
    uu____8[1U] = (uint8_t)0x50U;
    uu____8[2U] = (uint8_t)0x4bU;
    uu____8[3U] = (uint8_t)0x45U;
    {
      uint8_t *uu____9 = suite_id + (uint32_t)4U;
      uu____9[0U] = (uint8_t)0U;
      uu____9[1U] = (uint8_t)16U;
      {
        uint8_t *uu____10 = suite_id + (uint32_t)6U;
        uu____10[0U] = (uint8_t)0U;
        uu____10[1U] = (uint8_t)1U;
        {
          uint8_t *uu____11 = suite_id + (uint32_t)8U;
          uu____11[0U] = (uint8_t)0U;
          uu____11[1U] = (uint8_t)3U;
          {
            uint8_t
            label_psk_id_hash[11U] =
              {
                (uint8_t)0x70U, (uint8_t)0x73U, (uint8_t)0x6bU, (uint8_t)0x5fU, (uint8_t)0x69U,
                (uint8_t)0x64U, (uint8_t)0x5fU, (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x73U,
                (uint8_t)0x68U
              };
            uint8_t o_psk_id_hash[32U] = { 0U };
            uint8_t *empty = suite_id;
            uint32_t len0 = (uint32_t)7U + (uint32_t)10U + (uint32_t)11U + (uint32_t)0U;
            KRML_CHECK_SIZE(sizeof (uint8_t), len0);
            {
              uint8_t tmp0[len0];
              memset(tmp0, 0U, len0 * sizeof (uint8_t));
              {
                uint8_t *uu____12 = tmp0;
                uu____12[0U] = (uint8_t)0x48U;
                uu____12[1U] = (uint8_t)0x50U;
                uu____12[2U] = (uint8_t)0x4bU;
                uu____12[3U] = (uint8_t)0x45U;
                uu____12[4U] = (uint8_t)0x2dU;
                uu____12[5U] = (uint8_t)0x76U;
                uu____12[6U] = (uint8_t)0x31U;
                memcpy(tmp0 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
                memcpy(tmp0 + (uint32_t)7U + (uint32_t)10U,
                  label_psk_id_hash,
                  (uint32_t)11U * sizeof (uint8_t));
                memcpy(tmp0 + (uint32_t)7U + (uint32_t)10U + (uint32_t)11U,
                  empty,
                  (uint32_t)0U * sizeof (uint8_t));
                Hacl_HKDF_extract_sha2_256(o_psk_id_hash, empty, (uint32_t)0U, tmp0, len0);
                {
                  uint8_t
                  label_info_hash[9U] =
                    {
                      (uint8_t)0x69U, (uint8_t)0x6eU, (uint8_t)0x66U, (uint8_t)0x6fU, (uint8_t)0x5fU,
                      (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x73U, (uint8_t)0x68U
                    };
                  uint8_t o_info_hash[32U] = { 0U };
                  uint32_t len1 = (uint32_t)7U + (uint32_t)10U + (uint32_t)9U + infolen;
                  KRML_CHECK_SIZE(sizeof (uint8_t), len1);
                  {
                    uint8_t tmp1[len1];
                    memset(tmp1, 0U, len1 * sizeof (uint8_t));
                    {
                      uint8_t *uu____13 = tmp1;
                      uu____13[0U] = (uint8_t)0x48U;
                      uu____13[1U] = (uint8_t)0x50U;
                      uu____13[2U] = (uint8_t)0x4bU;
                      uu____13[3U] = (uint8_t)0x45U;
                      uu____13[4U] = (uint8_t)0x2dU;
                      uu____13[5U] = (uint8_t)0x76U;
                      uu____13[6U] = (uint8_t)0x31U;
                      memcpy(tmp1 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
                      memcpy(tmp1 + (uint32_t)7U + (uint32_t)10U,
                        label_info_hash,
                        (uint32_t)9U * sizeof (uint8_t));
                      memcpy(tmp1 + (uint32_t)7U + (uint32_t)10U + (uint32_t)9U,
                        info,
                        infolen * sizeof (uint8_t));
                      Hacl_HKDF_extract_sha2_256(o_info_hash, empty, (uint32_t)0U, tmp1, len1);
                      o_context[0U] = (uint8_t)0U;
                      {
                        uint8_t *uu____14 = o_context + (uint32_t)1U;
                        Spec_Agile_HPKE_ciphersuite lit0;
                        lit0.fst = Spec_Agile_DH_DH_P256;
                        lit0.snd = Spec_Hash_Definitions_SHA2_256;
                        lit0.thd.tag = Spec_Agile_HPKE_Seal;
                        lit0.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
                        lit0.f3 = Spec_Hash_Definitions_SHA2_256;
                        {
                          uint32_t sw0;
                          switch (Spec_Agile_HPKE_hash_of_cs(lit0))
                          {
                            case Spec_Hash_Definitions_SHA2_256:
                              {
                                sw0 = (uint32_t)32U;
                                break;
                              }
                            case Spec_Hash_Definitions_SHA2_384:
                              {
                                sw0 = (uint32_t)48U;
                                break;
                              }
                            case Spec_Hash_Definitions_SHA2_512:
                              {
                                sw0 = (uint32_t)64U;
                                break;
                              }
                            default:
                              {
                                KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                  __FILE__,
                                  __LINE__);
                                KRML_HOST_EXIT(253U);
                              }
                          }
                          memcpy(uu____14, o_psk_id_hash, sw0 * sizeof (uint8_t));
                          {
                            Spec_Agile_HPKE_ciphersuite lit1;
                            lit1.fst = Spec_Agile_DH_DH_P256;
                            lit1.snd = Spec_Hash_Definitions_SHA2_256;
                            lit1.thd.tag = Spec_Agile_HPKE_Seal;
                            lit1.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
                            lit1.f3 = Spec_Hash_Definitions_SHA2_256;
                            {
                              uint32_t sw1;
                              switch (Spec_Agile_HPKE_hash_of_cs(lit1))
                              {
                                case Spec_Hash_Definitions_SHA2_256:
                                  {
                                    sw1 = (uint32_t)33U;
                                    break;
                                  }
                                case Spec_Hash_Definitions_SHA2_384:
                                  {
                                    sw1 = (uint32_t)49U;
                                    break;
                                  }
                                case Spec_Hash_Definitions_SHA2_512:
                                  {
                                    sw1 = (uint32_t)65U;
                                    break;
                                  }
                                default:
                                  {
                                    KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                      __FILE__,
                                      __LINE__);
                                    KRML_HOST_EXIT(253U);
                                  }
                              }
                              {
                                uint8_t *uu____15 = o_context + sw1;
                                Spec_Agile_HPKE_ciphersuite lit2;
                                lit2.fst = Spec_Agile_DH_DH_P256;
                                lit2.snd = Spec_Hash_Definitions_SHA2_256;
                                lit2.thd.tag = Spec_Agile_HPKE_Seal;
                                lit2.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
                                lit2.f3 = Spec_Hash_Definitions_SHA2_256;
                                {
                                  uint32_t sw2;
                                  switch (Spec_Agile_HPKE_hash_of_cs(lit2))
                                  {
                                    case Spec_Hash_Definitions_SHA2_256:
                                      {
                                        sw2 = (uint32_t)32U;
                                        break;
                                      }
                                    case Spec_Hash_Definitions_SHA2_384:
                                      {
                                        sw2 = (uint32_t)48U;
                                        break;
                                      }
                                    case Spec_Hash_Definitions_SHA2_512:
                                      {
                                        sw2 = (uint32_t)64U;
                                        break;
                                      }
                                    default:
                                      {
                                        KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                          __FILE__,
                                          __LINE__);
                                        KRML_HOST_EXIT(253U);
                                      }
                                  }
                                  memcpy(uu____15, o_info_hash, sw2 * sizeof (uint8_t));
                                  {
                                    uint8_t
                                    label_secret[6U] =
                                      {
                                        (uint8_t)0x73U, (uint8_t)0x65U, (uint8_t)0x63U,
                                        (uint8_t)0x72U, (uint8_t)0x65U, (uint8_t)0x74U
                                      };
                                    uint32_t
                                    len = (uint32_t)7U + (uint32_t)10U + (uint32_t)6U + (uint32_t)0U;
                                    KRML_CHECK_SIZE(sizeof (uint8_t), len);
                                    {
                                      uint8_t tmp2[len];
                                      memset(tmp2, 0U, len * sizeof (uint8_t));
                                      {
                                        uint8_t *uu____16 = tmp2;
                                        uu____16[0U] = (uint8_t)0x48U;
                                        uu____16[1U] = (uint8_t)0x50U;
                                        uu____16[2U] = (uint8_t)0x4bU;
                                        uu____16[3U] = (uint8_t)0x45U;
                                        uu____16[4U] = (uint8_t)0x2dU;
                                        uu____16[5U] = (uint8_t)0x76U;
                                        uu____16[6U] = (uint8_t)0x31U;
                                        memcpy(tmp2 + (uint32_t)7U,
                                          suite_id,
                                          (uint32_t)10U * sizeof (uint8_t));
                                        memcpy(tmp2 + (uint32_t)7U + (uint32_t)10U,
                                          label_secret,
                                          (uint32_t)6U * sizeof (uint8_t));
                                        memcpy(tmp2 + (uint32_t)7U + (uint32_t)10U + (uint32_t)6U,
                                          empty,
                                          (uint32_t)0U * sizeof (uint8_t));
                                        {
                                          Spec_Agile_HPKE_ciphersuite lit3;
                                          lit3.fst = Spec_Agile_DH_DH_P256;
                                          lit3.snd = Spec_Hash_Definitions_SHA2_256;
                                          lit3.thd.tag = Spec_Agile_HPKE_Seal;
                                          lit3.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
                                          lit3.f3 = Spec_Hash_Definitions_SHA2_256;
                                          {
                                            uint32_t sw3;
                                            switch (Spec_Agile_HPKE_kem_hash_of_cs(lit3))
                                            {
                                              case Spec_Hash_Definitions_SHA2_256:
                                                {
                                                  sw3 = (uint32_t)32U;
                                                  break;
                                                }
                                              default:
                                                {
                                                  KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                    __FILE__,
                                                    __LINE__);
                                                  KRML_HOST_EXIT(253U);
                                                }
                                            }
                                            Hacl_HKDF_extract_sha2_256(o_secret,
                                              o_shared,
                                              sw3,
                                              tmp2,
                                              len);
                                            {
                                              uint8_t
                                              label_exp[3U] =
                                                { (uint8_t)0x65U, (uint8_t)0x78U, (uint8_t)0x70U };
                                              Spec_Agile_HPKE_ciphersuite lit4;
                                              lit4.fst = Spec_Agile_DH_DH_P256;
                                              lit4.snd = Spec_Hash_Definitions_SHA2_256;
                                              lit4.thd.tag = Spec_Agile_HPKE_Seal;
                                              lit4.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
                                              lit4.f3 = Spec_Hash_Definitions_SHA2_256;
                                              {
                                                uint32_t sw4;
                                                switch (Spec_Agile_HPKE_hash_of_cs(lit4))
                                                {
                                                  case Spec_Hash_Definitions_SHA2_256:
                                                    {
                                                      sw4 = (uint32_t)65U;
                                                      break;
                                                    }
                                                  case Spec_Hash_Definitions_SHA2_384:
                                                    {
                                                      sw4 = (uint32_t)97U;
                                                      break;
                                                    }
                                                  case Spec_Hash_Definitions_SHA2_512:
                                                    {
                                                      sw4 = (uint32_t)129U;
                                                      break;
                                                    }
                                                  default:
                                                    {
                                                      KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                        __FILE__,
                                                        __LINE__);
                                                      KRML_HOST_EXIT(253U);
                                                    }
                                                }
                                                {
                                                  uint32_t
                                                  len2 =
                                                    (uint32_t)9U
                                                    + (uint32_t)10U
                                                    + (uint32_t)3U
                                                    + sw4;
                                                  KRML_CHECK_SIZE(sizeof (uint8_t), len2);
                                                  {
                                                    uint8_t tmp3[len2];
                                                    memset(tmp3, 0U, len2 * sizeof (uint8_t));
                                                    {
                                                      uint8_t *uu____17 = tmp3;
                                                      uint8_t *uu____18 = uu____17;
                                                      Spec_Agile_HPKE_ciphersuite lit5;
                                                      lit5.fst = Spec_Agile_DH_DH_P256;
                                                      lit5.snd = Spec_Hash_Definitions_SHA2_256;
                                                      lit5.thd.tag = Spec_Agile_HPKE_Seal;
                                                      lit5.thd.alg =
                                                        Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                      lit5.f3 = Spec_Hash_Definitions_SHA2_256;
                                                      {
                                                        uint32_t sw5;
                                                        switch (Spec_Agile_HPKE_hash_of_cs(lit5))
                                                        {
                                                          case Spec_Hash_Definitions_SHA2_256:
                                                            {
                                                              sw5 = (uint32_t)32U;
                                                              break;
                                                            }
                                                          case Spec_Hash_Definitions_SHA2_384:
                                                            {
                                                              sw5 = (uint32_t)48U;
                                                              break;
                                                            }
                                                          case Spec_Hash_Definitions_SHA2_512:
                                                            {
                                                              sw5 = (uint32_t)64U;
                                                              break;
                                                            }
                                                          default:
                                                            {
                                                              KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                __FILE__,
                                                                __LINE__);
                                                              KRML_HOST_EXIT(253U);
                                                            }
                                                        }
                                                        store32_be(uu____18, sw5);
                                                        memcpy(uu____17,
                                                          uu____17 + (uint32_t)2U,
                                                          (uint32_t)2U * sizeof (uint8_t));
                                                        {
                                                          uint8_t *uu____19 = tmp3 + (uint32_t)2U;
                                                          uu____19[0U] = (uint8_t)0x48U;
                                                          uu____19[1U] = (uint8_t)0x50U;
                                                          uu____19[2U] = (uint8_t)0x4bU;
                                                          uu____19[3U] = (uint8_t)0x45U;
                                                          uu____19[4U] = (uint8_t)0x2dU;
                                                          uu____19[5U] = (uint8_t)0x76U;
                                                          uu____19[6U] = (uint8_t)0x31U;
                                                          memcpy(tmp3 + (uint32_t)9U,
                                                            suite_id,
                                                            (uint32_t)10U * sizeof (uint8_t));
                                                          memcpy(tmp3 + (uint32_t)9U + (uint32_t)10U,
                                                            label_exp,
                                                            (uint32_t)3U * sizeof (uint8_t));
                                                          {
                                                            uint8_t
                                                            *uu____20 =
                                                              tmp3
                                                              +
                                                                (uint32_t)9U
                                                                + (uint32_t)10U
                                                                + (uint32_t)3U;
                                                            Spec_Agile_HPKE_ciphersuite lit6;
                                                            lit6.fst = Spec_Agile_DH_DH_P256;
                                                            lit6.snd =
                                                              Spec_Hash_Definitions_SHA2_256;
                                                            lit6.thd.tag = Spec_Agile_HPKE_Seal;
                                                            lit6.thd.alg =
                                                              Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                            lit6.f3 = Spec_Hash_Definitions_SHA2_256;
                                                            {
                                                              uint32_t sw6;
                                                              switch
                                                              (Spec_Agile_HPKE_hash_of_cs(lit6))
                                                              {
                                                                case Spec_Hash_Definitions_SHA2_256:
                                                                  {
                                                                    sw6 = (uint32_t)65U;
                                                                    break;
                                                                  }
                                                                case Spec_Hash_Definitions_SHA2_384:
                                                                  {
                                                                    sw6 = (uint32_t)97U;
                                                                    break;
                                                                  }
                                                                case Spec_Hash_Definitions_SHA2_512:
                                                                  {
                                                                    sw6 = (uint32_t)129U;
                                                                    break;
                                                                  }
                                                                default:
                                                                  {
                                                                    KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                      __FILE__,
                                                                      __LINE__);
                                                                    KRML_HOST_EXIT(253U);
                                                                  }
                                                              }
                                                              memcpy(uu____20,
                                                                o_context,
                                                                sw6 * sizeof (uint8_t));
                                                              {
                                                                Spec_Agile_HPKE_ciphersuite lit7;
                                                                lit7.fst = Spec_Agile_DH_DH_P256;
                                                                lit7.snd =
                                                                  Spec_Hash_Definitions_SHA2_256;
                                                                lit7.thd.tag = Spec_Agile_HPKE_Seal;
                                                                lit7.thd.alg =
                                                                  Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                lit7.f3 =
                                                                  Spec_Hash_Definitions_SHA2_256;
                                                                {
                                                                  uint32_t sw7;
                                                                  switch
                                                                  (Spec_Agile_HPKE_hash_of_cs(lit7))
                                                                  {
                                                                    case
                                                                    Spec_Hash_Definitions_SHA2_256:
                                                                      {
                                                                        sw7 = (uint32_t)32U;
                                                                        break;
                                                                      }
                                                                    case
                                                                    Spec_Hash_Definitions_SHA2_384:
                                                                      {
                                                                        sw7 = (uint32_t)48U;
                                                                        break;
                                                                      }
                                                                    case
                                                                    Spec_Hash_Definitions_SHA2_512:
                                                                      {
                                                                        sw7 = (uint32_t)64U;
                                                                        break;
                                                                      }
                                                                    default:
                                                                      {
                                                                        KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                          __FILE__,
                                                                          __LINE__);
                                                                        KRML_HOST_EXIT(253U);
                                                                      }
                                                                  }
                                                                  {
                                                                    Spec_Agile_HPKE_ciphersuite
                                                                    lit8;
                                                                    lit8.fst = Spec_Agile_DH_DH_P256;
                                                                    lit8.snd =
                                                                      Spec_Hash_Definitions_SHA2_256;
                                                                    lit8.thd.tag =
                                                                      Spec_Agile_HPKE_Seal;
                                                                    lit8.thd.alg =
                                                                      Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                    lit8.f3 =
                                                                      Spec_Hash_Definitions_SHA2_256;
                                                                    {
                                                                      uint32_t sw8;
                                                                      switch
                                                                      (
                                                                        Spec_Agile_HPKE_hash_of_cs(lit8)
                                                                      )
                                                                      {
                                                                        case
                                                                        Spec_Hash_Definitions_SHA2_256:
                                                                          {
                                                                            sw8 = (uint32_t)32U;
                                                                            break;
                                                                          }
                                                                        case
                                                                        Spec_Hash_Definitions_SHA2_384:
                                                                          {
                                                                            sw8 = (uint32_t)48U;
                                                                            break;
                                                                          }
                                                                        case
                                                                        Spec_Hash_Definitions_SHA2_512:
                                                                          {
                                                                            sw8 = (uint32_t)64U;
                                                                            break;
                                                                          }
                                                                        default:
                                                                          {
                                                                            KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                              __FILE__,
                                                                              __LINE__);
                                                                            KRML_HOST_EXIT(253U);
                                                                          }
                                                                      }
                                                                      Hacl_HKDF_expand_sha2_256(o_ctx.ctx_exporter,
                                                                        o_secret,
                                                                        sw7,
                                                                        tmp3,
                                                                        len2,
                                                                        sw8);
                                                                      {
                                                                        Spec_Agile_HPKE_ciphersuite
                                                                        lit9;
                                                                        lit9.fst =
                                                                          Spec_Agile_DH_DH_P256;
                                                                        lit9.snd =
                                                                          Spec_Hash_Definitions_SHA2_256;
                                                                        lit9.thd.tag =
                                                                          Spec_Agile_HPKE_Seal;
                                                                        lit9.thd.alg =
                                                                          Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                        lit9.f3 =
                                                                          Spec_Hash_Definitions_SHA2_256;
                                                                        {
                                                                          Spec_Agile_HPKE_aead
                                                                          scrut =
                                                                            Spec_Agile_HPKE_aead_of_cs(lit9);
                                                                          if
                                                                          (
                                                                            scrut.tag
                                                                            ==
                                                                              Spec_Agile_HPKE_ExportOnly
                                                                          )
                                                                          {
                                                                            o_ctx.ctx_seq[0U] =
                                                                              (uint64_t)0U;
                                                                          }
                                                                          else
                                                                          {
                                                                            uint8_t
                                                                            label_key[3U] =
                                                                              {
                                                                                (uint8_t)0x6bU,
                                                                                (uint8_t)0x65U,
                                                                                (uint8_t)0x79U
                                                                              };
                                                                            Spec_Agile_HPKE_ciphersuite
                                                                            lit10;
                                                                            lit10.fst =
                                                                              Spec_Agile_DH_DH_P256;
                                                                            lit10.snd =
                                                                              Spec_Hash_Definitions_SHA2_256;
                                                                            lit10.thd.tag =
                                                                              Spec_Agile_HPKE_Seal;
                                                                            lit10.thd.alg =
                                                                              Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                            lit10.f3 =
                                                                              Spec_Hash_Definitions_SHA2_256;
                                                                            {
                                                                              uint32_t sw9;
                                                                              switch
                                                                              (
                                                                                Spec_Agile_HPKE_hash_of_cs(lit10)
                                                                              )
                                                                              {
                                                                                case
                                                                                Spec_Hash_Definitions_SHA2_256:
                                                                                  {
                                                                                    sw9 =
                                                                                      (uint32_t)65U;
                                                                                    break;
                                                                                  }
                                                                                case
                                                                                Spec_Hash_Definitions_SHA2_384:
                                                                                  {
                                                                                    sw9 =
                                                                                      (uint32_t)97U;
                                                                                    break;
                                                                                  }
                                                                                case
                                                                                Spec_Hash_Definitions_SHA2_512:
                                                                                  {
                                                                                    sw9 =
                                                                                      (uint32_t)129U;
                                                                                    break;
                                                                                  }
                                                                                default:
                                                                                  {
                                                                                    KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                      __FILE__,
                                                                                      __LINE__);
                                                                                    KRML_HOST_EXIT(253U);
                                                                                  }
                                                                              }
                                                                              {
                                                                                uint32_t
                                                                                len3 =
                                                                                  (uint32_t)9U
                                                                                  + (uint32_t)10U
                                                                                  + (uint32_t)3U
                                                                                  + sw9;
                                                                                KRML_CHECK_SIZE(sizeof (
                                                                                    uint8_t
                                                                                  ),
                                                                                  len3);
                                                                                {
                                                                                  uint8_t
                                                                                  tmp4[len3];
                                                                                  memset(tmp4,
                                                                                    0U,
                                                                                    len3
                                                                                    *
                                                                                      sizeof (
                                                                                        uint8_t
                                                                                      ));
                                                                                  {
                                                                                    uint8_t
                                                                                    *uu____21 = tmp4;
                                                                                    uint8_t
                                                                                    *uu____22 =
                                                                                      uu____21;
                                                                                    Spec_Agile_HPKE_ciphersuite
                                                                                    lit11;
                                                                                    lit11.fst =
                                                                                      Spec_Agile_DH_DH_P256;
                                                                                    lit11.snd =
                                                                                      Spec_Hash_Definitions_SHA2_256;
                                                                                    lit11.thd.tag =
                                                                                      Spec_Agile_HPKE_Seal;
                                                                                    lit11.thd.alg =
                                                                                      Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                    lit11.f3 =
                                                                                      Spec_Hash_Definitions_SHA2_256;
                                                                                    {
                                                                                      Spec_Agile_HPKE_aead
                                                                                      scrut0 =
                                                                                        Spec_Agile_HPKE_aead_of_cs(lit11);
                                                                                      uint32_t ite1;
                                                                                      if
                                                                                      (
                                                                                        scrut0.tag
                                                                                        ==
                                                                                          Spec_Agile_HPKE_ExportOnly
                                                                                      )
                                                                                      {
                                                                                        ite1 =
                                                                                          (uint32_t)0U;
                                                                                      }
                                                                                      else if
                                                                                      (
                                                                                        scrut0.tag
                                                                                        ==
                                                                                          Spec_Agile_HPKE_Seal
                                                                                        &&
                                                                                          scrut0.alg
                                                                                          ==
                                                                                            Spec_Agile_AEAD_AES128_GCM
                                                                                      )
                                                                                      {
                                                                                        ite1 =
                                                                                          (uint32_t)16U;
                                                                                      }
                                                                                      else if
                                                                                      (
                                                                                        scrut0.tag
                                                                                        ==
                                                                                          Spec_Agile_HPKE_Seal
                                                                                        &&
                                                                                          scrut0.alg
                                                                                          ==
                                                                                            Spec_Agile_AEAD_AES256_GCM
                                                                                      )
                                                                                      {
                                                                                        ite1 =
                                                                                          (uint32_t)32U;
                                                                                      }
                                                                                      else if
                                                                                      (
                                                                                        scrut0.tag
                                                                                        ==
                                                                                          Spec_Agile_HPKE_Seal
                                                                                        &&
                                                                                          scrut0.alg
                                                                                          ==
                                                                                            Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                                      )
                                                                                      {
                                                                                        ite1 =
                                                                                          (uint32_t)32U;
                                                                                      }
                                                                                      else
                                                                                      {
                                                                                        ite1 =
                                                                                          KRML_EABORT(uint32_t,
                                                                                            "unreachable (pattern matches are exhaustive in F*)");
                                                                                      }
                                                                                      store32_be(uu____22,
                                                                                        ite1);
                                                                                      memcpy(uu____21,
                                                                                        uu____21
                                                                                        +
                                                                                          (uint32_t)2U,
                                                                                        (uint32_t)2U
                                                                                        *
                                                                                          sizeof (
                                                                                            uint8_t
                                                                                          ));
                                                                                      {
                                                                                        uint8_t
                                                                                        *uu____23 =
                                                                                          tmp4
                                                                                          +
                                                                                            (uint32_t)2U;
                                                                                        uu____23[0U]
                                                                                        =
                                                                                          (uint8_t)0x48U;
                                                                                        uu____23[1U]
                                                                                        =
                                                                                          (uint8_t)0x50U;
                                                                                        uu____23[2U]
                                                                                        =
                                                                                          (uint8_t)0x4bU;
                                                                                        uu____23[3U]
                                                                                        =
                                                                                          (uint8_t)0x45U;
                                                                                        uu____23[4U]
                                                                                        =
                                                                                          (uint8_t)0x2dU;
                                                                                        uu____23[5U]
                                                                                        =
                                                                                          (uint8_t)0x76U;
                                                                                        uu____23[6U]
                                                                                        =
                                                                                          (uint8_t)0x31U;
                                                                                        memcpy(tmp4
                                                                                          +
                                                                                            (uint32_t)9U,
                                                                                          suite_id,
                                                                                          (uint32_t)10U
                                                                                          *
                                                                                            sizeof (
                                                                                              uint8_t
                                                                                            ));
                                                                                        memcpy(tmp4
                                                                                          +
                                                                                            (uint32_t)9U
                                                                                            +
                                                                                              (uint32_t)10U,
                                                                                          label_key,
                                                                                          (uint32_t)3U
                                                                                          *
                                                                                            sizeof (
                                                                                              uint8_t
                                                                                            ));
                                                                                        {
                                                                                          uint8_t
                                                                                          *uu____24 =
                                                                                            tmp4
                                                                                            +
                                                                                              (uint32_t)9U
                                                                                              +
                                                                                                (uint32_t)10U
                                                                                              +
                                                                                                (uint32_t)3U;
                                                                                          Spec_Agile_HPKE_ciphersuite
                                                                                          lit12;
                                                                                          lit12.fst
                                                                                          =
                                                                                            Spec_Agile_DH_DH_P256;
                                                                                          lit12.snd
                                                                                          =
                                                                                            Spec_Hash_Definitions_SHA2_256;
                                                                                          lit12.thd.tag
                                                                                          =
                                                                                            Spec_Agile_HPKE_Seal;
                                                                                          lit12.thd.alg
                                                                                          =
                                                                                            Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                          lit12.f3 =
                                                                                            Spec_Hash_Definitions_SHA2_256;
                                                                                          {
                                                                                            uint32_t
                                                                                            sw10;
                                                                                            switch
                                                                                            (
                                                                                              Spec_Agile_HPKE_hash_of_cs(lit12)
                                                                                            )
                                                                                            {
                                                                                              case
                                                                                              Spec_Hash_Definitions_SHA2_256:
                                                                                                {
                                                                                                  sw10
                                                                                                  =
                                                                                                    (uint32_t)65U;
                                                                                                  break;
                                                                                                }
                                                                                              case
                                                                                              Spec_Hash_Definitions_SHA2_384:
                                                                                                {
                                                                                                  sw10
                                                                                                  =
                                                                                                    (uint32_t)97U;
                                                                                                  break;
                                                                                                }
                                                                                              case
                                                                                              Spec_Hash_Definitions_SHA2_512:
                                                                                                {
                                                                                                  sw10
                                                                                                  =
                                                                                                    (uint32_t)129U;
                                                                                                  break;
                                                                                                }
                                                                                              default:
                                                                                                {
                                                                                                  KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                                    __FILE__,
                                                                                                    __LINE__);
                                                                                                  KRML_HOST_EXIT(253U);
                                                                                                }
                                                                                            }
                                                                                            memcpy(uu____24,
                                                                                              o_context,
                                                                                              sw10
                                                                                              *
                                                                                                sizeof (
                                                                                                  uint8_t
                                                                                                ));
                                                                                            {
                                                                                              Spec_Agile_HPKE_ciphersuite
                                                                                              lit13;
                                                                                              lit13.fst
                                                                                              =
                                                                                                Spec_Agile_DH_DH_P256;
                                                                                              lit13.snd
                                                                                              =
                                                                                                Spec_Hash_Definitions_SHA2_256;
                                                                                              lit13.thd.tag
                                                                                              =
                                                                                                Spec_Agile_HPKE_Seal;
                                                                                              lit13.thd.alg
                                                                                              =
                                                                                                Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                              lit13.f3
                                                                                              =
                                                                                                Spec_Hash_Definitions_SHA2_256;
                                                                                              {
                                                                                                uint32_t
                                                                                                sw11;
                                                                                                switch
                                                                                                (
                                                                                                  Spec_Agile_HPKE_hash_of_cs(lit13)
                                                                                                )
                                                                                                {
                                                                                                  case
                                                                                                  Spec_Hash_Definitions_SHA2_256:
                                                                                                    {
                                                                                                      sw11
                                                                                                      =
                                                                                                        (uint32_t)32U;
                                                                                                      break;
                                                                                                    }
                                                                                                  case
                                                                                                  Spec_Hash_Definitions_SHA2_384:
                                                                                                    {
                                                                                                      sw11
                                                                                                      =
                                                                                                        (uint32_t)48U;
                                                                                                      break;
                                                                                                    }
                                                                                                  case
                                                                                                  Spec_Hash_Definitions_SHA2_512:
                                                                                                    {
                                                                                                      sw11
                                                                                                      =
                                                                                                        (uint32_t)64U;
                                                                                                      break;
                                                                                                    }
                                                                                                  default:
                                                                                                    {
                                                                                                      KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                                        __FILE__,
                                                                                                        __LINE__);
                                                                                                      KRML_HOST_EXIT(253U);
                                                                                                    }
                                                                                                }
                                                                                                {
                                                                                                  Spec_Agile_HPKE_ciphersuite
                                                                                                  lit14;
                                                                                                  lit14.fst
                                                                                                  =
                                                                                                    Spec_Agile_DH_DH_P256;
                                                                                                  lit14.snd
                                                                                                  =
                                                                                                    Spec_Hash_Definitions_SHA2_256;
                                                                                                  lit14.thd.tag
                                                                                                  =
                                                                                                    Spec_Agile_HPKE_Seal;
                                                                                                  lit14.thd.alg
                                                                                                  =
                                                                                                    Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                                  lit14.f3
                                                                                                  =
                                                                                                    Spec_Hash_Definitions_SHA2_256;
                                                                                                  {
                                                                                                    Spec_Agile_HPKE_aead
                                                                                                    scrut1 =
                                                                                                      Spec_Agile_HPKE_aead_of_cs(lit14);
                                                                                                    uint32_t
                                                                                                    ite2;
                                                                                                    if
                                                                                                    (
                                                                                                      scrut1.tag
                                                                                                      ==
                                                                                                        Spec_Agile_HPKE_ExportOnly
                                                                                                    )
                                                                                                    {
                                                                                                      ite2
                                                                                                      =
                                                                                                        (uint32_t)0U;
                                                                                                    }
                                                                                                    else if
                                                                                                    (
                                                                                                      scrut1.tag
                                                                                                      ==
                                                                                                        Spec_Agile_HPKE_Seal
                                                                                                      &&
                                                                                                        scrut1.alg
                                                                                                        ==
                                                                                                          Spec_Agile_AEAD_AES128_GCM
                                                                                                    )
                                                                                                    {
                                                                                                      ite2
                                                                                                      =
                                                                                                        (uint32_t)16U;
                                                                                                    }
                                                                                                    else if
                                                                                                    (
                                                                                                      scrut1.tag
                                                                                                      ==
                                                                                                        Spec_Agile_HPKE_Seal
                                                                                                      &&
                                                                                                        scrut1.alg
                                                                                                        ==
                                                                                                          Spec_Agile_AEAD_AES256_GCM
                                                                                                    )
                                                                                                    {
                                                                                                      ite2
                                                                                                      =
                                                                                                        (uint32_t)32U;
                                                                                                    }
                                                                                                    else if
                                                                                                    (
                                                                                                      scrut1.tag
                                                                                                      ==
                                                                                                        Spec_Agile_HPKE_Seal
                                                                                                      &&
                                                                                                        scrut1.alg
                                                                                                        ==
                                                                                                          Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                                                    )
                                                                                                    {
                                                                                                      ite2
                                                                                                      =
                                                                                                        (uint32_t)32U;
                                                                                                    }
                                                                                                    else
                                                                                                    {
                                                                                                      ite2
                                                                                                      =
                                                                                                        KRML_EABORT(uint32_t,
                                                                                                          "unreachable (pattern matches are exhaustive in F*)");
                                                                                                    }
                                                                                                    Hacl_HKDF_expand_sha2_256(o_ctx.ctx_key,
                                                                                                      o_secret,
                                                                                                      sw11,
                                                                                                      tmp4,
                                                                                                      len3,
                                                                                                      ite2);
                                                                                                    {
                                                                                                      uint8_t
                                                                                                      label_base_nonce[10U] =
                                                                                                        {
                                                                                                          (uint8_t)0x62U,
                                                                                                          (uint8_t)0x61U,
                                                                                                          (uint8_t)0x73U,
                                                                                                          (uint8_t)0x65U,
                                                                                                          (uint8_t)0x5fU,
                                                                                                          (uint8_t)0x6eU,
                                                                                                          (uint8_t)0x6fU,
                                                                                                          (uint8_t)0x6eU,
                                                                                                          (uint8_t)0x63U,
                                                                                                          (uint8_t)0x65U
                                                                                                        };
                                                                                                      Spec_Agile_HPKE_ciphersuite
                                                                                                      lit15;
                                                                                                      lit15.fst
                                                                                                      =
                                                                                                        Spec_Agile_DH_DH_P256;
                                                                                                      lit15.snd
                                                                                                      =
                                                                                                        Spec_Hash_Definitions_SHA2_256;
                                                                                                      lit15.thd.tag
                                                                                                      =
                                                                                                        Spec_Agile_HPKE_Seal;
                                                                                                      lit15.thd.alg
                                                                                                      =
                                                                                                        Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                                      lit15.f3
                                                                                                      =
                                                                                                        Spec_Hash_Definitions_SHA2_256;
                                                                                                      {
                                                                                                        uint32_t
                                                                                                        sw12;
                                                                                                        switch
                                                                                                        (
                                                                                                          Spec_Agile_HPKE_hash_of_cs(lit15)
                                                                                                        )
                                                                                                        {
                                                                                                          case
                                                                                                          Spec_Hash_Definitions_SHA2_256:
                                                                                                            {
                                                                                                              sw12
                                                                                                              =
                                                                                                                (uint32_t)65U;
                                                                                                              break;
                                                                                                            }
                                                                                                          case
                                                                                                          Spec_Hash_Definitions_SHA2_384:
                                                                                                            {
                                                                                                              sw12
                                                                                                              =
                                                                                                                (uint32_t)97U;
                                                                                                              break;
                                                                                                            }
                                                                                                          case
                                                                                                          Spec_Hash_Definitions_SHA2_512:
                                                                                                            {
                                                                                                              sw12
                                                                                                              =
                                                                                                                (uint32_t)129U;
                                                                                                              break;
                                                                                                            }
                                                                                                          default:
                                                                                                            {
                                                                                                              KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                                                __FILE__,
                                                                                                                __LINE__);
                                                                                                              KRML_HOST_EXIT(253U);
                                                                                                            }
                                                                                                        }
                                                                                                        {
                                                                                                          uint32_t
                                                                                                          len4 =
                                                                                                            (uint32_t)9U
                                                                                                            +
                                                                                                              (uint32_t)10U
                                                                                                            +
                                                                                                              (uint32_t)10U
                                                                                                            +
                                                                                                              sw12;
                                                                                                          KRML_CHECK_SIZE(sizeof (
                                                                                                              uint8_t
                                                                                                            ),
                                                                                                            len4);
                                                                                                          {
                                                                                                            uint8_t
                                                                                                            tmp[len4];
                                                                                                            memset(tmp,
                                                                                                              0U,
                                                                                                              len4
                                                                                                              *
                                                                                                                sizeof (
                                                                                                                  uint8_t
                                                                                                                ));
                                                                                                            {
                                                                                                              uint8_t
                                                                                                              *uu____25 =
                                                                                                                tmp;
                                                                                                              uint8_t
                                                                                                              *uu____26 =
                                                                                                                uu____25;
                                                                                                              Spec_Agile_HPKE_ciphersuite
                                                                                                              lit16;
                                                                                                              lit16.fst
                                                                                                              =
                                                                                                                Spec_Agile_DH_DH_P256;
                                                                                                              lit16.snd
                                                                                                              =
                                                                                                                Spec_Hash_Definitions_SHA2_256;
                                                                                                              lit16.thd.tag
                                                                                                              =
                                                                                                                Spec_Agile_HPKE_Seal;
                                                                                                              lit16.thd.alg
                                                                                                              =
                                                                                                                Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                                              lit16.f3
                                                                                                              =
                                                                                                                Spec_Hash_Definitions_SHA2_256;
                                                                                                              {
                                                                                                                Spec_Agile_HPKE_aead
                                                                                                                scrut2 =
                                                                                                                  Spec_Agile_HPKE_aead_of_cs(lit16);
                                                                                                                uint32_t
                                                                                                                ite3;
                                                                                                                if
                                                                                                                (
                                                                                                                  scrut2.tag
                                                                                                                  ==
                                                                                                                    Spec_Agile_HPKE_ExportOnly
                                                                                                                )
                                                                                                                {
                                                                                                                  ite3
                                                                                                                  =
                                                                                                                    (uint32_t)0U;
                                                                                                                }
                                                                                                                else if
                                                                                                                (
                                                                                                                  scrut2.tag
                                                                                                                  ==
                                                                                                                    Spec_Agile_HPKE_Seal
                                                                                                                )
                                                                                                                {
                                                                                                                  ite3
                                                                                                                  =
                                                                                                                    (uint32_t)12U;
                                                                                                                }
                                                                                                                else
                                                                                                                {
                                                                                                                  ite3
                                                                                                                  =
                                                                                                                    KRML_EABORT(uint32_t,
                                                                                                                      "unreachable (pattern matches are exhaustive in F*)");
                                                                                                                }
                                                                                                                store32_be(uu____26,
                                                                                                                  ite3);
                                                                                                                memcpy(uu____25,
                                                                                                                  uu____25
                                                                                                                  +
                                                                                                                    (uint32_t)2U,
                                                                                                                  (uint32_t)2U
                                                                                                                  *
                                                                                                                    sizeof (
                                                                                                                      uint8_t
                                                                                                                    ));
                                                                                                                {
                                                                                                                  uint8_t
                                                                                                                  *uu____27 =
                                                                                                                    tmp
                                                                                                                    +
                                                                                                                      (uint32_t)2U;
                                                                                                                  uu____27[0U]
                                                                                                                  =
                                                                                                                    (uint8_t)0x48U;
                                                                                                                  uu____27[1U]
                                                                                                                  =
                                                                                                                    (uint8_t)0x50U;
                                                                                                                  uu____27[2U]
                                                                                                                  =
                                                                                                                    (uint8_t)0x4bU;
                                                                                                                  uu____27[3U]
                                                                                                                  =
                                                                                                                    (uint8_t)0x45U;
                                                                                                                  uu____27[4U]
                                                                                                                  =
                                                                                                                    (uint8_t)0x2dU;
                                                                                                                  uu____27[5U]
                                                                                                                  =
                                                                                                                    (uint8_t)0x76U;
                                                                                                                  uu____27[6U]
                                                                                                                  =
                                                                                                                    (uint8_t)0x31U;
                                                                                                                  memcpy(tmp
                                                                                                                    +
                                                                                                                      (uint32_t)9U,
                                                                                                                    suite_id,
                                                                                                                    (uint32_t)10U
                                                                                                                    *
                                                                                                                      sizeof (
                                                                                                                        uint8_t
                                                                                                                      ));
                                                                                                                  memcpy(tmp
                                                                                                                    +
                                                                                                                      (uint32_t)9U
                                                                                                                      +
                                                                                                                        (uint32_t)10U,
                                                                                                                    label_base_nonce,
                                                                                                                    (uint32_t)10U
                                                                                                                    *
                                                                                                                      sizeof (
                                                                                                                        uint8_t
                                                                                                                      ));
                                                                                                                  {
                                                                                                                    uint8_t
                                                                                                                    *uu____28 =
                                                                                                                      tmp
                                                                                                                      +
                                                                                                                        (uint32_t)9U
                                                                                                                        +
                                                                                                                          (uint32_t)10U
                                                                                                                        +
                                                                                                                          (uint32_t)10U;
                                                                                                                    Spec_Agile_HPKE_ciphersuite
                                                                                                                    lit17;
                                                                                                                    lit17.fst
                                                                                                                    =
                                                                                                                      Spec_Agile_DH_DH_P256;
                                                                                                                    lit17.snd
                                                                                                                    =
                                                                                                                      Spec_Hash_Definitions_SHA2_256;
                                                                                                                    lit17.thd.tag
                                                                                                                    =
                                                                                                                      Spec_Agile_HPKE_Seal;
                                                                                                                    lit17.thd.alg
                                                                                                                    =
                                                                                                                      Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                                                    lit17.f3
                                                                                                                    =
                                                                                                                      Spec_Hash_Definitions_SHA2_256;
                                                                                                                    {
                                                                                                                      uint32_t
                                                                                                                      sw13;
                                                                                                                      switch
                                                                                                                      (
                                                                                                                        Spec_Agile_HPKE_hash_of_cs(lit17)
                                                                                                                      )
                                                                                                                      {
                                                                                                                        case
                                                                                                                        Spec_Hash_Definitions_SHA2_256:
                                                                                                                          {
                                                                                                                            sw13
                                                                                                                            =
                                                                                                                              (uint32_t)65U;
                                                                                                                            break;
                                                                                                                          }
                                                                                                                        case
                                                                                                                        Spec_Hash_Definitions_SHA2_384:
                                                                                                                          {
                                                                                                                            sw13
                                                                                                                            =
                                                                                                                              (uint32_t)97U;
                                                                                                                            break;
                                                                                                                          }
                                                                                                                        case
                                                                                                                        Spec_Hash_Definitions_SHA2_512:
                                                                                                                          {
                                                                                                                            sw13
                                                                                                                            =
                                                                                                                              (uint32_t)129U;
                                                                                                                            break;
                                                                                                                          }
                                                                                                                        default:
                                                                                                                          {
                                                                                                                            KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                                                              __FILE__,
                                                                                                                              __LINE__);
                                                                                                                            KRML_HOST_EXIT(253U);
                                                                                                                          }
                                                                                                                      }
                                                                                                                      memcpy(uu____28,
                                                                                                                        o_context,
                                                                                                                        sw13
                                                                                                                        *
                                                                                                                          sizeof (
                                                                                                                            uint8_t
                                                                                                                          ));
                                                                                                                      {
                                                                                                                        Spec_Agile_HPKE_ciphersuite
                                                                                                                        lit18;
                                                                                                                        lit18.fst
                                                                                                                        =
                                                                                                                          Spec_Agile_DH_DH_P256;
                                                                                                                        lit18.snd
                                                                                                                        =
                                                                                                                          Spec_Hash_Definitions_SHA2_256;
                                                                                                                        lit18.thd.tag
                                                                                                                        =
                                                                                                                          Spec_Agile_HPKE_Seal;
                                                                                                                        lit18.thd.alg
                                                                                                                        =
                                                                                                                          Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                                                        lit18.f3
                                                                                                                        =
                                                                                                                          Spec_Hash_Definitions_SHA2_256;
                                                                                                                        {
                                                                                                                          uint32_t
                                                                                                                          sw;
                                                                                                                          switch
                                                                                                                          (
                                                                                                                            Spec_Agile_HPKE_hash_of_cs(lit18)
                                                                                                                          )
                                                                                                                          {
                                                                                                                            case
                                                                                                                            Spec_Hash_Definitions_SHA2_256:
                                                                                                                              {
                                                                                                                                sw
                                                                                                                                =
                                                                                                                                  (uint32_t)32U;
                                                                                                                                break;
                                                                                                                              }
                                                                                                                            case
                                                                                                                            Spec_Hash_Definitions_SHA2_384:
                                                                                                                              {
                                                                                                                                sw
                                                                                                                                =
                                                                                                                                  (uint32_t)48U;
                                                                                                                                break;
                                                                                                                              }
                                                                                                                            case
                                                                                                                            Spec_Hash_Definitions_SHA2_512:
                                                                                                                              {
                                                                                                                                sw
                                                                                                                                =
                                                                                                                                  (uint32_t)64U;
                                                                                                                                break;
                                                                                                                              }
                                                                                                                            default:
                                                                                                                              {
                                                                                                                                KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                                                                  __FILE__,
                                                                                                                                  __LINE__);
                                                                                                                                KRML_HOST_EXIT(253U);
                                                                                                                              }
                                                                                                                          }
                                                                                                                          {
                                                                                                                            Spec_Agile_HPKE_ciphersuite
                                                                                                                            lit;
                                                                                                                            lit.fst
                                                                                                                            =
                                                                                                                              Spec_Agile_DH_DH_P256;
                                                                                                                            lit.snd
                                                                                                                            =
                                                                                                                              Spec_Hash_Definitions_SHA2_256;
                                                                                                                            lit.thd.tag
                                                                                                                            =
                                                                                                                              Spec_Agile_HPKE_Seal;
                                                                                                                            lit.thd.alg
                                                                                                                            =
                                                                                                                              Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                                                            lit.f3
                                                                                                                            =
                                                                                                                              Spec_Hash_Definitions_SHA2_256;
                                                                                                                            {
                                                                                                                              Spec_Agile_HPKE_aead
                                                                                                                              scrut3 =
                                                                                                                                Spec_Agile_HPKE_aead_of_cs(lit);
                                                                                                                              uint32_t
                                                                                                                              ite;
                                                                                                                              if
                                                                                                                              (
                                                                                                                                scrut3.tag
                                                                                                                                ==
                                                                                                                                  Spec_Agile_HPKE_ExportOnly
                                                                                                                              )
                                                                                                                              {
                                                                                                                                ite
                                                                                                                                =
                                                                                                                                  (uint32_t)0U;
                                                                                                                              }
                                                                                                                              else if
                                                                                                                              (
                                                                                                                                scrut3.tag
                                                                                                                                ==
                                                                                                                                  Spec_Agile_HPKE_Seal
                                                                                                                              )
                                                                                                                              {
                                                                                                                                ite
                                                                                                                                =
                                                                                                                                  (uint32_t)12U;
                                                                                                                              }
                                                                                                                              else
                                                                                                                              {
                                                                                                                                ite
                                                                                                                                =
                                                                                                                                  KRML_EABORT(uint32_t,
                                                                                                                                    "unreachable (pattern matches are exhaustive in F*)");
                                                                                                                              }
                                                                                                                              Hacl_HKDF_expand_sha2_256(o_ctx.ctx_nonce,
                                                                                                                                o_secret,
                                                                                                                                sw,
                                                                                                                                tmp,
                                                                                                                                len4,
                                                                                                                                ite);
                                                                                                                              o_ctx.ctx_seq[0U]
                                                                                                                              =
                                                                                                                                (uint64_t)0U;
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
                                                                          ite0 = res;
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
  {
    ite0 = res;
  }
  return ite0;
}

uint32_t
Hacl_HPKE_P256_CP128_SHA256_setupBaseR(
  Hacl_Impl_HPKE_context_s o_ctx,
  uint8_t *enc,
  uint8_t *skR,
  uint32_t infolen,
  uint8_t *info
)
{
  uint8_t pkR[64U] = { 0U };
  uint64_t tempBuffer0[100U] = { 0U };
  uint64_t resultBuffer0[12U] = { 0U };
  uint64_t *resultBufferX0 = resultBuffer0;
  uint64_t *resultBufferY0 = resultBuffer0 + (uint32_t)4U;
  uint8_t *resultX0 = pkR;
  uint8_t *resultY0 = pkR + (uint32_t)32U;
  uint64_t flag0;
  bool res;
  uint32_t res1;
  uint32_t ite0;
  Hacl_Impl_P256_Core_secretToPublic(resultBuffer0, skR, tempBuffer0);
  flag0 = Hacl_Impl_P256_Core_isPointAtInfinityPrivate(resultBuffer0);
  Hacl_Impl_P256_LowLevel_changeEndian(resultBufferX0);
  Hacl_Impl_P256_LowLevel_changeEndian(resultBufferY0);
  Hacl_Impl_P256_LowLevel_toUint8(resultBufferX0, resultX0);
  Hacl_Impl_P256_LowLevel_toUint8(resultBufferY0, resultY0);
  res = flag0 == (uint64_t)0U;
  if (res)
  {
    res1 = (uint32_t)0U;
  }
  else
  {
    res1 = (uint32_t)1U;
  }
  if (res1 == (uint32_t)0U)
  {
    uint8_t shared[32U] = { 0U };
    uint8_t *pkE = enc + (uint32_t)1U;
    uint8_t dh[64U] = { 0U };
    uint8_t tmp0[64U] = { 0U };
    uint64_t resultBufferFelem[12U] = { 0U };
    uint64_t *resultBufferFelemX = resultBufferFelem;
    uint64_t *resultBufferFelemY = resultBufferFelem + (uint32_t)4U;
    uint8_t *resultX1 = tmp0;
    uint8_t *resultY1 = tmp0 + (uint32_t)32U;
    uint64_t publicKeyAsFelem[8U] = { 0U };
    uint64_t *publicKeyFelemX = publicKeyAsFelem;
    uint64_t *publicKeyFelemY = publicKeyAsFelem + (uint32_t)4U;
    uint8_t *pubKeyX = pkE;
    uint8_t *pubKeyY = pkE + (uint32_t)32U;
    Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
    Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
    {
      uint64_t flag1 = Hacl_Impl_P256_DH__ecp256dh_r(resultBufferFelem, publicKeyAsFelem, skR);
      Hacl_Impl_P256_LowLevel_changeEndian(resultBufferFelemX);
      Hacl_Impl_P256_LowLevel_changeEndian(resultBufferFelemY);
      Hacl_Impl_P256_LowLevel_toUint8(resultBufferFelemX, resultX1);
      Hacl_Impl_P256_LowLevel_toUint8(resultBufferFelemY, resultY1);
      {
        bool res0 = flag1 == (uint64_t)0U;
        memcpy(dh, tmp0, (uint32_t)64U * sizeof (uint8_t));
        {
          uint32_t res11;
          if (res0)
          {
            res11 = (uint32_t)0U;
          }
          else
          {
            res11 = (uint32_t)1U;
          }
          {
            uint32_t res20;
            if (res11 == (uint32_t)0U)
            {
              uint8_t kemcontext[130U] = { 0U };
              Spec_Agile_HPKE_ciphersuite lit0;
              lit0.fst = Spec_Agile_DH_DH_P256;
              lit0.snd = Spec_Hash_Definitions_SHA2_256;
              lit0.thd.tag = Spec_Agile_HPKE_Seal;
              lit0.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
              lit0.f3 = Spec_Hash_Definitions_SHA2_256;
              {
                uint32_t sw0;
                switch (Spec_Agile_HPKE_kem_dh_of_cs(lit0))
                {
                  case Spec_Agile_DH_DH_Curve25519:
                    {
                      sw0 = (uint32_t)32U;
                      break;
                    }
                  case Spec_Agile_DH_DH_P256:
                    {
                      sw0 = (uint32_t)65U;
                      break;
                    }
                  default:
                    {
                      KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
                      KRML_HOST_EXIT(253U);
                    }
                }
                {
                  uint8_t *pkRm = kemcontext + sw0;
                  uint8_t *pkR1 = pkRm + (uint32_t)1U;
                  uint64_t tempBuffer[100U] = { 0U };
                  uint64_t resultBuffer[12U] = { 0U };
                  uint64_t *resultBufferX = resultBuffer;
                  uint64_t *resultBufferY = resultBuffer + (uint32_t)4U;
                  uint8_t *resultX = pkR1;
                  uint8_t *resultY = pkR1 + (uint32_t)32U;
                  Hacl_Impl_P256_Core_secretToPublic(resultBuffer, skR, tempBuffer);
                  {
                    uint64_t flag = Hacl_Impl_P256_Core_isPointAtInfinityPrivate(resultBuffer);
                    Hacl_Impl_P256_LowLevel_changeEndian(resultBufferX);
                    Hacl_Impl_P256_LowLevel_changeEndian(resultBufferY);
                    Hacl_Impl_P256_LowLevel_toUint8(resultBufferX, resultX);
                    Hacl_Impl_P256_LowLevel_toUint8(resultBufferY, resultY);
                    {
                      bool res3 = flag == (uint64_t)0U;
                      uint32_t res2;
                      if (res3)
                      {
                        res2 = (uint32_t)0U;
                      }
                      else
                      {
                        res2 = (uint32_t)1U;
                      }
                      if (res2 == (uint32_t)0U)
                      {
                        uint8_t *uu____0 = kemcontext;
                        Spec_Agile_HPKE_ciphersuite lit1;
                        lit1.fst = Spec_Agile_DH_DH_P256;
                        lit1.snd = Spec_Hash_Definitions_SHA2_256;
                        lit1.thd.tag = Spec_Agile_HPKE_Seal;
                        lit1.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
                        lit1.f3 = Spec_Hash_Definitions_SHA2_256;
                        {
                          uint32_t sw1;
                          switch (Spec_Agile_HPKE_kem_dh_of_cs(lit1))
                          {
                            case Spec_Agile_DH_DH_Curve25519:
                              {
                                sw1 = (uint32_t)32U;
                                break;
                              }
                            case Spec_Agile_DH_DH_P256:
                              {
                                sw1 = (uint32_t)65U;
                                break;
                              }
                            default:
                              {
                                KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                  __FILE__,
                                  __LINE__);
                                KRML_HOST_EXIT(253U);
                              }
                          }
                          memcpy(uu____0, enc, sw1 * sizeof (uint8_t));
                          pkRm[0U] = (uint8_t)4U;
                          {
                            uint8_t *dhm = dh;
                            uint8_t o_eae_prk[32U] = { 0U };
                            uint8_t suite_id_kem[5U] = { 0U };
                            uint8_t *uu____1 = suite_id_kem;
                            uu____1[0U] = (uint8_t)0x4bU;
                            uu____1[1U] = (uint8_t)0x45U;
                            uu____1[2U] = (uint8_t)0x4dU;
                            {
                              uint8_t *uu____2 = suite_id_kem + (uint32_t)3U;
                              uu____2[0U] = (uint8_t)0U;
                              uu____2[1U] = (uint8_t)16U;
                              {
                                uint8_t *empty = suite_id_kem;
                                uint8_t
                                label_eae_prk[7U] =
                                  {
                                    (uint8_t)0x65U, (uint8_t)0x61U, (uint8_t)0x65U, (uint8_t)0x5fU,
                                    (uint8_t)0x70U, (uint8_t)0x72U, (uint8_t)0x6bU
                                  };
                                uint32_t
                                len = (uint32_t)7U + (uint32_t)5U + (uint32_t)7U + (uint32_t)32U;
                                KRML_CHECK_SIZE(sizeof (uint8_t), len);
                                {
                                  uint8_t tmp1[len];
                                  memset(tmp1, 0U, len * sizeof (uint8_t));
                                  {
                                    uint8_t *uu____3 = tmp1;
                                    uu____3[0U] = (uint8_t)0x48U;
                                    uu____3[1U] = (uint8_t)0x50U;
                                    uu____3[2U] = (uint8_t)0x4bU;
                                    uu____3[3U] = (uint8_t)0x45U;
                                    uu____3[4U] = (uint8_t)0x2dU;
                                    uu____3[5U] = (uint8_t)0x76U;
                                    uu____3[6U] = (uint8_t)0x31U;
                                    memcpy(tmp1 + (uint32_t)7U,
                                      suite_id_kem,
                                      (uint32_t)5U * sizeof (uint8_t));
                                    memcpy(tmp1 + (uint32_t)7U + (uint32_t)5U,
                                      label_eae_prk,
                                      (uint32_t)7U * sizeof (uint8_t));
                                    memcpy(tmp1 + (uint32_t)7U + (uint32_t)5U + (uint32_t)7U,
                                      dhm,
                                      (uint32_t)32U * sizeof (uint8_t));
                                    Hacl_HKDF_extract_sha2_256(o_eae_prk,
                                      empty,
                                      (uint32_t)0U,
                                      tmp1,
                                      len);
                                    {
                                      uint8_t
                                      label_shared_secret[13U] =
                                        {
                                          (uint8_t)0x73U, (uint8_t)0x68U, (uint8_t)0x61U,
                                          (uint8_t)0x72U, (uint8_t)0x65U, (uint8_t)0x64U,
                                          (uint8_t)0x5fU, (uint8_t)0x73U, (uint8_t)0x65U,
                                          (uint8_t)0x63U, (uint8_t)0x72U, (uint8_t)0x65U,
                                          (uint8_t)0x74U
                                        };
                                      Spec_Agile_HPKE_ciphersuite lit2;
                                      lit2.fst = Spec_Agile_DH_DH_P256;
                                      lit2.snd = Spec_Hash_Definitions_SHA2_256;
                                      lit2.thd.tag = Spec_Agile_HPKE_Seal;
                                      lit2.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
                                      lit2.f3 = Spec_Hash_Definitions_SHA2_256;
                                      {
                                        uint32_t sw2;
                                        switch (Spec_Agile_HPKE_kem_dh_of_cs(lit2))
                                        {
                                          case Spec_Agile_DH_DH_Curve25519:
                                            {
                                              sw2 = (uint32_t)64U;
                                              break;
                                            }
                                          case Spec_Agile_DH_DH_P256:
                                            {
                                              sw2 = (uint32_t)130U;
                                              break;
                                            }
                                          default:
                                            {
                                              KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                __FILE__,
                                                __LINE__);
                                              KRML_HOST_EXIT(253U);
                                            }
                                        }
                                        {
                                          uint32_t
                                          len0 = (uint32_t)9U + (uint32_t)5U + (uint32_t)13U + sw2;
                                          KRML_CHECK_SIZE(sizeof (uint8_t), len0);
                                          {
                                            uint8_t tmp[len0];
                                            memset(tmp, 0U, len0 * sizeof (uint8_t));
                                            {
                                              uint8_t *uu____4 = tmp;
                                              uint8_t *uu____5 = uu____4;
                                              Spec_Agile_HPKE_ciphersuite lit3;
                                              lit3.fst = Spec_Agile_DH_DH_P256;
                                              lit3.snd = Spec_Hash_Definitions_SHA2_256;
                                              lit3.thd.tag = Spec_Agile_HPKE_Seal;
                                              lit3.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
                                              lit3.f3 = Spec_Hash_Definitions_SHA2_256;
                                              {
                                                uint32_t sw3;
                                                switch (Spec_Agile_HPKE_kem_hash_of_cs(lit3))
                                                {
                                                  case Spec_Hash_Definitions_SHA2_256:
                                                    {
                                                      sw3 = (uint32_t)32U;
                                                      break;
                                                    }
                                                  default:
                                                    {
                                                      KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                        __FILE__,
                                                        __LINE__);
                                                      KRML_HOST_EXIT(253U);
                                                    }
                                                }
                                                store32_be(uu____5, sw3);
                                                memcpy(uu____4,
                                                  uu____4 + (uint32_t)2U,
                                                  (uint32_t)2U * sizeof (uint8_t));
                                                {
                                                  uint8_t *uu____6 = tmp + (uint32_t)2U;
                                                  uu____6[0U] = (uint8_t)0x48U;
                                                  uu____6[1U] = (uint8_t)0x50U;
                                                  uu____6[2U] = (uint8_t)0x4bU;
                                                  uu____6[3U] = (uint8_t)0x45U;
                                                  uu____6[4U] = (uint8_t)0x2dU;
                                                  uu____6[5U] = (uint8_t)0x76U;
                                                  uu____6[6U] = (uint8_t)0x31U;
                                                  memcpy(tmp + (uint32_t)9U,
                                                    suite_id_kem,
                                                    (uint32_t)5U * sizeof (uint8_t));
                                                  memcpy(tmp + (uint32_t)9U + (uint32_t)5U,
                                                    label_shared_secret,
                                                    (uint32_t)13U * sizeof (uint8_t));
                                                  {
                                                    uint8_t
                                                    *uu____7 =
                                                      tmp
                                                      + (uint32_t)9U + (uint32_t)5U + (uint32_t)13U;
                                                    Spec_Agile_HPKE_ciphersuite lit4;
                                                    lit4.fst = Spec_Agile_DH_DH_P256;
                                                    lit4.snd = Spec_Hash_Definitions_SHA2_256;
                                                    lit4.thd.tag = Spec_Agile_HPKE_Seal;
                                                    lit4.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                    lit4.f3 = Spec_Hash_Definitions_SHA2_256;
                                                    {
                                                      uint32_t sw4;
                                                      switch (Spec_Agile_HPKE_kem_dh_of_cs(lit4))
                                                      {
                                                        case Spec_Agile_DH_DH_Curve25519:
                                                          {
                                                            sw4 = (uint32_t)64U;
                                                            break;
                                                          }
                                                        case Spec_Agile_DH_DH_P256:
                                                          {
                                                            sw4 = (uint32_t)130U;
                                                            break;
                                                          }
                                                        default:
                                                          {
                                                            KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                              __FILE__,
                                                              __LINE__);
                                                            KRML_HOST_EXIT(253U);
                                                          }
                                                      }
                                                      memcpy(uu____7,
                                                        kemcontext,
                                                        sw4 * sizeof (uint8_t));
                                                      {
                                                        Spec_Agile_HPKE_ciphersuite lit5;
                                                        lit5.fst = Spec_Agile_DH_DH_P256;
                                                        lit5.snd = Spec_Hash_Definitions_SHA2_256;
                                                        lit5.thd.tag = Spec_Agile_HPKE_Seal;
                                                        lit5.thd.alg =
                                                          Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                        lit5.f3 = Spec_Hash_Definitions_SHA2_256;
                                                        {
                                                          uint32_t sw5;
                                                          switch
                                                          (Spec_Agile_HPKE_kem_hash_of_cs(lit5))
                                                          {
                                                            case Spec_Hash_Definitions_SHA2_256:
                                                              {
                                                                sw5 = (uint32_t)32U;
                                                                break;
                                                              }
                                                            default:
                                                              {
                                                                KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                  __FILE__,
                                                                  __LINE__);
                                                                KRML_HOST_EXIT(253U);
                                                              }
                                                          }
                                                          {
                                                            Spec_Agile_HPKE_ciphersuite lit;
                                                            lit.fst = Spec_Agile_DH_DH_P256;
                                                            lit.snd = Spec_Hash_Definitions_SHA2_256;
                                                            lit.thd.tag = Spec_Agile_HPKE_Seal;
                                                            lit.thd.alg =
                                                              Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                            lit.f3 = Spec_Hash_Definitions_SHA2_256;
                                                            {
                                                              uint32_t sw;
                                                              switch
                                                              (Spec_Agile_HPKE_kem_hash_of_cs(lit))
                                                              {
                                                                case Spec_Hash_Definitions_SHA2_256:
                                                                  {
                                                                    sw = (uint32_t)32U;
                                                                    break;
                                                                  }
                                                                default:
                                                                  {
                                                                    KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
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
                                                              res20 = (uint32_t)0U;
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
                      {
                        res20 = (uint32_t)1U;
                      }
                    }
                  }
                }
              }
            }
            else
            {
              res20 = (uint32_t)1U;
            }
            if (res20 == (uint32_t)0U)
            {
              uint8_t o_context[65U] = { 0U };
              uint8_t o_secret[32U] = { 0U };
              uint8_t suite_id[10U] = { 0U };
              uint8_t *uu____8 = suite_id;
              uu____8[0U] = (uint8_t)0x48U;
              uu____8[1U] = (uint8_t)0x50U;
              uu____8[2U] = (uint8_t)0x4bU;
              uu____8[3U] = (uint8_t)0x45U;
              {
                uint8_t *uu____9 = suite_id + (uint32_t)4U;
                uu____9[0U] = (uint8_t)0U;
                uu____9[1U] = (uint8_t)16U;
                {
                  uint8_t *uu____10 = suite_id + (uint32_t)6U;
                  uu____10[0U] = (uint8_t)0U;
                  uu____10[1U] = (uint8_t)1U;
                  {
                    uint8_t *uu____11 = suite_id + (uint32_t)8U;
                    uu____11[0U] = (uint8_t)0U;
                    uu____11[1U] = (uint8_t)3U;
                    {
                      uint8_t
                      label_psk_id_hash[11U] =
                        {
                          (uint8_t)0x70U, (uint8_t)0x73U, (uint8_t)0x6bU, (uint8_t)0x5fU,
                          (uint8_t)0x69U, (uint8_t)0x64U, (uint8_t)0x5fU, (uint8_t)0x68U,
                          (uint8_t)0x61U, (uint8_t)0x73U, (uint8_t)0x68U
                        };
                      uint8_t o_psk_id_hash[32U] = { 0U };
                      uint8_t *empty = suite_id;
                      uint32_t len0 = (uint32_t)7U + (uint32_t)10U + (uint32_t)11U + (uint32_t)0U;
                      KRML_CHECK_SIZE(sizeof (uint8_t), len0);
                      {
                        uint8_t tmp1[len0];
                        memset(tmp1, 0U, len0 * sizeof (uint8_t));
                        {
                          uint8_t *uu____12 = tmp1;
                          uu____12[0U] = (uint8_t)0x48U;
                          uu____12[1U] = (uint8_t)0x50U;
                          uu____12[2U] = (uint8_t)0x4bU;
                          uu____12[3U] = (uint8_t)0x45U;
                          uu____12[4U] = (uint8_t)0x2dU;
                          uu____12[5U] = (uint8_t)0x76U;
                          uu____12[6U] = (uint8_t)0x31U;
                          memcpy(tmp1 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
                          memcpy(tmp1 + (uint32_t)7U + (uint32_t)10U,
                            label_psk_id_hash,
                            (uint32_t)11U * sizeof (uint8_t));
                          memcpy(tmp1 + (uint32_t)7U + (uint32_t)10U + (uint32_t)11U,
                            empty,
                            (uint32_t)0U * sizeof (uint8_t));
                          Hacl_HKDF_extract_sha2_256(o_psk_id_hash,
                            empty,
                            (uint32_t)0U,
                            tmp1,
                            len0);
                          {
                            uint8_t
                            label_info_hash[9U] =
                              {
                                (uint8_t)0x69U, (uint8_t)0x6eU, (uint8_t)0x66U, (uint8_t)0x6fU,
                                (uint8_t)0x5fU, (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x73U,
                                (uint8_t)0x68U
                              };
                            uint8_t o_info_hash[32U] = { 0U };
                            uint32_t len1 = (uint32_t)7U + (uint32_t)10U + (uint32_t)9U + infolen;
                            KRML_CHECK_SIZE(sizeof (uint8_t), len1);
                            {
                              uint8_t tmp2[len1];
                              memset(tmp2, 0U, len1 * sizeof (uint8_t));
                              {
                                uint8_t *uu____13 = tmp2;
                                uu____13[0U] = (uint8_t)0x48U;
                                uu____13[1U] = (uint8_t)0x50U;
                                uu____13[2U] = (uint8_t)0x4bU;
                                uu____13[3U] = (uint8_t)0x45U;
                                uu____13[4U] = (uint8_t)0x2dU;
                                uu____13[5U] = (uint8_t)0x76U;
                                uu____13[6U] = (uint8_t)0x31U;
                                memcpy(tmp2 + (uint32_t)7U,
                                  suite_id,
                                  (uint32_t)10U * sizeof (uint8_t));
                                memcpy(tmp2 + (uint32_t)7U + (uint32_t)10U,
                                  label_info_hash,
                                  (uint32_t)9U * sizeof (uint8_t));
                                memcpy(tmp2 + (uint32_t)7U + (uint32_t)10U + (uint32_t)9U,
                                  info,
                                  infolen * sizeof (uint8_t));
                                Hacl_HKDF_extract_sha2_256(o_info_hash,
                                  empty,
                                  (uint32_t)0U,
                                  tmp2,
                                  len1);
                                o_context[0U] = (uint8_t)0U;
                                {
                                  uint8_t *uu____14 = o_context + (uint32_t)1U;
                                  Spec_Agile_HPKE_ciphersuite lit0;
                                  lit0.fst = Spec_Agile_DH_DH_P256;
                                  lit0.snd = Spec_Hash_Definitions_SHA2_256;
                                  lit0.thd.tag = Spec_Agile_HPKE_Seal;
                                  lit0.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
                                  lit0.f3 = Spec_Hash_Definitions_SHA2_256;
                                  {
                                    uint32_t sw0;
                                    switch (Spec_Agile_HPKE_hash_of_cs(lit0))
                                    {
                                      case Spec_Hash_Definitions_SHA2_256:
                                        {
                                          sw0 = (uint32_t)32U;
                                          break;
                                        }
                                      case Spec_Hash_Definitions_SHA2_384:
                                        {
                                          sw0 = (uint32_t)48U;
                                          break;
                                        }
                                      case Spec_Hash_Definitions_SHA2_512:
                                        {
                                          sw0 = (uint32_t)64U;
                                          break;
                                        }
                                      default:
                                        {
                                          KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                            __FILE__,
                                            __LINE__);
                                          KRML_HOST_EXIT(253U);
                                        }
                                    }
                                    memcpy(uu____14, o_psk_id_hash, sw0 * sizeof (uint8_t));
                                    {
                                      Spec_Agile_HPKE_ciphersuite lit1;
                                      lit1.fst = Spec_Agile_DH_DH_P256;
                                      lit1.snd = Spec_Hash_Definitions_SHA2_256;
                                      lit1.thd.tag = Spec_Agile_HPKE_Seal;
                                      lit1.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
                                      lit1.f3 = Spec_Hash_Definitions_SHA2_256;
                                      {
                                        uint32_t sw1;
                                        switch (Spec_Agile_HPKE_hash_of_cs(lit1))
                                        {
                                          case Spec_Hash_Definitions_SHA2_256:
                                            {
                                              sw1 = (uint32_t)33U;
                                              break;
                                            }
                                          case Spec_Hash_Definitions_SHA2_384:
                                            {
                                              sw1 = (uint32_t)49U;
                                              break;
                                            }
                                          case Spec_Hash_Definitions_SHA2_512:
                                            {
                                              sw1 = (uint32_t)65U;
                                              break;
                                            }
                                          default:
                                            {
                                              KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                __FILE__,
                                                __LINE__);
                                              KRML_HOST_EXIT(253U);
                                            }
                                        }
                                        {
                                          uint8_t *uu____15 = o_context + sw1;
                                          Spec_Agile_HPKE_ciphersuite lit2;
                                          lit2.fst = Spec_Agile_DH_DH_P256;
                                          lit2.snd = Spec_Hash_Definitions_SHA2_256;
                                          lit2.thd.tag = Spec_Agile_HPKE_Seal;
                                          lit2.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
                                          lit2.f3 = Spec_Hash_Definitions_SHA2_256;
                                          {
                                            uint32_t sw2;
                                            switch (Spec_Agile_HPKE_hash_of_cs(lit2))
                                            {
                                              case Spec_Hash_Definitions_SHA2_256:
                                                {
                                                  sw2 = (uint32_t)32U;
                                                  break;
                                                }
                                              case Spec_Hash_Definitions_SHA2_384:
                                                {
                                                  sw2 = (uint32_t)48U;
                                                  break;
                                                }
                                              case Spec_Hash_Definitions_SHA2_512:
                                                {
                                                  sw2 = (uint32_t)64U;
                                                  break;
                                                }
                                              default:
                                                {
                                                  KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                    __FILE__,
                                                    __LINE__);
                                                  KRML_HOST_EXIT(253U);
                                                }
                                            }
                                            memcpy(uu____15, o_info_hash, sw2 * sizeof (uint8_t));
                                            {
                                              uint8_t
                                              label_secret[6U] =
                                                {
                                                  (uint8_t)0x73U, (uint8_t)0x65U, (uint8_t)0x63U,
                                                  (uint8_t)0x72U, (uint8_t)0x65U, (uint8_t)0x74U
                                                };
                                              uint32_t
                                              len =
                                                (uint32_t)7U
                                                + (uint32_t)10U
                                                + (uint32_t)6U
                                                + (uint32_t)0U;
                                              KRML_CHECK_SIZE(sizeof (uint8_t), len);
                                              {
                                                uint8_t tmp3[len];
                                                memset(tmp3, 0U, len * sizeof (uint8_t));
                                                {
                                                  uint8_t *uu____16 = tmp3;
                                                  uu____16[0U] = (uint8_t)0x48U;
                                                  uu____16[1U] = (uint8_t)0x50U;
                                                  uu____16[2U] = (uint8_t)0x4bU;
                                                  uu____16[3U] = (uint8_t)0x45U;
                                                  uu____16[4U] = (uint8_t)0x2dU;
                                                  uu____16[5U] = (uint8_t)0x76U;
                                                  uu____16[6U] = (uint8_t)0x31U;
                                                  memcpy(tmp3 + (uint32_t)7U,
                                                    suite_id,
                                                    (uint32_t)10U * sizeof (uint8_t));
                                                  memcpy(tmp3 + (uint32_t)7U + (uint32_t)10U,
                                                    label_secret,
                                                    (uint32_t)6U * sizeof (uint8_t));
                                                  memcpy(tmp3
                                                    + (uint32_t)7U + (uint32_t)10U + (uint32_t)6U,
                                                    empty,
                                                    (uint32_t)0U * sizeof (uint8_t));
                                                  {
                                                    Spec_Agile_HPKE_ciphersuite lit3;
                                                    lit3.fst = Spec_Agile_DH_DH_P256;
                                                    lit3.snd = Spec_Hash_Definitions_SHA2_256;
                                                    lit3.thd.tag = Spec_Agile_HPKE_Seal;
                                                    lit3.thd.alg = Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                    lit3.f3 = Spec_Hash_Definitions_SHA2_256;
                                                    {
                                                      uint32_t sw3;
                                                      switch (Spec_Agile_HPKE_kem_hash_of_cs(lit3))
                                                      {
                                                        case Spec_Hash_Definitions_SHA2_256:
                                                          {
                                                            sw3 = (uint32_t)32U;
                                                            break;
                                                          }
                                                        default:
                                                          {
                                                            KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                              __FILE__,
                                                              __LINE__);
                                                            KRML_HOST_EXIT(253U);
                                                          }
                                                      }
                                                      Hacl_HKDF_extract_sha2_256(o_secret,
                                                        shared,
                                                        sw3,
                                                        tmp3,
                                                        len);
                                                      {
                                                        uint8_t
                                                        label_exp[3U] =
                                                          {
                                                            (uint8_t)0x65U,
                                                            (uint8_t)0x78U,
                                                            (uint8_t)0x70U
                                                          };
                                                        Spec_Agile_HPKE_ciphersuite lit4;
                                                        lit4.fst = Spec_Agile_DH_DH_P256;
                                                        lit4.snd = Spec_Hash_Definitions_SHA2_256;
                                                        lit4.thd.tag = Spec_Agile_HPKE_Seal;
                                                        lit4.thd.alg =
                                                          Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                        lit4.f3 = Spec_Hash_Definitions_SHA2_256;
                                                        {
                                                          uint32_t sw4;
                                                          switch (Spec_Agile_HPKE_hash_of_cs(lit4))
                                                          {
                                                            case Spec_Hash_Definitions_SHA2_256:
                                                              {
                                                                sw4 = (uint32_t)65U;
                                                                break;
                                                              }
                                                            case Spec_Hash_Definitions_SHA2_384:
                                                              {
                                                                sw4 = (uint32_t)97U;
                                                                break;
                                                              }
                                                            case Spec_Hash_Definitions_SHA2_512:
                                                              {
                                                                sw4 = (uint32_t)129U;
                                                                break;
                                                              }
                                                            default:
                                                              {
                                                                KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                  __FILE__,
                                                                  __LINE__);
                                                                KRML_HOST_EXIT(253U);
                                                              }
                                                          }
                                                          {
                                                            uint32_t
                                                            len2 =
                                                              (uint32_t)9U
                                                              + (uint32_t)10U
                                                              + (uint32_t)3U
                                                              + sw4;
                                                            KRML_CHECK_SIZE(sizeof (uint8_t), len2);
                                                            {
                                                              uint8_t tmp4[len2];
                                                              memset(tmp4,
                                                                0U,
                                                                len2 * sizeof (uint8_t));
                                                              {
                                                                uint8_t *uu____17 = tmp4;
                                                                uint8_t *uu____18 = uu____17;
                                                                Spec_Agile_HPKE_ciphersuite lit5;
                                                                lit5.fst = Spec_Agile_DH_DH_P256;
                                                                lit5.snd =
                                                                  Spec_Hash_Definitions_SHA2_256;
                                                                lit5.thd.tag = Spec_Agile_HPKE_Seal;
                                                                lit5.thd.alg =
                                                                  Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                lit5.f3 =
                                                                  Spec_Hash_Definitions_SHA2_256;
                                                                {
                                                                  uint32_t sw5;
                                                                  switch
                                                                  (Spec_Agile_HPKE_hash_of_cs(lit5))
                                                                  {
                                                                    case
                                                                    Spec_Hash_Definitions_SHA2_256:
                                                                      {
                                                                        sw5 = (uint32_t)32U;
                                                                        break;
                                                                      }
                                                                    case
                                                                    Spec_Hash_Definitions_SHA2_384:
                                                                      {
                                                                        sw5 = (uint32_t)48U;
                                                                        break;
                                                                      }
                                                                    case
                                                                    Spec_Hash_Definitions_SHA2_512:
                                                                      {
                                                                        sw5 = (uint32_t)64U;
                                                                        break;
                                                                      }
                                                                    default:
                                                                      {
                                                                        KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                          __FILE__,
                                                                          __LINE__);
                                                                        KRML_HOST_EXIT(253U);
                                                                      }
                                                                  }
                                                                  store32_be(uu____18, sw5);
                                                                  memcpy(uu____17,
                                                                    uu____17 + (uint32_t)2U,
                                                                    (uint32_t)2U * sizeof (uint8_t));
                                                                  {
                                                                    uint8_t
                                                                    *uu____19 = tmp4 + (uint32_t)2U;
                                                                    uu____19[0U] = (uint8_t)0x48U;
                                                                    uu____19[1U] = (uint8_t)0x50U;
                                                                    uu____19[2U] = (uint8_t)0x4bU;
                                                                    uu____19[3U] = (uint8_t)0x45U;
                                                                    uu____19[4U] = (uint8_t)0x2dU;
                                                                    uu____19[5U] = (uint8_t)0x76U;
                                                                    uu____19[6U] = (uint8_t)0x31U;
                                                                    memcpy(tmp4 + (uint32_t)9U,
                                                                      suite_id,
                                                                      (uint32_t)10U
                                                                      * sizeof (uint8_t));
                                                                    memcpy(tmp4
                                                                      + (uint32_t)9U + (uint32_t)10U,
                                                                      label_exp,
                                                                      (uint32_t)3U
                                                                      * sizeof (uint8_t));
                                                                    {
                                                                      uint8_t
                                                                      *uu____20 =
                                                                        tmp4
                                                                        +
                                                                          (uint32_t)9U
                                                                          + (uint32_t)10U
                                                                          + (uint32_t)3U;
                                                                      Spec_Agile_HPKE_ciphersuite
                                                                      lit6;
                                                                      lit6.fst =
                                                                        Spec_Agile_DH_DH_P256;
                                                                      lit6.snd =
                                                                        Spec_Hash_Definitions_SHA2_256;
                                                                      lit6.thd.tag =
                                                                        Spec_Agile_HPKE_Seal;
                                                                      lit6.thd.alg =
                                                                        Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                      lit6.f3 =
                                                                        Spec_Hash_Definitions_SHA2_256;
                                                                      {
                                                                        uint32_t sw6;
                                                                        switch
                                                                        (
                                                                          Spec_Agile_HPKE_hash_of_cs(lit6)
                                                                        )
                                                                        {
                                                                          case
                                                                          Spec_Hash_Definitions_SHA2_256:
                                                                            {
                                                                              sw6 = (uint32_t)65U;
                                                                              break;
                                                                            }
                                                                          case
                                                                          Spec_Hash_Definitions_SHA2_384:
                                                                            {
                                                                              sw6 = (uint32_t)97U;
                                                                              break;
                                                                            }
                                                                          case
                                                                          Spec_Hash_Definitions_SHA2_512:
                                                                            {
                                                                              sw6 = (uint32_t)129U;
                                                                              break;
                                                                            }
                                                                          default:
                                                                            {
                                                                              KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                __FILE__,
                                                                                __LINE__);
                                                                              KRML_HOST_EXIT(253U);
                                                                            }
                                                                        }
                                                                        memcpy(uu____20,
                                                                          o_context,
                                                                          sw6 * sizeof (uint8_t));
                                                                        {
                                                                          Spec_Agile_HPKE_ciphersuite
                                                                          lit7;
                                                                          lit7.fst =
                                                                            Spec_Agile_DH_DH_P256;
                                                                          lit7.snd =
                                                                            Spec_Hash_Definitions_SHA2_256;
                                                                          lit7.thd.tag =
                                                                            Spec_Agile_HPKE_Seal;
                                                                          lit7.thd.alg =
                                                                            Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                          lit7.f3 =
                                                                            Spec_Hash_Definitions_SHA2_256;
                                                                          {
                                                                            uint32_t sw7;
                                                                            switch
                                                                            (
                                                                              Spec_Agile_HPKE_hash_of_cs(lit7)
                                                                            )
                                                                            {
                                                                              case
                                                                              Spec_Hash_Definitions_SHA2_256:
                                                                                {
                                                                                  sw7 =
                                                                                    (uint32_t)32U;
                                                                                  break;
                                                                                }
                                                                              case
                                                                              Spec_Hash_Definitions_SHA2_384:
                                                                                {
                                                                                  sw7 =
                                                                                    (uint32_t)48U;
                                                                                  break;
                                                                                }
                                                                              case
                                                                              Spec_Hash_Definitions_SHA2_512:
                                                                                {
                                                                                  sw7 =
                                                                                    (uint32_t)64U;
                                                                                  break;
                                                                                }
                                                                              default:
                                                                                {
                                                                                  KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                    __FILE__,
                                                                                    __LINE__);
                                                                                  KRML_HOST_EXIT(253U);
                                                                                }
                                                                            }
                                                                            {
                                                                              Spec_Agile_HPKE_ciphersuite
                                                                              lit8;
                                                                              lit8.fst =
                                                                                Spec_Agile_DH_DH_P256;
                                                                              lit8.snd =
                                                                                Spec_Hash_Definitions_SHA2_256;
                                                                              lit8.thd.tag =
                                                                                Spec_Agile_HPKE_Seal;
                                                                              lit8.thd.alg =
                                                                                Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                              lit8.f3 =
                                                                                Spec_Hash_Definitions_SHA2_256;
                                                                              {
                                                                                uint32_t sw8;
                                                                                switch
                                                                                (
                                                                                  Spec_Agile_HPKE_hash_of_cs(lit8)
                                                                                )
                                                                                {
                                                                                  case
                                                                                  Spec_Hash_Definitions_SHA2_256:
                                                                                    {
                                                                                      sw8 =
                                                                                        (uint32_t)32U;
                                                                                      break;
                                                                                    }
                                                                                  case
                                                                                  Spec_Hash_Definitions_SHA2_384:
                                                                                    {
                                                                                      sw8 =
                                                                                        (uint32_t)48U;
                                                                                      break;
                                                                                    }
                                                                                  case
                                                                                  Spec_Hash_Definitions_SHA2_512:
                                                                                    {
                                                                                      sw8 =
                                                                                        (uint32_t)64U;
                                                                                      break;
                                                                                    }
                                                                                  default:
                                                                                    {
                                                                                      KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                        __FILE__,
                                                                                        __LINE__);
                                                                                      KRML_HOST_EXIT(253U);
                                                                                    }
                                                                                }
                                                                                Hacl_HKDF_expand_sha2_256(o_ctx.ctx_exporter,
                                                                                  o_secret,
                                                                                  sw7,
                                                                                  tmp4,
                                                                                  len2,
                                                                                  sw8);
                                                                                {
                                                                                  Spec_Agile_HPKE_ciphersuite
                                                                                  lit9;
                                                                                  lit9.fst =
                                                                                    Spec_Agile_DH_DH_P256;
                                                                                  lit9.snd =
                                                                                    Spec_Hash_Definitions_SHA2_256;
                                                                                  lit9.thd.tag =
                                                                                    Spec_Agile_HPKE_Seal;
                                                                                  lit9.thd.alg =
                                                                                    Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                  lit9.f3 =
                                                                                    Spec_Hash_Definitions_SHA2_256;
                                                                                  {
                                                                                    Spec_Agile_HPKE_aead
                                                                                    scrut =
                                                                                      Spec_Agile_HPKE_aead_of_cs(lit9);
                                                                                    if
                                                                                    (
                                                                                      scrut.tag
                                                                                      ==
                                                                                        Spec_Agile_HPKE_ExportOnly
                                                                                    )
                                                                                    {
                                                                                      o_ctx.ctx_seq[0U]
                                                                                      = (uint64_t)0U;
                                                                                    }
                                                                                    else
                                                                                    {
                                                                                      uint8_t
                                                                                      label_key[3U] =
                                                                                        {
                                                                                          (uint8_t)0x6bU,
                                                                                          (uint8_t)0x65U,
                                                                                          (uint8_t)0x79U
                                                                                        };
                                                                                      Spec_Agile_HPKE_ciphersuite
                                                                                      lit10;
                                                                                      lit10.fst =
                                                                                        Spec_Agile_DH_DH_P256;
                                                                                      lit10.snd =
                                                                                        Spec_Hash_Definitions_SHA2_256;
                                                                                      lit10.thd.tag
                                                                                      =
                                                                                        Spec_Agile_HPKE_Seal;
                                                                                      lit10.thd.alg
                                                                                      =
                                                                                        Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                      lit10.f3 =
                                                                                        Spec_Hash_Definitions_SHA2_256;
                                                                                      {
                                                                                        uint32_t
                                                                                        sw9;
                                                                                        switch
                                                                                        (
                                                                                          Spec_Agile_HPKE_hash_of_cs(lit10)
                                                                                        )
                                                                                        {
                                                                                          case
                                                                                          Spec_Hash_Definitions_SHA2_256:
                                                                                            {
                                                                                              sw9 =
                                                                                                (uint32_t)65U;
                                                                                              break;
                                                                                            }
                                                                                          case
                                                                                          Spec_Hash_Definitions_SHA2_384:
                                                                                            {
                                                                                              sw9 =
                                                                                                (uint32_t)97U;
                                                                                              break;
                                                                                            }
                                                                                          case
                                                                                          Spec_Hash_Definitions_SHA2_512:
                                                                                            {
                                                                                              sw9 =
                                                                                                (uint32_t)129U;
                                                                                              break;
                                                                                            }
                                                                                          default:
                                                                                            {
                                                                                              KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                                __FILE__,
                                                                                                __LINE__);
                                                                                              KRML_HOST_EXIT(253U);
                                                                                            }
                                                                                        }
                                                                                        {
                                                                                          uint32_t
                                                                                          len3 =
                                                                                            (uint32_t)9U
                                                                                            +
                                                                                              (uint32_t)10U
                                                                                            +
                                                                                              (uint32_t)3U
                                                                                            + sw9;
                                                                                          KRML_CHECK_SIZE(sizeof (
                                                                                              uint8_t
                                                                                            ),
                                                                                            len3);
                                                                                          {
                                                                                            uint8_t
                                                                                            tmp5[len3];
                                                                                            memset(tmp5,
                                                                                              0U,
                                                                                              len3
                                                                                              *
                                                                                                sizeof (
                                                                                                  uint8_t
                                                                                                ));
                                                                                            {
                                                                                              uint8_t
                                                                                              *uu____21 =
                                                                                                tmp5;
                                                                                              uint8_t
                                                                                              *uu____22 =
                                                                                                uu____21;
                                                                                              Spec_Agile_HPKE_ciphersuite
                                                                                              lit11;
                                                                                              lit11.fst
                                                                                              =
                                                                                                Spec_Agile_DH_DH_P256;
                                                                                              lit11.snd
                                                                                              =
                                                                                                Spec_Hash_Definitions_SHA2_256;
                                                                                              lit11.thd.tag
                                                                                              =
                                                                                                Spec_Agile_HPKE_Seal;
                                                                                              lit11.thd.alg
                                                                                              =
                                                                                                Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                              lit11.f3
                                                                                              =
                                                                                                Spec_Hash_Definitions_SHA2_256;
                                                                                              {
                                                                                                Spec_Agile_HPKE_aead
                                                                                                scrut0 =
                                                                                                  Spec_Agile_HPKE_aead_of_cs(lit11);
                                                                                                uint32_t
                                                                                                ite1;
                                                                                                if
                                                                                                (
                                                                                                  scrut0.tag
                                                                                                  ==
                                                                                                    Spec_Agile_HPKE_ExportOnly
                                                                                                )
                                                                                                {
                                                                                                  ite1
                                                                                                  =
                                                                                                    (uint32_t)0U;
                                                                                                }
                                                                                                else if
                                                                                                (
                                                                                                  scrut0.tag
                                                                                                  ==
                                                                                                    Spec_Agile_HPKE_Seal
                                                                                                  &&
                                                                                                    scrut0.alg
                                                                                                    ==
                                                                                                      Spec_Agile_AEAD_AES128_GCM
                                                                                                )
                                                                                                {
                                                                                                  ite1
                                                                                                  =
                                                                                                    (uint32_t)16U;
                                                                                                }
                                                                                                else if
                                                                                                (
                                                                                                  scrut0.tag
                                                                                                  ==
                                                                                                    Spec_Agile_HPKE_Seal
                                                                                                  &&
                                                                                                    scrut0.alg
                                                                                                    ==
                                                                                                      Spec_Agile_AEAD_AES256_GCM
                                                                                                )
                                                                                                {
                                                                                                  ite1
                                                                                                  =
                                                                                                    (uint32_t)32U;
                                                                                                }
                                                                                                else if
                                                                                                (
                                                                                                  scrut0.tag
                                                                                                  ==
                                                                                                    Spec_Agile_HPKE_Seal
                                                                                                  &&
                                                                                                    scrut0.alg
                                                                                                    ==
                                                                                                      Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                                                )
                                                                                                {
                                                                                                  ite1
                                                                                                  =
                                                                                                    (uint32_t)32U;
                                                                                                }
                                                                                                else
                                                                                                {
                                                                                                  ite1
                                                                                                  =
                                                                                                    KRML_EABORT(uint32_t,
                                                                                                      "unreachable (pattern matches are exhaustive in F*)");
                                                                                                }
                                                                                                store32_be(uu____22,
                                                                                                  ite1);
                                                                                                memcpy(uu____21,
                                                                                                  uu____21
                                                                                                  +
                                                                                                    (uint32_t)2U,
                                                                                                  (uint32_t)2U
                                                                                                  *
                                                                                                    sizeof (
                                                                                                      uint8_t
                                                                                                    ));
                                                                                                {
                                                                                                  uint8_t
                                                                                                  *uu____23 =
                                                                                                    tmp5
                                                                                                    +
                                                                                                      (uint32_t)2U;
                                                                                                  uu____23[0U]
                                                                                                  =
                                                                                                    (uint8_t)0x48U;
                                                                                                  uu____23[1U]
                                                                                                  =
                                                                                                    (uint8_t)0x50U;
                                                                                                  uu____23[2U]
                                                                                                  =
                                                                                                    (uint8_t)0x4bU;
                                                                                                  uu____23[3U]
                                                                                                  =
                                                                                                    (uint8_t)0x45U;
                                                                                                  uu____23[4U]
                                                                                                  =
                                                                                                    (uint8_t)0x2dU;
                                                                                                  uu____23[5U]
                                                                                                  =
                                                                                                    (uint8_t)0x76U;
                                                                                                  uu____23[6U]
                                                                                                  =
                                                                                                    (uint8_t)0x31U;
                                                                                                  memcpy(tmp5
                                                                                                    +
                                                                                                      (uint32_t)9U,
                                                                                                    suite_id,
                                                                                                    (uint32_t)10U
                                                                                                    *
                                                                                                      sizeof (
                                                                                                        uint8_t
                                                                                                      ));
                                                                                                  memcpy(tmp5
                                                                                                    +
                                                                                                      (uint32_t)9U
                                                                                                      +
                                                                                                        (uint32_t)10U,
                                                                                                    label_key,
                                                                                                    (uint32_t)3U
                                                                                                    *
                                                                                                      sizeof (
                                                                                                        uint8_t
                                                                                                      ));
                                                                                                  {
                                                                                                    uint8_t
                                                                                                    *uu____24 =
                                                                                                      tmp5
                                                                                                      +
                                                                                                        (uint32_t)9U
                                                                                                        +
                                                                                                          (uint32_t)10U
                                                                                                        +
                                                                                                          (uint32_t)3U;
                                                                                                    Spec_Agile_HPKE_ciphersuite
                                                                                                    lit12;
                                                                                                    lit12.fst
                                                                                                    =
                                                                                                      Spec_Agile_DH_DH_P256;
                                                                                                    lit12.snd
                                                                                                    =
                                                                                                      Spec_Hash_Definitions_SHA2_256;
                                                                                                    lit12.thd.tag
                                                                                                    =
                                                                                                      Spec_Agile_HPKE_Seal;
                                                                                                    lit12.thd.alg
                                                                                                    =
                                                                                                      Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                                    lit12.f3
                                                                                                    =
                                                                                                      Spec_Hash_Definitions_SHA2_256;
                                                                                                    {
                                                                                                      uint32_t
                                                                                                      sw10;
                                                                                                      switch
                                                                                                      (
                                                                                                        Spec_Agile_HPKE_hash_of_cs(lit12)
                                                                                                      )
                                                                                                      {
                                                                                                        case
                                                                                                        Spec_Hash_Definitions_SHA2_256:
                                                                                                          {
                                                                                                            sw10
                                                                                                            =
                                                                                                              (uint32_t)65U;
                                                                                                            break;
                                                                                                          }
                                                                                                        case
                                                                                                        Spec_Hash_Definitions_SHA2_384:
                                                                                                          {
                                                                                                            sw10
                                                                                                            =
                                                                                                              (uint32_t)97U;
                                                                                                            break;
                                                                                                          }
                                                                                                        case
                                                                                                        Spec_Hash_Definitions_SHA2_512:
                                                                                                          {
                                                                                                            sw10
                                                                                                            =
                                                                                                              (uint32_t)129U;
                                                                                                            break;
                                                                                                          }
                                                                                                        default:
                                                                                                          {
                                                                                                            KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                                              __FILE__,
                                                                                                              __LINE__);
                                                                                                            KRML_HOST_EXIT(253U);
                                                                                                          }
                                                                                                      }
                                                                                                      memcpy(uu____24,
                                                                                                        o_context,
                                                                                                        sw10
                                                                                                        *
                                                                                                          sizeof (
                                                                                                            uint8_t
                                                                                                          ));
                                                                                                      {
                                                                                                        Spec_Agile_HPKE_ciphersuite
                                                                                                        lit13;
                                                                                                        lit13.fst
                                                                                                        =
                                                                                                          Spec_Agile_DH_DH_P256;
                                                                                                        lit13.snd
                                                                                                        =
                                                                                                          Spec_Hash_Definitions_SHA2_256;
                                                                                                        lit13.thd.tag
                                                                                                        =
                                                                                                          Spec_Agile_HPKE_Seal;
                                                                                                        lit13.thd.alg
                                                                                                        =
                                                                                                          Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                                        lit13.f3
                                                                                                        =
                                                                                                          Spec_Hash_Definitions_SHA2_256;
                                                                                                        {
                                                                                                          uint32_t
                                                                                                          sw11;
                                                                                                          switch
                                                                                                          (
                                                                                                            Spec_Agile_HPKE_hash_of_cs(lit13)
                                                                                                          )
                                                                                                          {
                                                                                                            case
                                                                                                            Spec_Hash_Definitions_SHA2_256:
                                                                                                              {
                                                                                                                sw11
                                                                                                                =
                                                                                                                  (uint32_t)32U;
                                                                                                                break;
                                                                                                              }
                                                                                                            case
                                                                                                            Spec_Hash_Definitions_SHA2_384:
                                                                                                              {
                                                                                                                sw11
                                                                                                                =
                                                                                                                  (uint32_t)48U;
                                                                                                                break;
                                                                                                              }
                                                                                                            case
                                                                                                            Spec_Hash_Definitions_SHA2_512:
                                                                                                              {
                                                                                                                sw11
                                                                                                                =
                                                                                                                  (uint32_t)64U;
                                                                                                                break;
                                                                                                              }
                                                                                                            default:
                                                                                                              {
                                                                                                                KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                                                  __FILE__,
                                                                                                                  __LINE__);
                                                                                                                KRML_HOST_EXIT(253U);
                                                                                                              }
                                                                                                          }
                                                                                                          {
                                                                                                            Spec_Agile_HPKE_ciphersuite
                                                                                                            lit14;
                                                                                                            lit14.fst
                                                                                                            =
                                                                                                              Spec_Agile_DH_DH_P256;
                                                                                                            lit14.snd
                                                                                                            =
                                                                                                              Spec_Hash_Definitions_SHA2_256;
                                                                                                            lit14.thd.tag
                                                                                                            =
                                                                                                              Spec_Agile_HPKE_Seal;
                                                                                                            lit14.thd.alg
                                                                                                            =
                                                                                                              Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                                            lit14.f3
                                                                                                            =
                                                                                                              Spec_Hash_Definitions_SHA2_256;
                                                                                                            {
                                                                                                              Spec_Agile_HPKE_aead
                                                                                                              scrut1 =
                                                                                                                Spec_Agile_HPKE_aead_of_cs(lit14);
                                                                                                              uint32_t
                                                                                                              ite2;
                                                                                                              if
                                                                                                              (
                                                                                                                scrut1.tag
                                                                                                                ==
                                                                                                                  Spec_Agile_HPKE_ExportOnly
                                                                                                              )
                                                                                                              {
                                                                                                                ite2
                                                                                                                =
                                                                                                                  (uint32_t)0U;
                                                                                                              }
                                                                                                              else if
                                                                                                              (
                                                                                                                scrut1.tag
                                                                                                                ==
                                                                                                                  Spec_Agile_HPKE_Seal
                                                                                                                &&
                                                                                                                  scrut1.alg
                                                                                                                  ==
                                                                                                                    Spec_Agile_AEAD_AES128_GCM
                                                                                                              )
                                                                                                              {
                                                                                                                ite2
                                                                                                                =
                                                                                                                  (uint32_t)16U;
                                                                                                              }
                                                                                                              else if
                                                                                                              (
                                                                                                                scrut1.tag
                                                                                                                ==
                                                                                                                  Spec_Agile_HPKE_Seal
                                                                                                                &&
                                                                                                                  scrut1.alg
                                                                                                                  ==
                                                                                                                    Spec_Agile_AEAD_AES256_GCM
                                                                                                              )
                                                                                                              {
                                                                                                                ite2
                                                                                                                =
                                                                                                                  (uint32_t)32U;
                                                                                                              }
                                                                                                              else if
                                                                                                              (
                                                                                                                scrut1.tag
                                                                                                                ==
                                                                                                                  Spec_Agile_HPKE_Seal
                                                                                                                &&
                                                                                                                  scrut1.alg
                                                                                                                  ==
                                                                                                                    Spec_Agile_AEAD_CHACHA20_POLY1305
                                                                                                              )
                                                                                                              {
                                                                                                                ite2
                                                                                                                =
                                                                                                                  (uint32_t)32U;
                                                                                                              }
                                                                                                              else
                                                                                                              {
                                                                                                                ite2
                                                                                                                =
                                                                                                                  KRML_EABORT(uint32_t,
                                                                                                                    "unreachable (pattern matches are exhaustive in F*)");
                                                                                                              }
                                                                                                              Hacl_HKDF_expand_sha2_256(o_ctx.ctx_key,
                                                                                                                o_secret,
                                                                                                                sw11,
                                                                                                                tmp5,
                                                                                                                len3,
                                                                                                                ite2);
                                                                                                              {
                                                                                                                uint8_t
                                                                                                                label_base_nonce[10U] =
                                                                                                                  {
                                                                                                                    (uint8_t)0x62U,
                                                                                                                    (uint8_t)0x61U,
                                                                                                                    (uint8_t)0x73U,
                                                                                                                    (uint8_t)0x65U,
                                                                                                                    (uint8_t)0x5fU,
                                                                                                                    (uint8_t)0x6eU,
                                                                                                                    (uint8_t)0x6fU,
                                                                                                                    (uint8_t)0x6eU,
                                                                                                                    (uint8_t)0x63U,
                                                                                                                    (uint8_t)0x65U
                                                                                                                  };
                                                                                                                Spec_Agile_HPKE_ciphersuite
                                                                                                                lit15;
                                                                                                                lit15.fst
                                                                                                                =
                                                                                                                  Spec_Agile_DH_DH_P256;
                                                                                                                lit15.snd
                                                                                                                =
                                                                                                                  Spec_Hash_Definitions_SHA2_256;
                                                                                                                lit15.thd.tag
                                                                                                                =
                                                                                                                  Spec_Agile_HPKE_Seal;
                                                                                                                lit15.thd.alg
                                                                                                                =
                                                                                                                  Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                                                lit15.f3
                                                                                                                =
                                                                                                                  Spec_Hash_Definitions_SHA2_256;
                                                                                                                {
                                                                                                                  uint32_t
                                                                                                                  sw12;
                                                                                                                  switch
                                                                                                                  (
                                                                                                                    Spec_Agile_HPKE_hash_of_cs(lit15)
                                                                                                                  )
                                                                                                                  {
                                                                                                                    case
                                                                                                                    Spec_Hash_Definitions_SHA2_256:
                                                                                                                      {
                                                                                                                        sw12
                                                                                                                        =
                                                                                                                          (uint32_t)65U;
                                                                                                                        break;
                                                                                                                      }
                                                                                                                    case
                                                                                                                    Spec_Hash_Definitions_SHA2_384:
                                                                                                                      {
                                                                                                                        sw12
                                                                                                                        =
                                                                                                                          (uint32_t)97U;
                                                                                                                        break;
                                                                                                                      }
                                                                                                                    case
                                                                                                                    Spec_Hash_Definitions_SHA2_512:
                                                                                                                      {
                                                                                                                        sw12
                                                                                                                        =
                                                                                                                          (uint32_t)129U;
                                                                                                                        break;
                                                                                                                      }
                                                                                                                    default:
                                                                                                                      {
                                                                                                                        KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                                                          __FILE__,
                                                                                                                          __LINE__);
                                                                                                                        KRML_HOST_EXIT(253U);
                                                                                                                      }
                                                                                                                  }
                                                                                                                  {
                                                                                                                    uint32_t
                                                                                                                    len4 =
                                                                                                                      (uint32_t)9U
                                                                                                                      +
                                                                                                                        (uint32_t)10U
                                                                                                                      +
                                                                                                                        (uint32_t)10U
                                                                                                                      +
                                                                                                                        sw12;
                                                                                                                    KRML_CHECK_SIZE(sizeof (
                                                                                                                        uint8_t
                                                                                                                      ),
                                                                                                                      len4);
                                                                                                                    {
                                                                                                                      uint8_t
                                                                                                                      tmp[len4];
                                                                                                                      memset(tmp,
                                                                                                                        0U,
                                                                                                                        len4
                                                                                                                        *
                                                                                                                          sizeof (
                                                                                                                            uint8_t
                                                                                                                          ));
                                                                                                                      {
                                                                                                                        uint8_t
                                                                                                                        *uu____25 =
                                                                                                                          tmp;
                                                                                                                        uint8_t
                                                                                                                        *uu____26 =
                                                                                                                          uu____25;
                                                                                                                        Spec_Agile_HPKE_ciphersuite
                                                                                                                        lit16;
                                                                                                                        lit16.fst
                                                                                                                        =
                                                                                                                          Spec_Agile_DH_DH_P256;
                                                                                                                        lit16.snd
                                                                                                                        =
                                                                                                                          Spec_Hash_Definitions_SHA2_256;
                                                                                                                        lit16.thd.tag
                                                                                                                        =
                                                                                                                          Spec_Agile_HPKE_Seal;
                                                                                                                        lit16.thd.alg
                                                                                                                        =
                                                                                                                          Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                                                        lit16.f3
                                                                                                                        =
                                                                                                                          Spec_Hash_Definitions_SHA2_256;
                                                                                                                        {
                                                                                                                          Spec_Agile_HPKE_aead
                                                                                                                          scrut2 =
                                                                                                                            Spec_Agile_HPKE_aead_of_cs(lit16);
                                                                                                                          uint32_t
                                                                                                                          ite3;
                                                                                                                          if
                                                                                                                          (
                                                                                                                            scrut2.tag
                                                                                                                            ==
                                                                                                                              Spec_Agile_HPKE_ExportOnly
                                                                                                                          )
                                                                                                                          {
                                                                                                                            ite3
                                                                                                                            =
                                                                                                                              (uint32_t)0U;
                                                                                                                          }
                                                                                                                          else if
                                                                                                                          (
                                                                                                                            scrut2.tag
                                                                                                                            ==
                                                                                                                              Spec_Agile_HPKE_Seal
                                                                                                                          )
                                                                                                                          {
                                                                                                                            ite3
                                                                                                                            =
                                                                                                                              (uint32_t)12U;
                                                                                                                          }
                                                                                                                          else
                                                                                                                          {
                                                                                                                            ite3
                                                                                                                            =
                                                                                                                              KRML_EABORT(uint32_t,
                                                                                                                                "unreachable (pattern matches are exhaustive in F*)");
                                                                                                                          }
                                                                                                                          store32_be(uu____26,
                                                                                                                            ite3);
                                                                                                                          memcpy(uu____25,
                                                                                                                            uu____25
                                                                                                                            +
                                                                                                                              (uint32_t)2U,
                                                                                                                            (uint32_t)2U
                                                                                                                            *
                                                                                                                              sizeof (
                                                                                                                                uint8_t
                                                                                                                              ));
                                                                                                                          {
                                                                                                                            uint8_t
                                                                                                                            *uu____27 =
                                                                                                                              tmp
                                                                                                                              +
                                                                                                                                (uint32_t)2U;
                                                                                                                            uu____27[0U]
                                                                                                                            =
                                                                                                                              (uint8_t)0x48U;
                                                                                                                            uu____27[1U]
                                                                                                                            =
                                                                                                                              (uint8_t)0x50U;
                                                                                                                            uu____27[2U]
                                                                                                                            =
                                                                                                                              (uint8_t)0x4bU;
                                                                                                                            uu____27[3U]
                                                                                                                            =
                                                                                                                              (uint8_t)0x45U;
                                                                                                                            uu____27[4U]
                                                                                                                            =
                                                                                                                              (uint8_t)0x2dU;
                                                                                                                            uu____27[5U]
                                                                                                                            =
                                                                                                                              (uint8_t)0x76U;
                                                                                                                            uu____27[6U]
                                                                                                                            =
                                                                                                                              (uint8_t)0x31U;
                                                                                                                            memcpy(tmp
                                                                                                                              +
                                                                                                                                (uint32_t)9U,
                                                                                                                              suite_id,
                                                                                                                              (uint32_t)10U
                                                                                                                              *
                                                                                                                                sizeof (
                                                                                                                                  uint8_t
                                                                                                                                ));
                                                                                                                            memcpy(tmp
                                                                                                                              +
                                                                                                                                (uint32_t)9U
                                                                                                                                +
                                                                                                                                  (uint32_t)10U,
                                                                                                                              label_base_nonce,
                                                                                                                              (uint32_t)10U
                                                                                                                              *
                                                                                                                                sizeof (
                                                                                                                                  uint8_t
                                                                                                                                ));
                                                                                                                            {
                                                                                                                              uint8_t
                                                                                                                              *uu____28 =
                                                                                                                                tmp
                                                                                                                                +
                                                                                                                                  (uint32_t)9U
                                                                                                                                  +
                                                                                                                                    (uint32_t)10U
                                                                                                                                  +
                                                                                                                                    (uint32_t)10U;
                                                                                                                              Spec_Agile_HPKE_ciphersuite
                                                                                                                              lit17;
                                                                                                                              lit17.fst
                                                                                                                              =
                                                                                                                                Spec_Agile_DH_DH_P256;
                                                                                                                              lit17.snd
                                                                                                                              =
                                                                                                                                Spec_Hash_Definitions_SHA2_256;
                                                                                                                              lit17.thd.tag
                                                                                                                              =
                                                                                                                                Spec_Agile_HPKE_Seal;
                                                                                                                              lit17.thd.alg
                                                                                                                              =
                                                                                                                                Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                                                              lit17.f3
                                                                                                                              =
                                                                                                                                Spec_Hash_Definitions_SHA2_256;
                                                                                                                              {
                                                                                                                                uint32_t
                                                                                                                                sw13;
                                                                                                                                switch
                                                                                                                                (
                                                                                                                                  Spec_Agile_HPKE_hash_of_cs(lit17)
                                                                                                                                )
                                                                                                                                {
                                                                                                                                  case
                                                                                                                                  Spec_Hash_Definitions_SHA2_256:
                                                                                                                                    {
                                                                                                                                      sw13
                                                                                                                                      =
                                                                                                                                        (uint32_t)65U;
                                                                                                                                      break;
                                                                                                                                    }
                                                                                                                                  case
                                                                                                                                  Spec_Hash_Definitions_SHA2_384:
                                                                                                                                    {
                                                                                                                                      sw13
                                                                                                                                      =
                                                                                                                                        (uint32_t)97U;
                                                                                                                                      break;
                                                                                                                                    }
                                                                                                                                  case
                                                                                                                                  Spec_Hash_Definitions_SHA2_512:
                                                                                                                                    {
                                                                                                                                      sw13
                                                                                                                                      =
                                                                                                                                        (uint32_t)129U;
                                                                                                                                      break;
                                                                                                                                    }
                                                                                                                                  default:
                                                                                                                                    {
                                                                                                                                      KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                                                                        __FILE__,
                                                                                                                                        __LINE__);
                                                                                                                                      KRML_HOST_EXIT(253U);
                                                                                                                                    }
                                                                                                                                }
                                                                                                                                memcpy(uu____28,
                                                                                                                                  o_context,
                                                                                                                                  sw13
                                                                                                                                  *
                                                                                                                                    sizeof (
                                                                                                                                      uint8_t
                                                                                                                                    ));
                                                                                                                                {
                                                                                                                                  Spec_Agile_HPKE_ciphersuite
                                                                                                                                  lit18;
                                                                                                                                  lit18.fst
                                                                                                                                  =
                                                                                                                                    Spec_Agile_DH_DH_P256;
                                                                                                                                  lit18.snd
                                                                                                                                  =
                                                                                                                                    Spec_Hash_Definitions_SHA2_256;
                                                                                                                                  lit18.thd.tag
                                                                                                                                  =
                                                                                                                                    Spec_Agile_HPKE_Seal;
                                                                                                                                  lit18.thd.alg
                                                                                                                                  =
                                                                                                                                    Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                                                                  lit18.f3
                                                                                                                                  =
                                                                                                                                    Spec_Hash_Definitions_SHA2_256;
                                                                                                                                  {
                                                                                                                                    uint32_t
                                                                                                                                    sw;
                                                                                                                                    switch
                                                                                                                                    (
                                                                                                                                      Spec_Agile_HPKE_hash_of_cs(lit18)
                                                                                                                                    )
                                                                                                                                    {
                                                                                                                                      case
                                                                                                                                      Spec_Hash_Definitions_SHA2_256:
                                                                                                                                        {
                                                                                                                                          sw
                                                                                                                                          =
                                                                                                                                            (uint32_t)32U;
                                                                                                                                          break;
                                                                                                                                        }
                                                                                                                                      case
                                                                                                                                      Spec_Hash_Definitions_SHA2_384:
                                                                                                                                        {
                                                                                                                                          sw
                                                                                                                                          =
                                                                                                                                            (uint32_t)48U;
                                                                                                                                          break;
                                                                                                                                        }
                                                                                                                                      case
                                                                                                                                      Spec_Hash_Definitions_SHA2_512:
                                                                                                                                        {
                                                                                                                                          sw
                                                                                                                                          =
                                                                                                                                            (uint32_t)64U;
                                                                                                                                          break;
                                                                                                                                        }
                                                                                                                                      default:
                                                                                                                                        {
                                                                                                                                          KRML_HOST_PRINTF("KaRaMeL incomplete match at %s:%d\n",
                                                                                                                                            __FILE__,
                                                                                                                                            __LINE__);
                                                                                                                                          KRML_HOST_EXIT(253U);
                                                                                                                                        }
                                                                                                                                    }
                                                                                                                                    {
                                                                                                                                      Spec_Agile_HPKE_ciphersuite
                                                                                                                                      lit;
                                                                                                                                      lit.fst
                                                                                                                                      =
                                                                                                                                        Spec_Agile_DH_DH_P256;
                                                                                                                                      lit.snd
                                                                                                                                      =
                                                                                                                                        Spec_Hash_Definitions_SHA2_256;
                                                                                                                                      lit.thd.tag
                                                                                                                                      =
                                                                                                                                        Spec_Agile_HPKE_Seal;
                                                                                                                                      lit.thd.alg
                                                                                                                                      =
                                                                                                                                        Spec_Agile_AEAD_CHACHA20_POLY1305;
                                                                                                                                      lit.f3
                                                                                                                                      =
                                                                                                                                        Spec_Hash_Definitions_SHA2_256;
                                                                                                                                      {
                                                                                                                                        Spec_Agile_HPKE_aead
                                                                                                                                        scrut3 =
                                                                                                                                          Spec_Agile_HPKE_aead_of_cs(lit);
                                                                                                                                        uint32_t
                                                                                                                                        ite;
                                                                                                                                        if
                                                                                                                                        (
                                                                                                                                          scrut3.tag
                                                                                                                                          ==
                                                                                                                                            Spec_Agile_HPKE_ExportOnly
                                                                                                                                        )
                                                                                                                                        {
                                                                                                                                          ite
                                                                                                                                          =
                                                                                                                                            (uint32_t)0U;
                                                                                                                                        }
                                                                                                                                        else if
                                                                                                                                        (
                                                                                                                                          scrut3.tag
                                                                                                                                          ==
                                                                                                                                            Spec_Agile_HPKE_Seal
                                                                                                                                        )
                                                                                                                                        {
                                                                                                                                          ite
                                                                                                                                          =
                                                                                                                                            (uint32_t)12U;
                                                                                                                                        }
                                                                                                                                        else
                                                                                                                                        {
                                                                                                                                          ite
                                                                                                                                          =
                                                                                                                                            KRML_EABORT(uint32_t,
                                                                                                                                              "unreachable (pattern matches are exhaustive in F*)");
                                                                                                                                        }
                                                                                                                                        Hacl_HKDF_expand_sha2_256(o_ctx.ctx_nonce,
                                                                                                                                          o_secret,
                                                                                                                                          sw,
                                                                                                                                          tmp,
                                                                                                                                          len4,
                                                                                                                                          ite);
                                                                                                                                        o_ctx.ctx_seq[0U]
                                                                                                                                        =
                                                                                                                                          (uint64_t)0U;
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
                                                                                    ite0 =
                                                                                      (uint32_t)0U;
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
            {
              ite0 = (uint32_t)1U;
            }
          }
        }
      }
    }
  }
  else
  {
    ite0 = (uint32_t)1U;
  }
  return ite0;
}

uint32_t
Hacl_HPKE_P256_CP128_SHA256_sealBase(
  uint8_t *skE,
  uint8_t *pkR,
  uint32_t infolen,
  uint8_t *info,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t plainlen,
  uint8_t *plain,
  uint8_t *o_enc,
  uint8_t *o_ct
)
{
  uint8_t ctx_key[32U] = { 0U };
  uint8_t ctx_nonce[12U] = { 0U };
  uint64_t ctx_seq = (uint64_t)0U;
  uint8_t ctx_exporter[32U] = { 0U };
  Hacl_Impl_HPKE_context_s o_ctx;
  uint32_t res;
  uint32_t ite;
  o_ctx.ctx_key = ctx_key;
  o_ctx.ctx_nonce = ctx_nonce;
  o_ctx.ctx_seq = &ctx_seq;
  o_ctx.ctx_exporter = ctx_exporter;
  res = Hacl_HPKE_P256_CP128_SHA256_setupBaseS(o_enc, o_ctx, skE, pkR, infolen, info);
  if (res == (uint32_t)0U)
  {
    uint8_t nonce[12U] = { 0U };
    uint64_t s = o_ctx.ctx_seq[0U];
    uint8_t enc[12U] = { 0U };
    store64_be(enc + (uint32_t)4U, s);
    {
      uint32_t i;
      for (i = (uint32_t)0U; i < (uint32_t)12U; i++)
      {
        uint8_t xi = enc[i];
        uint8_t yi = o_ctx.ctx_nonce[i];
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
      uint64_t s1 = o_ctx.ctx_seq[0U];
      uint32_t res1;
      if (s1 == (uint64_t)18446744073709551615U)
      {
        res1 = (uint32_t)1U;
      }
      else
      {
        uint64_t s_ = s1 + (uint64_t)1U;
        o_ctx.ctx_seq[0U] = s_;
        res1 = (uint32_t)0U;
      }
      {
        uint32_t res10 = res1;
        ite = res10;
      }
    }
  }
  else
  {
    ite = (uint32_t)1U;
  }
  return ite;
}

uint32_t
Hacl_HPKE_P256_CP128_SHA256_openBase(
  uint8_t *pkE,
  uint8_t *skR,
  uint32_t infolen,
  uint8_t *info,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t ctlen,
  uint8_t *ct,
  uint8_t *o_pt
)
{
  uint8_t ctx_key[32U] = { 0U };
  uint8_t ctx_nonce[12U] = { 0U };
  uint64_t ctx_seq = (uint64_t)0U;
  uint8_t ctx_exporter[32U] = { 0U };
  Hacl_Impl_HPKE_context_s o_ctx;
  uint32_t res;
  uint32_t ite;
  o_ctx.ctx_key = ctx_key;
  o_ctx.ctx_nonce = ctx_nonce;
  o_ctx.ctx_seq = &ctx_seq;
  o_ctx.ctx_exporter = ctx_exporter;
  res = Hacl_HPKE_P256_CP128_SHA256_setupBaseR(o_ctx, pkE, skR, infolen, info);
  if (res == (uint32_t)0U)
  {
    uint8_t nonce[12U] = { 0U };
    uint64_t s = o_ctx.ctx_seq[0U];
    uint8_t enc[12U] = { 0U };
    store64_be(enc + (uint32_t)4U, s);
    {
      uint32_t i;
      for (i = (uint32_t)0U; i < (uint32_t)12U; i++)
      {
        uint8_t xi = enc[i];
        uint8_t yi = o_ctx.ctx_nonce[i];
        nonce[i] = xi ^ yi;
      }
    }
    {
      uint32_t
      res10 =
        Hacl_Chacha20Poly1305_128_aead_decrypt(o_ctx.ctx_key,
          nonce,
          aadlen,
          aad,
          ctlen - (uint32_t)16U,
          o_pt,
          ct,
          ct + ctlen - (uint32_t)16U);
      uint32_t res1;
      if (res10 == (uint32_t)0U)
      {
        uint64_t s1 = o_ctx.ctx_seq[0U];
        uint32_t res2;
        if (s1 == (uint64_t)18446744073709551615U)
        {
          res2 = (uint32_t)1U;
        }
        else
        {
          uint64_t s_ = s1 + (uint64_t)1U;
          o_ctx.ctx_seq[0U] = s_;
          res2 = (uint32_t)0U;
        }
        res1 = res2;
      }
      else
      {
        res1 = (uint32_t)1U;
      }
      ite = res1;
    }
  }
  else
  {
    ite = (uint32_t)1U;
  }
  return ite;
}

