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


#include "Hacl_HPKE_Curve64_CP128_SHA512.h"

#include "internal/Hacl_Spec.h"
#include "internal/Hacl_Krmllib.h"

uint32_t
Hacl_HPKE_Curve64_CP128_SHA512_setupBaseS(
  uint8_t *o_pkE,
  Hacl_Impl_HPKE_context_s o_ctx,
  uint8_t *skE,
  uint8_t *pkR,
  uint32_t infolen,
  uint8_t *info
)
{
  uint8_t o_shared[32U] = { 0U };
  uint8_t *o_pkE1 = o_pkE;
  Hacl_Curve25519_64_secret_to_public(o_pkE1, skE);
  uint32_t res1 = (uint32_t)0U;
  uint32_t res0;
  if (res1 == (uint32_t)0U)
  {
    uint8_t o_dh[32U] = { 0U };
    uint8_t zeros[32U] = { 0U };
    Hacl_Curve25519_64_scalarmult(o_dh, skE, pkR);
    uint8_t res2 = (uint8_t)255U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
    {
      uint8_t uu____0 = FStar_UInt8_eq_mask(o_dh[i], zeros[i]);
      res2 = uu____0 & res2;
    }
    uint8_t z = res2;
    uint32_t res;
    if (z == (uint8_t)255U)
    {
      res = (uint32_t)1U;
    }
    else
    {
      res = (uint32_t)0U;
    }
    uint32_t res20 = res;
    uint8_t o_kemcontext[64U];
    if (res20 == (uint32_t)0U)
    {
      uint8_t init = (uint8_t)0U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
      {
        o_kemcontext[i] = init;
      }
      uint8_t *uu____1 = o_kemcontext;
      uint32_t sw0;
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
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      memcpy(uu____1, o_pkE, sw0 * sizeof (uint8_t));
      uint32_t sw1;
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
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      uint8_t *o_pkRm = o_kemcontext + sw1;
      uint8_t *o_pkR = o_pkRm;
      uint32_t sw2;
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
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      memcpy(o_pkR, pkR, sw2 * sizeof (uint8_t));
      uint8_t *o_dhm = o_dh;
      uint8_t o_eae_prk[32U] = { 0U };
      uint8_t suite_id_kem[5U] = { 0U };
      uint8_t *uu____2 = suite_id_kem;
      uu____2[0U] = (uint8_t)0x4bU;
      uu____2[1U] = (uint8_t)0x45U;
      uu____2[2U] = (uint8_t)0x4dU;
      uint8_t *uu____3 = suite_id_kem + (uint32_t)3U;
      uu____3[0U] = (uint8_t)0U;
      uu____3[1U] = (uint8_t)32U;
      uint8_t *empty = suite_id_kem;
      uint8_t
      label_eae_prk[7U] =
        {
          (uint8_t)0x65U, (uint8_t)0x61U, (uint8_t)0x65U, (uint8_t)0x5fU, (uint8_t)0x70U,
          (uint8_t)0x72U, (uint8_t)0x6bU
        };
      uint32_t len = (uint32_t)7U + (uint32_t)5U + (uint32_t)7U + (uint32_t)32U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len);
      uint8_t *tmp0 = alloca(len * sizeof (uint8_t));
      memset(tmp0, 0U, len * sizeof (uint8_t));
      uint8_t *uu____4 = tmp0;
      uu____4[0U] = (uint8_t)0x48U;
      uu____4[1U] = (uint8_t)0x50U;
      uu____4[2U] = (uint8_t)0x4bU;
      uu____4[3U] = (uint8_t)0x45U;
      uu____4[4U] = (uint8_t)0x2dU;
      uu____4[5U] = (uint8_t)0x76U;
      uu____4[6U] = (uint8_t)0x31U;
      memcpy(tmp0 + (uint32_t)7U, suite_id_kem, (uint32_t)5U * sizeof (uint8_t));
      memcpy(tmp0 + (uint32_t)7U + (uint32_t)5U, label_eae_prk, (uint32_t)7U * sizeof (uint8_t));
      memcpy(tmp0 + (uint32_t)7U + (uint32_t)5U + (uint32_t)7U,
        o_dhm,
        (uint32_t)32U * sizeof (uint8_t));
      Hacl_HKDF_extract_sha2_256(o_eae_prk, empty, (uint32_t)0U, tmp0, len);
      uint8_t
      label_shared_secret[13U] =
        {
          (uint8_t)0x73U, (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x72U, (uint8_t)0x65U,
          (uint8_t)0x64U, (uint8_t)0x5fU, (uint8_t)0x73U, (uint8_t)0x65U, (uint8_t)0x63U,
          (uint8_t)0x72U, (uint8_t)0x65U, (uint8_t)0x74U
        };
      uint32_t sw3;
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
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      uint32_t len0 = (uint32_t)9U + (uint32_t)5U + (uint32_t)13U + sw3;
      KRML_CHECK_SIZE(sizeof (uint8_t), len0);
      uint8_t *tmp = alloca(len0 * sizeof (uint8_t));
      memset(tmp, 0U, len0 * sizeof (uint8_t));
      uint8_t *uu____5 = tmp;
      uint8_t *uu____6 = uu____5;
      uint32_t sw4;
      switch
      (
        Spec_Agile_HPKE_kem_hash_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ))
      )
      {
        case Spec_Hash_Definitions_SHA2_256:
          {
            sw4 = (uint32_t)32U;
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      store32_be(uu____6, sw4);
      memcpy(uu____5, uu____5 + (uint32_t)2U, (uint32_t)2U * sizeof (uint8_t));
      uint8_t *uu____7 = tmp + (uint32_t)2U;
      uu____7[0U] = (uint8_t)0x48U;
      uu____7[1U] = (uint8_t)0x50U;
      uu____7[2U] = (uint8_t)0x4bU;
      uu____7[3U] = (uint8_t)0x45U;
      uu____7[4U] = (uint8_t)0x2dU;
      uu____7[5U] = (uint8_t)0x76U;
      uu____7[6U] = (uint8_t)0x31U;
      memcpy(tmp + (uint32_t)9U, suite_id_kem, (uint32_t)5U * sizeof (uint8_t));
      memcpy(tmp + (uint32_t)9U + (uint32_t)5U,
        label_shared_secret,
        (uint32_t)13U * sizeof (uint8_t));
      uint8_t *uu____8 = tmp + (uint32_t)9U + (uint32_t)5U + (uint32_t)13U;
      uint32_t sw5;
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
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      memcpy(uu____8, o_kemcontext, sw5 * sizeof (uint8_t));
      uint32_t sw6;
      switch
      (
        Spec_Agile_HPKE_kem_hash_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ))
      )
      {
        case Spec_Hash_Definitions_SHA2_256:
          {
            sw6 = (uint32_t)32U;
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      uint32_t sw;
      switch
      (
        Spec_Agile_HPKE_kem_hash_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ))
      )
      {
        case Spec_Hash_Definitions_SHA2_256:
          {
            sw = (uint32_t)32U;
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      Hacl_HKDF_expand_sha2_256(o_shared, o_eae_prk, sw6, tmp, len0, sw);
      res0 = (uint32_t)0U;
    }
    else
    {
      res0 = (uint32_t)1U;
    }
  }
  else
  {
    res0 = (uint32_t)1U;
  }
  if (res0 == (uint32_t)0U)
  {
    uint8_t o_context[129U] = { 0U };
    uint8_t o_secret[64U] = { 0U };
    uint8_t suite_id[10U] = { 0U };
    uint8_t *uu____9 = suite_id;
    uu____9[0U] = (uint8_t)0x48U;
    uu____9[1U] = (uint8_t)0x50U;
    uu____9[2U] = (uint8_t)0x4bU;
    uu____9[3U] = (uint8_t)0x45U;
    uint8_t *uu____10 = suite_id + (uint32_t)4U;
    uu____10[0U] = (uint8_t)0U;
    uu____10[1U] = (uint8_t)32U;
    uint8_t *uu____11 = suite_id + (uint32_t)6U;
    uu____11[0U] = (uint8_t)0U;
    uu____11[1U] = (uint8_t)3U;
    uint8_t *uu____12 = suite_id + (uint32_t)8U;
    uu____12[0U] = (uint8_t)0U;
    uu____12[1U] = (uint8_t)3U;
    uint8_t
    label_psk_id_hash[11U] =
      {
        (uint8_t)0x70U, (uint8_t)0x73U, (uint8_t)0x6bU, (uint8_t)0x5fU, (uint8_t)0x69U,
        (uint8_t)0x64U, (uint8_t)0x5fU, (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x73U,
        (uint8_t)0x68U
      };
    uint8_t o_psk_id_hash[64U] = { 0U };
    uint8_t *empty = suite_id;
    uint32_t len0 = (uint32_t)7U + (uint32_t)10U + (uint32_t)11U + (uint32_t)0U;
    KRML_CHECK_SIZE(sizeof (uint8_t), len0);
    uint8_t *tmp0 = alloca(len0 * sizeof (uint8_t));
    memset(tmp0, 0U, len0 * sizeof (uint8_t));
    uint8_t *uu____13 = tmp0;
    uu____13[0U] = (uint8_t)0x48U;
    uu____13[1U] = (uint8_t)0x50U;
    uu____13[2U] = (uint8_t)0x4bU;
    uu____13[3U] = (uint8_t)0x45U;
    uu____13[4U] = (uint8_t)0x2dU;
    uu____13[5U] = (uint8_t)0x76U;
    uu____13[6U] = (uint8_t)0x31U;
    memcpy(tmp0 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
    memcpy(tmp0 + (uint32_t)7U + (uint32_t)10U,
      label_psk_id_hash,
      (uint32_t)11U * sizeof (uint8_t));
    memcpy(tmp0 + (uint32_t)7U + (uint32_t)10U + (uint32_t)11U,
      empty,
      (uint32_t)0U * sizeof (uint8_t));
    Hacl_HKDF_extract_sha2_512(o_psk_id_hash, empty, (uint32_t)0U, tmp0, len0);
    uint8_t
    label_info_hash[9U] =
      {
        (uint8_t)0x69U, (uint8_t)0x6eU, (uint8_t)0x66U, (uint8_t)0x6fU, (uint8_t)0x5fU,
        (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x73U, (uint8_t)0x68U
      };
    uint8_t o_info_hash[64U] = { 0U };
    uint32_t len1 = (uint32_t)7U + (uint32_t)10U + (uint32_t)9U + infolen;
    KRML_CHECK_SIZE(sizeof (uint8_t), len1);
    uint8_t *tmp1 = alloca(len1 * sizeof (uint8_t));
    memset(tmp1, 0U, len1 * sizeof (uint8_t));
    uint8_t *uu____14 = tmp1;
    uu____14[0U] = (uint8_t)0x48U;
    uu____14[1U] = (uint8_t)0x50U;
    uu____14[2U] = (uint8_t)0x4bU;
    uu____14[3U] = (uint8_t)0x45U;
    uu____14[4U] = (uint8_t)0x2dU;
    uu____14[5U] = (uint8_t)0x76U;
    uu____14[6U] = (uint8_t)0x31U;
    memcpy(tmp1 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
    memcpy(tmp1 + (uint32_t)7U + (uint32_t)10U, label_info_hash, (uint32_t)9U * sizeof (uint8_t));
    memcpy(tmp1 + (uint32_t)7U + (uint32_t)10U + (uint32_t)9U, info, infolen * sizeof (uint8_t));
    Hacl_HKDF_extract_sha2_512(o_info_hash, empty, (uint32_t)0U, tmp1, len1);
    o_context[0U] = (uint8_t)0U;
    uint8_t *uu____15 = o_context + (uint32_t)1U;
    uint32_t sw0;
    switch
    (
      Spec_Agile_HPKE_hash_of_cs((
          (Spec_Agile_HPKE_ciphersuite){
            .fst = Spec_Agile_DH_DH_Curve25519,
            .snd = Spec_Hash_Definitions_SHA2_256,
            .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
            .f3 = Spec_Hash_Definitions_SHA2_512
          }
        ))
    )
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
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    memcpy(uu____15, o_psk_id_hash, sw0 * sizeof (uint8_t));
    uint32_t sw1;
    switch
    (
      Spec_Agile_HPKE_hash_of_cs((
          (Spec_Agile_HPKE_ciphersuite){
            .fst = Spec_Agile_DH_DH_Curve25519,
            .snd = Spec_Hash_Definitions_SHA2_256,
            .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
            .f3 = Spec_Hash_Definitions_SHA2_512
          }
        ))
    )
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
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    uint8_t *uu____16 = o_context + sw1;
    uint32_t sw2;
    switch
    (
      Spec_Agile_HPKE_hash_of_cs((
          (Spec_Agile_HPKE_ciphersuite){
            .fst = Spec_Agile_DH_DH_Curve25519,
            .snd = Spec_Hash_Definitions_SHA2_256,
            .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
            .f3 = Spec_Hash_Definitions_SHA2_512
          }
        ))
    )
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
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    memcpy(uu____16, o_info_hash, sw2 * sizeof (uint8_t));
    uint8_t
    label_secret[6U] =
      {
        (uint8_t)0x73U, (uint8_t)0x65U, (uint8_t)0x63U, (uint8_t)0x72U, (uint8_t)0x65U,
        (uint8_t)0x74U
      };
    uint32_t len = (uint32_t)7U + (uint32_t)10U + (uint32_t)6U + (uint32_t)0U;
    KRML_CHECK_SIZE(sizeof (uint8_t), len);
    uint8_t *tmp2 = alloca(len * sizeof (uint8_t));
    memset(tmp2, 0U, len * sizeof (uint8_t));
    uint8_t *uu____17 = tmp2;
    uu____17[0U] = (uint8_t)0x48U;
    uu____17[1U] = (uint8_t)0x50U;
    uu____17[2U] = (uint8_t)0x4bU;
    uu____17[3U] = (uint8_t)0x45U;
    uu____17[4U] = (uint8_t)0x2dU;
    uu____17[5U] = (uint8_t)0x76U;
    uu____17[6U] = (uint8_t)0x31U;
    memcpy(tmp2 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
    memcpy(tmp2 + (uint32_t)7U + (uint32_t)10U, label_secret, (uint32_t)6U * sizeof (uint8_t));
    memcpy(tmp2 + (uint32_t)7U + (uint32_t)10U + (uint32_t)6U,
      empty,
      (uint32_t)0U * sizeof (uint8_t));
    uint32_t sw3;
    switch
    (
      Spec_Agile_HPKE_kem_hash_of_cs((
          (Spec_Agile_HPKE_ciphersuite){
            .fst = Spec_Agile_DH_DH_Curve25519,
            .snd = Spec_Hash_Definitions_SHA2_256,
            .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
            .f3 = Spec_Hash_Definitions_SHA2_512
          }
        ))
    )
    {
      case Spec_Hash_Definitions_SHA2_256:
        {
          sw3 = (uint32_t)32U;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    Hacl_HKDF_extract_sha2_512(o_secret, o_shared, sw3, tmp2, len);
    uint8_t label_exp[3U] = { (uint8_t)0x65U, (uint8_t)0x78U, (uint8_t)0x70U };
    uint32_t sw4;
    switch
    (
      Spec_Agile_HPKE_hash_of_cs((
          (Spec_Agile_HPKE_ciphersuite){
            .fst = Spec_Agile_DH_DH_Curve25519,
            .snd = Spec_Hash_Definitions_SHA2_256,
            .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
            .f3 = Spec_Hash_Definitions_SHA2_512
          }
        ))
    )
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
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    uint32_t len2 = (uint32_t)9U + (uint32_t)10U + (uint32_t)3U + sw4;
    KRML_CHECK_SIZE(sizeof (uint8_t), len2);
    uint8_t *tmp3 = alloca(len2 * sizeof (uint8_t));
    memset(tmp3, 0U, len2 * sizeof (uint8_t));
    uint8_t *uu____18 = tmp3;
    uint8_t *uu____19 = uu____18;
    uint32_t sw5;
    switch
    (
      Spec_Agile_HPKE_hash_of_cs((
          (Spec_Agile_HPKE_ciphersuite){
            .fst = Spec_Agile_DH_DH_Curve25519,
            .snd = Spec_Hash_Definitions_SHA2_256,
            .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
            .f3 = Spec_Hash_Definitions_SHA2_512
          }
        ))
    )
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
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    store32_be(uu____19, sw5);
    memcpy(uu____18, uu____18 + (uint32_t)2U, (uint32_t)2U * sizeof (uint8_t));
    uint8_t *uu____20 = tmp3 + (uint32_t)2U;
    uu____20[0U] = (uint8_t)0x48U;
    uu____20[1U] = (uint8_t)0x50U;
    uu____20[2U] = (uint8_t)0x4bU;
    uu____20[3U] = (uint8_t)0x45U;
    uu____20[4U] = (uint8_t)0x2dU;
    uu____20[5U] = (uint8_t)0x76U;
    uu____20[6U] = (uint8_t)0x31U;
    memcpy(tmp3 + (uint32_t)9U, suite_id, (uint32_t)10U * sizeof (uint8_t));
    memcpy(tmp3 + (uint32_t)9U + (uint32_t)10U, label_exp, (uint32_t)3U * sizeof (uint8_t));
    uint8_t *uu____21 = tmp3 + (uint32_t)9U + (uint32_t)10U + (uint32_t)3U;
    uint32_t sw6;
    switch
    (
      Spec_Agile_HPKE_hash_of_cs((
          (Spec_Agile_HPKE_ciphersuite){
            .fst = Spec_Agile_DH_DH_Curve25519,
            .snd = Spec_Hash_Definitions_SHA2_256,
            .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
            .f3 = Spec_Hash_Definitions_SHA2_512
          }
        ))
    )
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
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    memcpy(uu____21, o_context, sw6 * sizeof (uint8_t));
    uint32_t sw7;
    switch
    (
      Spec_Agile_HPKE_hash_of_cs((
          (Spec_Agile_HPKE_ciphersuite){
            .fst = Spec_Agile_DH_DH_Curve25519,
            .snd = Spec_Hash_Definitions_SHA2_256,
            .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
            .f3 = Spec_Hash_Definitions_SHA2_512
          }
        ))
    )
    {
      case Spec_Hash_Definitions_SHA2_256:
        {
          sw7 = (uint32_t)32U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_384:
        {
          sw7 = (uint32_t)48U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_512:
        {
          sw7 = (uint32_t)64U;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    uint32_t sw8;
    switch
    (
      Spec_Agile_HPKE_hash_of_cs((
          (Spec_Agile_HPKE_ciphersuite){
            .fst = Spec_Agile_DH_DH_Curve25519,
            .snd = Spec_Hash_Definitions_SHA2_256,
            .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
            .f3 = Spec_Hash_Definitions_SHA2_512
          }
        ))
    )
    {
      case Spec_Hash_Definitions_SHA2_256:
        {
          sw8 = (uint32_t)32U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_384:
        {
          sw8 = (uint32_t)48U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_512:
        {
          sw8 = (uint32_t)64U;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    Hacl_HKDF_expand_sha2_512(o_ctx.ctx_exporter, o_secret, sw7, tmp3, len2, sw8);
    Spec_Agile_HPKE_aead
    scrut0 =
      Spec_Agile_HPKE_aead_of_cs((
          (Spec_Agile_HPKE_ciphersuite){
            .fst = Spec_Agile_DH_DH_Curve25519,
            .snd = Spec_Hash_Definitions_SHA2_256,
            .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
            .f3 = Spec_Hash_Definitions_SHA2_512
          }
        ));
    if (scrut0.tag == Spec_Agile_HPKE_ExportOnly)
    {
      o_ctx.ctx_seq[0U] = (uint64_t)0U;
    }
    else
    {
      uint8_t label_key[3U] = { (uint8_t)0x6bU, (uint8_t)0x65U, (uint8_t)0x79U };
      uint32_t sw9;
      switch
      (
        Spec_Agile_HPKE_hash_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ))
      )
      {
        case Spec_Hash_Definitions_SHA2_256:
          {
            sw9 = (uint32_t)65U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_384:
          {
            sw9 = (uint32_t)97U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_512:
          {
            sw9 = (uint32_t)129U;
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      uint32_t len3 = (uint32_t)9U + (uint32_t)10U + (uint32_t)3U + sw9;
      KRML_CHECK_SIZE(sizeof (uint8_t), len3);
      uint8_t *tmp4 = alloca(len3 * sizeof (uint8_t));
      memset(tmp4, 0U, len3 * sizeof (uint8_t));
      uint8_t *uu____22 = tmp4;
      uint8_t *uu____23 = uu____22;
      Spec_Agile_HPKE_aead
      scrut1 =
        Spec_Agile_HPKE_aead_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ));
      uint32_t ite0;
      if (scrut1.tag == Spec_Agile_HPKE_ExportOnly)
      {
        ite0 = (uint32_t)0U;
      }
      else if (scrut1.tag == Spec_Agile_HPKE_Seal && scrut1.alg == Spec_Agile_AEAD_AES128_GCM)
      {
        ite0 = (uint32_t)16U;
      }
      else if (scrut1.tag == Spec_Agile_HPKE_Seal && scrut1.alg == Spec_Agile_AEAD_AES256_GCM)
      {
        ite0 = (uint32_t)32U;
      }
      else if
      (scrut1.tag == Spec_Agile_HPKE_Seal && scrut1.alg == Spec_Agile_AEAD_CHACHA20_POLY1305)
      {
        ite0 = (uint32_t)32U;
      }
      else
      {
        ite0 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
      }
      store32_be(uu____23, ite0);
      memcpy(uu____22, uu____22 + (uint32_t)2U, (uint32_t)2U * sizeof (uint8_t));
      uint8_t *uu____24 = tmp4 + (uint32_t)2U;
      uu____24[0U] = (uint8_t)0x48U;
      uu____24[1U] = (uint8_t)0x50U;
      uu____24[2U] = (uint8_t)0x4bU;
      uu____24[3U] = (uint8_t)0x45U;
      uu____24[4U] = (uint8_t)0x2dU;
      uu____24[5U] = (uint8_t)0x76U;
      uu____24[6U] = (uint8_t)0x31U;
      memcpy(tmp4 + (uint32_t)9U, suite_id, (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp4 + (uint32_t)9U + (uint32_t)10U, label_key, (uint32_t)3U * sizeof (uint8_t));
      uint8_t *uu____25 = tmp4 + (uint32_t)9U + (uint32_t)10U + (uint32_t)3U;
      uint32_t sw10;
      switch
      (
        Spec_Agile_HPKE_hash_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ))
      )
      {
        case Spec_Hash_Definitions_SHA2_256:
          {
            sw10 = (uint32_t)65U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_384:
          {
            sw10 = (uint32_t)97U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_512:
          {
            sw10 = (uint32_t)129U;
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      memcpy(uu____25, o_context, sw10 * sizeof (uint8_t));
      uint32_t sw11;
      switch
      (
        Spec_Agile_HPKE_hash_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ))
      )
      {
        case Spec_Hash_Definitions_SHA2_256:
          {
            sw11 = (uint32_t)32U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_384:
          {
            sw11 = (uint32_t)48U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_512:
          {
            sw11 = (uint32_t)64U;
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      Spec_Agile_HPKE_aead
      scrut2 =
        Spec_Agile_HPKE_aead_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ));
      uint32_t ite1;
      if (scrut2.tag == Spec_Agile_HPKE_ExportOnly)
      {
        ite1 = (uint32_t)0U;
      }
      else if (scrut2.tag == Spec_Agile_HPKE_Seal && scrut2.alg == Spec_Agile_AEAD_AES128_GCM)
      {
        ite1 = (uint32_t)16U;
      }
      else if (scrut2.tag == Spec_Agile_HPKE_Seal && scrut2.alg == Spec_Agile_AEAD_AES256_GCM)
      {
        ite1 = (uint32_t)32U;
      }
      else if
      (scrut2.tag == Spec_Agile_HPKE_Seal && scrut2.alg == Spec_Agile_AEAD_CHACHA20_POLY1305)
      {
        ite1 = (uint32_t)32U;
      }
      else
      {
        ite1 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
      }
      Hacl_HKDF_expand_sha2_512(o_ctx.ctx_key, o_secret, sw11, tmp4, len3, ite1);
      uint8_t
      label_base_nonce[10U] =
        {
          (uint8_t)0x62U, (uint8_t)0x61U, (uint8_t)0x73U, (uint8_t)0x65U, (uint8_t)0x5fU,
          (uint8_t)0x6eU, (uint8_t)0x6fU, (uint8_t)0x6eU, (uint8_t)0x63U, (uint8_t)0x65U
        };
      uint32_t sw12;
      switch
      (
        Spec_Agile_HPKE_hash_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ))
      )
      {
        case Spec_Hash_Definitions_SHA2_256:
          {
            sw12 = (uint32_t)65U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_384:
          {
            sw12 = (uint32_t)97U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_512:
          {
            sw12 = (uint32_t)129U;
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      uint32_t len4 = (uint32_t)9U + (uint32_t)10U + (uint32_t)10U + sw12;
      KRML_CHECK_SIZE(sizeof (uint8_t), len4);
      uint8_t *tmp = alloca(len4 * sizeof (uint8_t));
      memset(tmp, 0U, len4 * sizeof (uint8_t));
      uint8_t *uu____26 = tmp;
      uint8_t *uu____27 = uu____26;
      Spec_Agile_HPKE_aead
      scrut3 =
        Spec_Agile_HPKE_aead_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ));
      uint32_t ite2;
      if (scrut3.tag == Spec_Agile_HPKE_ExportOnly)
      {
        ite2 = (uint32_t)0U;
      }
      else if (scrut3.tag == Spec_Agile_HPKE_Seal)
      {
        ite2 = (uint32_t)12U;
      }
      else
      {
        ite2 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
      }
      store32_be(uu____27, ite2);
      memcpy(uu____26, uu____26 + (uint32_t)2U, (uint32_t)2U * sizeof (uint8_t));
      uint8_t *uu____28 = tmp + (uint32_t)2U;
      uu____28[0U] = (uint8_t)0x48U;
      uu____28[1U] = (uint8_t)0x50U;
      uu____28[2U] = (uint8_t)0x4bU;
      uu____28[3U] = (uint8_t)0x45U;
      uu____28[4U] = (uint8_t)0x2dU;
      uu____28[5U] = (uint8_t)0x76U;
      uu____28[6U] = (uint8_t)0x31U;
      memcpy(tmp + (uint32_t)9U, suite_id, (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp + (uint32_t)9U + (uint32_t)10U,
        label_base_nonce,
        (uint32_t)10U * sizeof (uint8_t));
      uint8_t *uu____29 = tmp + (uint32_t)9U + (uint32_t)10U + (uint32_t)10U;
      uint32_t sw;
      switch
      (
        Spec_Agile_HPKE_hash_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ))
      )
      {
        case Spec_Hash_Definitions_SHA2_256:
          {
            sw = (uint32_t)65U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_384:
          {
            sw = (uint32_t)97U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_512:
          {
            sw = (uint32_t)129U;
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      memcpy(uu____29, o_context, sw * sizeof (uint8_t));
      uint32_t sw13;
      switch
      (
        Spec_Agile_HPKE_hash_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ))
      )
      {
        case Spec_Hash_Definitions_SHA2_256:
          {
            sw13 = (uint32_t)32U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_384:
          {
            sw13 = (uint32_t)48U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_512:
          {
            sw13 = (uint32_t)64U;
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      Spec_Agile_HPKE_aead
      scrut =
        Spec_Agile_HPKE_aead_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ));
      uint32_t ite;
      if (scrut.tag == Spec_Agile_HPKE_ExportOnly)
      {
        ite = (uint32_t)0U;
      }
      else if (scrut.tag == Spec_Agile_HPKE_Seal)
      {
        ite = (uint32_t)12U;
      }
      else
      {
        ite = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
      }
      Hacl_HKDF_expand_sha2_512(o_ctx.ctx_nonce, o_secret, sw13, tmp, len4, ite);
      o_ctx.ctx_seq[0U] = (uint64_t)0U;
    }
    return res0;
  }
  return res0;
}

uint32_t
Hacl_HPKE_Curve64_CP128_SHA512_setupBaseR(
  Hacl_Impl_HPKE_context_s o_ctx,
  uint8_t *enc,
  uint8_t *skR,
  uint32_t infolen,
  uint8_t *info
)
{
  uint8_t pkR[32U] = { 0U };
  Hacl_Curve25519_64_secret_to_public(pkR, skR);
  uint32_t res1 = (uint32_t)0U;
  uint8_t shared[32U];
  if (res1 == (uint32_t)0U)
  {
    uint8_t init = (uint8_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
    {
      shared[i] = init;
    }
    uint8_t *pkE = enc;
    uint8_t dh[32U] = { 0U };
    uint8_t zeros[32U] = { 0U };
    Hacl_Curve25519_64_scalarmult(dh, skR, pkE);
    uint8_t res0 = (uint8_t)255U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
    {
      uint8_t uu____0 = FStar_UInt8_eq_mask(dh[i], zeros[i]);
      res0 = uu____0 & res0;
    }
    uint8_t z = res0;
    uint32_t res;
    if (z == (uint8_t)255U)
    {
      res = (uint32_t)1U;
    }
    else
    {
      res = (uint32_t)0U;
    }
    uint32_t res11 = res;
    uint8_t kemcontext[64U];
    uint32_t res2;
    if (res11 == (uint32_t)0U)
    {
      uint8_t init = (uint8_t)0U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
      {
        kemcontext[i] = init;
      }
      uint32_t sw0;
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
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      uint8_t *pkRm = kemcontext + sw0;
      uint8_t *pkR1 = pkRm;
      Hacl_Curve25519_64_secret_to_public(pkR1, skR);
      uint32_t res20 = (uint32_t)0U;
      if (res20 == (uint32_t)0U)
      {
        uint8_t *uu____1 = kemcontext;
        uint32_t sw1;
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
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        memcpy(uu____1, enc, sw1 * sizeof (uint8_t));
        uint8_t *dhm = dh;
        uint8_t o_eae_prk[32U] = { 0U };
        uint8_t suite_id_kem[5U] = { 0U };
        uint8_t *uu____2 = suite_id_kem;
        uu____2[0U] = (uint8_t)0x4bU;
        uu____2[1U] = (uint8_t)0x45U;
        uu____2[2U] = (uint8_t)0x4dU;
        uint8_t *uu____3 = suite_id_kem + (uint32_t)3U;
        uu____3[0U] = (uint8_t)0U;
        uu____3[1U] = (uint8_t)32U;
        uint8_t *empty = suite_id_kem;
        uint8_t
        label_eae_prk[7U] =
          {
            (uint8_t)0x65U, (uint8_t)0x61U, (uint8_t)0x65U, (uint8_t)0x5fU, (uint8_t)0x70U,
            (uint8_t)0x72U, (uint8_t)0x6bU
          };
        uint32_t len = (uint32_t)7U + (uint32_t)5U + (uint32_t)7U + (uint32_t)32U;
        KRML_CHECK_SIZE(sizeof (uint8_t), len);
        uint8_t *tmp0 = alloca(len * sizeof (uint8_t));
        memset(tmp0, 0U, len * sizeof (uint8_t));
        uint8_t *uu____4 = tmp0;
        uu____4[0U] = (uint8_t)0x48U;
        uu____4[1U] = (uint8_t)0x50U;
        uu____4[2U] = (uint8_t)0x4bU;
        uu____4[3U] = (uint8_t)0x45U;
        uu____4[4U] = (uint8_t)0x2dU;
        uu____4[5U] = (uint8_t)0x76U;
        uu____4[6U] = (uint8_t)0x31U;
        memcpy(tmp0 + (uint32_t)7U, suite_id_kem, (uint32_t)5U * sizeof (uint8_t));
        memcpy(tmp0 + (uint32_t)7U + (uint32_t)5U, label_eae_prk, (uint32_t)7U * sizeof (uint8_t));
        memcpy(tmp0 + (uint32_t)7U + (uint32_t)5U + (uint32_t)7U,
          dhm,
          (uint32_t)32U * sizeof (uint8_t));
        Hacl_HKDF_extract_sha2_256(o_eae_prk, empty, (uint32_t)0U, tmp0, len);
        uint8_t
        label_shared_secret[13U] =
          {
            (uint8_t)0x73U, (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x72U, (uint8_t)0x65U,
            (uint8_t)0x64U, (uint8_t)0x5fU, (uint8_t)0x73U, (uint8_t)0x65U, (uint8_t)0x63U,
            (uint8_t)0x72U, (uint8_t)0x65U, (uint8_t)0x74U
          };
        uint32_t sw2;
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
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        uint32_t len0 = (uint32_t)9U + (uint32_t)5U + (uint32_t)13U + sw2;
        KRML_CHECK_SIZE(sizeof (uint8_t), len0);
        uint8_t *tmp = alloca(len0 * sizeof (uint8_t));
        memset(tmp, 0U, len0 * sizeof (uint8_t));
        uint8_t *uu____5 = tmp;
        uint8_t *uu____6 = uu____5;
        uint32_t sw3;
        switch
        (
          Spec_Agile_HPKE_kem_hash_of_cs((
              (Spec_Agile_HPKE_ciphersuite){
                .fst = Spec_Agile_DH_DH_Curve25519,
                .snd = Spec_Hash_Definitions_SHA2_256,
                .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
                .f3 = Spec_Hash_Definitions_SHA2_512
              }
            ))
        )
        {
          case Spec_Hash_Definitions_SHA2_256:
            {
              sw3 = (uint32_t)32U;
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        store32_be(uu____6, sw3);
        memcpy(uu____5, uu____5 + (uint32_t)2U, (uint32_t)2U * sizeof (uint8_t));
        uint8_t *uu____7 = tmp + (uint32_t)2U;
        uu____7[0U] = (uint8_t)0x48U;
        uu____7[1U] = (uint8_t)0x50U;
        uu____7[2U] = (uint8_t)0x4bU;
        uu____7[3U] = (uint8_t)0x45U;
        uu____7[4U] = (uint8_t)0x2dU;
        uu____7[5U] = (uint8_t)0x76U;
        uu____7[6U] = (uint8_t)0x31U;
        memcpy(tmp + (uint32_t)9U, suite_id_kem, (uint32_t)5U * sizeof (uint8_t));
        memcpy(tmp + (uint32_t)9U + (uint32_t)5U,
          label_shared_secret,
          (uint32_t)13U * sizeof (uint8_t));
        uint8_t *uu____8 = tmp + (uint32_t)9U + (uint32_t)5U + (uint32_t)13U;
        uint32_t sw4;
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
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        memcpy(uu____8, kemcontext, sw4 * sizeof (uint8_t));
        uint32_t sw5;
        switch
        (
          Spec_Agile_HPKE_kem_hash_of_cs((
              (Spec_Agile_HPKE_ciphersuite){
                .fst = Spec_Agile_DH_DH_Curve25519,
                .snd = Spec_Hash_Definitions_SHA2_256,
                .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
                .f3 = Spec_Hash_Definitions_SHA2_512
              }
            ))
        )
        {
          case Spec_Hash_Definitions_SHA2_256:
            {
              sw5 = (uint32_t)32U;
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        uint32_t sw;
        switch
        (
          Spec_Agile_HPKE_kem_hash_of_cs((
              (Spec_Agile_HPKE_ciphersuite){
                .fst = Spec_Agile_DH_DH_Curve25519,
                .snd = Spec_Hash_Definitions_SHA2_256,
                .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
                .f3 = Spec_Hash_Definitions_SHA2_512
              }
            ))
        )
        {
          case Spec_Hash_Definitions_SHA2_256:
            {
              sw = (uint32_t)32U;
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        Hacl_HKDF_expand_sha2_256(shared, o_eae_prk, sw5, tmp, len0, sw);
        res2 = (uint32_t)0U;
      }
      else
      {
        res2 = (uint32_t)1U;
      }
    }
    else
    {
      res2 = (uint32_t)1U;
    }
    if (res2 == (uint32_t)0U)
    {
      uint8_t o_context[129U] = { 0U };
      uint8_t o_secret[64U] = { 0U };
      uint8_t suite_id[10U] = { 0U };
      uint8_t *uu____9 = suite_id;
      uu____9[0U] = (uint8_t)0x48U;
      uu____9[1U] = (uint8_t)0x50U;
      uu____9[2U] = (uint8_t)0x4bU;
      uu____9[3U] = (uint8_t)0x45U;
      uint8_t *uu____10 = suite_id + (uint32_t)4U;
      uu____10[0U] = (uint8_t)0U;
      uu____10[1U] = (uint8_t)32U;
      uint8_t *uu____11 = suite_id + (uint32_t)6U;
      uu____11[0U] = (uint8_t)0U;
      uu____11[1U] = (uint8_t)3U;
      uint8_t *uu____12 = suite_id + (uint32_t)8U;
      uu____12[0U] = (uint8_t)0U;
      uu____12[1U] = (uint8_t)3U;
      uint8_t
      label_psk_id_hash[11U] =
        {
          (uint8_t)0x70U, (uint8_t)0x73U, (uint8_t)0x6bU, (uint8_t)0x5fU, (uint8_t)0x69U,
          (uint8_t)0x64U, (uint8_t)0x5fU, (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x73U,
          (uint8_t)0x68U
        };
      uint8_t o_psk_id_hash[64U] = { 0U };
      uint8_t *empty = suite_id;
      uint32_t len0 = (uint32_t)7U + (uint32_t)10U + (uint32_t)11U + (uint32_t)0U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len0);
      uint8_t *tmp0 = alloca(len0 * sizeof (uint8_t));
      memset(tmp0, 0U, len0 * sizeof (uint8_t));
      uint8_t *uu____13 = tmp0;
      uu____13[0U] = (uint8_t)0x48U;
      uu____13[1U] = (uint8_t)0x50U;
      uu____13[2U] = (uint8_t)0x4bU;
      uu____13[3U] = (uint8_t)0x45U;
      uu____13[4U] = (uint8_t)0x2dU;
      uu____13[5U] = (uint8_t)0x76U;
      uu____13[6U] = (uint8_t)0x31U;
      memcpy(tmp0 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp0 + (uint32_t)7U + (uint32_t)10U,
        label_psk_id_hash,
        (uint32_t)11U * sizeof (uint8_t));
      memcpy(tmp0 + (uint32_t)7U + (uint32_t)10U + (uint32_t)11U,
        empty,
        (uint32_t)0U * sizeof (uint8_t));
      Hacl_HKDF_extract_sha2_512(o_psk_id_hash, empty, (uint32_t)0U, tmp0, len0);
      uint8_t
      label_info_hash[9U] =
        {
          (uint8_t)0x69U, (uint8_t)0x6eU, (uint8_t)0x66U, (uint8_t)0x6fU, (uint8_t)0x5fU,
          (uint8_t)0x68U, (uint8_t)0x61U, (uint8_t)0x73U, (uint8_t)0x68U
        };
      uint8_t o_info_hash[64U] = { 0U };
      uint32_t len1 = (uint32_t)7U + (uint32_t)10U + (uint32_t)9U + infolen;
      KRML_CHECK_SIZE(sizeof (uint8_t), len1);
      uint8_t *tmp1 = alloca(len1 * sizeof (uint8_t));
      memset(tmp1, 0U, len1 * sizeof (uint8_t));
      uint8_t *uu____14 = tmp1;
      uu____14[0U] = (uint8_t)0x48U;
      uu____14[1U] = (uint8_t)0x50U;
      uu____14[2U] = (uint8_t)0x4bU;
      uu____14[3U] = (uint8_t)0x45U;
      uu____14[4U] = (uint8_t)0x2dU;
      uu____14[5U] = (uint8_t)0x76U;
      uu____14[6U] = (uint8_t)0x31U;
      memcpy(tmp1 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp1 + (uint32_t)7U + (uint32_t)10U, label_info_hash, (uint32_t)9U * sizeof (uint8_t));
      memcpy(tmp1 + (uint32_t)7U + (uint32_t)10U + (uint32_t)9U, info, infolen * sizeof (uint8_t));
      Hacl_HKDF_extract_sha2_512(o_info_hash, empty, (uint32_t)0U, tmp1, len1);
      o_context[0U] = (uint8_t)0U;
      uint8_t *uu____15 = o_context + (uint32_t)1U;
      uint32_t sw0;
      switch
      (
        Spec_Agile_HPKE_hash_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ))
      )
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
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      memcpy(uu____15, o_psk_id_hash, sw0 * sizeof (uint8_t));
      uint32_t sw1;
      switch
      (
        Spec_Agile_HPKE_hash_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ))
      )
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
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      uint8_t *uu____16 = o_context + sw1;
      uint32_t sw2;
      switch
      (
        Spec_Agile_HPKE_hash_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ))
      )
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
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      memcpy(uu____16, o_info_hash, sw2 * sizeof (uint8_t));
      uint8_t
      label_secret[6U] =
        {
          (uint8_t)0x73U, (uint8_t)0x65U, (uint8_t)0x63U, (uint8_t)0x72U, (uint8_t)0x65U,
          (uint8_t)0x74U
        };
      uint32_t len = (uint32_t)7U + (uint32_t)10U + (uint32_t)6U + (uint32_t)0U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len);
      uint8_t *tmp2 = alloca(len * sizeof (uint8_t));
      memset(tmp2, 0U, len * sizeof (uint8_t));
      uint8_t *uu____17 = tmp2;
      uu____17[0U] = (uint8_t)0x48U;
      uu____17[1U] = (uint8_t)0x50U;
      uu____17[2U] = (uint8_t)0x4bU;
      uu____17[3U] = (uint8_t)0x45U;
      uu____17[4U] = (uint8_t)0x2dU;
      uu____17[5U] = (uint8_t)0x76U;
      uu____17[6U] = (uint8_t)0x31U;
      memcpy(tmp2 + (uint32_t)7U, suite_id, (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp2 + (uint32_t)7U + (uint32_t)10U, label_secret, (uint32_t)6U * sizeof (uint8_t));
      memcpy(tmp2 + (uint32_t)7U + (uint32_t)10U + (uint32_t)6U,
        empty,
        (uint32_t)0U * sizeof (uint8_t));
      uint32_t sw3;
      switch
      (
        Spec_Agile_HPKE_kem_hash_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ))
      )
      {
        case Spec_Hash_Definitions_SHA2_256:
          {
            sw3 = (uint32_t)32U;
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      Hacl_HKDF_extract_sha2_512(o_secret, shared, sw3, tmp2, len);
      uint8_t label_exp[3U] = { (uint8_t)0x65U, (uint8_t)0x78U, (uint8_t)0x70U };
      uint32_t sw4;
      switch
      (
        Spec_Agile_HPKE_hash_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ))
      )
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
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      uint32_t len2 = (uint32_t)9U + (uint32_t)10U + (uint32_t)3U + sw4;
      KRML_CHECK_SIZE(sizeof (uint8_t), len2);
      uint8_t *tmp3 = alloca(len2 * sizeof (uint8_t));
      memset(tmp3, 0U, len2 * sizeof (uint8_t));
      uint8_t *uu____18 = tmp3;
      uint8_t *uu____19 = uu____18;
      uint32_t sw5;
      switch
      (
        Spec_Agile_HPKE_hash_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ))
      )
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
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      store32_be(uu____19, sw5);
      memcpy(uu____18, uu____18 + (uint32_t)2U, (uint32_t)2U * sizeof (uint8_t));
      uint8_t *uu____20 = tmp3 + (uint32_t)2U;
      uu____20[0U] = (uint8_t)0x48U;
      uu____20[1U] = (uint8_t)0x50U;
      uu____20[2U] = (uint8_t)0x4bU;
      uu____20[3U] = (uint8_t)0x45U;
      uu____20[4U] = (uint8_t)0x2dU;
      uu____20[5U] = (uint8_t)0x76U;
      uu____20[6U] = (uint8_t)0x31U;
      memcpy(tmp3 + (uint32_t)9U, suite_id, (uint32_t)10U * sizeof (uint8_t));
      memcpy(tmp3 + (uint32_t)9U + (uint32_t)10U, label_exp, (uint32_t)3U * sizeof (uint8_t));
      uint8_t *uu____21 = tmp3 + (uint32_t)9U + (uint32_t)10U + (uint32_t)3U;
      uint32_t sw6;
      switch
      (
        Spec_Agile_HPKE_hash_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ))
      )
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
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      memcpy(uu____21, o_context, sw6 * sizeof (uint8_t));
      uint32_t sw7;
      switch
      (
        Spec_Agile_HPKE_hash_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ))
      )
      {
        case Spec_Hash_Definitions_SHA2_256:
          {
            sw7 = (uint32_t)32U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_384:
          {
            sw7 = (uint32_t)48U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_512:
          {
            sw7 = (uint32_t)64U;
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      uint32_t sw8;
      switch
      (
        Spec_Agile_HPKE_hash_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ))
      )
      {
        case Spec_Hash_Definitions_SHA2_256:
          {
            sw8 = (uint32_t)32U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_384:
          {
            sw8 = (uint32_t)48U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_512:
          {
            sw8 = (uint32_t)64U;
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      Hacl_HKDF_expand_sha2_512(o_ctx.ctx_exporter, o_secret, sw7, tmp3, len2, sw8);
      Spec_Agile_HPKE_aead
      scrut0 =
        Spec_Agile_HPKE_aead_of_cs((
            (Spec_Agile_HPKE_ciphersuite){
              .fst = Spec_Agile_DH_DH_Curve25519,
              .snd = Spec_Hash_Definitions_SHA2_256,
              .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
              .f3 = Spec_Hash_Definitions_SHA2_512
            }
          ));
      if (scrut0.tag == Spec_Agile_HPKE_ExportOnly)
      {
        o_ctx.ctx_seq[0U] = (uint64_t)0U;
      }
      else
      {
        uint8_t label_key[3U] = { (uint8_t)0x6bU, (uint8_t)0x65U, (uint8_t)0x79U };
        uint32_t sw9;
        switch
        (
          Spec_Agile_HPKE_hash_of_cs((
              (Spec_Agile_HPKE_ciphersuite){
                .fst = Spec_Agile_DH_DH_Curve25519,
                .snd = Spec_Hash_Definitions_SHA2_256,
                .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
                .f3 = Spec_Hash_Definitions_SHA2_512
              }
            ))
        )
        {
          case Spec_Hash_Definitions_SHA2_256:
            {
              sw9 = (uint32_t)65U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_384:
            {
              sw9 = (uint32_t)97U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_512:
            {
              sw9 = (uint32_t)129U;
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        uint32_t len3 = (uint32_t)9U + (uint32_t)10U + (uint32_t)3U + sw9;
        KRML_CHECK_SIZE(sizeof (uint8_t), len3);
        uint8_t *tmp4 = alloca(len3 * sizeof (uint8_t));
        memset(tmp4, 0U, len3 * sizeof (uint8_t));
        uint8_t *uu____22 = tmp4;
        uint8_t *uu____23 = uu____22;
        Spec_Agile_HPKE_aead
        scrut1 =
          Spec_Agile_HPKE_aead_of_cs((
              (Spec_Agile_HPKE_ciphersuite){
                .fst = Spec_Agile_DH_DH_Curve25519,
                .snd = Spec_Hash_Definitions_SHA2_256,
                .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
                .f3 = Spec_Hash_Definitions_SHA2_512
              }
            ));
        uint32_t ite0;
        if (scrut1.tag == Spec_Agile_HPKE_ExportOnly)
        {
          ite0 = (uint32_t)0U;
        }
        else if (scrut1.tag == Spec_Agile_HPKE_Seal && scrut1.alg == Spec_Agile_AEAD_AES128_GCM)
        {
          ite0 = (uint32_t)16U;
        }
        else if (scrut1.tag == Spec_Agile_HPKE_Seal && scrut1.alg == Spec_Agile_AEAD_AES256_GCM)
        {
          ite0 = (uint32_t)32U;
        }
        else if
        (scrut1.tag == Spec_Agile_HPKE_Seal && scrut1.alg == Spec_Agile_AEAD_CHACHA20_POLY1305)
        {
          ite0 = (uint32_t)32U;
        }
        else
        {
          ite0 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
        }
        store32_be(uu____23, ite0);
        memcpy(uu____22, uu____22 + (uint32_t)2U, (uint32_t)2U * sizeof (uint8_t));
        uint8_t *uu____24 = tmp4 + (uint32_t)2U;
        uu____24[0U] = (uint8_t)0x48U;
        uu____24[1U] = (uint8_t)0x50U;
        uu____24[2U] = (uint8_t)0x4bU;
        uu____24[3U] = (uint8_t)0x45U;
        uu____24[4U] = (uint8_t)0x2dU;
        uu____24[5U] = (uint8_t)0x76U;
        uu____24[6U] = (uint8_t)0x31U;
        memcpy(tmp4 + (uint32_t)9U, suite_id, (uint32_t)10U * sizeof (uint8_t));
        memcpy(tmp4 + (uint32_t)9U + (uint32_t)10U, label_key, (uint32_t)3U * sizeof (uint8_t));
        uint8_t *uu____25 = tmp4 + (uint32_t)9U + (uint32_t)10U + (uint32_t)3U;
        uint32_t sw10;
        switch
        (
          Spec_Agile_HPKE_hash_of_cs((
              (Spec_Agile_HPKE_ciphersuite){
                .fst = Spec_Agile_DH_DH_Curve25519,
                .snd = Spec_Hash_Definitions_SHA2_256,
                .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
                .f3 = Spec_Hash_Definitions_SHA2_512
              }
            ))
        )
        {
          case Spec_Hash_Definitions_SHA2_256:
            {
              sw10 = (uint32_t)65U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_384:
            {
              sw10 = (uint32_t)97U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_512:
            {
              sw10 = (uint32_t)129U;
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        memcpy(uu____25, o_context, sw10 * sizeof (uint8_t));
        uint32_t sw11;
        switch
        (
          Spec_Agile_HPKE_hash_of_cs((
              (Spec_Agile_HPKE_ciphersuite){
                .fst = Spec_Agile_DH_DH_Curve25519,
                .snd = Spec_Hash_Definitions_SHA2_256,
                .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
                .f3 = Spec_Hash_Definitions_SHA2_512
              }
            ))
        )
        {
          case Spec_Hash_Definitions_SHA2_256:
            {
              sw11 = (uint32_t)32U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_384:
            {
              sw11 = (uint32_t)48U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_512:
            {
              sw11 = (uint32_t)64U;
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        Spec_Agile_HPKE_aead
        scrut2 =
          Spec_Agile_HPKE_aead_of_cs((
              (Spec_Agile_HPKE_ciphersuite){
                .fst = Spec_Agile_DH_DH_Curve25519,
                .snd = Spec_Hash_Definitions_SHA2_256,
                .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
                .f3 = Spec_Hash_Definitions_SHA2_512
              }
            ));
        uint32_t ite1;
        if (scrut2.tag == Spec_Agile_HPKE_ExportOnly)
        {
          ite1 = (uint32_t)0U;
        }
        else if (scrut2.tag == Spec_Agile_HPKE_Seal && scrut2.alg == Spec_Agile_AEAD_AES128_GCM)
        {
          ite1 = (uint32_t)16U;
        }
        else if (scrut2.tag == Spec_Agile_HPKE_Seal && scrut2.alg == Spec_Agile_AEAD_AES256_GCM)
        {
          ite1 = (uint32_t)32U;
        }
        else if
        (scrut2.tag == Spec_Agile_HPKE_Seal && scrut2.alg == Spec_Agile_AEAD_CHACHA20_POLY1305)
        {
          ite1 = (uint32_t)32U;
        }
        else
        {
          ite1 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
        }
        Hacl_HKDF_expand_sha2_512(o_ctx.ctx_key, o_secret, sw11, tmp4, len3, ite1);
        uint8_t
        label_base_nonce[10U] =
          {
            (uint8_t)0x62U, (uint8_t)0x61U, (uint8_t)0x73U, (uint8_t)0x65U, (uint8_t)0x5fU,
            (uint8_t)0x6eU, (uint8_t)0x6fU, (uint8_t)0x6eU, (uint8_t)0x63U, (uint8_t)0x65U
          };
        uint32_t sw12;
        switch
        (
          Spec_Agile_HPKE_hash_of_cs((
              (Spec_Agile_HPKE_ciphersuite){
                .fst = Spec_Agile_DH_DH_Curve25519,
                .snd = Spec_Hash_Definitions_SHA2_256,
                .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
                .f3 = Spec_Hash_Definitions_SHA2_512
              }
            ))
        )
        {
          case Spec_Hash_Definitions_SHA2_256:
            {
              sw12 = (uint32_t)65U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_384:
            {
              sw12 = (uint32_t)97U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_512:
            {
              sw12 = (uint32_t)129U;
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        uint32_t len4 = (uint32_t)9U + (uint32_t)10U + (uint32_t)10U + sw12;
        KRML_CHECK_SIZE(sizeof (uint8_t), len4);
        uint8_t *tmp = alloca(len4 * sizeof (uint8_t));
        memset(tmp, 0U, len4 * sizeof (uint8_t));
        uint8_t *uu____26 = tmp;
        uint8_t *uu____27 = uu____26;
        Spec_Agile_HPKE_aead
        scrut3 =
          Spec_Agile_HPKE_aead_of_cs((
              (Spec_Agile_HPKE_ciphersuite){
                .fst = Spec_Agile_DH_DH_Curve25519,
                .snd = Spec_Hash_Definitions_SHA2_256,
                .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
                .f3 = Spec_Hash_Definitions_SHA2_512
              }
            ));
        uint32_t ite2;
        if (scrut3.tag == Spec_Agile_HPKE_ExportOnly)
        {
          ite2 = (uint32_t)0U;
        }
        else if (scrut3.tag == Spec_Agile_HPKE_Seal)
        {
          ite2 = (uint32_t)12U;
        }
        else
        {
          ite2 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
        }
        store32_be(uu____27, ite2);
        memcpy(uu____26, uu____26 + (uint32_t)2U, (uint32_t)2U * sizeof (uint8_t));
        uint8_t *uu____28 = tmp + (uint32_t)2U;
        uu____28[0U] = (uint8_t)0x48U;
        uu____28[1U] = (uint8_t)0x50U;
        uu____28[2U] = (uint8_t)0x4bU;
        uu____28[3U] = (uint8_t)0x45U;
        uu____28[4U] = (uint8_t)0x2dU;
        uu____28[5U] = (uint8_t)0x76U;
        uu____28[6U] = (uint8_t)0x31U;
        memcpy(tmp + (uint32_t)9U, suite_id, (uint32_t)10U * sizeof (uint8_t));
        memcpy(tmp + (uint32_t)9U + (uint32_t)10U,
          label_base_nonce,
          (uint32_t)10U * sizeof (uint8_t));
        uint8_t *uu____29 = tmp + (uint32_t)9U + (uint32_t)10U + (uint32_t)10U;
        uint32_t sw;
        switch
        (
          Spec_Agile_HPKE_hash_of_cs((
              (Spec_Agile_HPKE_ciphersuite){
                .fst = Spec_Agile_DH_DH_Curve25519,
                .snd = Spec_Hash_Definitions_SHA2_256,
                .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
                .f3 = Spec_Hash_Definitions_SHA2_512
              }
            ))
        )
        {
          case Spec_Hash_Definitions_SHA2_256:
            {
              sw = (uint32_t)65U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_384:
            {
              sw = (uint32_t)97U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_512:
            {
              sw = (uint32_t)129U;
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        memcpy(uu____29, o_context, sw * sizeof (uint8_t));
        uint32_t sw13;
        switch
        (
          Spec_Agile_HPKE_hash_of_cs((
              (Spec_Agile_HPKE_ciphersuite){
                .fst = Spec_Agile_DH_DH_Curve25519,
                .snd = Spec_Hash_Definitions_SHA2_256,
                .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
                .f3 = Spec_Hash_Definitions_SHA2_512
              }
            ))
        )
        {
          case Spec_Hash_Definitions_SHA2_256:
            {
              sw13 = (uint32_t)32U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_384:
            {
              sw13 = (uint32_t)48U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_512:
            {
              sw13 = (uint32_t)64U;
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        Spec_Agile_HPKE_aead
        scrut =
          Spec_Agile_HPKE_aead_of_cs((
              (Spec_Agile_HPKE_ciphersuite){
                .fst = Spec_Agile_DH_DH_Curve25519,
                .snd = Spec_Hash_Definitions_SHA2_256,
                .thd = { .tag = Spec_Agile_HPKE_Seal, .alg = Spec_Agile_AEAD_CHACHA20_POLY1305 },
                .f3 = Spec_Hash_Definitions_SHA2_512
              }
            ));
        uint32_t ite;
        if (scrut.tag == Spec_Agile_HPKE_ExportOnly)
        {
          ite = (uint32_t)0U;
        }
        else if (scrut.tag == Spec_Agile_HPKE_Seal)
        {
          ite = (uint32_t)12U;
        }
        else
        {
          ite = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
        }
        Hacl_HKDF_expand_sha2_512(o_ctx.ctx_nonce, o_secret, sw13, tmp, len4, ite);
        o_ctx.ctx_seq[0U] = (uint64_t)0U;
      }
      return (uint32_t)0U;
    }
    return (uint32_t)1U;
  }
  return (uint32_t)1U;
}

uint32_t
Hacl_HPKE_Curve64_CP128_SHA512_sealBase(
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
  uint8_t ctx_exporter[64U] = { 0U };
  Hacl_Impl_HPKE_context_s
  o_ctx =
    {
      .ctx_key = ctx_key,
      .ctx_nonce = ctx_nonce,
      .ctx_seq = &ctx_seq,
      .ctx_exporter = ctx_exporter
    };
  uint32_t
  res = Hacl_HPKE_Curve64_CP128_SHA512_setupBaseS(o_enc, o_ctx, skE, pkR, infolen, info);
  if (res == (uint32_t)0U)
  {
    uint8_t nonce[12U] = { 0U };
    uint64_t s = o_ctx.ctx_seq[0U];
    uint8_t enc[12U] = { 0U };
    store64_be(enc + (uint32_t)4U, s);
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)12U; i++)
    {
      uint8_t xi = enc[i];
      uint8_t yi = o_ctx.ctx_nonce[i];
      nonce[i] = xi ^ yi;
    }
    Hacl_Chacha20Poly1305_128_aead_encrypt(o_ctx.ctx_key,
      nonce,
      aadlen,
      aad,
      plainlen,
      plain,
      o_ct,
      o_ct + plainlen);
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
    uint32_t res10 = res1;
    return res10;
  }
  return (uint32_t)1U;
}

uint32_t
Hacl_HPKE_Curve64_CP128_SHA512_openBase(
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
  uint8_t ctx_exporter[64U] = { 0U };
  Hacl_Impl_HPKE_context_s
  o_ctx =
    {
      .ctx_key = ctx_key,
      .ctx_nonce = ctx_nonce,
      .ctx_seq = &ctx_seq,
      .ctx_exporter = ctx_exporter
    };
  uint32_t res = Hacl_HPKE_Curve64_CP128_SHA512_setupBaseR(o_ctx, pkE, skR, infolen, info);
  if (res == (uint32_t)0U)
  {
    uint8_t nonce[12U] = { 0U };
    uint64_t s = o_ctx.ctx_seq[0U];
    uint8_t enc[12U] = { 0U };
    store64_be(enc + (uint32_t)4U, s);
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)12U; i++)
    {
      uint8_t xi = enc[i];
      uint8_t yi = o_ctx.ctx_nonce[i];
      nonce[i] = xi ^ yi;
    }
    uint32_t
    res1 =
      Hacl_Chacha20Poly1305_128_aead_decrypt(o_ctx.ctx_key,
        nonce,
        aadlen,
        aad,
        ctlen - (uint32_t)16U,
        o_pt,
        ct,
        ct + ctlen - (uint32_t)16U);
    if (res1 == (uint32_t)0U)
    {
      uint64_t s1 = o_ctx.ctx_seq[0U];
      if (s1 == (uint64_t)18446744073709551615U)
      {
        return (uint32_t)1U;
      }
      uint64_t s_ = s1 + (uint64_t)1U;
      o_ctx.ctx_seq[0U] = s_;
      return (uint32_t)0U;
    }
    return (uint32_t)1U;
  }
  return (uint32_t)1U;
}

