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


#include "EverCrypt_Hash.h"

#include "internal/Vale.h"
#include "internal/Hacl_Hash_SHA2.h"
#include "internal/Hacl_Hash_SHA1.h"
#include "internal/Hacl_Hash_MD5.h"
#include "internal/Hacl_Hash_Blake2.h"

C_String_t EverCrypt_Hash_string_of_alg(Spec_Hash_Definitions_hash_alg uu___)
{
  switch (uu___)
  {
    case Spec_Hash_Definitions_MD5:
      {
        return "MD5";
      }
    case Spec_Hash_Definitions_SHA1:
      {
        return "SHA1";
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        return "SHA2_224";
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        return "SHA2_256";
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        return "SHA2_384";
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        return "SHA2_512";
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        return "Blake2S";
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        return "Blake2B";
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

bool
EverCrypt_Hash_uu___is_MD5_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_MD5_s)
  {
    return true;
  }
  return false;
}

bool
EverCrypt_Hash_uu___is_SHA1_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA1_s)
  {
    return true;
  }
  return false;
}

bool
EverCrypt_Hash_uu___is_SHA2_224_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_224_s)
  {
    return true;
  }
  return false;
}

bool
EverCrypt_Hash_uu___is_SHA2_256_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_256_s)
  {
    return true;
  }
  return false;
}

bool
EverCrypt_Hash_uu___is_SHA2_384_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_384_s)
  {
    return true;
  }
  return false;
}

bool
EverCrypt_Hash_uu___is_SHA2_512_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_SHA2_512_s)
  {
    return true;
  }
  return false;
}

bool
EverCrypt_Hash_uu___is_Blake2S_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_Blake2S_s)
  {
    return true;
  }
  return false;
}

bool
EverCrypt_Hash_uu___is_Blake2B_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
)
{
  if (projectee.tag == EverCrypt_Hash_Blake2B_s)
  {
    return true;
  }
  return false;
}

Spec_Hash_Definitions_hash_alg EverCrypt_Hash_alg_of_state(EverCrypt_Hash_state_s *s)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    return Spec_Hash_Definitions_MD5;
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    return Spec_Hash_Definitions_SHA1;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    return Spec_Hash_Definitions_SHA2_224;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    return Spec_Hash_Definitions_SHA2_256;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    return Spec_Hash_Definitions_SHA2_384;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    return Spec_Hash_Definitions_SHA2_512;
  }
  if (scrut.tag == EverCrypt_Hash_Blake2S_s)
  {
    return Spec_Hash_Definitions_Blake2S;
  }
  if (scrut.tag == EverCrypt_Hash_Blake2B_s)
  {
    return Spec_Hash_Definitions_Blake2B;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

EverCrypt_Hash_state_s *EverCrypt_Hash_create_in(Spec_Hash_Definitions_hash_alg a)
{
  EverCrypt_Hash_state_s s;
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        uint32_t *buf = KRML_HOST_CALLOC((uint32_t)4U, sizeof (uint32_t));
        s = ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_MD5_s, { .case_MD5_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        uint32_t *buf = KRML_HOST_CALLOC((uint32_t)5U, sizeof (uint32_t));
        s = ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_SHA1_s, { .case_SHA1_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        uint32_t *buf = KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint32_t));
        s =
          ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_SHA2_224_s, { .case_SHA2_224_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        uint32_t *buf = KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint32_t));
        s =
          ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_SHA2_256_s, { .case_SHA2_256_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        uint64_t *buf = KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint64_t));
        s =
          ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_SHA2_384_s, { .case_SHA2_384_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        uint64_t *buf = KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint64_t));
        s =
          ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_SHA2_512_s, { .case_SHA2_512_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        uint32_t *buf = KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint32_t));
        s = ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_Blake2S_s, { .case_Blake2S_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        uint64_t *buf = KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint64_t));
        s = ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_Blake2B_s, { .case_Blake2B_s = buf } });
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  KRML_CHECK_SIZE(sizeof (EverCrypt_Hash_state_s), (uint32_t)1U);
  EverCrypt_Hash_state_s *buf = KRML_HOST_MALLOC(sizeof (EverCrypt_Hash_state_s));
  buf[0U] = s;
  return buf;
}

EverCrypt_Hash_state_s *EverCrypt_Hash_create(Spec_Hash_Definitions_hash_alg a)
{
  return EverCrypt_Hash_create_in(a);
}

void EverCrypt_Hash_init(EverCrypt_Hash_state_s *s)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    Hacl_Hash_Core_MD5_legacy_init(p1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    Hacl_Hash_Core_SHA1_legacy_init(p1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    Hacl_Hash_Core_SHA2_init_224(p1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    Hacl_Hash_Core_SHA2_init_256(p1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    Hacl_Hash_Core_SHA2_init_384(p1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    Hacl_Hash_Core_SHA2_init_512(p1);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_Blake2S_s)
  {
    uint32_t *p1 = scrut.case_Blake2S_s;
    uint32_t *r0 = p1 + (uint32_t)0U * (uint32_t)4U;
    uint32_t *r1 = p1 + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r2 = p1 + (uint32_t)2U * (uint32_t)4U;
    uint32_t *r3 = p1 + (uint32_t)3U * (uint32_t)4U;
    uint32_t iv0 = Hacl_Impl_Blake2_Constants_ivTable_S[0U];
    uint32_t iv1 = Hacl_Impl_Blake2_Constants_ivTable_S[1U];
    uint32_t iv2 = Hacl_Impl_Blake2_Constants_ivTable_S[2U];
    uint32_t iv3 = Hacl_Impl_Blake2_Constants_ivTable_S[3U];
    uint32_t iv4 = Hacl_Impl_Blake2_Constants_ivTable_S[4U];
    uint32_t iv5 = Hacl_Impl_Blake2_Constants_ivTable_S[5U];
    uint32_t iv6 = Hacl_Impl_Blake2_Constants_ivTable_S[6U];
    uint32_t iv7 = Hacl_Impl_Blake2_Constants_ivTable_S[7U];
    r2[0U] = iv0;
    r2[1U] = iv1;
    r2[2U] = iv2;
    r2[3U] = iv3;
    r3[0U] = iv4;
    r3[1U] = iv5;
    r3[2U] = iv6;
    r3[3U] = iv7;
    uint32_t kk_shift_8 = (uint32_t)0U;
    uint32_t iv0_ = iv0 ^ ((uint32_t)0x01010000U ^ (kk_shift_8 ^ (uint32_t)32U));
    r0[0U] = iv0_;
    r0[1U] = iv1;
    r0[2U] = iv2;
    r0[3U] = iv3;
    r1[0U] = iv4;
    r1[1U] = iv5;
    r1[2U] = iv6;
    r1[3U] = iv7;
    uint64_t uu____0 = (uint64_t)0U;
    return;
  }
  if (scrut.tag == EverCrypt_Hash_Blake2B_s)
  {
    uint64_t *p1 = scrut.case_Blake2B_s;
    uint64_t *r0 = p1 + (uint32_t)0U * (uint32_t)4U;
    uint64_t *r1 = p1 + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r2 = p1 + (uint32_t)2U * (uint32_t)4U;
    uint64_t *r3 = p1 + (uint32_t)3U * (uint32_t)4U;
    uint64_t iv0 = Hacl_Impl_Blake2_Constants_ivTable_B[0U];
    uint64_t iv1 = Hacl_Impl_Blake2_Constants_ivTable_B[1U];
    uint64_t iv2 = Hacl_Impl_Blake2_Constants_ivTable_B[2U];
    uint64_t iv3 = Hacl_Impl_Blake2_Constants_ivTable_B[3U];
    uint64_t iv4 = Hacl_Impl_Blake2_Constants_ivTable_B[4U];
    uint64_t iv5 = Hacl_Impl_Blake2_Constants_ivTable_B[5U];
    uint64_t iv6 = Hacl_Impl_Blake2_Constants_ivTable_B[6U];
    uint64_t iv7 = Hacl_Impl_Blake2_Constants_ivTable_B[7U];
    r2[0U] = iv0;
    r2[1U] = iv1;
    r2[2U] = iv2;
    r2[3U] = iv3;
    r3[0U] = iv4;
    r3[1U] = iv5;
    r3[2U] = iv6;
    r3[3U] = iv7;
    uint64_t kk_shift_8 = (uint64_t)(uint32_t)0U << (uint32_t)8U;
    uint64_t iv0_ = iv0 ^ ((uint64_t)0x01010000U ^ (kk_shift_8 ^ (uint64_t)(uint32_t)64U));
    r0[0U] = iv0_;
    r0[1U] = iv1;
    r0[2U] = iv2;
    r0[3U] = iv3;
    r1[0U] = iv4;
    r1[1U] = iv5;
    r1[2U] = iv6;
    r1[3U] = iv7;
    FStar_UInt128_uint128 uu____1 = FStar_UInt128_uint64_to_uint128((uint64_t)0U);
    return;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

static uint32_t
k224_256[64U] =
  {
    (uint32_t)0x428a2f98U, (uint32_t)0x71374491U, (uint32_t)0xb5c0fbcfU, (uint32_t)0xe9b5dba5U,
    (uint32_t)0x3956c25bU, (uint32_t)0x59f111f1U, (uint32_t)0x923f82a4U, (uint32_t)0xab1c5ed5U,
    (uint32_t)0xd807aa98U, (uint32_t)0x12835b01U, (uint32_t)0x243185beU, (uint32_t)0x550c7dc3U,
    (uint32_t)0x72be5d74U, (uint32_t)0x80deb1feU, (uint32_t)0x9bdc06a7U, (uint32_t)0xc19bf174U,
    (uint32_t)0xe49b69c1U, (uint32_t)0xefbe4786U, (uint32_t)0x0fc19dc6U, (uint32_t)0x240ca1ccU,
    (uint32_t)0x2de92c6fU, (uint32_t)0x4a7484aaU, (uint32_t)0x5cb0a9dcU, (uint32_t)0x76f988daU,
    (uint32_t)0x983e5152U, (uint32_t)0xa831c66dU, (uint32_t)0xb00327c8U, (uint32_t)0xbf597fc7U,
    (uint32_t)0xc6e00bf3U, (uint32_t)0xd5a79147U, (uint32_t)0x06ca6351U, (uint32_t)0x14292967U,
    (uint32_t)0x27b70a85U, (uint32_t)0x2e1b2138U, (uint32_t)0x4d2c6dfcU, (uint32_t)0x53380d13U,
    (uint32_t)0x650a7354U, (uint32_t)0x766a0abbU, (uint32_t)0x81c2c92eU, (uint32_t)0x92722c85U,
    (uint32_t)0xa2bfe8a1U, (uint32_t)0xa81a664bU, (uint32_t)0xc24b8b70U, (uint32_t)0xc76c51a3U,
    (uint32_t)0xd192e819U, (uint32_t)0xd6990624U, (uint32_t)0xf40e3585U, (uint32_t)0x106aa070U,
    (uint32_t)0x19a4c116U, (uint32_t)0x1e376c08U, (uint32_t)0x2748774cU, (uint32_t)0x34b0bcb5U,
    (uint32_t)0x391c0cb3U, (uint32_t)0x4ed8aa4aU, (uint32_t)0x5b9cca4fU, (uint32_t)0x682e6ff3U,
    (uint32_t)0x748f82eeU, (uint32_t)0x78a5636fU, (uint32_t)0x84c87814U, (uint32_t)0x8cc70208U,
    (uint32_t)0x90befffaU, (uint32_t)0xa4506cebU, (uint32_t)0xbef9a3f7U, (uint32_t)0xc67178f2U
  };

void EverCrypt_Hash_update_multi_256(uint32_t *s, uint8_t *blocks, uint32_t n)
{
  bool has_shaext = EverCrypt_AutoConfig2_has_shaext();
  bool has_sse = EverCrypt_AutoConfig2_has_sse();
  #if HACL_CAN_COMPILE_VALE
  if (has_shaext && has_sse)
  {
    uint64_t n1 = (uint64_t)n;
    uint64_t scrut = sha256_update(s, blocks, n1, k224_256);
    return;
  }
  #endif
  Hacl_Hash_SHA2_update_multi_256(s, blocks, n);
}

void EverCrypt_Hash_update2(EverCrypt_Hash_state_s *s, uint64_t prevlen, uint8_t *block)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    Hacl_Hash_Core_MD5_legacy_update(p1, block);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    Hacl_Hash_Core_SHA1_legacy_update(p1, block);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    EverCrypt_Hash_update_multi_256(p1, block, (uint32_t)1U);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    EverCrypt_Hash_update_multi_256(p1, block, (uint32_t)1U);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    Hacl_Hash_Core_SHA2_update_384(p1, block);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    Hacl_Hash_Core_SHA2_update_512(p1, block);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_Blake2S_s)
  {
    uint32_t *p1 = scrut.case_Blake2S_s;
    uint64_t uu____0 = Hacl_Hash_Core_Blake2_update_blake2s_32(p1, prevlen, block);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_Blake2B_s)
  {
    uint64_t *p1 = scrut.case_Blake2B_s;
    FStar_UInt128_uint128
    uu____1 =
      Hacl_Hash_Core_Blake2_update_blake2b_32(p1,
        FStar_UInt128_uint64_to_uint128(prevlen),
        block);
    return;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

KRML_DEPRECATED("Use update2 instead")

void EverCrypt_Hash_update(EverCrypt_Hash_state_s *s, uint8_t *block)
{
  EverCrypt_Hash_update2(s, (uint64_t)0U, block);
}

void
EverCrypt_Hash_update_multi2(
  EverCrypt_Hash_state_s *s,
  uint64_t prevlen,
  uint8_t *blocks,
  uint32_t len
)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    uint32_t n = len / (uint32_t)64U;
    Hacl_Hash_MD5_legacy_update_multi(p1, blocks, n);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    uint32_t n = len / (uint32_t)64U;
    Hacl_Hash_SHA1_legacy_update_multi(p1, blocks, n);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    uint32_t n = len / (uint32_t)64U;
    EverCrypt_Hash_update_multi_256(p1, blocks, n);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    uint32_t n = len / (uint32_t)64U;
    EverCrypt_Hash_update_multi_256(p1, blocks, n);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    uint32_t n = len / (uint32_t)128U;
    Hacl_Hash_SHA2_update_multi_384(p1, blocks, n);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    uint32_t n = len / (uint32_t)128U;
    Hacl_Hash_SHA2_update_multi_512(p1, blocks, n);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_Blake2S_s)
  {
    uint32_t *p1 = scrut.case_Blake2S_s;
    uint32_t n = len / (uint32_t)64U;
    uint64_t uu____0 = Hacl_Hash_Blake2_update_multi_blake2s_32(p1, prevlen, blocks, n);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_Blake2B_s)
  {
    uint64_t *p1 = scrut.case_Blake2B_s;
    uint32_t n = len / (uint32_t)128U;
    FStar_UInt128_uint128
    uu____1 =
      Hacl_Hash_Blake2_update_multi_blake2b_32(p1,
        FStar_UInt128_uint64_to_uint128(prevlen),
        blocks,
        n);
    return;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

KRML_DEPRECATED("Use update_multi2 instead")

void EverCrypt_Hash_update_multi(EverCrypt_Hash_state_s *s, uint8_t *blocks, uint32_t len)
{
  EverCrypt_Hash_update_multi2(s, (uint64_t)0U, blocks, len);
}

void
EverCrypt_Hash_update_last_256(
  uint32_t *s,
  uint64_t input,
  uint8_t *input_len,
  uint32_t input_len1
)
{
  uint32_t blocks_n = input_len1 / (uint32_t)64U;
  uint32_t blocks_len = blocks_n * (uint32_t)64U;
  uint8_t *blocks = input_len;
  uint32_t rest_len = input_len1 - blocks_len;
  uint8_t *rest = input_len + blocks_len;
  EverCrypt_Hash_update_multi_256(s, blocks, blocks_n);
  uint64_t total_input_len = input + (uint64_t)input_len1;
  uint32_t
  pad_len =
    (uint32_t)1U
    +
      ((uint32_t)128U - ((uint32_t)9U + (uint32_t)(total_input_len % (uint64_t)(uint32_t)64U)))
      % (uint32_t)64U
    + (uint32_t)8U;
  uint32_t tmp_len = rest_len + pad_len;
  uint8_t tmp_twoblocks[128U] = { 0U };
  uint8_t *tmp = tmp_twoblocks;
  uint8_t *tmp_rest = tmp;
  uint8_t *tmp_pad = tmp + rest_len;
  memcpy(tmp_rest, rest, rest_len * sizeof (uint8_t));
  Hacl_Hash_Core_SHA2_pad_256(total_input_len, tmp_pad);
  EverCrypt_Hash_update_multi_256(s, tmp, tmp_len / (uint32_t)64U);
}

void
EverCrypt_Hash_update_last2(
  EverCrypt_Hash_state_s *s,
  uint64_t prev_len,
  uint8_t *last,
  uint32_t last_len
)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    Hacl_Hash_MD5_legacy_update_last(p1, prev_len, last, last_len);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    Hacl_Hash_SHA1_legacy_update_last(p1, prev_len, last, last_len);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    EverCrypt_Hash_update_last_256(p1, prev_len, last, last_len);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    EverCrypt_Hash_update_last_256(p1, prev_len, last, last_len);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    Hacl_Hash_SHA2_update_last_384(p1, FStar_UInt128_uint64_to_uint128(prev_len), last, last_len);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    Hacl_Hash_SHA2_update_last_512(p1, FStar_UInt128_uint64_to_uint128(prev_len), last, last_len);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_Blake2S_s)
  {
    uint32_t *p1 = scrut.case_Blake2S_s;
    uint64_t x = Hacl_Hash_Blake2_update_last_blake2s_32(p1, prev_len, prev_len, last, last_len);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_Blake2B_s)
  {
    uint64_t *p1 = scrut.case_Blake2B_s;
    FStar_UInt128_uint128
    x =
      Hacl_Hash_Blake2_update_last_blake2b_32(p1,
        FStar_UInt128_uint64_to_uint128(prev_len),
        FStar_UInt128_uint64_to_uint128(prev_len),
        last,
        last_len);
    return;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

KRML_DEPRECATED("Use update_last2 instead")

void EverCrypt_Hash_update_last(EverCrypt_Hash_state_s *s, uint8_t *last, uint64_t total_len)
{
  Spec_Hash_Definitions_hash_alg a = EverCrypt_Hash_alg_of_state(s);
  uint32_t sw;
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw = (uint32_t)128U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw = (uint32_t)128U;
        break;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        sw = (uint32_t)64U;
        break;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        sw = (uint32_t)128U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint64_t last_len = total_len % (uint64_t)sw;
  uint64_t prev_len = total_len - last_len;
  EverCrypt_Hash_update_last2(s, prev_len, last, (uint32_t)last_len);
}

void EverCrypt_Hash_finish(EverCrypt_Hash_state_s *s, uint8_t *dst)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    Hacl_Hash_Core_MD5_legacy_finish(p1, dst);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    Hacl_Hash_Core_SHA1_legacy_finish(p1, dst);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    Hacl_Hash_Core_SHA2_finish_224(p1, dst);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    Hacl_Hash_Core_SHA2_finish_256(p1, dst);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    Hacl_Hash_Core_SHA2_finish_384(p1, dst);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    Hacl_Hash_Core_SHA2_finish_512(p1, dst);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_Blake2S_s)
  {
    uint32_t *p1 = scrut.case_Blake2S_s;
    Hacl_Hash_Core_Blake2_finish_blake2s_32(p1, (uint64_t)0U, dst);
    return;
  }
  if (scrut.tag == EverCrypt_Hash_Blake2B_s)
  {
    uint64_t *p1 = scrut.case_Blake2B_s;
    Hacl_Hash_Core_Blake2_finish_blake2b_32(p1,
      FStar_UInt128_uint64_to_uint128((uint64_t)0U),
      dst);
    return;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

void EverCrypt_Hash_free(EverCrypt_Hash_state_s *s)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_Blake2S_s)
  {
    uint32_t *p1 = scrut.case_Blake2S_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == EverCrypt_Hash_Blake2B_s)
  {
    uint64_t *p1 = scrut.case_Blake2B_s;
    KRML_HOST_FREE(p1);
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
  KRML_HOST_FREE(s);
}

void EverCrypt_Hash_copy(EverCrypt_Hash_state_s *s_src, EverCrypt_Hash_state_s *s_dst)
{
  EverCrypt_Hash_state_s scrut = *s_src;
  if (scrut.tag == EverCrypt_Hash_MD5_s)
  {
    uint32_t *p_src = scrut.case_MD5_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint32_t *p_dst;
    if (x1.tag == EverCrypt_Hash_MD5_s)
    {
      p_dst = x1.case_MD5_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint32_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)4U * sizeof (uint32_t));
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA1_s)
  {
    uint32_t *p_src = scrut.case_SHA1_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint32_t *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA1_s)
    {
      p_dst = x1.case_SHA1_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint32_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)5U * sizeof (uint32_t));
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_224_s)
  {
    uint32_t *p_src = scrut.case_SHA2_224_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint32_t *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA2_224_s)
    {
      p_dst = x1.case_SHA2_224_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint32_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)8U * sizeof (uint32_t));
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_256_s)
  {
    uint32_t *p_src = scrut.case_SHA2_256_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint32_t *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA2_256_s)
    {
      p_dst = x1.case_SHA2_256_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint32_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)8U * sizeof (uint32_t));
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_384_s)
  {
    uint64_t *p_src = scrut.case_SHA2_384_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint64_t *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA2_384_s)
    {
      p_dst = x1.case_SHA2_384_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint64_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)8U * sizeof (uint64_t));
    return;
  }
  if (scrut.tag == EverCrypt_Hash_SHA2_512_s)
  {
    uint64_t *p_src = scrut.case_SHA2_512_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint64_t *p_dst;
    if (x1.tag == EverCrypt_Hash_SHA2_512_s)
    {
      p_dst = x1.case_SHA2_512_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint64_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)8U * sizeof (uint64_t));
    return;
  }
  if (scrut.tag == EverCrypt_Hash_Blake2S_s)
  {
    uint32_t *p_src = scrut.case_Blake2S_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint32_t *p_dst;
    if (x1.tag == EverCrypt_Hash_Blake2S_s)
    {
      p_dst = x1.case_Blake2S_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint32_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)16U * sizeof (uint32_t));
    return;
  }
  if (scrut.tag == EverCrypt_Hash_Blake2B_s)
  {
    uint64_t *p_src = scrut.case_Blake2B_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint64_t *p_dst;
    if (x1.tag == EverCrypt_Hash_Blake2B_s)
    {
      p_dst = x1.case_Blake2B_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint64_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)16U * sizeof (uint64_t));
    return;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

void EverCrypt_Hash_hash_256(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint32_t
  scrut[8U] =
    {
      (uint32_t)0x6a09e667U, (uint32_t)0xbb67ae85U, (uint32_t)0x3c6ef372U, (uint32_t)0xa54ff53aU,
      (uint32_t)0x510e527fU, (uint32_t)0x9b05688cU, (uint32_t)0x1f83d9abU, (uint32_t)0x5be0cd19U
    };
  uint32_t *s = scrut;
  uint32_t blocks_n0 = input_len / (uint32_t)64U;
  uint32_t blocks_n1;
  if (input_len % (uint32_t)64U == (uint32_t)0U && blocks_n0 > (uint32_t)0U)
  {
    blocks_n1 = blocks_n0 - (uint32_t)1U;
  }
  else
  {
    blocks_n1 = blocks_n0;
  }
  uint32_t blocks_len0 = blocks_n1 * (uint32_t)64U;
  uint8_t *blocks0 = input;
  uint32_t rest_len0 = input_len - blocks_len0;
  uint8_t *rest0 = input + blocks_len0;
  uint32_t blocks_n = blocks_n1;
  uint32_t blocks_len = blocks_len0;
  uint8_t *blocks = blocks0;
  uint32_t rest_len = rest_len0;
  uint8_t *rest = rest0;
  EverCrypt_Hash_update_multi_256(s, blocks, blocks_n);
  EverCrypt_Hash_update_last_256(s, (uint64_t)blocks_len, rest, rest_len);
  Hacl_Hash_Core_SHA2_finish_256(s, dst);
}

void EverCrypt_Hash_hash_224(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint32_t
  scrut[8U] =
    {
      (uint32_t)0xc1059ed8U, (uint32_t)0x367cd507U, (uint32_t)0x3070dd17U, (uint32_t)0xf70e5939U,
      (uint32_t)0xffc00b31U, (uint32_t)0x68581511U, (uint32_t)0x64f98fa7U, (uint32_t)0xbefa4fa4U
    };
  uint32_t *s = scrut;
  uint32_t blocks_n0 = input_len / (uint32_t)64U;
  uint32_t blocks_n1;
  if (input_len % (uint32_t)64U == (uint32_t)0U && blocks_n0 > (uint32_t)0U)
  {
    blocks_n1 = blocks_n0 - (uint32_t)1U;
  }
  else
  {
    blocks_n1 = blocks_n0;
  }
  uint32_t blocks_len0 = blocks_n1 * (uint32_t)64U;
  uint8_t *blocks0 = input;
  uint32_t rest_len0 = input_len - blocks_len0;
  uint8_t *rest0 = input + blocks_len0;
  uint32_t blocks_n = blocks_n1;
  uint32_t blocks_len = blocks_len0;
  uint8_t *blocks = blocks0;
  uint32_t rest_len = rest_len0;
  uint8_t *rest = rest0;
  EverCrypt_Hash_update_multi_256(s, blocks, blocks_n);
  EverCrypt_Hash_update_last_256(s, (uint64_t)blocks_len, rest, rest_len);
  Hacl_Hash_Core_SHA2_finish_224(s, dst);
}

void
EverCrypt_Hash_hash(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *dst,
  uint8_t *input,
  uint32_t len
)
{
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        Hacl_Hash_MD5_legacy_hash(input, len, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        Hacl_Hash_SHA1_legacy_hash(input, len, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        EverCrypt_Hash_hash_224(input, len, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        EverCrypt_Hash_hash_256(input, len, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        Hacl_Hash_SHA2_hash_384(input, len, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        Hacl_Hash_SHA2_hash_512(input, len, dst);
        break;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        Hacl_Hash_Blake2_hash_blake2s_32(input, len, dst);
        break;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        Hacl_Hash_Blake2_hash_blake2b_32(input, len, dst);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

uint32_t EverCrypt_Hash_Incremental_hash_len(Spec_Hash_Definitions_hash_alg a)
{
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        return (uint32_t)16U;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        return (uint32_t)20U;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        return (uint32_t)28U;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        return (uint32_t)32U;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        return (uint32_t)48U;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        return (uint32_t)64U;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        return (uint32_t)32U;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        return (uint32_t)64U;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

uint32_t EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_hash_alg a)
{
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        return (uint32_t)64U;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        return (uint32_t)64U;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        return (uint32_t)64U;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        return (uint32_t)64U;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        return (uint32_t)128U;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        return (uint32_t)128U;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        return (uint32_t)64U;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        return (uint32_t)128U;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____
*EverCrypt_Hash_Incremental_create_in(Spec_Hash_Definitions_hash_alg a)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), EverCrypt_Hash_Incremental_block_len(a));
  uint8_t *buf = KRML_HOST_CALLOC(EverCrypt_Hash_Incremental_block_len(a), sizeof (uint8_t));
  EverCrypt_Hash_state_s *block_state = EverCrypt_Hash_create_in(a);
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____
  s = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U };
  KRML_CHECK_SIZE(sizeof (Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____),
    (uint32_t)1U);
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____
  *p = KRML_HOST_MALLOC(sizeof (Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____));
  p[0U] = s;
  EverCrypt_Hash_init(block_state);
  return p;
}

void
EverCrypt_Hash_Incremental_init(Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *s;
  uint8_t *buf = scrut.buf;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  Spec_Hash_Definitions_hash_alg i = EverCrypt_Hash_alg_of_state(block_state);
  EverCrypt_Hash_init(block_state);
  s[0U] =
    (
      (Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____){
        .block_state = block_state,
        .buf = buf,
        .total_len = (uint64_t)0U
      }
    );
}

void
EverCrypt_Hash_Incremental_update(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ s = *p;
  EverCrypt_Hash_state_s *block_state = s.block_state;
  uint64_t total_len = s.total_len;
  Spec_Hash_Definitions_hash_alg i1 = EverCrypt_Hash_alg_of_state(block_state);
  uint32_t sz;
  if
  (
    total_len
    % (uint64_t)EverCrypt_Hash_Incremental_block_len(i1)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    sz = EverCrypt_Hash_Incremental_block_len(i1);
  }
  else
  {
    sz = (uint32_t)(total_len % (uint64_t)EverCrypt_Hash_Incremental_block_len(i1));
  }
  if (len <= EverCrypt_Hash_Incremental_block_len(i1) - sz)
  {
    Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ s1 = *p;
    EverCrypt_Hash_state_s *block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    Spec_Hash_Definitions_hash_alg i2 = EverCrypt_Hash_alg_of_state(block_state1);
    uint32_t sz1;
    if
    (
      total_len1
      % (uint64_t)EverCrypt_Hash_Incremental_block_len(i2)
      == (uint64_t)0U
      && total_len1 > (uint64_t)0U
    )
    {
      sz1 = EverCrypt_Hash_Incremental_block_len(i2);
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)EverCrypt_Hash_Incremental_block_len(i2));
    }
    uint8_t *buf2 = buf + sz1;
    memcpy(buf2, data, len * sizeof (uint8_t));
    uint64_t total_len2 = total_len1 + (uint64_t)len;
    *p
    =
      (
        (Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len2
        }
      );
    return;
  }
  if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ s1 = *p;
    EverCrypt_Hash_state_s *block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    Spec_Hash_Definitions_hash_alg i2 = EverCrypt_Hash_alg_of_state(block_state1);
    uint32_t sz1;
    if
    (
      total_len1
      % (uint64_t)EverCrypt_Hash_Incremental_block_len(i2)
      == (uint64_t)0U
      && total_len1 > (uint64_t)0U
    )
    {
      sz1 = EverCrypt_Hash_Incremental_block_len(i2);
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)EverCrypt_Hash_Incremental_block_len(i2));
    }
    if (!(sz1 == (uint32_t)0U))
    {
      uint64_t prevlen = total_len1 - (uint64_t)sz1;
      EverCrypt_Hash_update_multi2(block_state1,
        prevlen,
        buf,
        EverCrypt_Hash_Incremental_block_len(i2));
    }
    uint32_t ite;
    if
    (
      (uint64_t)len
      % (uint64_t)EverCrypt_Hash_Incremental_block_len(i2)
      == (uint64_t)0U
      && (uint64_t)len > (uint64_t)0U
    )
    {
      ite = EverCrypt_Hash_Incremental_block_len(i2);
    }
    else
    {
      ite = (uint32_t)((uint64_t)len % (uint64_t)EverCrypt_Hash_Incremental_block_len(i2));
    }
    uint32_t n_blocks = (len - ite) / EverCrypt_Hash_Incremental_block_len(i2);
    uint32_t data1_len = n_blocks * EverCrypt_Hash_Incremental_block_len(i2);
    uint32_t data2_len = len - data1_len;
    uint8_t *data1 = data;
    uint8_t *data2 = data + data1_len;
    EverCrypt_Hash_update_multi2(block_state1, total_len1, data1, data1_len);
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *p
    =
      (
        (Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)len
        }
      );
    return;
  }
  uint32_t diff = EverCrypt_Hash_Incremental_block_len(i1) - sz;
  uint8_t *data1 = data;
  uint8_t *data2 = data + diff;
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ s1 = *p;
  EverCrypt_Hash_state_s *block_state10 = s1.block_state;
  uint8_t *buf0 = s1.buf;
  uint64_t total_len10 = s1.total_len;
  Spec_Hash_Definitions_hash_alg i20 = EverCrypt_Hash_alg_of_state(block_state10);
  uint32_t sz10;
  if
  (
    total_len10
    % (uint64_t)EverCrypt_Hash_Incremental_block_len(i20)
    == (uint64_t)0U
    && total_len10 > (uint64_t)0U
  )
  {
    sz10 = EverCrypt_Hash_Incremental_block_len(i20);
  }
  else
  {
    sz10 = (uint32_t)(total_len10 % (uint64_t)EverCrypt_Hash_Incremental_block_len(i20));
  }
  uint8_t *buf2 = buf0 + sz10;
  memcpy(buf2, data1, diff * sizeof (uint8_t));
  uint64_t total_len2 = total_len10 + (uint64_t)diff;
  *p
  =
    (
      (Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____){
        .block_state = block_state10,
        .buf = buf0,
        .total_len = total_len2
      }
    );
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ s10 = *p;
  EverCrypt_Hash_state_s *block_state1 = s10.block_state;
  uint8_t *buf = s10.buf;
  uint64_t total_len1 = s10.total_len;
  Spec_Hash_Definitions_hash_alg i2 = EverCrypt_Hash_alg_of_state(block_state1);
  uint32_t sz1;
  if
  (
    total_len1
    % (uint64_t)EverCrypt_Hash_Incremental_block_len(i2)
    == (uint64_t)0U
    && total_len1 > (uint64_t)0U
  )
  {
    sz1 = EverCrypt_Hash_Incremental_block_len(i2);
  }
  else
  {
    sz1 = (uint32_t)(total_len1 % (uint64_t)EverCrypt_Hash_Incremental_block_len(i2));
  }
  if (!(sz1 == (uint32_t)0U))
  {
    uint64_t prevlen = total_len1 - (uint64_t)sz1;
    EverCrypt_Hash_update_multi2(block_state1,
      prevlen,
      buf,
      EverCrypt_Hash_Incremental_block_len(i2));
  }
  uint32_t ite;
  if
  (
    (uint64_t)(len - diff)
    % (uint64_t)EverCrypt_Hash_Incremental_block_len(i2)
    == (uint64_t)0U
    && (uint64_t)(len - diff) > (uint64_t)0U
  )
  {
    ite = EverCrypt_Hash_Incremental_block_len(i2);
  }
  else
  {
    ite = (uint32_t)((uint64_t)(len - diff) % (uint64_t)EverCrypt_Hash_Incremental_block_len(i2));
  }
  uint32_t n_blocks = (len - diff - ite) / EverCrypt_Hash_Incremental_block_len(i2);
  uint32_t data1_len = n_blocks * EverCrypt_Hash_Incremental_block_len(i2);
  uint32_t data2_len = len - diff - data1_len;
  uint8_t *data11 = data2;
  uint8_t *data21 = data2 + data1_len;
  EverCrypt_Hash_update_multi2(block_state1, total_len1, data11, data1_len);
  uint8_t *dst = buf;
  memcpy(dst, data21, data2_len * sizeof (uint8_t));
  *p
  =
    (
      (Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____){
        .block_state = block_state1,
        .buf = buf,
        .total_len = total_len1 + (uint64_t)(len - diff)
      }
    );
}

void
EverCrypt_Hash_Incremental_finish_md5(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *p;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_MD5)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_MD5);
  }
  else
  {
    r =
      (uint32_t)(total_len
      % (uint64_t)EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_MD5));
  }
  uint8_t *buf_1 = buf_;
  uint32_t buf[4U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_MD5_s, { .case_MD5_s = buf } };
  EverCrypt_Hash_state_s tmp_block_state = s;
  EverCrypt_Hash_copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if
  (
    r
    % EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_MD5)
    == (uint32_t)0U
    && r > (uint32_t)0U
  )
  {
    ite = EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_MD5);
  }
  else
  {
    ite = r % EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_MD5);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  EverCrypt_Hash_update_multi2(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  EverCrypt_Hash_update_last2(&tmp_block_state, prev_len_last, buf_last, r);
  EverCrypt_Hash_finish(&tmp_block_state, dst);
}

void
EverCrypt_Hash_Incremental_finish_sha1(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *p;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA1)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA1);
  }
  else
  {
    r =
      (uint32_t)(total_len
      % (uint64_t)EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA1));
  }
  uint8_t *buf_1 = buf_;
  uint32_t buf[5U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_SHA1_s, { .case_SHA1_s = buf } };
  EverCrypt_Hash_state_s tmp_block_state = s;
  EverCrypt_Hash_copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if
  (
    r
    % EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA1)
    == (uint32_t)0U
    && r > (uint32_t)0U
  )
  {
    ite = EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA1);
  }
  else
  {
    ite = r % EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA1);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  EverCrypt_Hash_update_multi2(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  EverCrypt_Hash_update_last2(&tmp_block_state, prev_len_last, buf_last, r);
  EverCrypt_Hash_finish(&tmp_block_state, dst);
}

void
EverCrypt_Hash_Incremental_finish_sha224(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *p;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_224)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_224);
  }
  else
  {
    r =
      (uint32_t)(total_len
      % (uint64_t)EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_224));
  }
  uint8_t *buf_1 = buf_;
  uint32_t buf[8U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_SHA2_224_s, { .case_SHA2_224_s = buf } };
  EverCrypt_Hash_state_s tmp_block_state = s;
  EverCrypt_Hash_copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if
  (
    r
    % EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_224)
    == (uint32_t)0U
    && r > (uint32_t)0U
  )
  {
    ite = EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_224);
  }
  else
  {
    ite = r % EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_224);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  EverCrypt_Hash_update_multi2(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  EverCrypt_Hash_update_last2(&tmp_block_state, prev_len_last, buf_last, r);
  EverCrypt_Hash_finish(&tmp_block_state, dst);
}

void
EverCrypt_Hash_Incremental_finish_sha256(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *p;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_256)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_256);
  }
  else
  {
    r =
      (uint32_t)(total_len
      % (uint64_t)EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_256));
  }
  uint8_t *buf_1 = buf_;
  uint32_t buf[8U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_SHA2_256_s, { .case_SHA2_256_s = buf } };
  EverCrypt_Hash_state_s tmp_block_state = s;
  EverCrypt_Hash_copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if
  (
    r
    % EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_256)
    == (uint32_t)0U
    && r > (uint32_t)0U
  )
  {
    ite = EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_256);
  }
  else
  {
    ite = r % EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_256);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  EverCrypt_Hash_update_multi2(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  EverCrypt_Hash_update_last2(&tmp_block_state, prev_len_last, buf_last, r);
  EverCrypt_Hash_finish(&tmp_block_state, dst);
}

void
EverCrypt_Hash_Incremental_finish_sha384(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *p;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_384)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_384);
  }
  else
  {
    r =
      (uint32_t)(total_len
      % (uint64_t)EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_384));
  }
  uint8_t *buf_1 = buf_;
  uint64_t buf[8U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_SHA2_384_s, { .case_SHA2_384_s = buf } };
  EverCrypt_Hash_state_s tmp_block_state = s;
  EverCrypt_Hash_copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if
  (
    r
    % EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_384)
    == (uint32_t)0U
    && r > (uint32_t)0U
  )
  {
    ite = EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_384);
  }
  else
  {
    ite = r % EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_384);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  EverCrypt_Hash_update_multi2(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  EverCrypt_Hash_update_last2(&tmp_block_state, prev_len_last, buf_last, r);
  EverCrypt_Hash_finish(&tmp_block_state, dst);
}

void
EverCrypt_Hash_Incremental_finish_sha512(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *p;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_512)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_512);
  }
  else
  {
    r =
      (uint32_t)(total_len
      % (uint64_t)EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_512));
  }
  uint8_t *buf_1 = buf_;
  uint64_t buf[8U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_SHA2_512_s, { .case_SHA2_512_s = buf } };
  EverCrypt_Hash_state_s tmp_block_state = s;
  EverCrypt_Hash_copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if
  (
    r
    % EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_512)
    == (uint32_t)0U
    && r > (uint32_t)0U
  )
  {
    ite = EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_512);
  }
  else
  {
    ite = r % EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_SHA2_512);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  EverCrypt_Hash_update_multi2(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  EverCrypt_Hash_update_last2(&tmp_block_state, prev_len_last, buf_last, r);
  EverCrypt_Hash_finish(&tmp_block_state, dst);
}

void
EverCrypt_Hash_Incremental_finish_blake2s(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *p;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_Blake2S)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_Blake2S);
  }
  else
  {
    r =
      (uint32_t)(total_len
      % (uint64_t)EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_Blake2S));
  }
  uint8_t *buf_1 = buf_;
  uint32_t buf[16U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_Blake2S_s, { .case_Blake2S_s = buf } };
  EverCrypt_Hash_state_s tmp_block_state = s;
  EverCrypt_Hash_copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if
  (
    r
    % EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_Blake2S)
    == (uint32_t)0U
    && r > (uint32_t)0U
  )
  {
    ite = EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_Blake2S);
  }
  else
  {
    ite = r % EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_Blake2S);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  EverCrypt_Hash_update_multi2(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  EverCrypt_Hash_update_last2(&tmp_block_state, prev_len_last, buf_last, r);
  EverCrypt_Hash_finish(&tmp_block_state, dst);
}

void
EverCrypt_Hash_Incremental_finish_blake2b(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *p;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_Blake2B)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_Blake2B);
  }
  else
  {
    r =
      (uint32_t)(total_len
      % (uint64_t)EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_Blake2B));
  }
  uint8_t *buf_1 = buf_;
  uint64_t buf[16U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = EverCrypt_Hash_Blake2B_s, { .case_Blake2B_s = buf } };
  EverCrypt_Hash_state_s tmp_block_state = s;
  EverCrypt_Hash_copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if
  (
    r
    % EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_Blake2B)
    == (uint32_t)0U
    && r > (uint32_t)0U
  )
  {
    ite = EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_Blake2B);
  }
  else
  {
    ite = r % EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_Blake2B);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  EverCrypt_Hash_update_multi2(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  EverCrypt_Hash_update_last2(&tmp_block_state, prev_len_last, buf_last, r);
  EverCrypt_Hash_finish(&tmp_block_state, dst);
}

Spec_Hash_Definitions_hash_alg
EverCrypt_Hash_Incremental_alg_of_state(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s
)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *s;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  return EverCrypt_Hash_alg_of_state(block_state);
}

void
EverCrypt_Hash_Incremental_finish(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s,
  uint8_t *dst
)
{
  Spec_Hash_Definitions_hash_alg a1 = EverCrypt_Hash_Incremental_alg_of_state(s);
  switch (a1)
  {
    case Spec_Hash_Definitions_MD5:
      {
        EverCrypt_Hash_Incremental_finish_md5(s, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        EverCrypt_Hash_Incremental_finish_sha1(s, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        EverCrypt_Hash_Incremental_finish_sha224(s, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        EverCrypt_Hash_Incremental_finish_sha256(s, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        EverCrypt_Hash_Incremental_finish_sha384(s, dst);
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        EverCrypt_Hash_Incremental_finish_sha512(s, dst);
        break;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        EverCrypt_Hash_Incremental_finish_blake2s(s, dst);
        break;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        EverCrypt_Hash_Incremental_finish_blake2b(s, dst);
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
EverCrypt_Hash_Incremental_free(Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s)
{
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ scrut = *s;
  uint8_t *buf = scrut.buf;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  EverCrypt_Hash_free(block_state);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s);
}

