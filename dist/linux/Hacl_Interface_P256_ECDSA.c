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


#include "Hacl_Interface_P256_ECDSA.h"

u64
Hacl_Interface_P256_ECDSA_ecdsa_sign_p256_sha2(u8 *result, u32 mLen, u8 *m, u8 *privKey, u8 *k)
{
  u64 privKeyAsFelem[4U] = { 0U };
  u64 r[4U] = { 0U };
  u64 s[4U] = { 0U };
  u8 *resultR = result;
  u8 *resultS = result + (u32)32U;
  u64 flag;
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(privKey, privKeyAsFelem);
  flag =
    Hacl_Impl_ECDSA_P256_Signature_Agile_ecdsa_signature_core((
        (Spec_ECDSA_hash_alg_ecdsa){ .tag = Spec_ECDSA_Hash, ._0 = Spec_Hash_Definitions_SHA2_256 }
      ),
      r,
      s,
      mLen,
      m,
      privKeyAsFelem,
      k);
  Hacl_Impl_P256_LowLevel_changeEndian(r);
  Hacl_Impl_P256_LowLevel_toUint8(r, resultR);
  Hacl_Impl_P256_LowLevel_changeEndian(s);
  Hacl_Impl_P256_LowLevel_toUint8(s, resultS);
  return flag;
}

u64
Hacl_Interface_P256_ECDSA_ecdsa_sign_p256_sha384(
  u8 *result,
  u32 mLen,
  u8 *m,
  u8 *privKey,
  u8 *k
)
{
  u64 privKeyAsFelem[4U] = { 0U };
  u64 r[4U] = { 0U };
  u64 s[4U] = { 0U };
  u8 *resultR = result;
  u8 *resultS = result + (u32)32U;
  u64 flag;
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(privKey, privKeyAsFelem);
  flag =
    Hacl_Impl_ECDSA_P256_Signature_Agile_ecdsa_signature_core((
        (Spec_ECDSA_hash_alg_ecdsa){ .tag = Spec_ECDSA_Hash, ._0 = Spec_Hash_Definitions_SHA2_384 }
      ),
      r,
      s,
      mLen,
      m,
      privKeyAsFelem,
      k);
  Hacl_Impl_P256_LowLevel_changeEndian(r);
  Hacl_Impl_P256_LowLevel_toUint8(r, resultR);
  Hacl_Impl_P256_LowLevel_changeEndian(s);
  Hacl_Impl_P256_LowLevel_toUint8(s, resultS);
  return flag;
}

u64
Hacl_Interface_P256_ECDSA_ecdsa_sign_p256_sha512(
  u8 *result,
  u32 mLen,
  u8 *m,
  u8 *privKey,
  u8 *k
)
{
  u64 privKeyAsFelem[4U] = { 0U };
  u64 r[4U] = { 0U };
  u64 s[4U] = { 0U };
  u8 *resultR = result;
  u8 *resultS = result + (u32)32U;
  u64 flag;
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(privKey, privKeyAsFelem);
  flag =
    Hacl_Impl_ECDSA_P256_Signature_Agile_ecdsa_signature_core((
        (Spec_ECDSA_hash_alg_ecdsa){ .tag = Spec_ECDSA_Hash, ._0 = Spec_Hash_Definitions_SHA2_512 }
      ),
      r,
      s,
      mLen,
      m,
      privKeyAsFelem,
      k);
  Hacl_Impl_P256_LowLevel_changeEndian(r);
  Hacl_Impl_P256_LowLevel_toUint8(r, resultR);
  Hacl_Impl_P256_LowLevel_changeEndian(s);
  Hacl_Impl_P256_LowLevel_toUint8(s, resultS);
  return flag;
}

u64
Hacl_Interface_P256_ECDSA_ecdsa_sign_p256_without_hash(
  u8 *result,
  u32 mLen,
  u8 *m,
  u8 *privKey,
  u8 *k
)
{
  u64 privKeyAsFelem[4U] = { 0U };
  u64 r[4U] = { 0U };
  u64 s[4U] = { 0U };
  u8 *resultR = result;
  u8 *resultS = result + (u32)32U;
  u64 flag;
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(privKey, privKeyAsFelem);
  flag =
    Hacl_Impl_ECDSA_P256_Signature_Agile_ecdsa_signature_core((
        (Spec_ECDSA_hash_alg_ecdsa){ .tag = Spec_ECDSA_NoHash }
      ),
      r,
      s,
      mLen,
      m,
      privKeyAsFelem,
      k);
  Hacl_Impl_P256_LowLevel_changeEndian(r);
  Hacl_Impl_P256_LowLevel_toUint8(r, resultR);
  Hacl_Impl_P256_LowLevel_changeEndian(s);
  Hacl_Impl_P256_LowLevel_toUint8(s, resultS);
  return flag;
}

bool Hacl_Interface_P256_ECDSA_ecdsa_verif_p256_sha2(u32 mLen, u8 *m, u8 *pubKey, u8 *r, u8 *s)
{
  u64 publicKeyAsFelem[8U] = { 0U };
  u64 *publicKeyFelemX = publicKeyAsFelem;
  u64 *publicKeyFelemY = publicKeyAsFelem + (u32)4U;
  u64 rAsFelem[4U] = { 0U };
  u64 sAsFelem[4U] = { 0U };
  u8 *pubKeyX = pubKey;
  u8 *pubKeyY = pubKey + (u32)32U;
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(r, rAsFelem);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(s, sAsFelem);
  {
    u64 tempBufferU64[120U] = { 0U };
    u64 *publicKeyBuffer = tempBufferU64;
    u64 *hashAsFelem = tempBufferU64 + (u32)12U;
    u64 *tempBuffer = tempBufferU64 + (u32)16U;
    u64 *xBuffer = tempBufferU64 + (u32)116U;
    bool publicKeyCorrect;
    bool result;
    Hacl_Impl_P256_Signature_Common_bufferToJac(publicKeyAsFelem, publicKeyBuffer);
    publicKeyCorrect =
      Hacl_Impl_P256_Signature_Common_verifyQValidCurvePoint(publicKeyBuffer,
        tempBuffer);
    if (publicKeyCorrect == false)
      result = false;
    else
    {
      bool
      isRCorrect =
        Hacl_Impl_ECDSA_P256_Verification_Agile_isMoreThanZeroLessThanOrderMinusOne(rAsFelem);
      bool
      isSCorrect =
        Hacl_Impl_ECDSA_P256_Verification_Agile_isMoreThanZeroLessThanOrderMinusOne(sAsFelem);
      bool step1 = isRCorrect && isSCorrect;
      if (step1 == false)
        result = false;
      else
      {
        u8 tempBufferU8[64U] = { 0U };
        u8 *bufferU1 = tempBufferU8;
        u8 *bufferU2 = tempBufferU8 + (u32)32U;
        u32 sz = (u32)32U;
        KRML_CHECK_SIZE(sizeof (u8), sz);
        {
          u8 mHash[sz];
          memset(mHash, 0U, sz * sizeof (mHash[0U]));
          Hacl_Hash_SHA2_hash_256(m, mLen, mHash);
          {
            u8 *cutHash = mHash;
            Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(cutHash, hashAsFelem);
            Hacl_Impl_ECDSA_MontgomeryMultiplication_reduction_prime_2prime_order(hashAsFelem,
              hashAsFelem);
            {
              u64 tempBuffer1[12U] = { 0U };
              u64 *inverseS = tempBuffer1;
              u64 *u1 = tempBuffer1 + (u32)4U;
              u64 *u2 = tempBuffer1 + (u32)8U;
              Hacl_Impl_ECDSA_MM_Exponent_fromDomainImpl(sAsFelem, inverseS);
              Hacl_Impl_ECDSA_MM_Exponent_montgomery_ladder_exponent(inverseS);
              Hacl_Impl_ECDSA_MM_Exponent_multPowerPartial(sAsFelem, inverseS, hashAsFelem, u1);
              Hacl_Impl_ECDSA_MM_Exponent_multPowerPartial(sAsFelem, inverseS, rAsFelem, u2);
              Hacl_Impl_P256_LowLevel_changeEndian(u1);
              Hacl_Impl_P256_LowLevel_changeEndian(u2);
              Hacl_Impl_P256_LowLevel_toUint8(u1, bufferU1);
              Hacl_Impl_P256_LowLevel_toUint8(u2, bufferU2);
              {
                u64 pointSum[12U] = { 0U };
                u64 points[24U] = { 0U };
                u64 *buff = tempBuffer + (u32)12U;
                u64 *pointU1G = points;
                u64 *pointU2Q0 = points + (u32)12U;
                Hacl_Impl_P256_Core_secretToPublicWithoutNorm(pointU1G, bufferU1, tempBuffer);
                Hacl_Impl_P256_Core_scalarMultiplicationWithoutNorm(publicKeyBuffer,
                  pointU2Q0,
                  bufferU2,
                  tempBuffer);
                {
                  u64 *pointU1G0 = points;
                  u64 *pointU2Q = points + (u32)12U;
                  Hacl_Impl_P256_PointAdd_point_add(pointU1G0, pointU2Q, pointSum, buff);
                  Hacl_Impl_P256_Core_norm(pointSum, pointSum, buff);
                  {
                    bool
                    resultIsPAI = Hacl_Impl_P256_Signature_Common_isPointAtInfinityPublic(pointSum);
                    u64 *xCoordinateSum = pointSum;
                    memcpy(xBuffer, xCoordinateSum, (u32)4U * sizeof (xCoordinateSum[0U]));
                    {
                      bool r1 = !resultIsPAI;
                      bool state = r1;
                      if (state == false)
                        result = false;
                      else
                      {
                        bool
                        result0 =
                          Hacl_Impl_ECDSA_P256_Verification_Agile_compare_felem_bool(xBuffer,
                            rAsFelem);
                        result = result0;
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
    return result;
  }
}

bool
Hacl_Interface_P256_ECDSA_ecdsa_verif_p256_sha384(u32 mLen, u8 *m, u8 *pubKey, u8 *r, u8 *s)
{
  u64 publicKeyAsFelem[8U] = { 0U };
  u64 *publicKeyFelemX = publicKeyAsFelem;
  u64 *publicKeyFelemY = publicKeyAsFelem + (u32)4U;
  u64 rAsFelem[4U] = { 0U };
  u64 sAsFelem[4U] = { 0U };
  u8 *pubKeyX = pubKey;
  u8 *pubKeyY = pubKey + (u32)32U;
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(r, rAsFelem);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(s, sAsFelem);
  {
    u64 tempBufferU64[120U] = { 0U };
    u64 *publicKeyBuffer = tempBufferU64;
    u64 *hashAsFelem = tempBufferU64 + (u32)12U;
    u64 *tempBuffer = tempBufferU64 + (u32)16U;
    u64 *xBuffer = tempBufferU64 + (u32)116U;
    bool publicKeyCorrect;
    bool result;
    Hacl_Impl_P256_Signature_Common_bufferToJac(publicKeyAsFelem, publicKeyBuffer);
    publicKeyCorrect =
      Hacl_Impl_P256_Signature_Common_verifyQValidCurvePoint(publicKeyBuffer,
        tempBuffer);
    if (publicKeyCorrect == false)
      result = false;
    else
    {
      bool
      isRCorrect =
        Hacl_Impl_ECDSA_P256_Verification_Agile_isMoreThanZeroLessThanOrderMinusOne(rAsFelem);
      bool
      isSCorrect =
        Hacl_Impl_ECDSA_P256_Verification_Agile_isMoreThanZeroLessThanOrderMinusOne(sAsFelem);
      bool step1 = isRCorrect && isSCorrect;
      if (step1 == false)
        result = false;
      else
      {
        u8 tempBufferU8[64U] = { 0U };
        u8 *bufferU1 = tempBufferU8;
        u8 *bufferU2 = tempBufferU8 + (u32)32U;
        u32 sz = (u32)48U;
        KRML_CHECK_SIZE(sizeof (u8), sz);
        {
          u8 mHash[sz];
          memset(mHash, 0U, sz * sizeof (mHash[0U]));
          Hacl_Hash_SHA2_hash_384(m, mLen, mHash);
          {
            u8 *cutHash = mHash;
            Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(cutHash, hashAsFelem);
            Hacl_Impl_ECDSA_MontgomeryMultiplication_reduction_prime_2prime_order(hashAsFelem,
              hashAsFelem);
            {
              u64 tempBuffer1[12U] = { 0U };
              u64 *inverseS = tempBuffer1;
              u64 *u1 = tempBuffer1 + (u32)4U;
              u64 *u2 = tempBuffer1 + (u32)8U;
              Hacl_Impl_ECDSA_MM_Exponent_fromDomainImpl(sAsFelem, inverseS);
              Hacl_Impl_ECDSA_MM_Exponent_montgomery_ladder_exponent(inverseS);
              Hacl_Impl_ECDSA_MM_Exponent_multPowerPartial(sAsFelem, inverseS, hashAsFelem, u1);
              Hacl_Impl_ECDSA_MM_Exponent_multPowerPartial(sAsFelem, inverseS, rAsFelem, u2);
              Hacl_Impl_P256_LowLevel_changeEndian(u1);
              Hacl_Impl_P256_LowLevel_changeEndian(u2);
              Hacl_Impl_P256_LowLevel_toUint8(u1, bufferU1);
              Hacl_Impl_P256_LowLevel_toUint8(u2, bufferU2);
              {
                u64 pointSum[12U] = { 0U };
                u64 points[24U] = { 0U };
                u64 *buff = tempBuffer + (u32)12U;
                u64 *pointU1G = points;
                u64 *pointU2Q0 = points + (u32)12U;
                Hacl_Impl_P256_Core_secretToPublicWithoutNorm(pointU1G, bufferU1, tempBuffer);
                Hacl_Impl_P256_Core_scalarMultiplicationWithoutNorm(publicKeyBuffer,
                  pointU2Q0,
                  bufferU2,
                  tempBuffer);
                {
                  u64 *pointU1G0 = points;
                  u64 *pointU2Q = points + (u32)12U;
                  Hacl_Impl_P256_PointAdd_point_add(pointU1G0, pointU2Q, pointSum, buff);
                  Hacl_Impl_P256_Core_norm(pointSum, pointSum, buff);
                  {
                    bool
                    resultIsPAI = Hacl_Impl_P256_Signature_Common_isPointAtInfinityPublic(pointSum);
                    u64 *xCoordinateSum = pointSum;
                    memcpy(xBuffer, xCoordinateSum, (u32)4U * sizeof (xCoordinateSum[0U]));
                    {
                      bool r1 = !resultIsPAI;
                      bool state = r1;
                      if (state == false)
                        result = false;
                      else
                      {
                        bool
                        result0 =
                          Hacl_Impl_ECDSA_P256_Verification_Agile_compare_felem_bool(xBuffer,
                            rAsFelem);
                        result = result0;
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
    return result;
  }
}

bool
Hacl_Interface_P256_ECDSA_ecdsa_verif_p256_sha512(u32 mLen, u8 *m, u8 *pubKey, u8 *r, u8 *s)
{
  u64 publicKeyAsFelem[8U] = { 0U };
  u64 *publicKeyFelemX = publicKeyAsFelem;
  u64 *publicKeyFelemY = publicKeyAsFelem + (u32)4U;
  u64 rAsFelem[4U] = { 0U };
  u64 sAsFelem[4U] = { 0U };
  u8 *pubKeyX = pubKey;
  u8 *pubKeyY = pubKey + (u32)32U;
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(r, rAsFelem);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(s, sAsFelem);
  {
    u64 tempBufferU64[120U] = { 0U };
    u64 *publicKeyBuffer = tempBufferU64;
    u64 *hashAsFelem = tempBufferU64 + (u32)12U;
    u64 *tempBuffer = tempBufferU64 + (u32)16U;
    u64 *xBuffer = tempBufferU64 + (u32)116U;
    bool publicKeyCorrect;
    bool result;
    Hacl_Impl_P256_Signature_Common_bufferToJac(publicKeyAsFelem, publicKeyBuffer);
    publicKeyCorrect =
      Hacl_Impl_P256_Signature_Common_verifyQValidCurvePoint(publicKeyBuffer,
        tempBuffer);
    if (publicKeyCorrect == false)
      result = false;
    else
    {
      bool
      isRCorrect =
        Hacl_Impl_ECDSA_P256_Verification_Agile_isMoreThanZeroLessThanOrderMinusOne(rAsFelem);
      bool
      isSCorrect =
        Hacl_Impl_ECDSA_P256_Verification_Agile_isMoreThanZeroLessThanOrderMinusOne(sAsFelem);
      bool step1 = isRCorrect && isSCorrect;
      if (step1 == false)
        result = false;
      else
      {
        u8 tempBufferU8[64U] = { 0U };
        u8 *bufferU1 = tempBufferU8;
        u8 *bufferU2 = tempBufferU8 + (u32)32U;
        u32 sz = (u32)64U;
        KRML_CHECK_SIZE(sizeof (u8), sz);
        {
          u8 mHash[sz];
          memset(mHash, 0U, sz * sizeof (mHash[0U]));
          Hacl_Hash_SHA2_hash_512(m, mLen, mHash);
          {
            u8 *cutHash = mHash;
            Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(cutHash, hashAsFelem);
            Hacl_Impl_ECDSA_MontgomeryMultiplication_reduction_prime_2prime_order(hashAsFelem,
              hashAsFelem);
            {
              u64 tempBuffer1[12U] = { 0U };
              u64 *inverseS = tempBuffer1;
              u64 *u1 = tempBuffer1 + (u32)4U;
              u64 *u2 = tempBuffer1 + (u32)8U;
              Hacl_Impl_ECDSA_MM_Exponent_fromDomainImpl(sAsFelem, inverseS);
              Hacl_Impl_ECDSA_MM_Exponent_montgomery_ladder_exponent(inverseS);
              Hacl_Impl_ECDSA_MM_Exponent_multPowerPartial(sAsFelem, inverseS, hashAsFelem, u1);
              Hacl_Impl_ECDSA_MM_Exponent_multPowerPartial(sAsFelem, inverseS, rAsFelem, u2);
              Hacl_Impl_P256_LowLevel_changeEndian(u1);
              Hacl_Impl_P256_LowLevel_changeEndian(u2);
              Hacl_Impl_P256_LowLevel_toUint8(u1, bufferU1);
              Hacl_Impl_P256_LowLevel_toUint8(u2, bufferU2);
              {
                u64 pointSum[12U] = { 0U };
                u64 points[24U] = { 0U };
                u64 *buff = tempBuffer + (u32)12U;
                u64 *pointU1G = points;
                u64 *pointU2Q0 = points + (u32)12U;
                Hacl_Impl_P256_Core_secretToPublicWithoutNorm(pointU1G, bufferU1, tempBuffer);
                Hacl_Impl_P256_Core_scalarMultiplicationWithoutNorm(publicKeyBuffer,
                  pointU2Q0,
                  bufferU2,
                  tempBuffer);
                {
                  u64 *pointU1G0 = points;
                  u64 *pointU2Q = points + (u32)12U;
                  Hacl_Impl_P256_PointAdd_point_add(pointU1G0, pointU2Q, pointSum, buff);
                  Hacl_Impl_P256_Core_norm(pointSum, pointSum, buff);
                  {
                    bool
                    resultIsPAI = Hacl_Impl_P256_Signature_Common_isPointAtInfinityPublic(pointSum);
                    u64 *xCoordinateSum = pointSum;
                    memcpy(xBuffer, xCoordinateSum, (u32)4U * sizeof (xCoordinateSum[0U]));
                    {
                      bool r1 = !resultIsPAI;
                      bool state = r1;
                      if (state == false)
                        result = false;
                      else
                      {
                        bool
                        result0 =
                          Hacl_Impl_ECDSA_P256_Verification_Agile_compare_felem_bool(xBuffer,
                            rAsFelem);
                        result = result0;
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
    return result;
  }
}

bool
Hacl_Interface_P256_ECDSA_ecdsa_verif_without_hash(u32 mLen, u8 *m, u8 *pubKey, u8 *r, u8 *s)
{
  u64 publicKeyAsFelem[8U] = { 0U };
  u64 *publicKeyFelemX = publicKeyAsFelem;
  u64 *publicKeyFelemY = publicKeyAsFelem + (u32)4U;
  u64 rAsFelem[4U] = { 0U };
  u64 sAsFelem[4U] = { 0U };
  u8 *pubKeyX = pubKey;
  u8 *pubKeyY = pubKey + (u32)32U;
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(r, rAsFelem);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(s, sAsFelem);
  {
    u64 tempBufferU64[120U] = { 0U };
    u64 *publicKeyBuffer = tempBufferU64;
    u64 *hashAsFelem = tempBufferU64 + (u32)12U;
    u64 *tempBuffer = tempBufferU64 + (u32)16U;
    u64 *xBuffer = tempBufferU64 + (u32)116U;
    bool publicKeyCorrect;
    bool result;
    Hacl_Impl_P256_Signature_Common_bufferToJac(publicKeyAsFelem, publicKeyBuffer);
    publicKeyCorrect =
      Hacl_Impl_P256_Signature_Common_verifyQValidCurvePoint(publicKeyBuffer,
        tempBuffer);
    if (publicKeyCorrect == false)
      result = false;
    else
    {
      bool
      isRCorrect =
        Hacl_Impl_ECDSA_P256_Verification_Agile_isMoreThanZeroLessThanOrderMinusOne(rAsFelem);
      bool
      isSCorrect =
        Hacl_Impl_ECDSA_P256_Verification_Agile_isMoreThanZeroLessThanOrderMinusOne(sAsFelem);
      bool step1 = isRCorrect && isSCorrect;
      if (step1 == false)
        result = false;
      else
      {
        u8 tempBufferU8[64U] = { 0U };
        u8 *bufferU1 = tempBufferU8;
        u8 *bufferU2 = tempBufferU8 + (u32)32U;
        u32 sz = mLen;
        KRML_CHECK_SIZE(sizeof (u8), sz);
        {
          u8 mHash[sz];
          memset(mHash, 0U, sz * sizeof (mHash[0U]));
          memcpy(mHash, m, sz * sizeof (m[0U]));
          {
            u8 *cutHash = mHash;
            Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(cutHash, hashAsFelem);
            Hacl_Impl_ECDSA_MontgomeryMultiplication_reduction_prime_2prime_order(hashAsFelem,
              hashAsFelem);
            {
              u64 tempBuffer1[12U] = { 0U };
              u64 *inverseS = tempBuffer1;
              u64 *u1 = tempBuffer1 + (u32)4U;
              u64 *u2 = tempBuffer1 + (u32)8U;
              Hacl_Impl_ECDSA_MM_Exponent_fromDomainImpl(sAsFelem, inverseS);
              Hacl_Impl_ECDSA_MM_Exponent_montgomery_ladder_exponent(inverseS);
              Hacl_Impl_ECDSA_MM_Exponent_multPowerPartial(sAsFelem, inverseS, hashAsFelem, u1);
              Hacl_Impl_ECDSA_MM_Exponent_multPowerPartial(sAsFelem, inverseS, rAsFelem, u2);
              Hacl_Impl_P256_LowLevel_changeEndian(u1);
              Hacl_Impl_P256_LowLevel_changeEndian(u2);
              Hacl_Impl_P256_LowLevel_toUint8(u1, bufferU1);
              Hacl_Impl_P256_LowLevel_toUint8(u2, bufferU2);
              {
                u64 pointSum[12U] = { 0U };
                u64 points[24U] = { 0U };
                u64 *buff = tempBuffer + (u32)12U;
                u64 *pointU1G = points;
                u64 *pointU2Q0 = points + (u32)12U;
                Hacl_Impl_P256_Core_secretToPublicWithoutNorm(pointU1G, bufferU1, tempBuffer);
                Hacl_Impl_P256_Core_scalarMultiplicationWithoutNorm(publicKeyBuffer,
                  pointU2Q0,
                  bufferU2,
                  tempBuffer);
                {
                  u64 *pointU1G0 = points;
                  u64 *pointU2Q = points + (u32)12U;
                  Hacl_Impl_P256_PointAdd_point_add(pointU1G0, pointU2Q, pointSum, buff);
                  Hacl_Impl_P256_Core_norm(pointSum, pointSum, buff);
                  {
                    bool
                    resultIsPAI = Hacl_Impl_P256_Signature_Common_isPointAtInfinityPublic(pointSum);
                    u64 *xCoordinateSum = pointSum;
                    memcpy(xBuffer, xCoordinateSum, (u32)4U * sizeof (xCoordinateSum[0U]));
                    {
                      bool r1 = !resultIsPAI;
                      bool state = r1;
                      if (state == false)
                        result = false;
                      else
                      {
                        bool
                        result0 =
                          Hacl_Impl_ECDSA_P256_Verification_Agile_compare_felem_bool(xBuffer,
                            rAsFelem);
                        result = result0;
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
    return result;
  }
}

bool Hacl_Interface_P256_ECDSA_verify_q(u8 *pubKey)
{
  u8 *pubKeyX = pubKey;
  u8 *pubKeyY = pubKey + (u32)32U;
  u64 tempBuffer[120U] = { 0U };
  u64 *tempBufferV = tempBuffer;
  u64 *publicKeyJ = tempBuffer + (u32)100U;
  u64 *publicKeyB = tempBuffer + (u32)112U;
  u64 *publicKeyX = publicKeyB;
  u64 *publicKeyY = publicKeyB + (u32)4U;
  bool r;
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyX, publicKeyX);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyY, publicKeyY);
  Hacl_Impl_P256_Signature_Common_bufferToJac(publicKeyB, publicKeyJ);
  r = Hacl_Impl_P256_Signature_Common_verifyQValidCurvePoint(publicKeyJ, tempBufferV);
  return r;
}

bool Hacl_Interface_P256_ECDSA_decompression_not_compressed_form(u8 *b, u8 *result)
{
  u8 compressionIdentifier = b[0U];
  bool correctIdentifier = (u8)4U == compressionIdentifier;
  if (correctIdentifier)
    memcpy(result, b + (u32)1U, (u32)64U * sizeof ((b + (u32)1U)[0U]));
  return correctIdentifier;
}

bool Hacl_Interface_P256_ECDSA_decompression_compressed_form(u8 *b, u8 *result)
{
  u64 temp[8U] = { 0U };
  u64 *t0 = temp;
  u64 *t1 = temp + (u32)4U;
  u8 compressedIdentifier = b[0U];
  u8 correctIdentifier2 = FStar_UInt8_eq_mask((u8)2U, compressedIdentifier);
  u8 correctIdentifier3 = FStar_UInt8_eq_mask((u8)3U, compressedIdentifier);
  u8 isIdentifierCorrect = correctIdentifier2 | correctIdentifier3;
  bool flag = isIdentifierCorrect == (u8)255U;
  if (flag)
  {
    u8 *x = b + (u32)1U;
    memcpy(result, x, (u32)32U * sizeof (x[0U]));
    Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(x, t0);
    {
      u64 tempBuffer[4U] = { 0U };
      u64
      carry =
        Hacl_Impl_P256_LowLevel_sub4_il(t0,
          Hacl_Impl_P256_LowLevel_PrimeSpecific_prime256_buffer,
          tempBuffer);
      bool lessThanPrimeXCoordinate = carry == (u64)1U;
      if (!lessThanPrimeXCoordinate)
        return false;
      {
        u64 multBuffer[8U] = { 0U };
        Hacl_Impl_P256_LowLevel_shift_256_impl(t0, multBuffer);
        Hacl_Impl_SolinasReduction_solinas_reduction_impl(multBuffer, t0);
        {
          u64 identifierBit = (u64)(compressedIdentifier & (u8)1U);
          Hacl_Impl_P256_Compression_computeYFromX(t0, t1, identifierBit);
          Hacl_Impl_P256_LowLevel_changeEndian(t1);
          Hacl_Impl_P256_LowLevel_toUint8(t1, result + (u32)32U);
          return true;
        }
      }
    }
  }
  return false;
}

void Hacl_Interface_P256_ECDSA_compression_not_compressed_form(u8 *b, u8 *result)
{
  u8 *to = result + (u32)1U;
  memcpy(to, b, (u32)64U * sizeof (b[0U]));
  result[0U] = (u8)4U;
}

void Hacl_Interface_P256_ECDSA_compression_compressed_form(u8 *b, u8 *result)
{
  u8 *y = b + (u32)32U;
  u8 lastWordY = y[31U];
  u8 lastBitY = lastWordY & (u8)1U;
  u8 identifier = lastBitY + (u8)2U;
  memcpy(result + (u32)1U, b, (u32)32U * sizeof (b[0U]));
  result[0U] = identifier;
}

void Hacl_Interface_P256_ECDSA_reduction_8_32(u8 *x, u8 *result)
{
  u64 xAsFelem[4U] = { 0U };
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(x, xAsFelem);
  Hacl_Impl_ECDSA_MontgomeryMultiplication_reduction_prime_2prime_order(xAsFelem, xAsFelem);
  Hacl_Impl_P256_LowLevel_changeEndian(xAsFelem);
  Hacl_Impl_P256_LowLevel_toUint8(xAsFelem, result);
}

