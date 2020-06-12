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


#include "Hacl_P256_DH.h"

uint64_t
Hacl_P256_DH_ecdsa_sign_p256_sha2(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
)
{
  uint64_t privKeyAsFelem[4U] = { 0U };
  uint64_t r[4U] = { 0U };
  uint64_t s[4U] = { 0U };
  uint8_t *resultR = result;
  uint8_t *resultS = result + (uint32_t)32U;
  Hacl_P256_toUint64ChangeEndian(privKey, privKeyAsFelem);
  uint64_t
  flag =
    Hacl_P256_ecdsa_signature_core((
        (Spec_ECDSA_hash_alg_ecdsa){ .tag = Spec_ECDSA_Hash, ._0 = Spec_Hash_Definitions_SHA2_256 }
      ),
      r,
      s,
      mLen,
      m,
      privKeyAsFelem,
      k);
  Hacl_P256_changeEndian(r);
  Hacl_P256_toUint8(r, resultR);
  Hacl_P256_changeEndian(s);
  Hacl_P256_toUint8(s, resultS);
  return flag;
}

uint64_t
Hacl_P256_DH_ecdsa_sign_p256_sha384(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
)
{
  uint64_t privKeyAsFelem[4U] = { 0U };
  uint64_t r[4U] = { 0U };
  uint64_t s[4U] = { 0U };
  uint8_t *resultR = result;
  uint8_t *resultS = result + (uint32_t)32U;
  Hacl_P256_toUint64ChangeEndian(privKey, privKeyAsFelem);
  uint64_t
  flag =
    Hacl_P256_ecdsa_signature_core((
        (Spec_ECDSA_hash_alg_ecdsa){ .tag = Spec_ECDSA_Hash, ._0 = Spec_Hash_Definitions_SHA2_384 }
      ),
      r,
      s,
      mLen,
      m,
      privKeyAsFelem,
      k);
  Hacl_P256_changeEndian(r);
  Hacl_P256_toUint8(r, resultR);
  Hacl_P256_changeEndian(s);
  Hacl_P256_toUint8(s, resultS);
  return flag;
}

uint64_t
Hacl_P256_DH_ecdsa_sign_p256_sha512(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
)
{
  uint64_t privKeyAsFelem[4U] = { 0U };
  uint64_t r[4U] = { 0U };
  uint64_t s[4U] = { 0U };
  uint8_t *resultR = result;
  uint8_t *resultS = result + (uint32_t)32U;
  Hacl_P256_toUint64ChangeEndian(privKey, privKeyAsFelem);
  uint64_t
  flag =
    Hacl_P256_ecdsa_signature_core((
        (Spec_ECDSA_hash_alg_ecdsa){ .tag = Spec_ECDSA_Hash, ._0 = Spec_Hash_Definitions_SHA2_512 }
      ),
      r,
      s,
      mLen,
      m,
      privKeyAsFelem,
      k);
  Hacl_P256_changeEndian(r);
  Hacl_P256_toUint8(r, resultR);
  Hacl_P256_changeEndian(s);
  Hacl_P256_toUint8(s, resultS);
  return flag;
}

uint64_t
Hacl_P256_DH_ecdsa_sign_p256_without_hash(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
)
{
  uint64_t privKeyAsFelem[4U] = { 0U };
  uint64_t r[4U] = { 0U };
  uint64_t s[4U] = { 0U };
  uint8_t *resultR = result;
  uint8_t *resultS = result + (uint32_t)32U;
  Hacl_P256_toUint64ChangeEndian(privKey, privKeyAsFelem);
  uint64_t
  flag =
    Hacl_P256_ecdsa_signature_core(((Spec_ECDSA_hash_alg_ecdsa){ .tag = Spec_ECDSA_NoHash }),
      r,
      s,
      mLen,
      m,
      privKeyAsFelem,
      k);
  Hacl_P256_changeEndian(r);
  Hacl_P256_toUint8(r, resultR);
  Hacl_P256_changeEndian(s);
  Hacl_P256_toUint8(s, resultS);
  return flag;
}

bool
Hacl_P256_DH_ecdsa_verif_p256_sha2(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
)
{
  uint64_t publicKeyAsFelem[8U] = { 0U };
  uint64_t *publicKeyFelemX = publicKeyAsFelem;
  uint64_t *publicKeyFelemY = publicKeyAsFelem + (uint32_t)4U;
  uint64_t rAsFelem[4U] = { 0U };
  uint64_t sAsFelem[4U] = { 0U };
  uint8_t *pubKeyX = pubKey;
  uint8_t *pubKeyY = pubKey + (uint32_t)32U;
  Hacl_P256_toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  Hacl_P256_toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  Hacl_P256_toUint64ChangeEndian(r, rAsFelem);
  Hacl_P256_toUint64ChangeEndian(s, sAsFelem);
  uint64_t tempBufferU64[120U] = { 0U };
  uint64_t *publicKeyBuffer = tempBufferU64;
  uint64_t *hashAsFelem = tempBufferU64 + (uint32_t)12U;
  uint64_t *tempBuffer = tempBufferU64 + (uint32_t)16U;
  uint64_t *xBuffer = tempBufferU64 + (uint32_t)116U;
  Hacl_P256_bufferToJac(publicKeyAsFelem, publicKeyBuffer);
  bool publicKeyCorrect = Hacl_P256_verifyQValidCurvePoint(publicKeyBuffer, tempBuffer);
  if (publicKeyCorrect == false)
  {
    return false;
  }
  bool isRCorrect = Hacl_P256_isMoreThanZeroLessThanOrderMinusOne(rAsFelem);
  bool isSCorrect = Hacl_P256_isMoreThanZeroLessThanOrderMinusOne(sAsFelem);
  bool step1 = isRCorrect && isSCorrect;
  if (step1 == false)
  {
    return false;
  }
  uint8_t tempBufferU8[64U] = { 0U };
  uint8_t *bufferU1 = tempBufferU8;
  uint8_t *bufferU2 = tempBufferU8 + (uint32_t)32U;
  uint32_t sz = (uint32_t)32U;
  KRML_CHECK_SIZE(sizeof (uint8_t), sz);
  uint8_t mHash[sz];
  memset(mHash, 0U, sz * sizeof (mHash[0U]));
  Hacl_Hash_SHA2_hash_256(m, mLen, mHash);
  uint8_t *cutHash = mHash;
  Hacl_P256_toUint64ChangeEndian(cutHash, hashAsFelem);
  Hacl_P256_reduction_prime_2prime_order(hashAsFelem, hashAsFelem);
  uint64_t tempBuffer1[12U] = { 0U };
  uint64_t *inverseS = tempBuffer1;
  uint64_t *u1 = tempBuffer1 + (uint32_t)4U;
  uint64_t *u2 = tempBuffer1 + (uint32_t)8U;
  Hacl_P256_fromDomainImpl(sAsFelem, inverseS);
  Hacl_P256_montgomery_ladder_exponent(inverseS);
  Hacl_P256_multPowerPartial(sAsFelem, inverseS, hashAsFelem, u1);
  Hacl_P256_multPowerPartial(sAsFelem, inverseS, rAsFelem, u2);
  Hacl_P256_changeEndian(u1);
  Hacl_P256_changeEndian(u2);
  Hacl_P256_toUint8(u1, bufferU1);
  Hacl_P256_toUint8(u2, bufferU2);
  uint64_t pointSum[12U] = { 0U };
  uint64_t points[24U] = { 0U };
  uint64_t *buff = tempBuffer + (uint32_t)12U;
  uint64_t *pointU1G = points;
  uint64_t *pointU2Q0 = points + (uint32_t)12U;
  Hacl_P256_secretToPublicWithoutNorm(pointU1G, bufferU1, tempBuffer);
  Hacl_P256_scalarMultiplicationWithoutNorm(publicKeyBuffer, pointU2Q0, bufferU2, tempBuffer);
  uint64_t *pointU1G0 = points;
  uint64_t *pointU2Q = points + (uint32_t)12U;
  Hacl_P256_point_add(pointU1G0, pointU2Q, pointSum, buff);
  Hacl_P256_norm(pointSum, pointSum, buff);
  bool resultIsPAI = Hacl_P256_isPointAtInfinityPublic(pointSum);
  uint64_t *xCoordinateSum = pointSum;
  memcpy(xBuffer, xCoordinateSum, (uint32_t)4U * sizeof (xCoordinateSum[0U]));
  bool r1 = !resultIsPAI;
  bool state = r1;
  if (state == false)
  {
    return false;
  }
  bool result = Hacl_P256_compare_felem_bool(xBuffer, rAsFelem);
  return result;
}

bool
Hacl_P256_DH_ecdsa_verif_p256_sha384(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
)
{
  uint64_t publicKeyAsFelem[8U] = { 0U };
  uint64_t *publicKeyFelemX = publicKeyAsFelem;
  uint64_t *publicKeyFelemY = publicKeyAsFelem + (uint32_t)4U;
  uint64_t rAsFelem[4U] = { 0U };
  uint64_t sAsFelem[4U] = { 0U };
  uint8_t *pubKeyX = pubKey;
  uint8_t *pubKeyY = pubKey + (uint32_t)32U;
  Hacl_P256_toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  Hacl_P256_toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  Hacl_P256_toUint64ChangeEndian(r, rAsFelem);
  Hacl_P256_toUint64ChangeEndian(s, sAsFelem);
  uint64_t tempBufferU64[120U] = { 0U };
  uint64_t *publicKeyBuffer = tempBufferU64;
  uint64_t *hashAsFelem = tempBufferU64 + (uint32_t)12U;
  uint64_t *tempBuffer = tempBufferU64 + (uint32_t)16U;
  uint64_t *xBuffer = tempBufferU64 + (uint32_t)116U;
  Hacl_P256_bufferToJac(publicKeyAsFelem, publicKeyBuffer);
  bool publicKeyCorrect = Hacl_P256_verifyQValidCurvePoint(publicKeyBuffer, tempBuffer);
  if (publicKeyCorrect == false)
  {
    return false;
  }
  bool isRCorrect = Hacl_P256_isMoreThanZeroLessThanOrderMinusOne(rAsFelem);
  bool isSCorrect = Hacl_P256_isMoreThanZeroLessThanOrderMinusOne(sAsFelem);
  bool step1 = isRCorrect && isSCorrect;
  if (step1 == false)
  {
    return false;
  }
  uint8_t tempBufferU8[64U] = { 0U };
  uint8_t *bufferU1 = tempBufferU8;
  uint8_t *bufferU2 = tempBufferU8 + (uint32_t)32U;
  uint32_t sz = (uint32_t)48U;
  KRML_CHECK_SIZE(sizeof (uint8_t), sz);
  uint8_t mHash[sz];
  memset(mHash, 0U, sz * sizeof (mHash[0U]));
  Hacl_Hash_SHA2_hash_384(m, mLen, mHash);
  uint8_t *cutHash = mHash;
  Hacl_P256_toUint64ChangeEndian(cutHash, hashAsFelem);
  Hacl_P256_reduction_prime_2prime_order(hashAsFelem, hashAsFelem);
  uint64_t tempBuffer1[12U] = { 0U };
  uint64_t *inverseS = tempBuffer1;
  uint64_t *u1 = tempBuffer1 + (uint32_t)4U;
  uint64_t *u2 = tempBuffer1 + (uint32_t)8U;
  Hacl_P256_fromDomainImpl(sAsFelem, inverseS);
  Hacl_P256_montgomery_ladder_exponent(inverseS);
  Hacl_P256_multPowerPartial(sAsFelem, inverseS, hashAsFelem, u1);
  Hacl_P256_multPowerPartial(sAsFelem, inverseS, rAsFelem, u2);
  Hacl_P256_changeEndian(u1);
  Hacl_P256_changeEndian(u2);
  Hacl_P256_toUint8(u1, bufferU1);
  Hacl_P256_toUint8(u2, bufferU2);
  uint64_t pointSum[12U] = { 0U };
  uint64_t points[24U] = { 0U };
  uint64_t *buff = tempBuffer + (uint32_t)12U;
  uint64_t *pointU1G = points;
  uint64_t *pointU2Q0 = points + (uint32_t)12U;
  Hacl_P256_secretToPublicWithoutNorm(pointU1G, bufferU1, tempBuffer);
  Hacl_P256_scalarMultiplicationWithoutNorm(publicKeyBuffer, pointU2Q0, bufferU2, tempBuffer);
  uint64_t *pointU1G0 = points;
  uint64_t *pointU2Q = points + (uint32_t)12U;
  Hacl_P256_point_add(pointU1G0, pointU2Q, pointSum, buff);
  Hacl_P256_norm(pointSum, pointSum, buff);
  bool resultIsPAI = Hacl_P256_isPointAtInfinityPublic(pointSum);
  uint64_t *xCoordinateSum = pointSum;
  memcpy(xBuffer, xCoordinateSum, (uint32_t)4U * sizeof (xCoordinateSum[0U]));
  bool r1 = !resultIsPAI;
  bool state = r1;
  if (state == false)
  {
    return false;
  }
  bool result = Hacl_P256_compare_felem_bool(xBuffer, rAsFelem);
  return result;
}

bool
Hacl_P256_DH_ecdsa_verif_p256_sha512(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
)
{
  uint64_t publicKeyAsFelem[8U] = { 0U };
  uint64_t *publicKeyFelemX = publicKeyAsFelem;
  uint64_t *publicKeyFelemY = publicKeyAsFelem + (uint32_t)4U;
  uint64_t rAsFelem[4U] = { 0U };
  uint64_t sAsFelem[4U] = { 0U };
  uint8_t *pubKeyX = pubKey;
  uint8_t *pubKeyY = pubKey + (uint32_t)32U;
  Hacl_P256_toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  Hacl_P256_toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  Hacl_P256_toUint64ChangeEndian(r, rAsFelem);
  Hacl_P256_toUint64ChangeEndian(s, sAsFelem);
  uint64_t tempBufferU64[120U] = { 0U };
  uint64_t *publicKeyBuffer = tempBufferU64;
  uint64_t *hashAsFelem = tempBufferU64 + (uint32_t)12U;
  uint64_t *tempBuffer = tempBufferU64 + (uint32_t)16U;
  uint64_t *xBuffer = tempBufferU64 + (uint32_t)116U;
  Hacl_P256_bufferToJac(publicKeyAsFelem, publicKeyBuffer);
  bool publicKeyCorrect = Hacl_P256_verifyQValidCurvePoint(publicKeyBuffer, tempBuffer);
  if (publicKeyCorrect == false)
  {
    return false;
  }
  bool isRCorrect = Hacl_P256_isMoreThanZeroLessThanOrderMinusOne(rAsFelem);
  bool isSCorrect = Hacl_P256_isMoreThanZeroLessThanOrderMinusOne(sAsFelem);
  bool step1 = isRCorrect && isSCorrect;
  if (step1 == false)
  {
    return false;
  }
  uint8_t tempBufferU8[64U] = { 0U };
  uint8_t *bufferU1 = tempBufferU8;
  uint8_t *bufferU2 = tempBufferU8 + (uint32_t)32U;
  uint32_t sz = (uint32_t)64U;
  KRML_CHECK_SIZE(sizeof (uint8_t), sz);
  uint8_t mHash[sz];
  memset(mHash, 0U, sz * sizeof (mHash[0U]));
  Hacl_Hash_SHA2_hash_512(m, mLen, mHash);
  uint8_t *cutHash = mHash;
  Hacl_P256_toUint64ChangeEndian(cutHash, hashAsFelem);
  Hacl_P256_reduction_prime_2prime_order(hashAsFelem, hashAsFelem);
  uint64_t tempBuffer1[12U] = { 0U };
  uint64_t *inverseS = tempBuffer1;
  uint64_t *u1 = tempBuffer1 + (uint32_t)4U;
  uint64_t *u2 = tempBuffer1 + (uint32_t)8U;
  Hacl_P256_fromDomainImpl(sAsFelem, inverseS);
  Hacl_P256_montgomery_ladder_exponent(inverseS);
  Hacl_P256_multPowerPartial(sAsFelem, inverseS, hashAsFelem, u1);
  Hacl_P256_multPowerPartial(sAsFelem, inverseS, rAsFelem, u2);
  Hacl_P256_changeEndian(u1);
  Hacl_P256_changeEndian(u2);
  Hacl_P256_toUint8(u1, bufferU1);
  Hacl_P256_toUint8(u2, bufferU2);
  uint64_t pointSum[12U] = { 0U };
  uint64_t points[24U] = { 0U };
  uint64_t *buff = tempBuffer + (uint32_t)12U;
  uint64_t *pointU1G = points;
  uint64_t *pointU2Q0 = points + (uint32_t)12U;
  Hacl_P256_secretToPublicWithoutNorm(pointU1G, bufferU1, tempBuffer);
  Hacl_P256_scalarMultiplicationWithoutNorm(publicKeyBuffer, pointU2Q0, bufferU2, tempBuffer);
  uint64_t *pointU1G0 = points;
  uint64_t *pointU2Q = points + (uint32_t)12U;
  Hacl_P256_point_add(pointU1G0, pointU2Q, pointSum, buff);
  Hacl_P256_norm(pointSum, pointSum, buff);
  bool resultIsPAI = Hacl_P256_isPointAtInfinityPublic(pointSum);
  uint64_t *xCoordinateSum = pointSum;
  memcpy(xBuffer, xCoordinateSum, (uint32_t)4U * sizeof (xCoordinateSum[0U]));
  bool r1 = !resultIsPAI;
  bool state = r1;
  if (state == false)
  {
    return false;
  }
  bool result = Hacl_P256_compare_felem_bool(xBuffer, rAsFelem);
  return result;
}

bool
Hacl_P256_DH_ecdsa_verif_without_hash(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
)
{
  uint64_t publicKeyAsFelem[8U] = { 0U };
  uint64_t *publicKeyFelemX = publicKeyAsFelem;
  uint64_t *publicKeyFelemY = publicKeyAsFelem + (uint32_t)4U;
  uint64_t rAsFelem[4U] = { 0U };
  uint64_t sAsFelem[4U] = { 0U };
  uint8_t *pubKeyX = pubKey;
  uint8_t *pubKeyY = pubKey + (uint32_t)32U;
  Hacl_P256_toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  Hacl_P256_toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  Hacl_P256_toUint64ChangeEndian(r, rAsFelem);
  Hacl_P256_toUint64ChangeEndian(s, sAsFelem);
  uint64_t tempBufferU64[120U] = { 0U };
  uint64_t *publicKeyBuffer = tempBufferU64;
  uint64_t *hashAsFelem = tempBufferU64 + (uint32_t)12U;
  uint64_t *tempBuffer = tempBufferU64 + (uint32_t)16U;
  uint64_t *xBuffer = tempBufferU64 + (uint32_t)116U;
  Hacl_P256_bufferToJac(publicKeyAsFelem, publicKeyBuffer);
  bool publicKeyCorrect = Hacl_P256_verifyQValidCurvePoint(publicKeyBuffer, tempBuffer);
  if (publicKeyCorrect == false)
  {
    return false;
  }
  bool isRCorrect = Hacl_P256_isMoreThanZeroLessThanOrderMinusOne(rAsFelem);
  bool isSCorrect = Hacl_P256_isMoreThanZeroLessThanOrderMinusOne(sAsFelem);
  bool step1 = isRCorrect && isSCorrect;
  if (step1 == false)
  {
    return false;
  }
  uint8_t tempBufferU8[64U] = { 0U };
  uint8_t *bufferU1 = tempBufferU8;
  uint8_t *bufferU2 = tempBufferU8 + (uint32_t)32U;
  uint32_t sz = mLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), sz);
  uint8_t mHash[sz];
  memset(mHash, 0U, sz * sizeof (mHash[0U]));
  memcpy(mHash, m, sz * sizeof (m[0U]));
  uint8_t *cutHash = mHash;
  Hacl_P256_toUint64ChangeEndian(cutHash, hashAsFelem);
  Hacl_P256_reduction_prime_2prime_order(hashAsFelem, hashAsFelem);
  uint64_t tempBuffer1[12U] = { 0U };
  uint64_t *inverseS = tempBuffer1;
  uint64_t *u1 = tempBuffer1 + (uint32_t)4U;
  uint64_t *u2 = tempBuffer1 + (uint32_t)8U;
  Hacl_P256_fromDomainImpl(sAsFelem, inverseS);
  Hacl_P256_montgomery_ladder_exponent(inverseS);
  Hacl_P256_multPowerPartial(sAsFelem, inverseS, hashAsFelem, u1);
  Hacl_P256_multPowerPartial(sAsFelem, inverseS, rAsFelem, u2);
  Hacl_P256_changeEndian(u1);
  Hacl_P256_changeEndian(u2);
  Hacl_P256_toUint8(u1, bufferU1);
  Hacl_P256_toUint8(u2, bufferU2);
  uint64_t pointSum[12U] = { 0U };
  uint64_t points[24U] = { 0U };
  uint64_t *buff = tempBuffer + (uint32_t)12U;
  uint64_t *pointU1G = points;
  uint64_t *pointU2Q0 = points + (uint32_t)12U;
  Hacl_P256_secretToPublicWithoutNorm(pointU1G, bufferU1, tempBuffer);
  Hacl_P256_scalarMultiplicationWithoutNorm(publicKeyBuffer, pointU2Q0, bufferU2, tempBuffer);
  uint64_t *pointU1G0 = points;
  uint64_t *pointU2Q = points + (uint32_t)12U;
  Hacl_P256_point_add(pointU1G0, pointU2Q, pointSum, buff);
  Hacl_P256_norm(pointSum, pointSum, buff);
  bool resultIsPAI = Hacl_P256_isPointAtInfinityPublic(pointSum);
  uint64_t *xCoordinateSum = pointSum;
  memcpy(xBuffer, xCoordinateSum, (uint32_t)4U * sizeof (xCoordinateSum[0U]));
  bool r1 = !resultIsPAI;
  bool state = r1;
  if (state == false)
  {
    return false;
  }
  bool result = Hacl_P256_compare_felem_bool(xBuffer, rAsFelem);
  return result;
}

bool Hacl_P256_DH_verify_q(uint8_t *pubKey)
{
  uint8_t *pubKeyX = pubKey;
  uint8_t *pubKeyY = pubKey + (uint32_t)32U;
  uint64_t tempBuffer[120U] = { 0U };
  uint64_t *tempBufferV = tempBuffer;
  uint64_t *publicKeyJ = tempBuffer + (uint32_t)100U;
  uint64_t *publicKeyB = tempBuffer + (uint32_t)112U;
  uint64_t *publicKeyX = publicKeyB;
  uint64_t *publicKeyY = publicKeyB + (uint32_t)4U;
  Hacl_P256_toUint64ChangeEndian(pubKeyX, publicKeyX);
  Hacl_P256_toUint64ChangeEndian(pubKeyY, publicKeyY);
  Hacl_P256_bufferToJac(publicKeyB, publicKeyJ);
  bool r = Hacl_P256_verifyQValidCurvePoint(publicKeyJ, tempBufferV);
  return r;
}

bool Hacl_P256_DH_decompression_not_compressed_form(uint8_t *b, uint8_t *result)
{
  uint8_t compressionIdentifier = b[0U];
  bool correctIdentifier = (uint8_t)4U == compressionIdentifier;
  if (correctIdentifier)
  {
    memcpy(result, b + (uint32_t)1U, (uint32_t)64U * sizeof ((b + (uint32_t)1U)[0U]));
  }
  return correctIdentifier;
}

bool Hacl_P256_DH_decompression_compressed_form(uint8_t *b, uint8_t *result)
{
  uint64_t temp[8U] = { 0U };
  uint64_t *t0 = temp;
  uint64_t *t1 = temp + (uint32_t)4U;
  uint8_t compressedIdentifier = b[0U];
  uint8_t correctIdentifier2 = FStar_UInt8_eq_mask((uint8_t)2U, compressedIdentifier);
  uint8_t correctIdentifier3 = FStar_UInt8_eq_mask((uint8_t)3U, compressedIdentifier);
  uint8_t isIdentifierCorrect = correctIdentifier2 | correctIdentifier3;
  bool flag = isIdentifierCorrect == (uint8_t)255U;
  if (flag)
  {
    uint8_t *x = b + (uint32_t)1U;
    memcpy(result, x, (uint32_t)32U * sizeof (x[0U]));
    Hacl_P256_toUint64ChangeEndian(x, t0);
    uint64_t tempBuffer[4U] = { 0U };
    uint64_t carry = Hacl_P256_sub4_il(t0, Hacl_P256_prime256_buffer, tempBuffer);
    bool lessThanPrimeXCoordinate = carry == (uint64_t)1U;
    if (!lessThanPrimeXCoordinate)
    {
      return false;
    }
    uint64_t multBuffer[8U] = { 0U };
    Hacl_P256_shift_256_impl(t0, multBuffer);
    Hacl_P256_solinas_reduction_impl(multBuffer, t0);
    uint64_t identifierBit = (uint64_t)(compressedIdentifier & (uint8_t)1U);
    Hacl_P256_computeYFromX(t0, t1, identifierBit);
    Hacl_P256_changeEndian(t1);
    Hacl_P256_toUint8(t1, result + (uint32_t)32U);
    return true;
  }
  return false;
}

void Hacl_P256_DH_compression_not_compressed_form(uint8_t *b, uint8_t *result)
{
  uint8_t *to = result + (uint32_t)1U;
  memcpy(to, b, (uint32_t)64U * sizeof (b[0U]));
  result[0U] = (uint8_t)4U;
}

void Hacl_P256_DH_compression_compressed_form(uint8_t *b, uint8_t *result)
{
  uint8_t *y = b + (uint32_t)32U;
  uint8_t lastWordY = y[31U];
  uint8_t lastBitY = lastWordY & (uint8_t)1U;
  uint8_t identifier = lastBitY + (uint8_t)2U;
  memcpy(result + (uint32_t)1U, b, (uint32_t)32U * sizeof (b[0U]));
  result[0U] = identifier;
}

void Hacl_P256_DH_reduction_8_32(uint8_t *x, uint8_t *result)
{
  uint64_t xAsFelem[4U] = { 0U };
  Hacl_P256_toUint64ChangeEndian(x, xAsFelem);
  Hacl_P256_reduction_prime_2prime_order(xAsFelem, xAsFelem);
  Hacl_P256_changeEndian(xAsFelem);
  Hacl_P256_toUint8(xAsFelem, result);
}

