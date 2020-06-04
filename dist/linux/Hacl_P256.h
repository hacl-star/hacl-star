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

#include "lib_intrinsics.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"

#ifndef __Hacl_P256_H
#define __Hacl_P256_H

#include "Hacl_Kremlib.h"
#include "Hacl_Hash.h"
#include "Hacl_Spec.h"


u64 Hacl_Impl_P256_LowLevel_sub4_il(u64 *x, const u64 *y, u64 *result);

void Hacl_Impl_P256_LowLevel_shift_256_impl(u64 *i, u64 *o);

void Hacl_Impl_P256_LowLevel_toUint8(u64 *i, u8 *o);

void Hacl_Impl_P256_LowLevel_changeEndian(u64 *i);

void Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(u8 *i, u64 *o);

void
Hacl_Impl_ECDSA_MontgomeryMultiplication_reduction_prime_2prime_order(u64 *x, u64 *result);

extern const u64 Hacl_Impl_P256_LowLevel_PrimeSpecific_prime256_buffer[4U];

void Hacl_Impl_SolinasReduction_solinas_reduction_impl(u64 *i, u64 *o);

void Hacl_Impl_P256_PointAdd_point_add(u64 *p, u64 *q, u64 *result, u64 *tempBuffer);

void Hacl_Impl_P256_Core_norm(u64 *p, u64 *resultPoint, u64 *tempBuffer);

void
Hacl_Impl_P256_Core_scalarMultiplicationWithoutNorm(
  u64 *p,
  u64 *result,
  u8 *scalar,
  u64 *tempBuffer
);

void Hacl_Impl_P256_Core_secretToPublicWithoutNorm(u64 *result, u8 *scalar, u64 *tempBuffer);

void Hacl_Impl_P256_Signature_Common_bufferToJac(u64 *p, u64 *result);

bool Hacl_Impl_P256_Signature_Common_isPointAtInfinityPublic(u64 *p);

bool
Hacl_Impl_P256_Signature_Common_verifyQValidCurvePoint(u64 *pubKeyAsPoint, u64 *tempBuffer);

u64 Hacl_Impl_P256_DH_ecp256dh_i(u8 *result, u8 *scalar);

u64 Hacl_Impl_P256_DH_ecp256dh_r(u8 *result, u8 *pubKey, u8 *scalar);

void Hacl_Impl_P256_Compression_computeYFromX(u64 *x, u64 *result, u64 sign);

void Hacl_Impl_ECDSA_MM_Exponent_montgomery_ladder_exponent(u64 *r);

void Hacl_Impl_ECDSA_MM_Exponent_fromDomainImpl(u64 *a, u64 *result);

void Hacl_Impl_ECDSA_MM_Exponent_multPowerPartial(u64 *s, u64 *a, u64 *b, u64 *result);

bool Hacl_Impl_ECDSA_P256_Verification_Agile_isMoreThanZeroLessThanOrderMinusOne(u64 *f);

bool Hacl_Impl_ECDSA_P256_Verification_Agile_compare_felem_bool(u64 *a, u64 *b);

u64
Hacl_Impl_ECDSA_P256_Signature_Agile_ecdsa_signature_core(
  Spec_ECDSA_hash_alg_ecdsa alg,
  u64 *r,
  u64 *s,
  u32 mLen,
  u8 *m,
  u64 *privKeyAsFelem,
  u8 *k
);

u64 Hacl_Interface_P256_ecdsa_sign_p256_sha2(u8 *result, u32 mLen, u8 *m, u8 *privKey, u8 *k);

u64
Hacl_Interface_P256_ecdsa_sign_p256_sha384(u8 *result, u32 mLen, u8 *m, u8 *privKey, u8 *k);

u64
Hacl_Interface_P256_ecdsa_sign_p256_sha512(u8 *result, u32 mLen, u8 *m, u8 *privKey, u8 *k);

u64
Hacl_Interface_P256_ecdsa_sign_p256_without_hash(
  u8 *result,
  u32 mLen,
  u8 *m,
  u8 *privKey,
  u8 *k
);

bool Hacl_Interface_P256_ecdsa_verif_p256_sha2(u32 mLen, u8 *m, u8 *pubKey, u8 *r, u8 *s);

bool Hacl_Interface_P256_ecdsa_verif_p256_sha384(u32 mLen, u8 *m, u8 *pubKey, u8 *r, u8 *s);

bool Hacl_Interface_P256_ecdsa_verif_p256_sha512(u32 mLen, u8 *m, u8 *pubKey, u8 *r, u8 *s);

bool Hacl_Interface_P256_ecdsa_verif_without_hash(u32 mLen, u8 *m, u8 *pubKey, u8 *r, u8 *s);

bool Hacl_Interface_P256_verify_q(u8 *pubKey);

bool Hacl_Interface_P256_decompression_not_compressed_form(u8 *b, u8 *result);

bool Hacl_Interface_P256_decompression_compressed_form(u8 *b, u8 *result);

void Hacl_Interface_P256_compression_not_compressed_form(u8 *b, u8 *result);

void Hacl_Interface_P256_compression_compressed_form(u8 *b, u8 *result);

void Hacl_Interface_P256_reduction_8_32(u8 *x, u8 *result);

u64 Hacl_Interface_P256_ecp256dh_i(u8 *result, u8 *scalar);

u64 Hacl_Interface_P256_ecp256dh_r(u8 *result, u8 *pubKey, u8 *scalar);

#define __Hacl_P256_H_DEFINED
#endif
