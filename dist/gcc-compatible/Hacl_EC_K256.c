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


#include "Hacl_EC_K256.h"

#include "internal/Hacl_K256_ECDSA.h"
#include "internal/Hacl_Bignum.h"

/*******************************************************************************
  Verified field arithmetic modulo p = 2^256 - 0x1000003D1.

  This is a 64-bit optimized version, where a field element in radix-2^{52} is
  represented as an array of five unsigned 64-bit integers, i.e., uint64_t[5].
*******************************************************************************/


/*
Write the additive identity in `f`.

  The outparam `f` is meant to be 5 limbs in size, i.e., uint64_t[5].
*/
void Hacl_EC_K256_mk_felem_zero(uint64_t *f)
{
  memset(f, 0U, (uint32_t)5U * sizeof (uint64_t));
}

/*
Write the multiplicative identity in `f`.

  The outparam `f` is meant to be 5 limbs in size, i.e., uint64_t[5].
*/
void Hacl_EC_K256_mk_felem_one(uint64_t *f)
{
  memset(f, 0U, (uint32_t)5U * sizeof (uint64_t));
  f[0U] = (uint64_t)1U;
}

/*
Write `a + b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_K256_felem_add(uint64_t *a, uint64_t *b, uint64_t *out)
{
  Hacl_K256_Field_fadd(out, a, b);
  Hacl_K256_Field_fnormalize_weak(out, out);
}

/*
Write `a - b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_K256_felem_sub(uint64_t *a, uint64_t *b, uint64_t *out)
{
  Hacl_K256_Field_fsub(out, a, b, (uint64_t)2U);
  Hacl_K256_Field_fnormalize_weak(out, out);
}

/*
Write `a * b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_K256_felem_mul(uint64_t *a, uint64_t *b, uint64_t *out)
{
  Hacl_K256_Field_fmul(out, a, b);
}

/*
Write `a * a mod p` in `out`.

  The argument `a`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are either disjoint or equal
*/
void Hacl_EC_K256_felem_sqr(uint64_t *a, uint64_t *out)
{
  Hacl_K256_Field_fsqr(out, a);
}

/*
Write `a ^ (p - 2) mod p` in `out`.

  The function computes modular multiplicative inverse if `a` <> zero.

  The argument `a`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are disjoint
*/
void Hacl_EC_K256_felem_inv(uint64_t *a, uint64_t *out)
{
  Hacl_Impl_K256_Finv_finv(out, a);
}

/*
Load a bid-endian field element from memory.

  The argument `b` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The outparam `out` points to a field element of 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `b` and `out` are disjoint
*/
void Hacl_EC_K256_felem_load(uint8_t *b, uint64_t *out)
{
  Hacl_K256_Field_load_felem(out, b);
}

/*
Serialize a field element into big-endian memory.

  The argument `a` points to a field element of 5 limbs in size, i.e., uint64_t[5].
  The outparam `out` points to 32 bytes of valid memory, i.e., uint8_t[32].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are disjoint
*/
void Hacl_EC_K256_felem_store(uint64_t *a, uint8_t *out)
{
  uint64_t tmp[5U] = { 0U };
  Hacl_K256_Field_fnormalize(tmp, a);
  Hacl_K256_Field_store_felem(out, tmp);
}

/*******************************************************************************
  Verified group operations for the secp256k1 curve of the form y^2 = x^3 + 7.

  This is a 64-bit optimized version, where a group element in projective coordinates
  is represented as an array of 15 unsigned 64-bit integers, i.e., uint64_t[15].
*******************************************************************************/


/*
Write the point at infinity (additive identity) in `p`.

  The outparam `p` is meant to be 15 limbs in size, i.e., uint64_t[15].
*/
void Hacl_EC_K256_mk_point_at_inf(uint64_t *p)
{
  uint64_t *px = p;
  uint64_t *py = p + (uint32_t)5U;
  uint64_t *pz = p + (uint32_t)10U;
  memset(px, 0U, (uint32_t)5U * sizeof (uint64_t));
  memset(py, 0U, (uint32_t)5U * sizeof (uint64_t));
  py[0U] = (uint64_t)1U;
  memset(pz, 0U, (uint32_t)5U * sizeof (uint64_t));
}

/*
Write the base point (generator) in `p`.

  The outparam `p` is meant to be 15 limbs in size, i.e., uint64_t[15].
*/
void Hacl_EC_K256_mk_base_point(uint64_t *p)
{
  uint64_t *gx = p;
  uint64_t *gy = p + (uint32_t)5U;
  uint64_t *gz = p + (uint32_t)10U;
  gx[0U] = (uint64_t)0x2815b16f81798U;
  gx[1U] = (uint64_t)0xdb2dce28d959fU;
  gx[2U] = (uint64_t)0xe870b07029bfcU;
  gx[3U] = (uint64_t)0xbbac55a06295cU;
  gx[4U] = (uint64_t)0x79be667ef9dcU;
  gy[0U] = (uint64_t)0x7d08ffb10d4b8U;
  gy[1U] = (uint64_t)0x48a68554199c4U;
  gy[2U] = (uint64_t)0xe1108a8fd17b4U;
  gy[3U] = (uint64_t)0xc4655da4fbfc0U;
  gy[4U] = (uint64_t)0x483ada7726a3U;
  memset(gz, 0U, (uint32_t)5U * sizeof (uint64_t));
  gz[0U] = (uint64_t)1U;
}

/*
Write `-p` in `out` (point negation).

  The argument `p` and the outparam `out` are meant to be 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are either disjoint or equal
*/
void Hacl_EC_K256_point_negate(uint64_t *p, uint64_t *out)
{
  Hacl_Impl_K256_Point_point_negate(out, p);
}

/*
Write `p + q` in `out` (point addition).

  The arguments `p`, `q` and the outparam `out` are meant to be 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p`, `q`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_K256_point_add(uint64_t *p, uint64_t *q, uint64_t *out)
{
  Hacl_Impl_K256_PointAdd_point_add(out, p, q);
}

/*
Write `p + p` in `out` (point doubling).

  The argument `p` and the outparam `out` are meant to be 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are either disjoint or equal
*/
void Hacl_EC_K256_point_double(uint64_t *p, uint64_t *out)
{
  Hacl_Impl_K256_PointDouble_point_double(out, p);
}

/*
Write `[scalar]p` in `out` (point multiplication or scalar multiplication).

  The argument `p` and the outparam `out` are meant to be 15 limbs in size, i.e., uint64_t[15].
  The argument `scalar` is meant to be 32 bytes in size, i.e., uint8_t[32].

  The function first loads a bid-endian scalar element from `scalar` and
  then computes a point multiplication.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `scalar`, `p`, and `out` are pairwise disjoint
*/
void Hacl_EC_K256_point_mul(uint8_t *scalar, uint64_t *p, uint64_t *out)
{
  uint64_t scalar_q[4U] = { 0U };
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64((uint32_t)32U, scalar, scalar_q);
  Hacl_Impl_K256_PointMul_point_mul(out, scalar_q, p);
}

/*
Checks whether `p` is equal to `q` (point equality).

  The function returns `true` if `p` is equal to `q` and `false` otherwise.

  The arguments `p` and `q` are meant to be 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `q` are either disjoint or equal
*/
bool Hacl_EC_K256_point_eq(uint64_t *p, uint64_t *q)
{
  return Hacl_Impl_K256_Point_point_eq(p, q);
}

/*
Compress a point in projective coordinates to its compressed form.

  The argument `p` points to a point of 15 limbs in size, i.e., uint64_t[15].
  The outparam `out` points to 33 bytes of valid memory, i.e., uint8_t[33].

  The function first converts a given point `p` from projective to affine coordinates
  and then writes [ 0x02 for even `y` and 0x03 for odd `y`; `x` ] in `out`.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are disjoint
*/
void Hacl_EC_K256_point_compress(uint64_t *p, uint8_t *out)
{
  uint64_t xa[5U] = { 0U };
  uint64_t ya[5U] = { 0U };
  uint64_t *x1 = p;
  uint64_t *y1 = p + (uint32_t)5U;
  uint64_t *z1 = p + (uint32_t)10U;
  uint64_t zinv[5U] = { 0U };
  Hacl_Impl_K256_Finv_finv(zinv, z1);
  Hacl_K256_Field_fmul(xa, x1, zinv);
  Hacl_K256_Field_fmul(ya, y1, zinv);
  Hacl_Impl_K256_Point_aff_point_compress_vartime(out, xa, ya);
}

/*
Decompress a point in projective coordinates from its compressed form.

  The function returns `true` for successful decompression of a compressed point
  and `false` otherwise.

  The argument `s` points to 33 bytes of valid memory, i.e., uint8_t[33].
  The outparam `out` points to a point of 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `s` and `out` are disjoint
*/
bool Hacl_EC_K256_point_decompress(uint8_t *s, uint64_t *out)
{
  uint64_t *px = out;
  uint64_t *py = out + (uint32_t)5U;
  uint64_t *pz = out + (uint32_t)10U;
  bool b = Hacl_Impl_K256_Point_aff_point_decompress_vartime(px, py, s);
  memset(pz, 0U, (uint32_t)5U * sizeof (uint64_t));
  pz[0U] = (uint64_t)1U;
  return b;
}

