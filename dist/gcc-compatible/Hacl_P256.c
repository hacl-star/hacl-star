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


#include "internal/Hacl_P256.h"

#include "internal/Hacl_Spec.h"
#include "internal/Hacl_Kremlib.h"

static uint64_t isZero_uint64_CT(uint64_t *f)
{
  uint64_t a0 = f[0U];
  uint64_t a1 = f[1U];
  uint64_t a2 = f[2U];
  uint64_t a3 = f[3U];
  uint64_t r0 = FStar_UInt64_eq_mask(a0, (uint64_t)0U);
  uint64_t r1 = FStar_UInt64_eq_mask(a1, (uint64_t)0U);
  uint64_t r2 = FStar_UInt64_eq_mask(a2, (uint64_t)0U);
  uint64_t r3 = FStar_UInt64_eq_mask(a3, (uint64_t)0U);
  uint64_t r01 = r0 & r1;
  uint64_t r23 = r2 & r3;
  return r01 & r23;
}

static uint64_t compare_felem(uint64_t *a, uint64_t *b)
{
  uint64_t a_0 = a[0U];
  uint64_t a_1 = a[1U];
  uint64_t a_2 = a[2U];
  uint64_t a_3 = a[3U];
  uint64_t b_0 = b[0U];
  uint64_t b_1 = b[1U];
  uint64_t b_2 = b[2U];
  uint64_t b_3 = b[3U];
  uint64_t r_0 = FStar_UInt64_eq_mask(a_0, b_0);
  uint64_t r_1 = FStar_UInt64_eq_mask(a_1, b_1);
  uint64_t r_2 = FStar_UInt64_eq_mask(a_2, b_2);
  uint64_t r_3 = FStar_UInt64_eq_mask(a_3, b_3);
  uint64_t r01 = r_0 & r_1;
  uint64_t r23 = r_2 & r_3;
  return r01 & r23;
}

static void copy_conditional(uint64_t *out, uint64_t *x, uint64_t mask)
{
  uint64_t out_0 = out[0U];
  uint64_t out_1 = out[1U];
  uint64_t out_2 = out[2U];
  uint64_t out_3 = out[3U];
  uint64_t x_0 = x[0U];
  uint64_t x_1 = x[1U];
  uint64_t x_2 = x[2U];
  uint64_t x_3 = x[3U];
  uint64_t r_0 = out_0 ^ (mask & (out_0 ^ x_0));
  uint64_t r_1 = out_1 ^ (mask & (out_1 ^ x_1));
  uint64_t r_2 = out_2 ^ (mask & (out_2 ^ x_2));
  uint64_t r_3 = out_3 ^ (mask & (out_3 ^ x_3));
  out[0U] = r_0;
  out[1U] = r_1;
  out[2U] = r_2;
  out[3U] = r_3;
}

static uint64_t add4(uint64_t *x, uint64_t *y, uint64_t *result)
{
  uint64_t *r0 = result;
  uint64_t *r1 = result + (uint32_t)1U;
  uint64_t *r2 = result + (uint32_t)2U;
  uint64_t *r3 = result + (uint32_t)3U;
  uint64_t cc0 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, x[0U], y[0U], r0);
  uint64_t cc1 = Lib_IntTypes_Intrinsics_add_carry_u64(cc0, x[1U], y[1U], r1);
  uint64_t cc2 = Lib_IntTypes_Intrinsics_add_carry_u64(cc1, x[2U], y[2U], r2);
  uint64_t cc3 = Lib_IntTypes_Intrinsics_add_carry_u64(cc2, x[3U], y[3U], r3);
  return cc3;
}

static uint64_t add4_with_carry(uint64_t c, uint64_t *x, uint64_t *y, uint64_t *result)
{
  uint64_t *r0 = result;
  uint64_t *r1 = result + (uint32_t)1U;
  uint64_t *r2 = result + (uint32_t)2U;
  uint64_t *r3 = result + (uint32_t)3U;
  uint64_t cc = Lib_IntTypes_Intrinsics_add_carry_u64(c, x[0U], y[0U], r0);
  uint64_t cc1 = Lib_IntTypes_Intrinsics_add_carry_u64(cc, x[1U], y[1U], r1);
  uint64_t cc2 = Lib_IntTypes_Intrinsics_add_carry_u64(cc1, x[2U], y[2U], r2);
  uint64_t cc3 = Lib_IntTypes_Intrinsics_add_carry_u64(cc2, x[3U], y[3U], r3);
  return cc3;
}

static uint64_t add8(uint64_t *x, uint64_t *y, uint64_t *result)
{
  uint64_t *a0 = x;
  uint64_t *a1 = x + (uint32_t)4U;
  uint64_t *b0 = y;
  uint64_t *b1 = y + (uint32_t)4U;
  uint64_t *c0 = result;
  uint64_t *c1 = result + (uint32_t)4U;
  uint64_t carry0 = add4(a0, b0, c0);
  uint64_t carry1 = add4_with_carry(carry0, a1, b1, c1);
  return carry1;
}

static uint64_t
add4_variables(
  uint64_t *x,
  uint64_t cin,
  uint64_t y0,
  uint64_t y1,
  uint64_t y2,
  uint64_t y3,
  uint64_t *result
)
{
  uint64_t *r0 = result;
  uint64_t *r1 = result + (uint32_t)1U;
  uint64_t *r2 = result + (uint32_t)2U;
  uint64_t *r3 = result + (uint32_t)3U;
  uint64_t cc = Lib_IntTypes_Intrinsics_add_carry_u64(cin, x[0U], y0, r0);
  uint64_t cc1 = Lib_IntTypes_Intrinsics_add_carry_u64(cc, x[1U], y1, r1);
  uint64_t cc2 = Lib_IntTypes_Intrinsics_add_carry_u64(cc1, x[2U], y2, r2);
  uint64_t cc3 = Lib_IntTypes_Intrinsics_add_carry_u64(cc2, x[3U], y3, r3);
  return cc3;
}

static uint64_t sub4_il(uint64_t *x, const uint64_t *y, uint64_t *result)
{
  uint64_t *r0 = result;
  uint64_t *r1 = result + (uint32_t)1U;
  uint64_t *r2 = result + (uint32_t)2U;
  uint64_t *r3 = result + (uint32_t)3U;
  uint64_t cc = Lib_IntTypes_Intrinsics_sub_borrow_u64((uint64_t)0U, x[0U], y[0U], r0);
  uint64_t cc1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc, x[1U], y[1U], r1);
  uint64_t cc2 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc1, x[2U], y[2U], r2);
  uint64_t cc3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc2, x[3U], y[3U], r3);
  return cc3;
}

static uint64_t sub4(uint64_t *x, uint64_t *y, uint64_t *result)
{
  uint64_t *r0 = result;
  uint64_t *r1 = result + (uint32_t)1U;
  uint64_t *r2 = result + (uint32_t)2U;
  uint64_t *r3 = result + (uint32_t)3U;
  uint64_t cc = Lib_IntTypes_Intrinsics_sub_borrow_u64((uint64_t)0U, x[0U], y[0U], r0);
  uint64_t cc1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc, x[1U], y[1U], r1);
  uint64_t cc2 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc1, x[2U], y[2U], r2);
  uint64_t cc3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc2, x[3U], y[3U], r3);
  return cc3;
}

static void mul64(uint64_t x, uint64_t y, uint64_t *result, uint64_t *temp)
{
  FStar_UInt128_uint128 res = FStar_UInt128_mul_wide(x, y);
  uint64_t l0 = FStar_UInt128_uint128_to_uint64(res);
  uint64_t h0 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res, (uint32_t)64U));
  result[0U] = l0;
  temp[0U] = h0;
}

static void sq(uint64_t *f, uint64_t *out)
{
  uint64_t wb[17U] = { 0U };
  uint64_t *tb = wb;
  uint64_t *memory = wb + (uint32_t)5U;
  uint64_t *b0 = out;
  uint64_t f01 = f[0U];
  uint64_t f310 = f[3U];
  uint64_t *o30 = b0 + (uint32_t)3U;
  uint64_t *temp1 = tb;
  uint64_t f02 = f[0U];
  uint64_t f12 = f[1U];
  uint64_t f22 = f[2U];
  uint64_t *o01 = b0;
  uint64_t *o10 = b0 + (uint32_t)1U;
  uint64_t *o20 = b0 + (uint32_t)2U;
  mul64(f02, f02, o01, temp1);
  uint64_t h_00 = temp1[0U];
  mul64(f02, f12, o10, temp1);
  uint64_t l0 = o10[0U];
  memory[0U] = l0;
  memory[1U] = temp1[0U];
  uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l0, h_00, o10);
  uint64_t h_10 = temp1[0U];
  mul64(f02, f22, o20, temp1);
  uint64_t l10 = o20[0U];
  memory[2U] = l10;
  memory[3U] = temp1[0U];
  uint64_t c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l10, h_10, o20);
  uint64_t h_20 = temp1[0U];
  mul64(f01, f310, o30, temp1);
  uint64_t l3 = o30[0U];
  memory[4U] = l3;
  memory[5U] = temp1[0U];
  uint64_t c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l3, h_20, o30);
  uint64_t temp0 = temp1[0U];
  uint64_t c0 = c3 + temp0;
  out[4U] = c0;
  uint64_t *b1 = out + (uint32_t)1U;
  uint64_t *temp2 = tb;
  uint64_t *tempBufferResult0 = tb + (uint32_t)1U;
  uint64_t f11 = f[1U];
  uint64_t f210 = f[2U];
  uint64_t f311 = f[3U];
  uint64_t *o00 = tempBufferResult0;
  uint64_t *o11 = tempBufferResult0 + (uint32_t)1U;
  uint64_t *o21 = tempBufferResult0 + (uint32_t)2U;
  uint64_t *o31 = tempBufferResult0 + (uint32_t)3U;
  o00[0U] = memory[0U];
  uint64_t h_01 = memory[1U];
  mul64(f11, f11, o11, temp2);
  uint64_t l4 = o11[0U];
  uint64_t c10 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l4, h_01, o11);
  uint64_t h_11 = temp2[0U];
  mul64(f11, f210, o21, temp2);
  uint64_t l11 = o21[0U];
  memory[6U] = l11;
  memory[7U] = temp2[0U];
  uint64_t c20 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, l11, h_11, o21);
  uint64_t h_21 = temp2[0U];
  mul64(f11, f311, o31, temp2);
  uint64_t l20 = o31[0U];
  memory[8U] = l20;
  memory[9U] = temp2[0U];
  uint64_t c30 = Lib_IntTypes_Intrinsics_add_carry_u64(c20, l20, h_21, o31);
  uint64_t h_30 = temp2[0U];
  uint64_t c40 = add4(tempBufferResult0, b1, b1);
  uint64_t c11 = c30 + h_30 + c40;
  out[5U] = c11;
  uint64_t *b2 = out + (uint32_t)2U;
  uint64_t *temp3 = tb;
  uint64_t *tempBufferResult1 = tb + (uint32_t)1U;
  uint64_t f21 = f[2U];
  uint64_t f312 = f[3U];
  uint64_t *o02 = tempBufferResult1;
  uint64_t *o12 = tempBufferResult1 + (uint32_t)1U;
  uint64_t *o22 = tempBufferResult1 + (uint32_t)2U;
  uint64_t *o32 = tempBufferResult1 + (uint32_t)3U;
  o02[0U] = memory[2U];
  uint64_t h_0 = memory[3U];
  o12[0U] = memory[6U];
  uint64_t l5 = o12[0U];
  uint64_t c110 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l5, h_0, o12);
  uint64_t h_1 = memory[7U];
  mul64(f21, f21, o22, temp3);
  uint64_t l12 = o22[0U];
  uint64_t c21 = Lib_IntTypes_Intrinsics_add_carry_u64(c110, l12, h_1, o22);
  uint64_t h_2 = temp3[0U];
  mul64(f21, f312, o32, temp3);
  uint64_t l21 = o32[0U];
  memory[10U] = l21;
  memory[11U] = temp3[0U];
  uint64_t c31 = Lib_IntTypes_Intrinsics_add_carry_u64(c21, l21, h_2, o32);
  uint64_t h_31 = temp3[0U];
  uint64_t c41 = add4(tempBufferResult1, b2, b2);
  uint64_t c22 = c31 + h_31 + c41;
  out[6U] = c22;
  uint64_t *b3 = out + (uint32_t)3U;
  uint64_t *temp = tb;
  uint64_t *tempBufferResult = tb + (uint32_t)1U;
  uint64_t f31 = f[3U];
  uint64_t *o0 = tempBufferResult;
  uint64_t *o1 = tempBufferResult + (uint32_t)1U;
  uint64_t *o2 = tempBufferResult + (uint32_t)2U;
  uint64_t *o3 = tempBufferResult + (uint32_t)3U;
  o0[0U] = memory[4U];
  uint64_t h = memory[5U];
  o1[0U] = memory[8U];
  uint64_t l = o1[0U];
  uint64_t c111 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h, o1);
  uint64_t h4 = memory[9U];
  o2[0U] = memory[10U];
  uint64_t l1 = o2[0U];
  uint64_t c210 = Lib_IntTypes_Intrinsics_add_carry_u64(c111, l1, h4, o2);
  uint64_t h5 = memory[11U];
  mul64(f31, f31, o3, temp);
  uint64_t l2 = o3[0U];
  uint64_t c32 = Lib_IntTypes_Intrinsics_add_carry_u64(c210, l2, h5, o3);
  uint64_t h_3 = temp[0U];
  uint64_t c4 = add4(tempBufferResult, b3, b3);
  uint64_t c33 = c32 + h_3 + c4;
  out[7U] = c33;
}

static void cmovznz4(uint64_t cin, uint64_t *x, uint64_t *y, uint64_t *r)
{
  uint64_t mask = ~FStar_UInt64_eq_mask(cin, (uint64_t)0U);
  uint64_t r0 = (y[0U] & mask) | (x[0U] & ~mask);
  uint64_t r1 = (y[1U] & mask) | (x[1U] & ~mask);
  uint64_t r2 = (y[2U] & mask) | (x[2U] & ~mask);
  uint64_t r3 = (y[3U] & mask) | (x[3U] & ~mask);
  r[0U] = r0;
  r[1U] = r1;
  r[2U] = r2;
  r[3U] = r3;
}

static void shift_256_impl(uint64_t *i, uint64_t *o)
{
  o[0U] = (uint64_t)0U;
  o[1U] = (uint64_t)0U;
  o[2U] = (uint64_t)0U;
  o[3U] = (uint64_t)0U;
  o[4U] = i[0U];
  o[5U] = i[1U];
  o[6U] = i[2U];
  o[7U] = i[3U];
}

static void shift8(uint64_t *t, uint64_t *out)
{
  uint64_t t1 = t[1U];
  uint64_t t2 = t[2U];
  uint64_t t3 = t[3U];
  uint64_t t4 = t[4U];
  uint64_t t5 = t[5U];
  uint64_t t6 = t[6U];
  uint64_t t7 = t[7U];
  out[0U] = t1;
  out[1U] = t2;
  out[2U] = t3;
  out[3U] = t4;
  out[4U] = t5;
  out[5U] = t6;
  out[6U] = t7;
  out[7U] = (uint64_t)0U;
}

static void uploadZeroImpl(uint64_t *f)
{
  f[0U] = (uint64_t)0U;
  f[1U] = (uint64_t)0U;
  f[2U] = (uint64_t)0U;
  f[3U] = (uint64_t)0U;
}

static void uploadOneImpl(uint64_t *f)
{
  f[0U] = (uint64_t)1U;
  f[1U] = (uint64_t)0U;
  f[2U] = (uint64_t)0U;
  f[3U] = (uint64_t)0U;
}

void Hacl_Impl_P256_LowLevel_toUint8(uint64_t *i, uint8_t *o)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    store64_be(o + i0 * (uint32_t)8U, i[i0]);
  }
}

void Hacl_Impl_P256_LowLevel_changeEndian(uint64_t *i)
{
  uint64_t zero = i[0U];
  uint64_t one = i[1U];
  uint64_t two = i[2U];
  uint64_t three = i[3U];
  i[0U] = three;
  i[1U] = two;
  i[2U] = one;
  i[3U] = zero;
}

void Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(uint8_t *i, uint64_t *o)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    uint64_t *os = o;
    uint8_t *bj = i + i0 * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i0] = x;
  }
  Hacl_Impl_P256_LowLevel_changeEndian(o);
}

static const
uint64_t
prime256_buffer[4U] =
  {
    (uint64_t)0xffffffffffffffffU,
    (uint64_t)0xffffffffU,
    (uint64_t)0U,
    (uint64_t)0xffffffff00000001U
  };

static void reduction_prime_2prime_impl(uint64_t *x, uint64_t *result)
{
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t c = sub4_il(x, prime256_buffer, tempBuffer);
  cmovznz4(c, tempBuffer, x, result);
}

static void p256_add(uint64_t *arg1, uint64_t *arg2, uint64_t *out)
{
  uint64_t t = add4(arg1, arg2, out);
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t c = sub4_il(out, prime256_buffer, tempBuffer);
  uint64_t
  carry = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t, (uint64_t)0U, &tempBufferForSubborrow);
  cmovznz4(carry, tempBuffer, out, out);
}

static void p256_double(uint64_t *arg1, uint64_t *out)
{
  uint64_t t = add4(arg1, arg1, out);
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t c = sub4_il(out, prime256_buffer, tempBuffer);
  uint64_t
  carry = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t, (uint64_t)0U, &tempBufferForSubborrow);
  cmovznz4(carry, tempBuffer, out, out);
}

static void p256_sub(uint64_t *arg1, uint64_t *arg2, uint64_t *out)
{
  uint64_t t = sub4(arg1, arg2, out);
  uint64_t t0 = (uint64_t)0U - t;
  uint64_t t1 = ((uint64_t)0U - t) >> (uint32_t)32U;
  uint64_t t2 = (uint64_t)0U;
  uint64_t t3 = t - (t << (uint32_t)32U);
  uint64_t c = add4_variables(out, (uint64_t)0U, t0, t1, t2, t3, out);
}

static void montgomery_multiplication_buffer_by_one(uint64_t *a, uint64_t *result)
{
  uint64_t t[8U] = { 0U };
  uint64_t *t_low = t;
  uint64_t round2[8U] = { 0U };
  uint64_t round4[8U] = { 0U };
  memcpy(t_low, a, (uint32_t)4U * sizeof (uint64_t));
  uint64_t tempRound[8U] = { 0U };
  uint64_t t20[8U] = { 0U };
  uint64_t t30[8U] = { 0U };
  uint64_t t10 = t[0U];
  uint64_t *result040 = t20;
  uint64_t temp1 = (uint64_t)0U;
  uint64_t f10 = prime256_buffer[1U];
  uint64_t f20 = prime256_buffer[2U];
  uint64_t f30 = prime256_buffer[3U];
  uint64_t *o00 = result040;
  uint64_t *o10 = result040 + (uint32_t)1U;
  uint64_t *o20 = result040 + (uint32_t)2U;
  uint64_t *o30 = result040 + (uint32_t)3U;
  uint64_t f010 = prime256_buffer[0U];
  mul64(f010, t10, o00, &temp1);
  uint64_t h0 = temp1;
  mul64(f10, t10, o10, &temp1);
  uint64_t l0 = o10[0U];
  uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l0, h0, o10);
  uint64_t h1 = temp1;
  mul64(f20, t10, o20, &temp1);
  uint64_t l1 = o20[0U];
  uint64_t c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l1, h1, o20);
  uint64_t h2 = temp1;
  mul64(f30, t10, o30, &temp1);
  uint64_t l2 = o30[0U];
  uint64_t c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l2, h2, o30);
  uint64_t temp00 = temp1;
  uint64_t c0 = c3 + temp00;
  t20[4U] = c0;
  uint64_t uu____0 = add8(t, t20, t30);
  shift8(t30, tempRound);
  uint64_t t21[8U] = { 0U };
  uint64_t t31[8U] = { 0U };
  uint64_t t11 = tempRound[0U];
  uint64_t *result041 = t21;
  uint64_t temp2 = (uint64_t)0U;
  uint64_t f11 = prime256_buffer[1U];
  uint64_t f21 = prime256_buffer[2U];
  uint64_t f31 = prime256_buffer[3U];
  uint64_t *o01 = result041;
  uint64_t *o11 = result041 + (uint32_t)1U;
  uint64_t *o21 = result041 + (uint32_t)2U;
  uint64_t *o31 = result041 + (uint32_t)3U;
  uint64_t f011 = prime256_buffer[0U];
  mul64(f011, t11, o01, &temp2);
  uint64_t h3 = temp2;
  mul64(f11, t11, o11, &temp2);
  uint64_t l3 = o11[0U];
  uint64_t c10 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l3, h3, o11);
  uint64_t h4 = temp2;
  mul64(f21, t11, o21, &temp2);
  uint64_t l4 = o21[0U];
  uint64_t c20 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, l4, h4, o21);
  uint64_t h5 = temp2;
  mul64(f31, t11, o31, &temp2);
  uint64_t l5 = o31[0U];
  uint64_t c30 = Lib_IntTypes_Intrinsics_add_carry_u64(c20, l5, h5, o31);
  uint64_t temp01 = temp2;
  uint64_t c4 = c30 + temp01;
  t21[4U] = c4;
  uint64_t uu____1 = add8(tempRound, t21, t31);
  shift8(t31, round2);
  uint64_t tempRound0[8U] = { 0U };
  uint64_t t2[8U] = { 0U };
  uint64_t t32[8U] = { 0U };
  uint64_t t12 = round2[0U];
  uint64_t *result042 = t2;
  uint64_t temp3 = (uint64_t)0U;
  uint64_t f12 = prime256_buffer[1U];
  uint64_t f22 = prime256_buffer[2U];
  uint64_t f32 = prime256_buffer[3U];
  uint64_t *o02 = result042;
  uint64_t *o12 = result042 + (uint32_t)1U;
  uint64_t *o22 = result042 + (uint32_t)2U;
  uint64_t *o32 = result042 + (uint32_t)3U;
  uint64_t f012 = prime256_buffer[0U];
  mul64(f012, t12, o02, &temp3);
  uint64_t h6 = temp3;
  mul64(f12, t12, o12, &temp3);
  uint64_t l6 = o12[0U];
  uint64_t c11 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l6, h6, o12);
  uint64_t h7 = temp3;
  mul64(f22, t12, o22, &temp3);
  uint64_t l7 = o22[0U];
  uint64_t c21 = Lib_IntTypes_Intrinsics_add_carry_u64(c11, l7, h7, o22);
  uint64_t h8 = temp3;
  mul64(f32, t12, o32, &temp3);
  uint64_t l8 = o32[0U];
  uint64_t c31 = Lib_IntTypes_Intrinsics_add_carry_u64(c21, l8, h8, o32);
  uint64_t temp02 = temp3;
  uint64_t c5 = c31 + temp02;
  t2[4U] = c5;
  uint64_t uu____2 = add8(round2, t2, t32);
  shift8(t32, tempRound0);
  uint64_t t22[8U] = { 0U };
  uint64_t t3[8U] = { 0U };
  uint64_t t1 = tempRound0[0U];
  uint64_t *result04 = t22;
  uint64_t temp = (uint64_t)0U;
  uint64_t f1 = prime256_buffer[1U];
  uint64_t f2 = prime256_buffer[2U];
  uint64_t f3 = prime256_buffer[3U];
  uint64_t *o0 = result04;
  uint64_t *o1 = result04 + (uint32_t)1U;
  uint64_t *o2 = result04 + (uint32_t)2U;
  uint64_t *o3 = result04 + (uint32_t)3U;
  uint64_t f01 = prime256_buffer[0U];
  mul64(f01, t1, o0, &temp);
  uint64_t h9 = temp;
  mul64(f1, t1, o1, &temp);
  uint64_t l9 = o1[0U];
  uint64_t c12 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l9, h9, o1);
  uint64_t h10 = temp;
  mul64(f2, t1, o2, &temp);
  uint64_t l10 = o2[0U];
  uint64_t c22 = Lib_IntTypes_Intrinsics_add_carry_u64(c12, l10, h10, o2);
  uint64_t h = temp;
  mul64(f3, t1, o3, &temp);
  uint64_t l = o3[0U];
  uint64_t c32 = Lib_IntTypes_Intrinsics_add_carry_u64(c22, l, h, o3);
  uint64_t temp0 = temp;
  uint64_t c6 = c32 + temp0;
  t22[4U] = c6;
  uint64_t uu____3 = add8(tempRound0, t22, t3);
  shift8(t3, round4);
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t cin = round4[4U];
  uint64_t *x_ = round4;
  uint64_t c = sub4_il(x_, prime256_buffer, tempBuffer);
  uint64_t
  carry = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, cin, (uint64_t)0U, &tempBufferForSubborrow);
  cmovznz4(carry, tempBuffer, x_, result);
}

static void montgomery_multiplication_buffer(uint64_t *a, uint64_t *b, uint64_t *result)
{
  uint64_t t[8U] = { 0U };
  uint64_t round2[8U] = { 0U };
  uint64_t round4[8U] = { 0U };
  uint64_t f0 = a[0U];
  uint64_t f10 = a[1U];
  uint64_t f20 = a[2U];
  uint64_t f30 = a[3U];
  uint64_t *b0 = t;
  uint64_t temp2 = (uint64_t)0U;
  uint64_t f110 = b[1U];
  uint64_t f210 = b[2U];
  uint64_t f310 = b[3U];
  uint64_t *o00 = b0;
  uint64_t *o10 = b0 + (uint32_t)1U;
  uint64_t *o20 = b0 + (uint32_t)2U;
  uint64_t *o30 = b0 + (uint32_t)3U;
  uint64_t f020 = b[0U];
  mul64(f020, f0, o00, &temp2);
  uint64_t h0 = temp2;
  mul64(f110, f0, o10, &temp2);
  uint64_t l0 = o10[0U];
  uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l0, h0, o10);
  uint64_t h1 = temp2;
  mul64(f210, f0, o20, &temp2);
  uint64_t l1 = o20[0U];
  uint64_t c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l1, h1, o20);
  uint64_t h2 = temp2;
  mul64(f310, f0, o30, &temp2);
  uint64_t l2 = o30[0U];
  uint64_t c30 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l2, h2, o30);
  uint64_t temp00 = temp2;
  uint64_t c0 = c30 + temp00;
  t[4U] = c0;
  uint64_t *b1 = t + (uint32_t)1U;
  uint64_t temp3[4U] = { 0U };
  uint64_t temp10 = (uint64_t)0U;
  uint64_t f111 = b[1U];
  uint64_t f211 = b[2U];
  uint64_t f311 = b[3U];
  uint64_t *o01 = temp3;
  uint64_t *o11 = temp3 + (uint32_t)1U;
  uint64_t *o21 = temp3 + (uint32_t)2U;
  uint64_t *o31 = temp3 + (uint32_t)3U;
  uint64_t f021 = b[0U];
  mul64(f021, f10, o01, &temp10);
  uint64_t h3 = temp10;
  mul64(f111, f10, o11, &temp10);
  uint64_t l3 = o11[0U];
  uint64_t c10 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l3, h3, o11);
  uint64_t h4 = temp10;
  mul64(f211, f10, o21, &temp10);
  uint64_t l4 = o21[0U];
  uint64_t c20 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, l4, h4, o21);
  uint64_t h5 = temp10;
  mul64(f311, f10, o31, &temp10);
  uint64_t l5 = o31[0U];
  uint64_t c31 = Lib_IntTypes_Intrinsics_add_carry_u64(c20, l5, h5, o31);
  uint64_t temp01 = temp10;
  uint64_t c4 = c31 + temp01;
  uint64_t c32 = add4(temp3, b1, b1);
  uint64_t c11 = c4 + c32;
  t[5U] = c11;
  uint64_t *b2 = t + (uint32_t)2U;
  uint64_t temp4[4U] = { 0U };
  uint64_t temp11 = (uint64_t)0U;
  uint64_t f112 = b[1U];
  uint64_t f212 = b[2U];
  uint64_t f312 = b[3U];
  uint64_t *o02 = temp4;
  uint64_t *o12 = temp4 + (uint32_t)1U;
  uint64_t *o22 = temp4 + (uint32_t)2U;
  uint64_t *o32 = temp4 + (uint32_t)3U;
  uint64_t f022 = b[0U];
  mul64(f022, f20, o02, &temp11);
  uint64_t h6 = temp11;
  mul64(f112, f20, o12, &temp11);
  uint64_t l6 = o12[0U];
  uint64_t c110 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l6, h6, o12);
  uint64_t h7 = temp11;
  mul64(f212, f20, o22, &temp11);
  uint64_t l7 = o22[0U];
  uint64_t c21 = Lib_IntTypes_Intrinsics_add_carry_u64(c110, l7, h7, o22);
  uint64_t h8 = temp11;
  mul64(f312, f20, o32, &temp11);
  uint64_t l8 = o32[0U];
  uint64_t c33 = Lib_IntTypes_Intrinsics_add_carry_u64(c21, l8, h8, o32);
  uint64_t temp02 = temp11;
  uint64_t c5 = c33 + temp02;
  uint64_t c34 = add4(temp4, b2, b2);
  uint64_t c22 = c5 + c34;
  t[6U] = c22;
  uint64_t *b3 = t + (uint32_t)3U;
  uint64_t temp5[4U] = { 0U };
  uint64_t temp1 = (uint64_t)0U;
  uint64_t f11 = b[1U];
  uint64_t f21 = b[2U];
  uint64_t f31 = b[3U];
  uint64_t *o03 = temp5;
  uint64_t *o13 = temp5 + (uint32_t)1U;
  uint64_t *o23 = temp5 + (uint32_t)2U;
  uint64_t *o33 = temp5 + (uint32_t)3U;
  uint64_t f02 = b[0U];
  mul64(f02, f30, o03, &temp1);
  uint64_t h9 = temp1;
  mul64(f11, f30, o13, &temp1);
  uint64_t l9 = o13[0U];
  uint64_t c111 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l9, h9, o13);
  uint64_t h10 = temp1;
  mul64(f21, f30, o23, &temp1);
  uint64_t l10 = o23[0U];
  uint64_t c210 = Lib_IntTypes_Intrinsics_add_carry_u64(c111, l10, h10, o23);
  uint64_t h11 = temp1;
  mul64(f31, f30, o33, &temp1);
  uint64_t l11 = o33[0U];
  uint64_t c35 = Lib_IntTypes_Intrinsics_add_carry_u64(c210, l11, h11, o33);
  uint64_t temp03 = temp1;
  uint64_t c6 = c35 + temp03;
  uint64_t c3 = add4(temp5, b3, b3);
  uint64_t c36 = c6 + c3;
  t[7U] = c36;
  uint64_t tempRound[8U] = { 0U };
  uint64_t t20[8U] = { 0U };
  uint64_t t30[8U] = { 0U };
  uint64_t t10 = t[0U];
  uint64_t *result040 = t20;
  uint64_t temp6 = (uint64_t)0U;
  uint64_t f12 = prime256_buffer[1U];
  uint64_t f22 = prime256_buffer[2U];
  uint64_t f32 = prime256_buffer[3U];
  uint64_t *o04 = result040;
  uint64_t *o14 = result040 + (uint32_t)1U;
  uint64_t *o24 = result040 + (uint32_t)2U;
  uint64_t *o34 = result040 + (uint32_t)3U;
  uint64_t f010 = prime256_buffer[0U];
  mul64(f010, t10, o04, &temp6);
  uint64_t h12 = temp6;
  mul64(f12, t10, o14, &temp6);
  uint64_t l12 = o14[0U];
  uint64_t c12 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l12, h12, o14);
  uint64_t h13 = temp6;
  mul64(f22, t10, o24, &temp6);
  uint64_t l13 = o24[0U];
  uint64_t c23 = Lib_IntTypes_Intrinsics_add_carry_u64(c12, l13, h13, o24);
  uint64_t h14 = temp6;
  mul64(f32, t10, o34, &temp6);
  uint64_t l14 = o34[0U];
  uint64_t c37 = Lib_IntTypes_Intrinsics_add_carry_u64(c23, l14, h14, o34);
  uint64_t temp04 = temp6;
  uint64_t c7 = c37 + temp04;
  t20[4U] = c7;
  uint64_t uu____0 = add8(t, t20, t30);
  shift8(t30, tempRound);
  uint64_t t21[8U] = { 0U };
  uint64_t t31[8U] = { 0U };
  uint64_t t11 = tempRound[0U];
  uint64_t *result041 = t21;
  uint64_t temp7 = (uint64_t)0U;
  uint64_t f13 = prime256_buffer[1U];
  uint64_t f23 = prime256_buffer[2U];
  uint64_t f33 = prime256_buffer[3U];
  uint64_t *o05 = result041;
  uint64_t *o15 = result041 + (uint32_t)1U;
  uint64_t *o25 = result041 + (uint32_t)2U;
  uint64_t *o35 = result041 + (uint32_t)3U;
  uint64_t f011 = prime256_buffer[0U];
  mul64(f011, t11, o05, &temp7);
  uint64_t h15 = temp7;
  mul64(f13, t11, o15, &temp7);
  uint64_t l15 = o15[0U];
  uint64_t c13 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l15, h15, o15);
  uint64_t h16 = temp7;
  mul64(f23, t11, o25, &temp7);
  uint64_t l16 = o25[0U];
  uint64_t c24 = Lib_IntTypes_Intrinsics_add_carry_u64(c13, l16, h16, o25);
  uint64_t h17 = temp7;
  mul64(f33, t11, o35, &temp7);
  uint64_t l17 = o35[0U];
  uint64_t c38 = Lib_IntTypes_Intrinsics_add_carry_u64(c24, l17, h17, o35);
  uint64_t temp05 = temp7;
  uint64_t c8 = c38 + temp05;
  t21[4U] = c8;
  uint64_t uu____1 = add8(tempRound, t21, t31);
  shift8(t31, round2);
  uint64_t tempRound0[8U] = { 0U };
  uint64_t t2[8U] = { 0U };
  uint64_t t32[8U] = { 0U };
  uint64_t t12 = round2[0U];
  uint64_t *result042 = t2;
  uint64_t temp8 = (uint64_t)0U;
  uint64_t f14 = prime256_buffer[1U];
  uint64_t f24 = prime256_buffer[2U];
  uint64_t f34 = prime256_buffer[3U];
  uint64_t *o06 = result042;
  uint64_t *o16 = result042 + (uint32_t)1U;
  uint64_t *o26 = result042 + (uint32_t)2U;
  uint64_t *o36 = result042 + (uint32_t)3U;
  uint64_t f012 = prime256_buffer[0U];
  mul64(f012, t12, o06, &temp8);
  uint64_t h18 = temp8;
  mul64(f14, t12, o16, &temp8);
  uint64_t l18 = o16[0U];
  uint64_t c14 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l18, h18, o16);
  uint64_t h19 = temp8;
  mul64(f24, t12, o26, &temp8);
  uint64_t l19 = o26[0U];
  uint64_t c25 = Lib_IntTypes_Intrinsics_add_carry_u64(c14, l19, h19, o26);
  uint64_t h20 = temp8;
  mul64(f34, t12, o36, &temp8);
  uint64_t l20 = o36[0U];
  uint64_t c39 = Lib_IntTypes_Intrinsics_add_carry_u64(c25, l20, h20, o36);
  uint64_t temp06 = temp8;
  uint64_t c9 = c39 + temp06;
  t2[4U] = c9;
  uint64_t uu____2 = add8(round2, t2, t32);
  shift8(t32, tempRound0);
  uint64_t t22[8U] = { 0U };
  uint64_t t3[8U] = { 0U };
  uint64_t t1 = tempRound0[0U];
  uint64_t *result04 = t22;
  uint64_t temp = (uint64_t)0U;
  uint64_t f1 = prime256_buffer[1U];
  uint64_t f2 = prime256_buffer[2U];
  uint64_t f3 = prime256_buffer[3U];
  uint64_t *o0 = result04;
  uint64_t *o1 = result04 + (uint32_t)1U;
  uint64_t *o2 = result04 + (uint32_t)2U;
  uint64_t *o3 = result04 + (uint32_t)3U;
  uint64_t f01 = prime256_buffer[0U];
  mul64(f01, t1, o0, &temp);
  uint64_t h21 = temp;
  mul64(f1, t1, o1, &temp);
  uint64_t l21 = o1[0U];
  uint64_t c15 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l21, h21, o1);
  uint64_t h22 = temp;
  mul64(f2, t1, o2, &temp);
  uint64_t l22 = o2[0U];
  uint64_t c26 = Lib_IntTypes_Intrinsics_add_carry_u64(c15, l22, h22, o2);
  uint64_t h = temp;
  mul64(f3, t1, o3, &temp);
  uint64_t l = o3[0U];
  uint64_t c310 = Lib_IntTypes_Intrinsics_add_carry_u64(c26, l, h, o3);
  uint64_t temp0 = temp;
  uint64_t c16 = c310 + temp0;
  t22[4U] = c16;
  uint64_t uu____3 = add8(tempRound0, t22, t3);
  shift8(t3, round4);
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t cin = round4[4U];
  uint64_t *x_ = round4;
  uint64_t c = sub4_il(x_, prime256_buffer, tempBuffer);
  uint64_t
  carry = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, cin, (uint64_t)0U, &tempBufferForSubborrow);
  cmovznz4(carry, tempBuffer, x_, result);
}

static void montgomery_square_buffer(uint64_t *a, uint64_t *result)
{
  uint64_t t[8U] = { 0U };
  uint64_t round2[8U] = { 0U };
  uint64_t round4[8U] = { 0U };
  sq(a, t);
  uint64_t tempRound[8U] = { 0U };
  uint64_t t20[8U] = { 0U };
  uint64_t t30[8U] = { 0U };
  uint64_t t10 = t[0U];
  uint64_t *result040 = t20;
  uint64_t temp1 = (uint64_t)0U;
  uint64_t f10 = prime256_buffer[1U];
  uint64_t f20 = prime256_buffer[2U];
  uint64_t f30 = prime256_buffer[3U];
  uint64_t *o00 = result040;
  uint64_t *o10 = result040 + (uint32_t)1U;
  uint64_t *o20 = result040 + (uint32_t)2U;
  uint64_t *o30 = result040 + (uint32_t)3U;
  uint64_t f010 = prime256_buffer[0U];
  mul64(f010, t10, o00, &temp1);
  uint64_t h0 = temp1;
  mul64(f10, t10, o10, &temp1);
  uint64_t l0 = o10[0U];
  uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l0, h0, o10);
  uint64_t h1 = temp1;
  mul64(f20, t10, o20, &temp1);
  uint64_t l1 = o20[0U];
  uint64_t c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l1, h1, o20);
  uint64_t h2 = temp1;
  mul64(f30, t10, o30, &temp1);
  uint64_t l2 = o30[0U];
  uint64_t c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l2, h2, o30);
  uint64_t temp00 = temp1;
  uint64_t c0 = c3 + temp00;
  t20[4U] = c0;
  uint64_t uu____0 = add8(t, t20, t30);
  shift8(t30, tempRound);
  uint64_t t21[8U] = { 0U };
  uint64_t t31[8U] = { 0U };
  uint64_t t11 = tempRound[0U];
  uint64_t *result041 = t21;
  uint64_t temp2 = (uint64_t)0U;
  uint64_t f11 = prime256_buffer[1U];
  uint64_t f21 = prime256_buffer[2U];
  uint64_t f31 = prime256_buffer[3U];
  uint64_t *o01 = result041;
  uint64_t *o11 = result041 + (uint32_t)1U;
  uint64_t *o21 = result041 + (uint32_t)2U;
  uint64_t *o31 = result041 + (uint32_t)3U;
  uint64_t f011 = prime256_buffer[0U];
  mul64(f011, t11, o01, &temp2);
  uint64_t h3 = temp2;
  mul64(f11, t11, o11, &temp2);
  uint64_t l3 = o11[0U];
  uint64_t c10 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l3, h3, o11);
  uint64_t h4 = temp2;
  mul64(f21, t11, o21, &temp2);
  uint64_t l4 = o21[0U];
  uint64_t c20 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, l4, h4, o21);
  uint64_t h5 = temp2;
  mul64(f31, t11, o31, &temp2);
  uint64_t l5 = o31[0U];
  uint64_t c30 = Lib_IntTypes_Intrinsics_add_carry_u64(c20, l5, h5, o31);
  uint64_t temp01 = temp2;
  uint64_t c4 = c30 + temp01;
  t21[4U] = c4;
  uint64_t uu____1 = add8(tempRound, t21, t31);
  shift8(t31, round2);
  uint64_t tempRound0[8U] = { 0U };
  uint64_t t2[8U] = { 0U };
  uint64_t t32[8U] = { 0U };
  uint64_t t12 = round2[0U];
  uint64_t *result042 = t2;
  uint64_t temp3 = (uint64_t)0U;
  uint64_t f12 = prime256_buffer[1U];
  uint64_t f22 = prime256_buffer[2U];
  uint64_t f32 = prime256_buffer[3U];
  uint64_t *o02 = result042;
  uint64_t *o12 = result042 + (uint32_t)1U;
  uint64_t *o22 = result042 + (uint32_t)2U;
  uint64_t *o32 = result042 + (uint32_t)3U;
  uint64_t f012 = prime256_buffer[0U];
  mul64(f012, t12, o02, &temp3);
  uint64_t h6 = temp3;
  mul64(f12, t12, o12, &temp3);
  uint64_t l6 = o12[0U];
  uint64_t c11 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l6, h6, o12);
  uint64_t h7 = temp3;
  mul64(f22, t12, o22, &temp3);
  uint64_t l7 = o22[0U];
  uint64_t c21 = Lib_IntTypes_Intrinsics_add_carry_u64(c11, l7, h7, o22);
  uint64_t h8 = temp3;
  mul64(f32, t12, o32, &temp3);
  uint64_t l8 = o32[0U];
  uint64_t c31 = Lib_IntTypes_Intrinsics_add_carry_u64(c21, l8, h8, o32);
  uint64_t temp02 = temp3;
  uint64_t c5 = c31 + temp02;
  t2[4U] = c5;
  uint64_t uu____2 = add8(round2, t2, t32);
  shift8(t32, tempRound0);
  uint64_t t22[8U] = { 0U };
  uint64_t t3[8U] = { 0U };
  uint64_t t1 = tempRound0[0U];
  uint64_t *result04 = t22;
  uint64_t temp = (uint64_t)0U;
  uint64_t f1 = prime256_buffer[1U];
  uint64_t f2 = prime256_buffer[2U];
  uint64_t f3 = prime256_buffer[3U];
  uint64_t *o0 = result04;
  uint64_t *o1 = result04 + (uint32_t)1U;
  uint64_t *o2 = result04 + (uint32_t)2U;
  uint64_t *o3 = result04 + (uint32_t)3U;
  uint64_t f01 = prime256_buffer[0U];
  mul64(f01, t1, o0, &temp);
  uint64_t h9 = temp;
  mul64(f1, t1, o1, &temp);
  uint64_t l9 = o1[0U];
  uint64_t c12 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l9, h9, o1);
  uint64_t h10 = temp;
  mul64(f2, t1, o2, &temp);
  uint64_t l10 = o2[0U];
  uint64_t c22 = Lib_IntTypes_Intrinsics_add_carry_u64(c12, l10, h10, o2);
  uint64_t h = temp;
  mul64(f3, t1, o3, &temp);
  uint64_t l = o3[0U];
  uint64_t c32 = Lib_IntTypes_Intrinsics_add_carry_u64(c22, l, h, o3);
  uint64_t temp0 = temp;
  uint64_t c6 = c32 + temp0;
  t22[4U] = c6;
  uint64_t uu____3 = add8(tempRound0, t22, t3);
  shift8(t3, round4);
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t cin = round4[4U];
  uint64_t *x_ = round4;
  uint64_t c = sub4_il(x_, prime256_buffer, tempBuffer);
  uint64_t
  carry = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, cin, (uint64_t)0U, &tempBufferForSubborrow);
  cmovznz4(carry, tempBuffer, x_, result);
}

static void fsquarePowN(uint32_t n, uint64_t *a)
{
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    montgomery_square_buffer(a, a);
  }
}

static void fsquarePowNminusOne(uint32_t n, uint64_t *a, uint64_t *b)
{
  b[0U] = (uint64_t)1U;
  b[1U] = (uint64_t)18446744069414584320U;
  b[2U] = (uint64_t)18446744073709551615U;
  b[3U] = (uint64_t)4294967294U;
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    montgomery_multiplication_buffer(b, a, b);
    montgomery_square_buffer(a, a);
  }
}

static void exponent(uint64_t *a, uint64_t *result, uint64_t *tempBuffer)
{
  uint64_t *buffer_norm_1 = tempBuffer;
  uint64_t *buffer_result1 = tempBuffer + (uint32_t)4U;
  uint64_t *buffer_result2 = tempBuffer + (uint32_t)8U;
  uint64_t *buffer_norm_3 = tempBuffer + (uint32_t)12U;
  uint64_t *buffer_result3 = tempBuffer + (uint32_t)16U;
  memcpy(buffer_norm_1, a, (uint32_t)4U * sizeof (uint64_t));
  uint64_t *buffer_a = buffer_norm_1;
  uint64_t *buffer_b0 = buffer_norm_1 + (uint32_t)4U;
  fsquarePowNminusOne((uint32_t)32U, buffer_a, buffer_b0);
  fsquarePowN((uint32_t)224U, buffer_b0);
  memcpy(buffer_result2, a, (uint32_t)4U * sizeof (uint64_t));
  fsquarePowN((uint32_t)192U, buffer_result2);
  memcpy(buffer_norm_3, a, (uint32_t)4U * sizeof (uint64_t));
  uint64_t *buffer_a0 = buffer_norm_3;
  uint64_t *buffer_b = buffer_norm_3 + (uint32_t)4U;
  fsquarePowNminusOne((uint32_t)94U, buffer_a0, buffer_b);
  fsquarePowN((uint32_t)2U, buffer_b);
  montgomery_multiplication_buffer(buffer_result1, buffer_result2, buffer_result1);
  montgomery_multiplication_buffer(buffer_result1, buffer_result3, buffer_result1);
  montgomery_multiplication_buffer(buffer_result1, a, buffer_result1);
  memcpy(result, buffer_result1, (uint32_t)4U * sizeof (uint64_t));
}

static void cube(uint64_t *a, uint64_t *result)
{
  montgomery_square_buffer(a, result);
  montgomery_multiplication_buffer(result, a, result);
}

static void multByTwo(uint64_t *a, uint64_t *out)
{
  p256_add(a, a, out);
}

static void multByThree(uint64_t *a, uint64_t *result)
{
  multByTwo(a, result);
  p256_add(a, result, result);
}

static void multByFour(uint64_t *a, uint64_t *result)
{
  multByTwo(a, result);
  multByTwo(result, result);
}

static void multByEight(uint64_t *a, uint64_t *result)
{
  multByTwo(a, result);
  multByTwo(result, result);
  multByTwo(result, result);
}

static uint64_t store_high_low_u(uint32_t high, uint32_t low)
{
  uint64_t as_uint64_high = (uint64_t)high;
  uint64_t as_uint64_high1 = as_uint64_high << (uint32_t)32U;
  uint64_t as_uint64_low = (uint64_t)low;
  return as_uint64_low ^ as_uint64_high1;
}

static void solinas_reduction_impl(uint64_t *i, uint64_t *o)
{
  uint64_t tempBuffer[36U] = { 0U };
  uint64_t i0 = i[0U];
  uint64_t i1 = i[1U];
  uint64_t i2 = i[2U];
  uint64_t i3 = i[3U];
  uint64_t i4 = i[4U];
  uint64_t i5 = i[5U];
  uint64_t i6 = i[6U];
  uint64_t i7 = i[7U];
  uint32_t c0 = (uint32_t)i0;
  uint32_t c1 = (uint32_t)(i0 >> (uint32_t)32U);
  uint32_t c2 = (uint32_t)i1;
  uint32_t c3 = (uint32_t)(i1 >> (uint32_t)32U);
  uint32_t c4 = (uint32_t)i2;
  uint32_t c5 = (uint32_t)(i2 >> (uint32_t)32U);
  uint32_t c6 = (uint32_t)i3;
  uint32_t c7 = (uint32_t)(i3 >> (uint32_t)32U);
  uint32_t c8 = (uint32_t)i4;
  uint32_t c9 = (uint32_t)(i4 >> (uint32_t)32U);
  uint32_t c10 = (uint32_t)i5;
  uint32_t c11 = (uint32_t)(i5 >> (uint32_t)32U);
  uint32_t c12 = (uint32_t)i6;
  uint32_t c13 = (uint32_t)(i6 >> (uint32_t)32U);
  uint32_t c14 = (uint32_t)i7;
  uint32_t c15 = (uint32_t)(i7 >> (uint32_t)32U);
  uint64_t *t01 = tempBuffer;
  uint64_t *t110 = tempBuffer + (uint32_t)4U;
  uint64_t *t210 = tempBuffer + (uint32_t)8U;
  uint64_t *t310 = tempBuffer + (uint32_t)12U;
  uint64_t *t410 = tempBuffer + (uint32_t)16U;
  uint64_t *t510 = tempBuffer + (uint32_t)20U;
  uint64_t *t610 = tempBuffer + (uint32_t)24U;
  uint64_t *t710 = tempBuffer + (uint32_t)28U;
  uint64_t *t810 = tempBuffer + (uint32_t)32U;
  uint64_t b0 = store_high_low_u(c1, c0);
  uint64_t b10 = store_high_low_u(c3, c2);
  uint64_t b20 = store_high_low_u(c5, c4);
  uint64_t b30 = store_high_low_u(c7, c6);
  t01[0U] = b0;
  t01[1U] = b10;
  t01[2U] = b20;
  t01[3U] = b30;
  reduction_prime_2prime_impl(t01, t01);
  uint64_t b00 = (uint64_t)0U;
  uint64_t b11 = store_high_low_u(c11, (uint32_t)0U);
  uint64_t b21 = store_high_low_u(c13, c12);
  uint64_t b31 = store_high_low_u(c15, c14);
  t110[0U] = b00;
  t110[1U] = b11;
  t110[2U] = b21;
  t110[3U] = b31;
  reduction_prime_2prime_impl(t110, t110);
  uint64_t b01 = (uint64_t)0U;
  uint64_t b12 = store_high_low_u(c12, (uint32_t)0U);
  uint64_t b22 = store_high_low_u(c14, c13);
  uint64_t b32 = store_high_low_u((uint32_t)0U, c15);
  t210[0U] = b01;
  t210[1U] = b12;
  t210[2U] = b22;
  t210[3U] = b32;
  uint64_t b02 = store_high_low_u(c9, c8);
  uint64_t b13 = store_high_low_u((uint32_t)0U, c10);
  uint64_t b23 = (uint64_t)0U;
  uint64_t b33 = store_high_low_u(c15, c14);
  t310[0U] = b02;
  t310[1U] = b13;
  t310[2U] = b23;
  t310[3U] = b33;
  reduction_prime_2prime_impl(t310, t310);
  uint64_t b03 = store_high_low_u(c10, c9);
  uint64_t b14 = store_high_low_u(c13, c11);
  uint64_t b24 = store_high_low_u(c15, c14);
  uint64_t b34 = store_high_low_u(c8, c13);
  t410[0U] = b03;
  t410[1U] = b14;
  t410[2U] = b24;
  t410[3U] = b34;
  reduction_prime_2prime_impl(t410, t410);
  uint64_t b04 = store_high_low_u(c12, c11);
  uint64_t b15 = store_high_low_u((uint32_t)0U, c13);
  uint64_t b25 = (uint64_t)0U;
  uint64_t b35 = store_high_low_u(c10, c8);
  t510[0U] = b04;
  t510[1U] = b15;
  t510[2U] = b25;
  t510[3U] = b35;
  reduction_prime_2prime_impl(t510, t510);
  uint64_t b05 = store_high_low_u(c13, c12);
  uint64_t b16 = store_high_low_u(c15, c14);
  uint64_t b26 = (uint64_t)0U;
  uint64_t b36 = store_high_low_u(c11, c9);
  t610[0U] = b05;
  t610[1U] = b16;
  t610[2U] = b26;
  t610[3U] = b36;
  reduction_prime_2prime_impl(t610, t610);
  uint64_t b06 = store_high_low_u(c14, c13);
  uint64_t b17 = store_high_low_u(c8, c15);
  uint64_t b27 = store_high_low_u(c10, c9);
  uint64_t b37 = store_high_low_u(c12, (uint32_t)0U);
  t710[0U] = b06;
  t710[1U] = b17;
  t710[2U] = b27;
  t710[3U] = b37;
  reduction_prime_2prime_impl(t710, t710);
  uint64_t b07 = store_high_low_u(c15, c14);
  uint64_t b1 = store_high_low_u(c9, (uint32_t)0U);
  uint64_t b2 = store_high_low_u(c11, c10);
  uint64_t b3 = store_high_low_u(c13, (uint32_t)0U);
  t810[0U] = b07;
  t810[1U] = b1;
  t810[2U] = b2;
  t810[3U] = b3;
  reduction_prime_2prime_impl(t810, t810);
  uint64_t *t010 = tempBuffer;
  uint64_t *t11 = tempBuffer + (uint32_t)4U;
  uint64_t *t21 = tempBuffer + (uint32_t)8U;
  uint64_t *t31 = tempBuffer + (uint32_t)12U;
  uint64_t *t41 = tempBuffer + (uint32_t)16U;
  uint64_t *t51 = tempBuffer + (uint32_t)20U;
  uint64_t *t61 = tempBuffer + (uint32_t)24U;
  uint64_t *t71 = tempBuffer + (uint32_t)28U;
  uint64_t *t81 = tempBuffer + (uint32_t)32U;
  p256_double(t21, t21);
  p256_double(t11, t11);
  p256_add(t010, t11, o);
  p256_add(t21, o, o);
  p256_add(t31, o, o);
  p256_add(t41, o, o);
  p256_sub(o, t51, o);
  p256_sub(o, t61, o);
  p256_sub(o, t71, o);
  p256_sub(o, t81, o);
}

static void
point_double_a_b_g(
  uint64_t *p,
  uint64_t *alpha,
  uint64_t *beta,
  uint64_t *gamma,
  uint64_t *delta,
  uint64_t *tempBuffer
)
{
  uint64_t *pX = p;
  uint64_t *pY = p + (uint32_t)4U;
  uint64_t *pZ = p + (uint32_t)8U;
  uint64_t *a0 = tempBuffer;
  uint64_t *a1 = tempBuffer + (uint32_t)4U;
  uint64_t *alpha0 = tempBuffer + (uint32_t)8U;
  montgomery_square_buffer(pZ, delta);
  montgomery_square_buffer(pY, gamma);
  montgomery_multiplication_buffer(pX, gamma, beta);
  p256_sub(pX, delta, a0);
  p256_add(pX, delta, a1);
  montgomery_multiplication_buffer(a0, a1, alpha0);
  multByThree(alpha0, alpha);
}

static void
point_double_x3(
  uint64_t *x3,
  uint64_t *alpha,
  uint64_t *fourBeta,
  uint64_t *beta,
  uint64_t *eightBeta
)
{
  montgomery_square_buffer(alpha, x3);
  multByFour(beta, fourBeta);
  multByTwo(fourBeta, eightBeta);
  p256_sub(x3, eightBeta, x3);
}

static void
point_double_z3(uint64_t *z3, uint64_t *pY, uint64_t *pZ, uint64_t *gamma, uint64_t *delta)
{
  p256_add(pY, pZ, z3);
  montgomery_square_buffer(z3, z3);
  p256_sub(z3, gamma, z3);
  p256_sub(z3, delta, z3);
}

static void
point_double_y3(
  uint64_t *y3,
  uint64_t *x3,
  uint64_t *alpha,
  uint64_t *gamma,
  uint64_t *eightGamma,
  uint64_t *fourBeta
)
{
  p256_sub(fourBeta, x3, y3);
  montgomery_multiplication_buffer(alpha, y3, y3);
  montgomery_square_buffer(gamma, gamma);
  multByEight(gamma, eightGamma);
  p256_sub(y3, eightGamma, y3);
}

static void point_double(uint64_t *p, uint64_t *result, uint64_t *tempBuffer)
{
  uint64_t *pY = p + (uint32_t)4U;
  uint64_t *pZ = p + (uint32_t)8U;
  uint64_t *x3 = result;
  uint64_t *y3 = result + (uint32_t)4U;
  uint64_t *z3 = result + (uint32_t)8U;
  uint64_t *delta = tempBuffer;
  uint64_t *gamma = tempBuffer + (uint32_t)4U;
  uint64_t *beta = tempBuffer + (uint32_t)8U;
  uint64_t *alpha = tempBuffer + (uint32_t)16U;
  uint64_t *fourBeta = tempBuffer + (uint32_t)20U;
  uint64_t *eightBeta = tempBuffer + (uint32_t)24U;
  uint64_t *eightGamma = tempBuffer + (uint32_t)28U;
  uint64_t *tmp = tempBuffer + (uint32_t)32U;
  point_double_a_b_g(p, alpha, beta, gamma, delta, tmp);
  point_double_x3(x3, alpha, fourBeta, beta, eightBeta);
  point_double_z3(z3, pY, pZ, gamma, delta);
  point_double_y3(y3, x3, alpha, gamma, eightGamma, fourBeta);
}

static void
copy_point_conditional(
  uint64_t *x3_out,
  uint64_t *y3_out,
  uint64_t *z3_out,
  uint64_t *p,
  uint64_t *maskPoint
)
{
  uint64_t *z = maskPoint + (uint32_t)8U;
  uint64_t mask = isZero_uint64_CT(z);
  uint64_t *p_x = p;
  uint64_t *p_y = p + (uint32_t)4U;
  uint64_t *p_z = p + (uint32_t)8U;
  copy_conditional(x3_out, p_x, mask);
  copy_conditional(y3_out, p_y, mask);
  copy_conditional(z3_out, p_z, mask);
}

static void point_add(uint64_t *p, uint64_t *q, uint64_t *result, uint64_t *tempBuffer)
{
  uint64_t *tempBuffer16 = tempBuffer;
  uint64_t *u1 = tempBuffer + (uint32_t)16U;
  uint64_t *u2 = tempBuffer + (uint32_t)20U;
  uint64_t *s1 = tempBuffer + (uint32_t)24U;
  uint64_t *s2 = tempBuffer + (uint32_t)28U;
  uint64_t *h = tempBuffer + (uint32_t)32U;
  uint64_t *r = tempBuffer + (uint32_t)36U;
  uint64_t *uh = tempBuffer + (uint32_t)40U;
  uint64_t *hCube = tempBuffer + (uint32_t)44U;
  uint64_t *tempBuffer28 = tempBuffer + (uint32_t)60U;
  uint64_t *pX = p;
  uint64_t *pY = p + (uint32_t)4U;
  uint64_t *pZ = p + (uint32_t)8U;
  uint64_t *qX = q;
  uint64_t *qY = q + (uint32_t)4U;
  uint64_t *qZ0 = q + (uint32_t)8U;
  uint64_t *z2Square = tempBuffer16;
  uint64_t *z1Square = tempBuffer16 + (uint32_t)4U;
  uint64_t *z2Cube = tempBuffer16 + (uint32_t)8U;
  uint64_t *z1Cube = tempBuffer16 + (uint32_t)12U;
  montgomery_square_buffer(qZ0, z2Square);
  montgomery_square_buffer(pZ, z1Square);
  montgomery_multiplication_buffer(z2Square, qZ0, z2Cube);
  montgomery_multiplication_buffer(z1Square, pZ, z1Cube);
  montgomery_multiplication_buffer(z2Square, pX, u1);
  montgomery_multiplication_buffer(z1Square, qX, u2);
  montgomery_multiplication_buffer(z2Cube, pY, s1);
  montgomery_multiplication_buffer(z1Cube, qY, s2);
  uint64_t *temp = tempBuffer16;
  p256_sub(u2, u1, h);
  p256_sub(s2, s1, r);
  montgomery_square_buffer(h, temp);
  montgomery_multiplication_buffer(temp, u1, uh);
  montgomery_multiplication_buffer(temp, h, hCube);
  uint64_t *pZ0 = p + (uint32_t)8U;
  uint64_t *qZ = q + (uint32_t)8U;
  uint64_t *tempBuffer161 = tempBuffer28;
  uint64_t *x3_out1 = tempBuffer28 + (uint32_t)16U;
  uint64_t *y3_out1 = tempBuffer28 + (uint32_t)20U;
  uint64_t *z3_out1 = tempBuffer28 + (uint32_t)24U;
  uint64_t *rSquare = tempBuffer161;
  uint64_t *rH = tempBuffer161 + (uint32_t)4U;
  uint64_t *twoUh = tempBuffer161 + (uint32_t)8U;
  montgomery_square_buffer(r, rSquare);
  p256_sub(rSquare, hCube, rH);
  multByTwo(uh, twoUh);
  p256_sub(rH, twoUh, x3_out1);
  uint64_t *s1hCube = tempBuffer161;
  uint64_t *u1hx3 = tempBuffer161 + (uint32_t)4U;
  uint64_t *ru1hx3 = tempBuffer161 + (uint32_t)8U;
  montgomery_multiplication_buffer(s1, hCube, s1hCube);
  p256_sub(uh, x3_out1, u1hx3);
  montgomery_multiplication_buffer(u1hx3, r, ru1hx3);
  p256_sub(ru1hx3, s1hCube, y3_out1);
  uint64_t *z1z2 = tempBuffer161;
  montgomery_multiplication_buffer(pZ0, qZ, z1z2);
  montgomery_multiplication_buffer(z1z2, h, z3_out1);
  copy_point_conditional(x3_out1, y3_out1, z3_out1, q, p);
  copy_point_conditional(x3_out1, y3_out1, z3_out1, p, q);
  memcpy(result, x3_out1, (uint32_t)4U * sizeof (uint64_t));
  memcpy(result + (uint32_t)4U, y3_out1, (uint32_t)4U * sizeof (uint64_t));
  memcpy(result + (uint32_t)8U, z3_out1, (uint32_t)4U * sizeof (uint64_t));
}

static void pointToDomain(uint64_t *p, uint64_t *result)
{
  uint64_t *p_x = p;
  uint64_t *p_y = p + (uint32_t)4U;
  uint64_t *p_z = p + (uint32_t)8U;
  uint64_t *r_x = result;
  uint64_t *r_y = result + (uint32_t)4U;
  uint64_t *r_z = result + (uint32_t)8U;
  uint64_t multBuffer[8U] = { 0U };
  shift_256_impl(p_x, multBuffer);
  solinas_reduction_impl(multBuffer, r_x);
  uint64_t multBuffer0[8U] = { 0U };
  shift_256_impl(p_y, multBuffer0);
  solinas_reduction_impl(multBuffer0, r_y);
  uint64_t multBuffer1[8U] = { 0U };
  shift_256_impl(p_z, multBuffer1);
  solinas_reduction_impl(multBuffer1, r_z);
}

static void copy_point(uint64_t *p, uint64_t *result)
{
  memcpy(result, p, (uint32_t)12U * sizeof (uint64_t));
}

uint64_t Hacl_Impl_P256_Core_isPointAtInfinityPrivate(uint64_t *p)
{
  uint64_t z0 = p[8U];
  uint64_t z1 = p[9U];
  uint64_t z2 = p[10U];
  uint64_t z3 = p[11U];
  uint64_t z0_zero = FStar_UInt64_eq_mask(z0, (uint64_t)0U);
  uint64_t z1_zero = FStar_UInt64_eq_mask(z1, (uint64_t)0U);
  uint64_t z2_zero = FStar_UInt64_eq_mask(z2, (uint64_t)0U);
  uint64_t z3_zero = FStar_UInt64_eq_mask(z3, (uint64_t)0U);
  return (z0_zero & z1_zero) & (z2_zero & z3_zero);
}

static inline void cswap(uint64_t bit, uint64_t *p1, uint64_t *p2)
{
  uint64_t mask = (uint64_t)0U - bit;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)12U; i++)
  {
    uint64_t dummy = mask & (p1[i] ^ p2[i]);
    p1[i] = p1[i] ^ dummy;
    p2[i] = p2[i] ^ dummy;
  }
}

static void norm(uint64_t *p, uint64_t *resultPoint, uint64_t *tempBuffer)
{
  uint64_t *xf = p;
  uint64_t *yf = p + (uint32_t)4U;
  uint64_t *zf = p + (uint32_t)8U;
  uint64_t *z2f = tempBuffer + (uint32_t)4U;
  uint64_t *z3f = tempBuffer + (uint32_t)8U;
  uint64_t *tempBuffer20 = tempBuffer + (uint32_t)12U;
  montgomery_square_buffer(zf, z2f);
  montgomery_multiplication_buffer(z2f, zf, z3f);
  exponent(z2f, z2f, tempBuffer20);
  exponent(z3f, z3f, tempBuffer20);
  montgomery_multiplication_buffer(xf, z2f, z2f);
  montgomery_multiplication_buffer(yf, z3f, z3f);
  uint64_t zeroBuffer[4U] = { 0U };
  uint64_t *resultX = resultPoint;
  uint64_t *resultY = resultPoint + (uint32_t)4U;
  uint64_t *resultZ = resultPoint + (uint32_t)8U;
  uint64_t bit = Hacl_Impl_P256_Core_isPointAtInfinityPrivate(p);
  montgomery_multiplication_buffer_by_one(z2f, resultX);
  montgomery_multiplication_buffer_by_one(z3f, resultY);
  uploadOneImpl(resultZ);
  copy_conditional(resultZ, zeroBuffer, bit);
}

static void normX(uint64_t *p, uint64_t *result, uint64_t *tempBuffer)
{
  uint64_t *xf = p;
  uint64_t *zf = p + (uint32_t)8U;
  uint64_t *z2f = tempBuffer + (uint32_t)4U;
  uint64_t *tempBuffer20 = tempBuffer + (uint32_t)12U;
  montgomery_square_buffer(zf, z2f);
  exponent(z2f, z2f, tempBuffer20);
  montgomery_multiplication_buffer(z2f, xf, z2f);
  montgomery_multiplication_buffer_by_one(z2f, result);
}

static void zero_buffer(uint64_t *p)
{
  p[0U] = (uint64_t)0U;
  p[1U] = (uint64_t)0U;
  p[2U] = (uint64_t)0U;
  p[3U] = (uint64_t)0U;
  p[4U] = (uint64_t)0U;
  p[5U] = (uint64_t)0U;
  p[6U] = (uint64_t)0U;
  p[7U] = (uint64_t)0U;
  p[8U] = (uint64_t)0U;
  p[9U] = (uint64_t)0U;
  p[10U] = (uint64_t)0U;
  p[11U] = (uint64_t)0U;
}

static void
scalarMultiplicationL(uint64_t *p, uint64_t *result, uint8_t *scalar, uint64_t *tempBuffer)
{
  uint64_t *q = tempBuffer;
  zero_buffer(q);
  uint64_t *buff = tempBuffer + (uint32_t)12U;
  pointToDomain(p, result);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)256U; i++)
  {
    uint32_t bit0 = (uint32_t)255U - i;
    uint64_t
    bit =
      (uint64_t)(scalar[(uint32_t)31U - bit0 / (uint32_t)8U] >> bit0 % (uint32_t)8U & (uint8_t)1U);
    cswap(bit, q, result);
    point_add(q, result, result, buff);
    point_double(q, q, buff);
    cswap(bit, q, result);
  }
  norm(q, result, buff);
}

static void
scalarMultiplicationC(
  uint64_t *p,
  uint64_t *result,
  const uint8_t *scalar,
  uint64_t *tempBuffer
)
{
  uint64_t *q = tempBuffer;
  zero_buffer(q);
  uint64_t *buff = tempBuffer + (uint32_t)12U;
  pointToDomain(p, result);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)256U; i++)
  {
    uint32_t bit0 = (uint32_t)255U - i;
    uint64_t
    bit =
      (uint64_t)(scalar[(uint32_t)31U - bit0 / (uint32_t)8U] >> bit0 % (uint32_t)8U & (uint8_t)1U);
    cswap(bit, q, result);
    point_add(q, result, result, buff);
    point_double(q, q, buff);
    cswap(bit, q, result);
  }
  norm(q, result, buff);
}

static void uploadBasePoint(uint64_t *p)
{
  p[0U] = (uint64_t)8784043285714375740U;
  p[1U] = (uint64_t)8483257759279461889U;
  p[2U] = (uint64_t)8789745728267363600U;
  p[3U] = (uint64_t)1770019616739251654U;
  p[4U] = (uint64_t)15992936863339206154U;
  p[5U] = (uint64_t)10037038012062884956U;
  p[6U] = (uint64_t)15197544864945402661U;
  p[7U] = (uint64_t)9615747158586711429U;
  p[8U] = (uint64_t)1U;
  p[9U] = (uint64_t)18446744069414584320U;
  p[10U] = (uint64_t)18446744073709551615U;
  p[11U] = (uint64_t)4294967294U;
}

static void
scalarMultiplicationWithoutNorm(
  uint64_t *p,
  uint64_t *result,
  uint8_t *scalar,
  uint64_t *tempBuffer
)
{
  uint64_t *q = tempBuffer;
  zero_buffer(q);
  uint64_t *buff = tempBuffer + (uint32_t)12U;
  pointToDomain(p, result);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)256U; i++)
  {
    uint32_t bit0 = (uint32_t)255U - i;
    uint64_t
    bit =
      (uint64_t)(scalar[(uint32_t)31U - bit0 / (uint32_t)8U] >> bit0 % (uint32_t)8U & (uint8_t)1U);
    cswap(bit, q, result);
    point_add(q, result, result, buff);
    point_double(q, q, buff);
    cswap(bit, q, result);
  }
  copy_point(q, result);
}

void
Hacl_Impl_P256_Core_secretToPublic(uint64_t *result, uint8_t *scalar, uint64_t *tempBuffer)
{
  uint64_t basePoint[12U] = { 0U };
  uploadBasePoint(basePoint);
  uint64_t *q = tempBuffer;
  uint64_t *buff = tempBuffer + (uint32_t)12U;
  zero_buffer(q);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)256U; i++)
  {
    uint32_t bit0 = (uint32_t)255U - i;
    uint64_t
    bit =
      (uint64_t)(scalar[(uint32_t)31U - bit0 / (uint32_t)8U] >> bit0 % (uint32_t)8U & (uint8_t)1U);
    cswap(bit, q, basePoint);
    point_add(q, basePoint, basePoint, buff);
    point_double(q, q, buff);
    cswap(bit, q, basePoint);
  }
  norm(q, result, buff);
}

static void secretToPublicWithoutNorm(uint64_t *result, uint8_t *scalar, uint64_t *tempBuffer)
{
  uint64_t basePoint[12U] = { 0U };
  uploadBasePoint(basePoint);
  uint64_t *q = tempBuffer;
  uint64_t *buff = tempBuffer + (uint32_t)12U;
  zero_buffer(q);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)256U; i++)
  {
    uint32_t bit0 = (uint32_t)255U - i;
    uint64_t
    bit =
      (uint64_t)(scalar[(uint32_t)31U - bit0 / (uint32_t)8U] >> bit0 % (uint32_t)8U & (uint8_t)1U);
    cswap(bit, q, basePoint);
    point_add(q, basePoint, basePoint, buff);
    point_double(q, q, buff);
    cswap(bit, q, basePoint);
  }
  copy_point(q, result);
}

static const
uint64_t
prime256order_buffer[4U] =
  {
    (uint64_t)17562291160714782033U,
    (uint64_t)13611842547513532036U,
    (uint64_t)18446744073709551615U,
    (uint64_t)18446744069414584320U
  };

static const
uint8_t
order_inverse_buffer[32U] =
  {
    (uint8_t)79U, (uint8_t)37U, (uint8_t)99U, (uint8_t)252U, (uint8_t)194U, (uint8_t)202U,
    (uint8_t)185U, (uint8_t)243U, (uint8_t)132U, (uint8_t)158U, (uint8_t)23U, (uint8_t)167U,
    (uint8_t)173U, (uint8_t)250U, (uint8_t)230U, (uint8_t)188U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U
  };

static const
uint8_t
order_buffer[32U] =
  {
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)188U, (uint8_t)230U,
    (uint8_t)250U, (uint8_t)173U, (uint8_t)167U, (uint8_t)23U, (uint8_t)158U, (uint8_t)132U,
    (uint8_t)243U, (uint8_t)185U, (uint8_t)202U, (uint8_t)194U, (uint8_t)252U, (uint8_t)99U,
    (uint8_t)37U, (uint8_t)81U
  };

static void montgomery_multiplication_round(uint64_t *t, uint64_t *round, uint64_t k0)
{
  uint64_t temp = (uint64_t)0U;
  uint64_t y = (uint64_t)0U;
  uint64_t t2[8U] = { 0U };
  uint64_t t3[8U] = { 0U };
  uint64_t t1 = t[0U];
  mul64(t1, k0, &y, &temp);
  uint64_t y_ = y;
  uint64_t *result04 = t2;
  uint64_t temp1 = (uint64_t)0U;
  uint64_t f1 = prime256order_buffer[1U];
  uint64_t f2 = prime256order_buffer[2U];
  uint64_t f3 = prime256order_buffer[3U];
  uint64_t *o0 = result04;
  uint64_t *o1 = result04 + (uint32_t)1U;
  uint64_t *o2 = result04 + (uint32_t)2U;
  uint64_t *o3 = result04 + (uint32_t)3U;
  uint64_t f01 = prime256order_buffer[0U];
  mul64(f01, y_, o0, &temp1);
  uint64_t h0 = temp1;
  mul64(f1, y_, o1, &temp1);
  uint64_t l0 = o1[0U];
  uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l0, h0, o1);
  uint64_t h1 = temp1;
  mul64(f2, y_, o2, &temp1);
  uint64_t l1 = o2[0U];
  uint64_t c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l1, h1, o2);
  uint64_t h = temp1;
  mul64(f3, y_, o3, &temp1);
  uint64_t l = o3[0U];
  uint64_t c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l, h, o3);
  uint64_t temp0 = temp1;
  uint64_t c = c3 + temp0;
  t2[4U] = c;
  uint64_t uu____0 = add8(t, t2, t3);
  shift8(t3, round);
}

static void montgomery_multiplication_round_twice(uint64_t *t, uint64_t *result, uint64_t k0)
{
  uint64_t tempRound[8U] = { 0U };
  montgomery_multiplication_round(t, tempRound, k0);
  montgomery_multiplication_round(tempRound, result, k0);
}

static void reduction_prime_2prime_with_carry(uint64_t *x, uint64_t *result)
{
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t cin = x[4U];
  uint64_t *x_ = x;
  uint64_t c = sub4_il(x_, prime256order_buffer, tempBuffer);
  uint64_t
  carry = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, cin, (uint64_t)0U, &tempBufferForSubborrow);
  cmovznz4(carry, tempBuffer, x_, result);
}

static void reduction_prime_2prime_order(uint64_t *x, uint64_t *result)
{
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t c = sub4_il(x, prime256order_buffer, tempBuffer);
  cmovznz4(c, tempBuffer, x, result);
}

static void montgomery_multiplication_ecdsa_module(uint64_t *a, uint64_t *b, uint64_t *result)
{
  uint64_t t[8U] = { 0U };
  uint64_t round2[8U] = { 0U };
  uint64_t round4[8U] = { 0U };
  uint64_t prime_p256_orderBuffer[4U] = { 0U };
  uint64_t k0 = (uint64_t)14758798090332847183U;
  uint64_t f0 = a[0U];
  uint64_t f1 = a[1U];
  uint64_t f2 = a[2U];
  uint64_t f3 = a[3U];
  uint64_t *b0 = t;
  uint64_t temp2 = (uint64_t)0U;
  uint64_t f110 = b[1U];
  uint64_t f210 = b[2U];
  uint64_t f310 = b[3U];
  uint64_t *o00 = b0;
  uint64_t *o10 = b0 + (uint32_t)1U;
  uint64_t *o20 = b0 + (uint32_t)2U;
  uint64_t *o30 = b0 + (uint32_t)3U;
  uint64_t f020 = b[0U];
  mul64(f020, f0, o00, &temp2);
  uint64_t h0 = temp2;
  mul64(f110, f0, o10, &temp2);
  uint64_t l0 = o10[0U];
  uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l0, h0, o10);
  uint64_t h1 = temp2;
  mul64(f210, f0, o20, &temp2);
  uint64_t l1 = o20[0U];
  uint64_t c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l1, h1, o20);
  uint64_t h2 = temp2;
  mul64(f310, f0, o30, &temp2);
  uint64_t l2 = o30[0U];
  uint64_t c30 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l2, h2, o30);
  uint64_t temp00 = temp2;
  uint64_t c0 = c30 + temp00;
  t[4U] = c0;
  uint64_t *b1 = t + (uint32_t)1U;
  uint64_t temp3[4U] = { 0U };
  uint64_t temp10 = (uint64_t)0U;
  uint64_t f111 = b[1U];
  uint64_t f211 = b[2U];
  uint64_t f311 = b[3U];
  uint64_t *o01 = temp3;
  uint64_t *o11 = temp3 + (uint32_t)1U;
  uint64_t *o21 = temp3 + (uint32_t)2U;
  uint64_t *o31 = temp3 + (uint32_t)3U;
  uint64_t f021 = b[0U];
  mul64(f021, f1, o01, &temp10);
  uint64_t h3 = temp10;
  mul64(f111, f1, o11, &temp10);
  uint64_t l3 = o11[0U];
  uint64_t c10 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l3, h3, o11);
  uint64_t h4 = temp10;
  mul64(f211, f1, o21, &temp10);
  uint64_t l4 = o21[0U];
  uint64_t c20 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, l4, h4, o21);
  uint64_t h5 = temp10;
  mul64(f311, f1, o31, &temp10);
  uint64_t l5 = o31[0U];
  uint64_t c31 = Lib_IntTypes_Intrinsics_add_carry_u64(c20, l5, h5, o31);
  uint64_t temp01 = temp10;
  uint64_t c = c31 + temp01;
  uint64_t c32 = add4(temp3, b1, b1);
  uint64_t c11 = c + c32;
  t[5U] = c11;
  uint64_t *b2 = t + (uint32_t)2U;
  uint64_t temp4[4U] = { 0U };
  uint64_t temp11 = (uint64_t)0U;
  uint64_t f112 = b[1U];
  uint64_t f212 = b[2U];
  uint64_t f312 = b[3U];
  uint64_t *o02 = temp4;
  uint64_t *o12 = temp4 + (uint32_t)1U;
  uint64_t *o22 = temp4 + (uint32_t)2U;
  uint64_t *o32 = temp4 + (uint32_t)3U;
  uint64_t f022 = b[0U];
  mul64(f022, f2, o02, &temp11);
  uint64_t h6 = temp11;
  mul64(f112, f2, o12, &temp11);
  uint64_t l6 = o12[0U];
  uint64_t c110 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l6, h6, o12);
  uint64_t h7 = temp11;
  mul64(f212, f2, o22, &temp11);
  uint64_t l7 = o22[0U];
  uint64_t c21 = Lib_IntTypes_Intrinsics_add_carry_u64(c110, l7, h7, o22);
  uint64_t h8 = temp11;
  mul64(f312, f2, o32, &temp11);
  uint64_t l8 = o32[0U];
  uint64_t c33 = Lib_IntTypes_Intrinsics_add_carry_u64(c21, l8, h8, o32);
  uint64_t temp02 = temp11;
  uint64_t c4 = c33 + temp02;
  uint64_t c34 = add4(temp4, b2, b2);
  uint64_t c22 = c4 + c34;
  t[6U] = c22;
  uint64_t *b3 = t + (uint32_t)3U;
  uint64_t temp[4U] = { 0U };
  uint64_t temp1 = (uint64_t)0U;
  uint64_t f11 = b[1U];
  uint64_t f21 = b[2U];
  uint64_t f31 = b[3U];
  uint64_t *o0 = temp;
  uint64_t *o1 = temp + (uint32_t)1U;
  uint64_t *o2 = temp + (uint32_t)2U;
  uint64_t *o3 = temp + (uint32_t)3U;
  uint64_t f02 = b[0U];
  mul64(f02, f3, o0, &temp1);
  uint64_t h9 = temp1;
  mul64(f11, f3, o1, &temp1);
  uint64_t l9 = o1[0U];
  uint64_t c111 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l9, h9, o1);
  uint64_t h10 = temp1;
  mul64(f21, f3, o2, &temp1);
  uint64_t l10 = o2[0U];
  uint64_t c210 = Lib_IntTypes_Intrinsics_add_carry_u64(c111, l10, h10, o2);
  uint64_t h = temp1;
  mul64(f31, f3, o3, &temp1);
  uint64_t l = o3[0U];
  uint64_t c35 = Lib_IntTypes_Intrinsics_add_carry_u64(c210, l, h, o3);
  uint64_t temp0 = temp1;
  uint64_t c5 = c35 + temp0;
  uint64_t c3 = add4(temp, b3, b3);
  uint64_t c36 = c5 + c3;
  t[7U] = c36;
  montgomery_multiplication_round_twice(t, round2, k0);
  montgomery_multiplication_round_twice(round2, round4, k0);
  reduction_prime_2prime_with_carry(round4, result);
}

static void bufferToJac(uint64_t *p, uint64_t *result)
{
  uint64_t *partPoint = result;
  memcpy(partPoint, p, (uint32_t)8U * sizeof (uint64_t));
  result[8U] = (uint64_t)1U;
  result[9U] = (uint64_t)0U;
  result[10U] = (uint64_t)0U;
  result[11U] = (uint64_t)0U;
}

/*
   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.
*/
static bool isPointAtInfinityPublic(uint64_t *p)
{
  uint64_t z0 = p[8U];
  uint64_t z1 = p[9U];
  uint64_t z2 = p[10U];
  uint64_t z3 = p[11U];
  bool z0_zero = z0 == (uint64_t)0U;
  bool z1_zero = z1 == (uint64_t)0U;
  bool z2_zero = z2 == (uint64_t)0U;
  bool z3_zero = z3 == (uint64_t)0U;
  return z0_zero && z1_zero && z2_zero && z3_zero;
}

/*
   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.
*/
static bool isPointOnCurvePublic(uint64_t *p)
{
  uint64_t y2Buffer[4U] = { 0U };
  uint64_t xBuffer[4U] = { 0U };
  uint64_t *x = p;
  uint64_t *y = p + (uint32_t)4U;
  uint64_t multBuffer0[8U] = { 0U };
  shift_256_impl(y, multBuffer0);
  solinas_reduction_impl(multBuffer0, y2Buffer);
  montgomery_square_buffer(y2Buffer, y2Buffer);
  uint64_t xToDomainBuffer[4U] = { 0U };
  uint64_t minusThreeXBuffer[4U] = { 0U };
  uint64_t p256_constant[4U] = { 0U };
  uint64_t multBuffer[8U] = { 0U };
  shift_256_impl(x, multBuffer);
  solinas_reduction_impl(multBuffer, xToDomainBuffer);
  montgomery_square_buffer(xToDomainBuffer, xBuffer);
  montgomery_multiplication_buffer(xBuffer, xToDomainBuffer, xBuffer);
  multByThree(xToDomainBuffer, minusThreeXBuffer);
  p256_sub(xBuffer, minusThreeXBuffer, xBuffer);
  p256_constant[0U] = (uint64_t)15608596021259845087U;
  p256_constant[1U] = (uint64_t)12461466548982526096U;
  p256_constant[2U] = (uint64_t)16546823903870267094U;
  p256_constant[3U] = (uint64_t)15866188208926050356U;
  p256_add(xBuffer, p256_constant, xBuffer);
  uint64_t r = compare_felem(y2Buffer, xBuffer);
  return !(r == (uint64_t)0U);
}

static bool isCoordinateValid(uint64_t *p)
{
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t *x = p;
  uint64_t *y = p + (uint32_t)4U;
  uint64_t carryX = sub4_il(x, prime256_buffer, tempBuffer);
  uint64_t carryY = sub4_il(y, prime256_buffer, tempBuffer);
  bool lessX = carryX == (uint64_t)1U;
  bool lessY = carryY == (uint64_t)1U;
  return lessX && lessY;
}

/*
   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.
*/
static bool isOrderCorrect(uint64_t *p, uint64_t *tempBuffer)
{
  uint64_t multResult[12U] = { 0U };
  uint64_t pBuffer[12U] = { 0U };
  memcpy(pBuffer, p, (uint32_t)12U * sizeof (uint64_t));
  scalarMultiplicationC(pBuffer, multResult, order_buffer, tempBuffer);
  bool result = isPointAtInfinityPublic(multResult);
  return result;
}

/*
   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.
*/
static bool verifyQValidCurvePoint(uint64_t *pubKeyAsPoint, uint64_t *tempBuffer)
{
  bool coordinatesValid = isCoordinateValid(pubKeyAsPoint);
  if (!coordinatesValid)
  {
    return false;
  }
  bool belongsToCurve = isPointOnCurvePublic(pubKeyAsPoint);
  bool orderCorrect = isOrderCorrect(pubKeyAsPoint, tempBuffer);
  return coordinatesValid && belongsToCurve && orderCorrect;
}

static bool isMoreThanZeroLessThanOrder(uint8_t *x)
{
  uint64_t xAsFelem[4U] = { 0U };
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(x, xAsFelem);
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t carry = sub4_il(xAsFelem, prime256order_buffer, tempBuffer);
  uint64_t less = FStar_UInt64_eq_mask(carry, (uint64_t)1U);
  uint64_t more = isZero_uint64_CT(xAsFelem);
  uint64_t notMore = ~more;
  uint64_t result = less & notMore;
  return ~result == (uint64_t)0U;
}

/*
  The pub(lic)_key input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over this variable.
*/
uint64_t Hacl_Impl_P256_DH__ecp256dh_r(uint64_t *result, uint64_t *pubKey, uint8_t *scalar)
{
  uint64_t tempBuffer[100U] = { 0U };
  uint64_t publicKeyBuffer[12U] = { 0U };
  bufferToJac(pubKey, publicKeyBuffer);
  bool publicKeyCorrect = verifyQValidCurvePoint(publicKeyBuffer, tempBuffer);
  if (publicKeyCorrect)
  {
    scalarMultiplicationL(publicKeyBuffer, result, scalar, tempBuffer);
    uint64_t flag = Hacl_Impl_P256_Core_isPointAtInfinityPrivate(result);
    return flag;
  }
  return (uint64_t)18446744073709551615U;
}

static inline void cswap0(uint64_t bit, uint64_t *p1, uint64_t *p2)
{
  uint64_t mask = (uint64_t)0U - bit;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t dummy = mask & (p1[i] ^ p2[i]);
    p1[i] = p1[i] ^ dummy;
    p2[i] = p2[i] ^ dummy;
  }
}

static void montgomery_ladder_exponent(uint64_t *r)
{
  uint64_t p[4U] = { 0U };
  p[0U] = (uint64_t)884452912994769583U;
  p[1U] = (uint64_t)4834901526196019579U;
  p[2U] = (uint64_t)0U;
  p[3U] = (uint64_t)4294967295U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)256U; i++)
  {
    uint32_t bit0 = (uint32_t)255U - i;
    uint64_t
    bit =
      (uint64_t)(order_inverse_buffer[bit0 / (uint32_t)8U] >> bit0 % (uint32_t)8U & (uint8_t)1U);
    cswap0(bit, p, r);
    montgomery_multiplication_ecdsa_module(p, r, r);
    montgomery_multiplication_ecdsa_module(p, p, p);
    cswap0(bit, p, r);
  }
  memcpy(r, p, (uint32_t)4U * sizeof (uint64_t));
}

static void fromDomainImpl(uint64_t *a, uint64_t *result)
{
  uint64_t one[4U] = { 0U };
  uploadOneImpl(one);
  montgomery_multiplication_ecdsa_module(one, a, result);
}

static void multPowerPartial(uint64_t *a, uint64_t *b, uint64_t *result)
{
  uint64_t buffFromDB[4U] = { 0U };
  fromDomainImpl(b, buffFromDB);
  fromDomainImpl(buffFromDB, buffFromDB);
  montgomery_multiplication_ecdsa_module(a, buffFromDB, result);
}

/*
   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.
*/
static bool isMoreThanZeroLessThanOrderMinusOne(uint64_t *f)
{
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t carry = sub4_il(f, prime256order_buffer, tempBuffer);
  bool less = carry == (uint64_t)1U;
  uint64_t f0 = f[0U];
  uint64_t f1 = f[1U];
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  bool z0_zero = f0 == (uint64_t)0U;
  bool z1_zero = f1 == (uint64_t)0U;
  bool z2_zero = f2 == (uint64_t)0U;
  bool z3_zero = f3 == (uint64_t)0U;
  bool more = z0_zero && z1_zero && z2_zero && z3_zero;
  return less && !more;
}

/*
   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.
*/
static bool compare_felem_bool(uint64_t *a, uint64_t *b)
{
  uint64_t a_0 = a[0U];
  uint64_t a_1 = a[1U];
  uint64_t a_2 = a[2U];
  uint64_t a_3 = a[3U];
  uint64_t b_0 = b[0U];
  uint64_t b_1 = b[1U];
  uint64_t b_2 = b[2U];
  uint64_t b_3 = b[3U];
  return a_0 == b_0 && a_1 == b_1 && a_2 == b_2 && a_3 == b_3;
}

/*
   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.
*/
static bool
ecdsa_verification_(
  Spec_ECDSA_hash_alg_ecdsa alg,
  uint64_t *pubKey,
  uint64_t *r,
  uint64_t *s,
  uint32_t mLen,
  uint8_t *m
)
{
  uint64_t tempBufferU64[120U] = { 0U };
  uint64_t *publicKeyBuffer = tempBufferU64;
  uint64_t *hashAsFelem = tempBufferU64 + (uint32_t)12U;
  uint64_t *tempBuffer = tempBufferU64 + (uint32_t)16U;
  uint64_t *xBuffer = tempBufferU64 + (uint32_t)116U;
  bufferToJac(pubKey, publicKeyBuffer);
  bool publicKeyCorrect = verifyQValidCurvePoint(publicKeyBuffer, tempBuffer);
  if (publicKeyCorrect == false)
  {
    return false;
  }
  bool isRCorrect = isMoreThanZeroLessThanOrderMinusOne(r);
  bool isSCorrect = isMoreThanZeroLessThanOrderMinusOne(s);
  bool step1 = isRCorrect && isSCorrect;
  if (step1 == false)
  {
    return false;
  }
  uint8_t tempBufferU8[64U] = { 0U };
  uint8_t *bufferU1 = tempBufferU8;
  uint8_t *bufferU2 = tempBufferU8 + (uint32_t)32U;
  uint32_t sz;
  if (alg.tag == Spec_ECDSA_NoHash)
  {
    sz = mLen;
  }
  else if (alg.tag == Spec_ECDSA_Hash)
  {
    Spec_Hash_Definitions_hash_alg a = alg._0;
    switch (a)
    {
      case Spec_Hash_Definitions_MD5:
        {
          sz = (uint32_t)16U;
          break;
        }
      case Spec_Hash_Definitions_SHA1:
        {
          sz = (uint32_t)20U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_224:
        {
          sz = (uint32_t)28U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_256:
        {
          sz = (uint32_t)32U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_384:
        {
          sz = (uint32_t)48U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_512:
        {
          sz = (uint32_t)64U;
          break;
        }
      case Spec_Hash_Definitions_Blake2S:
        {
          sz = (uint32_t)32U;
          break;
        }
      case Spec_Hash_Definitions_Blake2B:
        {
          sz = (uint32_t)64U;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
  }
  else
  {
    sz = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), sz);
  uint8_t mHash[sz];
  memset(mHash, 0U, sz * sizeof (uint8_t));
  if (alg.tag == Spec_ECDSA_NoHash)
  {
    memcpy(mHash, m, sz * sizeof (uint8_t));
  }
  else if (alg.tag == Spec_ECDSA_Hash)
  {
    Spec_Hash_Definitions_hash_alg a = alg._0;
    switch (a)
    {
      case Spec_Hash_Definitions_SHA2_256:
        {
          Hacl_Hash_SHA2_hash_256(m, mLen, mHash);
          break;
        }
      case Spec_Hash_Definitions_SHA2_384:
        {
          Hacl_Hash_SHA2_hash_384(m, mLen, mHash);
          break;
        }
      case Spec_Hash_Definitions_SHA2_512:
        {
          Hacl_Hash_SHA2_hash_512(m, mLen, mHash);
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
  uint8_t *cutHash = mHash;
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(cutHash, hashAsFelem);
  reduction_prime_2prime_order(hashAsFelem, hashAsFelem);
  uint64_t tempBuffer1[12U] = { 0U };
  uint64_t *inverseS = tempBuffer1;
  uint64_t *u1 = tempBuffer1 + (uint32_t)4U;
  uint64_t *u2 = tempBuffer1 + (uint32_t)8U;
  fromDomainImpl(s, inverseS);
  montgomery_ladder_exponent(inverseS);
  multPowerPartial(inverseS, hashAsFelem, u1);
  multPowerPartial(inverseS, r, u2);
  Hacl_Impl_P256_LowLevel_changeEndian(u1);
  Hacl_Impl_P256_LowLevel_changeEndian(u2);
  Hacl_Impl_P256_LowLevel_toUint8(u1, bufferU1);
  Hacl_Impl_P256_LowLevel_toUint8(u2, bufferU2);
  uint64_t pointSum[12U] = { 0U };
  uint64_t points[24U] = { 0U };
  uint64_t *buff = tempBuffer + (uint32_t)12U;
  uint64_t *pointU1G = points;
  uint64_t *pointU2Q0 = points + (uint32_t)12U;
  secretToPublicWithoutNorm(pointU1G, bufferU1, tempBuffer);
  scalarMultiplicationWithoutNorm(publicKeyBuffer, pointU2Q0, bufferU2, tempBuffer);
  uint64_t *pointU1G0 = points;
  uint64_t *pointU2Q = points + (uint32_t)12U;
  uint64_t tmp[112U] = { 0U };
  uint64_t *tmpForNorm = tmp;
  uint64_t *result0Norm = tmp + (uint32_t)88U;
  uint64_t *result1Norm = tmp + (uint32_t)100U;
  uint64_t *pointU1G1 = points;
  uint64_t *pointU2Q1 = points + (uint32_t)12U;
  norm(pointU1G1, result0Norm, tmpForNorm);
  norm(pointU2Q1, result1Norm, tmpForNorm);
  uint64_t *x0 = result0Norm;
  uint64_t *y0 = result0Norm + (uint32_t)4U;
  uint64_t *z0 = result0Norm + (uint32_t)8U;
  uint64_t *x1 = result1Norm;
  uint64_t *y1 = result1Norm + (uint32_t)4U;
  uint64_t *z1 = result1Norm + (uint32_t)8U;
  bool xEqual = compare_felem_bool(x0, x1);
  bool yEqual = compare_felem_bool(y0, y1);
  bool zEqual = compare_felem_bool(z0, z1);
  bool equalX = xEqual && yEqual && zEqual;
  bool equalX0 = equalX;
  if (equalX0)
  {
    point_double(pointU1G0, pointSum, buff);
  }
  else
  {
    point_add(pointU1G0, pointU2Q, pointSum, buff);
  }
  norm(pointSum, pointSum, buff);
  bool resultIsPAI = isPointAtInfinityPublic(pointSum);
  uint64_t *xCoordinateSum = pointSum;
  memcpy(xBuffer, xCoordinateSum, (uint32_t)4U * sizeof (uint64_t));
  reduction_prime_2prime_order(xBuffer, xBuffer);
  bool r1 = !resultIsPAI;
  bool state = r1;
  if (state == false)
  {
    return false;
  }
  bool result = compare_felem_bool(xBuffer, r);
  return result;
}

static uint64_t
ecdsa_signature_core(
  Spec_ECDSA_hash_alg_ecdsa alg,
  uint64_t *r,
  uint64_t *s,
  uint32_t mLen,
  uint8_t *m,
  uint64_t *privKeyAsFelem,
  uint8_t *k
)
{
  uint64_t hashAsFelem[4U] = { 0U };
  uint64_t tempBuffer[100U] = { 0U };
  uint64_t kAsFelem[4U] = { 0U };
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(k, kAsFelem);
  uint32_t sz;
  if (alg.tag == Spec_ECDSA_NoHash)
  {
    sz = mLen;
  }
  else if (alg.tag == Spec_ECDSA_Hash)
  {
    Spec_Hash_Definitions_hash_alg a = alg._0;
    switch (a)
    {
      case Spec_Hash_Definitions_MD5:
        {
          sz = (uint32_t)16U;
          break;
        }
      case Spec_Hash_Definitions_SHA1:
        {
          sz = (uint32_t)20U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_224:
        {
          sz = (uint32_t)28U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_256:
        {
          sz = (uint32_t)32U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_384:
        {
          sz = (uint32_t)48U;
          break;
        }
      case Spec_Hash_Definitions_SHA2_512:
        {
          sz = (uint32_t)64U;
          break;
        }
      case Spec_Hash_Definitions_Blake2S:
        {
          sz = (uint32_t)32U;
          break;
        }
      case Spec_Hash_Definitions_Blake2B:
        {
          sz = (uint32_t)64U;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
  }
  else
  {
    sz = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), sz);
  uint8_t mHash[sz];
  memset(mHash, 0U, sz * sizeof (uint8_t));
  if (alg.tag == Spec_ECDSA_NoHash)
  {
    memcpy(mHash, m, sz * sizeof (uint8_t));
  }
  else if (alg.tag == Spec_ECDSA_Hash)
  {
    Spec_Hash_Definitions_hash_alg a = alg._0;
    switch (a)
    {
      case Spec_Hash_Definitions_SHA2_256:
        {
          Hacl_Hash_SHA2_hash_256(m, mLen, mHash);
          break;
        }
      case Spec_Hash_Definitions_SHA2_384:
        {
          Hacl_Hash_SHA2_hash_384(m, mLen, mHash);
          break;
        }
      case Spec_Hash_Definitions_SHA2_512:
        {
          Hacl_Hash_SHA2_hash_512(m, mLen, mHash);
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
  uint8_t *cutHash = mHash;
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(cutHash, hashAsFelem);
  reduction_prime_2prime_order(hashAsFelem, hashAsFelem);
  uint64_t result[12U] = { 0U };
  uint64_t *tempForNorm = tempBuffer;
  secretToPublicWithoutNorm(result, k, tempBuffer);
  normX(result, r, tempForNorm);
  reduction_prime_2prime_order(r, r);
  uint64_t step5Flag = isZero_uint64_CT(r);
  uint64_t rda[4U] = { 0U };
  uint64_t zBuffer[4U] = { 0U };
  uint64_t kInv[4U] = { 0U };
  montgomery_multiplication_ecdsa_module(r, privKeyAsFelem, rda);
  fromDomainImpl(hashAsFelem, zBuffer);
  uint64_t t = add4(rda, zBuffer, zBuffer);
  uint64_t tempBuffer1[4U] = { 0U };
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t c = sub4_il(zBuffer, prime256order_buffer, tempBuffer1);
  uint64_t
  carry = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t, (uint64_t)0U, &tempBufferForSubborrow);
  cmovznz4(carry, tempBuffer1, zBuffer, zBuffer);
  memcpy(kInv, kAsFelem, (uint32_t)4U * sizeof (uint64_t));
  montgomery_ladder_exponent(kInv);
  montgomery_multiplication_ecdsa_module(zBuffer, kInv, s);
  uint64_t sIsZero = isZero_uint64_CT(s);
  return step5Flag | sIsZero;
}

static inline void cswap1(uint64_t bit, uint64_t *p1, uint64_t *p2)
{
  uint64_t mask = (uint64_t)0U - bit;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t dummy = mask & (p1[i] ^ p2[i]);
    p1[i] = p1[i] ^ dummy;
    p2[i] = p2[i] ^ dummy;
  }
}

static void montgomery_ladder_power(uint64_t *a, const uint8_t *scalar, uint64_t *result)
{
  uint64_t p[4U] = { 0U };
  p[0U] = (uint64_t)1U;
  p[1U] = (uint64_t)18446744069414584320U;
  p[2U] = (uint64_t)18446744073709551615U;
  p[3U] = (uint64_t)4294967294U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)256U; i++)
  {
    uint32_t bit0 = (uint32_t)255U - i;
    uint64_t bit = (uint64_t)(scalar[bit0 / (uint32_t)8U] >> bit0 % (uint32_t)8U & (uint8_t)1U);
    cswap1(bit, p, a);
    montgomery_multiplication_buffer(p, a, a);
    montgomery_square_buffer(p, p);
    cswap1(bit, p, a);
  }
  memcpy(result, p, (uint32_t)4U * sizeof (uint64_t));
}

static const
uint8_t
sqPower_buffer[32U] =
  {
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)64U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)64U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)192U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)63U
  };

static void computeYFromX(uint64_t *x, uint64_t *result, uint64_t sign)
{
  uint64_t aCoordinateBuffer[4U] = { 0U };
  uint64_t bCoordinateBuffer[4U] = { 0U };
  aCoordinateBuffer[0U] = (uint64_t)18446744073709551612U;
  aCoordinateBuffer[1U] = (uint64_t)17179869183U;
  aCoordinateBuffer[2U] = (uint64_t)0U;
  aCoordinateBuffer[3U] = (uint64_t)18446744056529682436U;
  bCoordinateBuffer[0U] = (uint64_t)15608596021259845087U;
  bCoordinateBuffer[1U] = (uint64_t)12461466548982526096U;
  bCoordinateBuffer[2U] = (uint64_t)16546823903870267094U;
  bCoordinateBuffer[3U] = (uint64_t)15866188208926050356U;
  montgomery_multiplication_buffer(aCoordinateBuffer, x, aCoordinateBuffer);
  cube(x, result);
  p256_add(result, aCoordinateBuffer, result);
  p256_add(result, bCoordinateBuffer, result);
  uploadZeroImpl(aCoordinateBuffer);
  montgomery_ladder_power(result, sqPower_buffer, result);
  montgomery_multiplication_buffer_by_one(result, result);
  p256_sub(aCoordinateBuffer, result, bCoordinateBuffer);
  uint64_t word = result[0U];
  uint64_t bitToCheck = word & (uint64_t)1U;
  uint64_t flag = FStar_UInt64_eq_mask(bitToCheck, sign);
  cmovznz4(flag, bCoordinateBuffer, result, result);
}

/*
 Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
 priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: bool, where True stands for the correct signature generation. False value means that an error has occurred. 
  
 The private key and the nonce are expected to be more than 0 and less than the curve order.
*/
bool
Hacl_P256_ecdsa_sign_p256_sha2(
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
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(privKey, privKeyAsFelem);
  uint64_t
  flag =
    ecdsa_signature_core((
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
  return flag == (uint64_t)0U;
}

/*
 Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
 priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: bool, where True stands for the correct signature generation. False value means that an error has occurred. 
  
 The private key and the nonce are expected to be more than 0 and less than the curve order.
*/
bool
Hacl_P256_ecdsa_sign_p256_sha384(
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
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(privKey, privKeyAsFelem);
  uint64_t
  flag =
    ecdsa_signature_core((
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
  return flag == (uint64_t)0U;
}

/*
 Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
 priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: bool, where True stands for the correct signature generation. False value means that an error has occurred. 
  
 The private key and the nonce are expected to be more than 0 and less than the curve order.
*/
bool
Hacl_P256_ecdsa_sign_p256_sha512(
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
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(privKey, privKeyAsFelem);
  uint64_t
  flag =
    ecdsa_signature_core((
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
  return flag == (uint64_t)0U;
}

/*
 Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
 priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: bool, where True stands for the correct signature generation. False value means that an error has occurred. 
  
 The private key and the nonce are expected to be more than 0 and less than the curve order.
  
 The message m is expected to be hashed by a strong hash function, the lenght of the message is expected to be 32 bytes and more.
*/
bool
Hacl_P256_ecdsa_sign_p256_without_hash(
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
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(privKey, privKeyAsFelem);
  uint64_t
  flag =
    ecdsa_signature_core(((Spec_ECDSA_hash_alg_ecdsa){ .tag = Spec_ECDSA_NoHash }),
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
  return flag == (uint64_t)0U;
}

/*
 The input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over the input.
  
 Input: m buffer: uint8 [mLen], 
 pub(lic)Key: uint8[64], 
 r: uint8[32], 
 s: uint8[32]. 
  
 Output: bool, where true stands for the correct signature verification. 
*/
bool
Hacl_P256_ecdsa_verif_p256_sha2(
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
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(r, rAsFelem);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(s, sAsFelem);
  bool
  result =
    ecdsa_verification_((
        (Spec_ECDSA_hash_alg_ecdsa){ .tag = Spec_ECDSA_Hash, ._0 = Spec_Hash_Definitions_SHA2_256 }
      ),
      publicKeyAsFelem,
      rAsFelem,
      sAsFelem,
      mLen,
      m);
  return result;
}

/*
  The input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over the input.
  
 Input: m buffer: uint8 [mLen], 
 pub(lic)Key: uint8[64], 
 r: uint8[32], 
 s: uint8[32]. 
  
 Output: bool, where true stands for the correct signature verification. 
*/
bool
Hacl_P256_ecdsa_verif_p256_sha384(
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
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(r, rAsFelem);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(s, sAsFelem);
  bool
  result =
    ecdsa_verification_((
        (Spec_ECDSA_hash_alg_ecdsa){ .tag = Spec_ECDSA_Hash, ._0 = Spec_Hash_Definitions_SHA2_384 }
      ),
      publicKeyAsFelem,
      rAsFelem,
      sAsFelem,
      mLen,
      m);
  return result;
}

/*
  The input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over the input.
  
 Input: m buffer: uint8 [mLen], 
 pub(lic)Key: uint8[64], 
 r: uint8[32], 
 s: uint8[32]. 
  
 Output: bool, where true stands for the correct signature verification. 
*/
bool
Hacl_P256_ecdsa_verif_p256_sha512(
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
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(r, rAsFelem);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(s, sAsFelem);
  bool
  result =
    ecdsa_verification_((
        (Spec_ECDSA_hash_alg_ecdsa){ .tag = Spec_ECDSA_Hash, ._0 = Spec_Hash_Definitions_SHA2_512 }
      ),
      publicKeyAsFelem,
      rAsFelem,
      sAsFelem,
      mLen,
      m);
  return result;
}

/*
 The input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over the input.
  
 Input: m buffer: uint8 [mLen], 
 pub(lic)Key: uint8[64], 
 r: uint8[32], 
 s: uint8[32]. 
  
 Output: bool, where true stands for the correct signature verification.
  
 The message m is expected to be hashed by a strong hash function, the lenght of the message is expected to be 32 bytes and more.
*/
bool
Hacl_P256_ecdsa_verif_without_hash(
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
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(r, rAsFelem);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(s, sAsFelem);
  bool
  result =
    ecdsa_verification_(((Spec_ECDSA_hash_alg_ecdsa){ .tag = Spec_ECDSA_NoHash }),
      publicKeyAsFelem,
      rAsFelem,
      sAsFelem,
      mLen,
      m);
  return result;
}

/*
 Public key verification function. 
  
  The input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over the input.
  
 Input: pub(lic)Key: uint8[64]. 
  
 Output: bool, where 0 stands for the public key to be correct with respect to SP 800-56A:  
 Verify that the public key is not the “point at infinity”, represented as O. 
 Verify that the affine x and y coordinates of the point represented by the public key are in the range [0, p – 1] where p is the prime defining the finite field. 
 Verify that y2 = x3 + ax + b where a and b are the coefficients of the curve equation. 
 Verify that nQ = O (the point at infinity), where n is the order of the curve and Q is the public key point.
  
 The last extract is taken from : https://neilmadden.blog/2017/05/17/so-how-do-you-validate-nist-ecdh-public-keys/
*/
bool Hacl_P256_verify_q(uint8_t *pubKey)
{
  uint8_t *pubKeyX = pubKey;
  uint8_t *pubKeyY = pubKey + (uint32_t)32U;
  uint64_t tempBuffer[120U] = { 0U };
  uint64_t *tempBufferV = tempBuffer;
  uint64_t *publicKeyJ = tempBuffer + (uint32_t)100U;
  uint64_t *publicKeyB = tempBuffer + (uint32_t)112U;
  uint64_t *publicKeyX = publicKeyB;
  uint64_t *publicKeyY = publicKeyB + (uint32_t)4U;
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyX, publicKeyX);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyY, publicKeyY);
  bufferToJac(publicKeyB, publicKeyJ);
  bool r = verifyQValidCurvePoint(publicKeyJ, tempBufferV);
  return r;
}

/*
 There and further we introduce notions of compressed point and not compressed point. 
  
 We denote || as byte concatenation. 
  
 A compressed point is a point representaion as follows: (0x2 + y % 2) || x.
  
 A not Compressed point is a point representation as follows: 0x4 || x || y.

  
 
 Input: a point in not compressed form (uint8[65]), 
 result: uint8[64] (internal point representation).
  
 Output: bool, where true stands for the correct decompression.
 
*/
bool Hacl_P256_decompression_not_compressed_form(uint8_t *b, uint8_t *result)
{
  uint8_t compressionIdentifier = b[0U];
  bool correctIdentifier = (uint8_t)4U == compressionIdentifier;
  if (correctIdentifier)
  {
    memcpy(result, b + (uint32_t)1U, (uint32_t)64U * sizeof (uint8_t));
  }
  return correctIdentifier;
}

/*
 Input: a point in compressed form (uint8[33]), 
 result: uint8[64] (internal point representation).
  
 Output: bool, where true stands for the correct decompression.
 
*/
bool Hacl_P256_decompression_compressed_form(uint8_t *b, uint8_t *result)
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
    memcpy(result, x, (uint32_t)32U * sizeof (uint8_t));
    Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(x, t0);
    uint64_t tempBuffer[4U] = { 0U };
    uint64_t carry = sub4_il(t0, prime256_buffer, tempBuffer);
    bool lessThanPrimeXCoordinate = carry == (uint64_t)1U;
    if (!lessThanPrimeXCoordinate)
    {
      return false;
    }
    uint64_t multBuffer[8U] = { 0U };
    shift_256_impl(t0, multBuffer);
    solinas_reduction_impl(multBuffer, t0);
    uint64_t identifierBit = (uint64_t)(compressedIdentifier & (uint8_t)1U);
    computeYFromX(t0, t1, identifierBit);
    Hacl_Impl_P256_LowLevel_changeEndian(t1);
    Hacl_Impl_P256_LowLevel_toUint8(t1, result + (uint32_t)32U);
    return true;
  }
  return false;
}

/*
 Input: a point buffer (internal representation: uint8[64]), 
 result: a point in not compressed form (uint8[65]).
*/
void Hacl_P256_compression_not_compressed_form(uint8_t *b, uint8_t *result)
{
  uint8_t *to = result + (uint32_t)1U;
  memcpy(to, b, (uint32_t)64U * sizeof (uint8_t));
  result[0U] = (uint8_t)4U;
}

/*
 Input: a point buffer (internal representation: uint8[64]), 
 result: a point in not compressed form (uint8[33]).
*/
void Hacl_P256_compression_compressed_form(uint8_t *b, uint8_t *result)
{
  uint8_t *y = b + (uint32_t)32U;
  uint8_t lastWordY = y[31U];
  uint8_t lastBitY = lastWordY & (uint8_t)1U;
  uint8_t identifier = lastBitY + (uint8_t)2U;
  memcpy(result + (uint32_t)1U, b, (uint32_t)32U * sizeof (uint8_t));
  result[0U] = identifier;
}

/*
 Input: result: uint8[64], 
 scalar: uint8[32].
  
 Output: bool, where True stands for the correct key generation. 
  
 False means that an error has occurred (possibly that the result respresents point at infinity). 
  
*/
bool Hacl_P256_ecp256dh_i(uint8_t *result, uint8_t *scalar)
{
  uint64_t tempBuffer[100U] = { 0U };
  uint64_t resultBuffer[12U] = { 0U };
  uint64_t *resultBufferX = resultBuffer;
  uint64_t *resultBufferY = resultBuffer + (uint32_t)4U;
  uint8_t *resultX = result;
  uint8_t *resultY = result + (uint32_t)32U;
  Hacl_Impl_P256_Core_secretToPublic(resultBuffer, scalar, tempBuffer);
  uint64_t flag = Hacl_Impl_P256_Core_isPointAtInfinityPrivate(resultBuffer);
  Hacl_Impl_P256_LowLevel_changeEndian(resultBufferX);
  Hacl_Impl_P256_LowLevel_changeEndian(resultBufferY);
  Hacl_Impl_P256_LowLevel_toUint8(resultBufferX, resultX);
  Hacl_Impl_P256_LowLevel_toUint8(resultBufferY, resultY);
  return flag == (uint64_t)0U;
}

/*
 
   The pub(lic)_key input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over this variable.
  
 Input: result: uint8[64], 
 pub(lic)Key: uint8[64], 
 scalar: uint8[32].
  
 Output: bool, where True stands for the correct key generation. False value means that an error has occurred (possibly the provided public key was incorrect or the result represents point at infinity). 
  
*/
bool Hacl_P256_ecp256dh_r(uint8_t *result, uint8_t *pubKey, uint8_t *scalar)
{
  uint64_t resultBufferFelem[12U] = { 0U };
  uint64_t *resultBufferFelemX = resultBufferFelem;
  uint64_t *resultBufferFelemY = resultBufferFelem + (uint32_t)4U;
  uint8_t *resultX = result;
  uint8_t *resultY = result + (uint32_t)32U;
  uint64_t publicKeyAsFelem[8U] = { 0U };
  uint64_t *publicKeyFelemX = publicKeyAsFelem;
  uint64_t *publicKeyFelemY = publicKeyAsFelem + (uint32_t)4U;
  uint8_t *pubKeyX = pubKey;
  uint8_t *pubKeyY = pubKey + (uint32_t)32U;
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  Hacl_Impl_P256_LowLevel_toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  uint64_t flag = Hacl_Impl_P256_DH__ecp256dh_r(resultBufferFelem, publicKeyAsFelem, scalar);
  Hacl_Impl_P256_LowLevel_changeEndian(resultBufferFelemX);
  Hacl_Impl_P256_LowLevel_changeEndian(resultBufferFelemY);
  Hacl_Impl_P256_LowLevel_toUint8(resultBufferFelemX, resultX);
  Hacl_Impl_P256_LowLevel_toUint8(resultBufferFelemY, resultY);
  return flag == (uint64_t)0U;
}

/*
 Input: scalar: uint8[32].
  
 Output: bool, where true stands for the scalar to be more than 0 and less than order.
*/
bool Hacl_P256_is_more_than_zero_less_than_order(uint8_t *x)
{
  return isMoreThanZeroLessThanOrder(x);
}

