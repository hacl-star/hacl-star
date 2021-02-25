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


#include "Hacl_P256.h"

static u64 isZero_uint64_CT(u64 *f)
{
  u64 a0 = f[0U];
  u64 a1 = f[1U];
  u64 a2 = f[2U];
  u64 a3 = f[3U];
  u64 r0 = FStar_UInt64_eq_mask(a0, (u64)0U);
  u64 r1 = FStar_UInt64_eq_mask(a1, (u64)0U);
  u64 r2 = FStar_UInt64_eq_mask(a2, (u64)0U);
  u64 r3 = FStar_UInt64_eq_mask(a3, (u64)0U);
  u64 r01 = r0 & r1;
  u64 r23 = r2 & r3;
  return r01 & r23;
}

static u64 compare_felem(u64 *a, u64 *b)
{
  u64 a_0 = a[0U];
  u64 a_1 = a[1U];
  u64 a_2 = a[2U];
  u64 a_3 = a[3U];
  u64 b_0 = b[0U];
  u64 b_1 = b[1U];
  u64 b_2 = b[2U];
  u64 b_3 = b[3U];
  u64 r_0 = FStar_UInt64_eq_mask(a_0, b_0);
  u64 r_1 = FStar_UInt64_eq_mask(a_1, b_1);
  u64 r_2 = FStar_UInt64_eq_mask(a_2, b_2);
  u64 r_3 = FStar_UInt64_eq_mask(a_3, b_3);
  u64 r01 = r_0 & r_1;
  u64 r23 = r_2 & r_3;
  return r01 & r23;
}

static void copy_conditional(u64 *out, u64 *x, u64 mask)
{
  u64 out_0 = out[0U];
  u64 out_1 = out[1U];
  u64 out_2 = out[2U];
  u64 out_3 = out[3U];
  u64 x_0 = x[0U];
  u64 x_1 = x[1U];
  u64 x_2 = x[2U];
  u64 x_3 = x[3U];
  u64 r_0 = out_0 ^ (mask & (out_0 ^ x_0));
  u64 r_1 = out_1 ^ (mask & (out_1 ^ x_1));
  u64 r_2 = out_2 ^ (mask & (out_2 ^ x_2));
  u64 r_3 = out_3 ^ (mask & (out_3 ^ x_3));
  out[0U] = r_0;
  out[1U] = r_1;
  out[2U] = r_2;
  out[3U] = r_3;
}

static u64 add4(u64 *x, u64 *y, u64 *result)
{
  u64 *r0 = result;
  u64 *r1 = result + (u32)1U;
  u64 *r2 = result + (u32)2U;
  u64 *r3 = result + (u32)3U;
  u64 cc0 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, x[0U], y[0U], r0);
  u64 cc1 = Lib_IntTypes_Intrinsics_add_carry_u64(cc0, x[1U], y[1U], r1);
  u64 cc2 = Lib_IntTypes_Intrinsics_add_carry_u64(cc1, x[2U], y[2U], r2);
  u64 cc3 = Lib_IntTypes_Intrinsics_add_carry_u64(cc2, x[3U], y[3U], r3);
  return cc3;
}

static u64 add4_with_carry(u64 c, u64 *x, u64 *y, u64 *result)
{
  u64 *r0 = result;
  u64 *r1 = result + (u32)1U;
  u64 *r2 = result + (u32)2U;
  u64 *r3 = result + (u32)3U;
  u64 cc = Lib_IntTypes_Intrinsics_add_carry_u64(c, x[0U], y[0U], r0);
  u64 cc1 = Lib_IntTypes_Intrinsics_add_carry_u64(cc, x[1U], y[1U], r1);
  u64 cc2 = Lib_IntTypes_Intrinsics_add_carry_u64(cc1, x[2U], y[2U], r2);
  u64 cc3 = Lib_IntTypes_Intrinsics_add_carry_u64(cc2, x[3U], y[3U], r3);
  return cc3;
}

static u64 add8(u64 *x, u64 *y, u64 *result)
{
  u64 *a0 = x;
  u64 *a1 = x + (u32)4U;
  u64 *b0 = y;
  u64 *b1 = y + (u32)4U;
  u64 *c0 = result;
  u64 *c1 = result + (u32)4U;
  u64 carry0 = add4(a0, b0, c0);
  u64 carry1 = add4_with_carry(carry0, a1, b1, c1);
  return carry1;
}

static u64 add4_variables(u64 *x, u64 cin, u64 y0, u64 y1, u64 y2, u64 y3, u64 *result)
{
  u64 *r0 = result;
  u64 *r1 = result + (u32)1U;
  u64 *r2 = result + (u32)2U;
  u64 *r3 = result + (u32)3U;
  u64 cc = Lib_IntTypes_Intrinsics_add_carry_u64(cin, x[0U], y0, r0);
  u64 cc1 = Lib_IntTypes_Intrinsics_add_carry_u64(cc, x[1U], y1, r1);
  u64 cc2 = Lib_IntTypes_Intrinsics_add_carry_u64(cc1, x[2U], y2, r2);
  u64 cc3 = Lib_IntTypes_Intrinsics_add_carry_u64(cc2, x[3U], y3, r3);
  return cc3;
}

static u64 sub4_il(u64 *x, const u64 *y, u64 *result)
{
  u64 *r0 = result;
  u64 *r1 = result + (u32)1U;
  u64 *r2 = result + (u32)2U;
  u64 *r3 = result + (u32)3U;
  u64 cc = Lib_IntTypes_Intrinsics_sub_borrow_u64((u64)0U, x[0U], y[0U], r0);
  u64 cc1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc, x[1U], y[1U], r1);
  u64 cc2 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc1, x[2U], y[2U], r2);
  u64 cc3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc2, x[3U], y[3U], r3);
  return cc3;
}

static u64 sub4(u64 *x, u64 *y, u64 *result)
{
  u64 *r0 = result;
  u64 *r1 = result + (u32)1U;
  u64 *r2 = result + (u32)2U;
  u64 *r3 = result + (u32)3U;
  u64 cc = Lib_IntTypes_Intrinsics_sub_borrow_u64((u64)0U, x[0U], y[0U], r0);
  u64 cc1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc, x[1U], y[1U], r1);
  u64 cc2 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc1, x[2U], y[2U], r2);
  u64 cc3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc2, x[3U], y[3U], r3);
  return cc3;
}

static void mul64(u64 x, u64 y, u64 *result, u64 *temp)
{
  uint128_t res = (uint128_t)x * y;
  u64 l0 = (uint64_t)res;
  u64 h0 = (uint64_t)(res >> (u32)64U);
  result[0U] = l0;
  temp[0U] = h0;
}

static void sq(u64 *f, u64 *out)
{
  u64 wb[17U] = { 0U };
  u64 *tb = wb;
  u64 *memory = wb + (u32)5U;
  u64 *b0 = out;
  u64 f01 = f[0U];
  u64 f310 = f[3U];
  u64 *o30 = b0 + (u32)3U;
  u64 *temp1 = tb;
  u64 f02 = f[0U];
  u64 f12 = f[1U];
  u64 f22 = f[2U];
  u64 *o01 = b0;
  u64 *o10 = b0 + (u32)1U;
  u64 *o20 = b0 + (u32)2U;
  u64 h_00;
  u64 l0;
  u64 c10;
  u64 h_10;
  u64 l10;
  u64 c20;
  u64 h_20;
  u64 l3;
  u64 c30;
  u64 temp0;
  u64 c0;
  u64 *b1;
  u64 *temp2;
  u64 *tempBufferResult0;
  u64 f11;
  u64 f210;
  u64 f311;
  u64 *o00;
  u64 *o11;
  u64 *o21;
  u64 *o31;
  u64 h_01;
  u64 l4;
  u64 c12;
  u64 h_11;
  u64 l11;
  u64 c22;
  u64 h_21;
  u64 l20;
  u64 c31;
  u64 h_30;
  u64 c40;
  u64 c1;
  u64 *b2;
  u64 *temp3;
  u64 *tempBufferResult1;
  u64 f21;
  u64 f312;
  u64 *o02;
  u64 *o12;
  u64 *o22;
  u64 *o32;
  u64 h_0;
  u64 l5;
  u64 c110;
  u64 h_1;
  u64 l12;
  u64 c23;
  u64 h_2;
  u64 l21;
  u64 c32;
  u64 h_31;
  u64 c41;
  u64 c2;
  u64 *b3;
  u64 *temp;
  u64 *tempBufferResult;
  u64 f31;
  u64 *o0;
  u64 *o1;
  u64 *o2;
  u64 *o3;
  u64 h;
  u64 l;
  u64 c11;
  u64 h4;
  u64 l1;
  u64 c21;
  u64 h5;
  u64 l2;
  u64 c33;
  u64 h_3;
  u64 c4;
  u64 c3;
  mul64(f02, f02, o01, temp1);
  h_00 = temp1[0U];
  mul64(f02, f12, o10, temp1);
  l0 = o10[0U];
  memory[0U] = l0;
  memory[1U] = temp1[0U];
  c10 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l0, h_00, o10);
  h_10 = temp1[0U];
  mul64(f02, f22, o20, temp1);
  l10 = o20[0U];
  memory[2U] = l10;
  memory[3U] = temp1[0U];
  c20 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, l10, h_10, o20);
  h_20 = temp1[0U];
  mul64(f01, f310, o30, temp1);
  l3 = o30[0U];
  memory[4U] = l3;
  memory[5U] = temp1[0U];
  c30 = Lib_IntTypes_Intrinsics_add_carry_u64(c20, l3, h_20, o30);
  temp0 = temp1[0U];
  c0 = c30 + temp0;
  out[4U] = c0;
  b1 = out + (u32)1U;
  temp2 = tb;
  tempBufferResult0 = tb + (u32)1U;
  f11 = f[1U];
  f210 = f[2U];
  f311 = f[3U];
  o00 = tempBufferResult0;
  o11 = tempBufferResult0 + (u32)1U;
  o21 = tempBufferResult0 + (u32)2U;
  o31 = tempBufferResult0 + (u32)3U;
  o00[0U] = memory[0U];
  h_01 = memory[1U];
  mul64(f11, f11, o11, temp2);
  l4 = o11[0U];
  c12 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l4, h_01, o11);
  h_11 = temp2[0U];
  mul64(f11, f210, o21, temp2);
  l11 = o21[0U];
  memory[6U] = l11;
  memory[7U] = temp2[0U];
  c22 = Lib_IntTypes_Intrinsics_add_carry_u64(c12, l11, h_11, o21);
  h_21 = temp2[0U];
  mul64(f11, f311, o31, temp2);
  l20 = o31[0U];
  memory[8U] = l20;
  memory[9U] = temp2[0U];
  c31 = Lib_IntTypes_Intrinsics_add_carry_u64(c22, l20, h_21, o31);
  h_30 = temp2[0U];
  c40 = add4(tempBufferResult0, b1, b1);
  c1 = c31 + h_30 + c40;
  out[5U] = c1;
  b2 = out + (u32)2U;
  temp3 = tb;
  tempBufferResult1 = tb + (u32)1U;
  f21 = f[2U];
  f312 = f[3U];
  o02 = tempBufferResult1;
  o12 = tempBufferResult1 + (u32)1U;
  o22 = tempBufferResult1 + (u32)2U;
  o32 = tempBufferResult1 + (u32)3U;
  o02[0U] = memory[2U];
  h_0 = memory[3U];
  o12[0U] = memory[6U];
  l5 = o12[0U];
  c110 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l5, h_0, o12);
  h_1 = memory[7U];
  mul64(f21, f21, o22, temp3);
  l12 = o22[0U];
  c23 = Lib_IntTypes_Intrinsics_add_carry_u64(c110, l12, h_1, o22);
  h_2 = temp3[0U];
  mul64(f21, f312, o32, temp3);
  l21 = o32[0U];
  memory[10U] = l21;
  memory[11U] = temp3[0U];
  c32 = Lib_IntTypes_Intrinsics_add_carry_u64(c23, l21, h_2, o32);
  h_31 = temp3[0U];
  c41 = add4(tempBufferResult1, b2, b2);
  c2 = c32 + h_31 + c41;
  out[6U] = c2;
  b3 = out + (u32)3U;
  temp = tb;
  tempBufferResult = tb + (u32)1U;
  f31 = f[3U];
  o0 = tempBufferResult;
  o1 = tempBufferResult + (u32)1U;
  o2 = tempBufferResult + (u32)2U;
  o3 = tempBufferResult + (u32)3U;
  o0[0U] = memory[4U];
  h = memory[5U];
  o1[0U] = memory[8U];
  l = o1[0U];
  c11 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l, h, o1);
  h4 = memory[9U];
  o2[0U] = memory[10U];
  l1 = o2[0U];
  c21 = Lib_IntTypes_Intrinsics_add_carry_u64(c11, l1, h4, o2);
  h5 = memory[11U];
  mul64(f31, f31, o3, temp);
  l2 = o3[0U];
  c33 = Lib_IntTypes_Intrinsics_add_carry_u64(c21, l2, h5, o3);
  h_3 = temp[0U];
  c4 = add4(tempBufferResult, b3, b3);
  c3 = c33 + h_3 + c4;
  out[7U] = c3;
}

static void cmovznz4(u64 cin, u64 *x, u64 *y, u64 *r)
{
  u64 mask = ~FStar_UInt64_eq_mask(cin, (u64)0U);
  u64 r0 = (y[0U] & mask) | (x[0U] & ~mask);
  u64 r1 = (y[1U] & mask) | (x[1U] & ~mask);
  u64 r2 = (y[2U] & mask) | (x[2U] & ~mask);
  u64 r3 = (y[3U] & mask) | (x[3U] & ~mask);
  r[0U] = r0;
  r[1U] = r1;
  r[2U] = r2;
  r[3U] = r3;
}

static void shift_256_impl(u64 *i, u64 *o)
{
  o[0U] = (u64)0U;
  o[1U] = (u64)0U;
  o[2U] = (u64)0U;
  o[3U] = (u64)0U;
  o[4U] = i[0U];
  o[5U] = i[1U];
  o[6U] = i[2U];
  o[7U] = i[3U];
}

static void shift8(u64 *t, u64 *out)
{
  u64 t1 = t[1U];
  u64 t2 = t[2U];
  u64 t3 = t[3U];
  u64 t4 = t[4U];
  u64 t5 = t[5U];
  u64 t6 = t[6U];
  u64 t7 = t[7U];
  out[0U] = t1;
  out[1U] = t2;
  out[2U] = t3;
  out[3U] = t4;
  out[4U] = t5;
  out[5U] = t6;
  out[6U] = t7;
  out[7U] = (u64)0U;
}

static void uploadZeroImpl(u64 *f)
{
  f[0U] = (u64)0U;
  f[1U] = (u64)0U;
  f[2U] = (u64)0U;
  f[3U] = (u64)0U;
}

static void uploadOneImpl(u64 *f)
{
  f[0U] = (u64)1U;
  f[1U] = (u64)0U;
  f[2U] = (u64)0U;
  f[3U] = (u64)0U;
}

static void toUint8(u64 *i, u8 *o)
{
  u32 i0;
  for (i0 = (u32)0U; i0 < (u32)4U; i0++)
    store64_be(o + i0 * (u32)8U, i[i0]);
}

static void changeEndian(u64 *i)
{
  u64 zero = i[0U];
  u64 one = i[1U];
  u64 two = i[2U];
  u64 three = i[3U];
  i[0U] = three;
  i[1U] = two;
  i[2U] = one;
  i[3U] = zero;
}

static void toUint64ChangeEndian(u8 *i, u64 *o)
{
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < (u32)4U; i0++)
    {
      u64 *os = o;
      u8 *bj = i + i0 * (u32)8U;
      u64 u = load64_be(bj);
      u64 r = u;
      u64 x = r;
      os[i0] = x;
    }
  }
  changeEndian(o);
}

static const
u64
prime256_buffer[4U] =
  { (u64)0xffffffffffffffffU, (u64)0xffffffffU, (u64)0U, (u64)0xffffffff00000001U };

static void reduction_prime_2prime_impl(u64 *x, u64 *result)
{
  u64 tempBuffer[4U] = { 0U };
  u64 c = sub4_il(x, prime256_buffer, tempBuffer);
  cmovznz4(c, tempBuffer, x, result);
}

static void p256_add(u64 *arg1, u64 *arg2, u64 *out)
{
  u64 t = add4(arg1, arg2, out);
  u64 tempBuffer[4U] = { 0U };
  u64 tempBufferForSubborrow = (u64)0U;
  u64 c = sub4_il(out, prime256_buffer, tempBuffer);
  u64 carry = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t, (u64)0U, &tempBufferForSubborrow);
  cmovznz4(carry, tempBuffer, out, out);
}

static void p256_double(u64 *arg1, u64 *out)
{
  u64 t = add4(arg1, arg1, out);
  u64 tempBuffer[4U] = { 0U };
  u64 tempBufferForSubborrow = (u64)0U;
  u64 c = sub4_il(out, prime256_buffer, tempBuffer);
  u64 carry = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t, (u64)0U, &tempBufferForSubborrow);
  cmovznz4(carry, tempBuffer, out, out);
}

static void p256_sub(u64 *arg1, u64 *arg2, u64 *out)
{
  u64 t = sub4(arg1, arg2, out);
  u64 t0 = (u64)0U - t;
  u64 t1 = ((u64)0U - t) >> (u32)32U;
  u64 t2 = (u64)0U;
  u64 t3 = t - (t << (u32)32U);
  u64 c = add4_variables(out, (u64)0U, t0, t1, t2, t3, out);
}

static void montgomery_multiplication_buffer_by_one(u64 *a, u64 *result)
{
  u64 t[8U] = { 0U };
  u64 *t_low = t;
  u64 round2[8U] = { 0U };
  u64 round4[8U] = { 0U };
  memcpy(t_low, a, (u32)4U * sizeof (u64));
  {
    u64 tempRound[8U] = { 0U };
    u64 t20[8U] = { 0U };
    u64 t30[8U] = { 0U };
    u64 t10 = t[0U];
    u64 *result040 = t20;
    u64 temp1 = (u64)0U;
    u64 f10 = prime256_buffer[1U];
    u64 f20 = prime256_buffer[2U];
    u64 f30 = prime256_buffer[3U];
    u64 *o00 = result040;
    u64 *o10 = result040 + (u32)1U;
    u64 *o20 = result040 + (u32)2U;
    u64 *o30 = result040 + (u32)3U;
    u64 f010 = prime256_buffer[0U];
    u64 h0;
    u64 l0;
    u64 c10;
    u64 h1;
    u64 l1;
    u64 c20;
    u64 h2;
    u64 l2;
    u64 c30;
    u64 temp00;
    u64 c0;
    u64 uu____0;
    mul64(f010, t10, o00, &temp1);
    h0 = temp1;
    mul64(f10, t10, o10, &temp1);
    l0 = o10[0U];
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l0, h0, o10);
    h1 = temp1;
    mul64(f20, t10, o20, &temp1);
    l1 = o20[0U];
    c20 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, l1, h1, o20);
    h2 = temp1;
    mul64(f30, t10, o30, &temp1);
    l2 = o30[0U];
    c30 = Lib_IntTypes_Intrinsics_add_carry_u64(c20, l2, h2, o30);
    temp00 = temp1;
    c0 = c30 + temp00;
    t20[4U] = c0;
    uu____0 = add8(t, t20, t30);
    shift8(t30, tempRound);
    {
      u64 t21[8U] = { 0U };
      u64 t31[8U] = { 0U };
      u64 t11 = tempRound[0U];
      u64 *result041 = t21;
      u64 temp2 = (u64)0U;
      u64 f11 = prime256_buffer[1U];
      u64 f21 = prime256_buffer[2U];
      u64 f31 = prime256_buffer[3U];
      u64 *o01 = result041;
      u64 *o11 = result041 + (u32)1U;
      u64 *o21 = result041 + (u32)2U;
      u64 *o31 = result041 + (u32)3U;
      u64 f011 = prime256_buffer[0U];
      u64 h3;
      u64 l3;
      u64 c11;
      u64 h4;
      u64 l4;
      u64 c21;
      u64 h5;
      u64 l5;
      u64 c31;
      u64 temp01;
      u64 c4;
      u64 uu____1;
      mul64(f011, t11, o01, &temp2);
      h3 = temp2;
      mul64(f11, t11, o11, &temp2);
      l3 = o11[0U];
      c11 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l3, h3, o11);
      h4 = temp2;
      mul64(f21, t11, o21, &temp2);
      l4 = o21[0U];
      c21 = Lib_IntTypes_Intrinsics_add_carry_u64(c11, l4, h4, o21);
      h5 = temp2;
      mul64(f31, t11, o31, &temp2);
      l5 = o31[0U];
      c31 = Lib_IntTypes_Intrinsics_add_carry_u64(c21, l5, h5, o31);
      temp01 = temp2;
      c4 = c31 + temp01;
      t21[4U] = c4;
      uu____1 = add8(tempRound, t21, t31);
      shift8(t31, round2);
      {
        u64 tempRound0[8U] = { 0U };
        u64 t2[8U] = { 0U };
        u64 t32[8U] = { 0U };
        u64 t12 = round2[0U];
        u64 *result042 = t2;
        u64 temp3 = (u64)0U;
        u64 f12 = prime256_buffer[1U];
        u64 f22 = prime256_buffer[2U];
        u64 f32 = prime256_buffer[3U];
        u64 *o02 = result042;
        u64 *o12 = result042 + (u32)1U;
        u64 *o22 = result042 + (u32)2U;
        u64 *o32 = result042 + (u32)3U;
        u64 f012 = prime256_buffer[0U];
        u64 h6;
        u64 l6;
        u64 c12;
        u64 h7;
        u64 l7;
        u64 c22;
        u64 h8;
        u64 l8;
        u64 c32;
        u64 temp02;
        u64 c5;
        u64 uu____2;
        mul64(f012, t12, o02, &temp3);
        h6 = temp3;
        mul64(f12, t12, o12, &temp3);
        l6 = o12[0U];
        c12 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l6, h6, o12);
        h7 = temp3;
        mul64(f22, t12, o22, &temp3);
        l7 = o22[0U];
        c22 = Lib_IntTypes_Intrinsics_add_carry_u64(c12, l7, h7, o22);
        h8 = temp3;
        mul64(f32, t12, o32, &temp3);
        l8 = o32[0U];
        c32 = Lib_IntTypes_Intrinsics_add_carry_u64(c22, l8, h8, o32);
        temp02 = temp3;
        c5 = c32 + temp02;
        t2[4U] = c5;
        uu____2 = add8(round2, t2, t32);
        shift8(t32, tempRound0);
        {
          u64 t22[8U] = { 0U };
          u64 t3[8U] = { 0U };
          u64 t1 = tempRound0[0U];
          u64 *result04 = t22;
          u64 temp = (u64)0U;
          u64 f1 = prime256_buffer[1U];
          u64 f2 = prime256_buffer[2U];
          u64 f3 = prime256_buffer[3U];
          u64 *o0 = result04;
          u64 *o1 = result04 + (u32)1U;
          u64 *o2 = result04 + (u32)2U;
          u64 *o3 = result04 + (u32)3U;
          u64 f01 = prime256_buffer[0U];
          u64 h9;
          u64 l9;
          u64 c1;
          u64 h10;
          u64 l10;
          u64 c2;
          u64 h;
          u64 l;
          u64 c3;
          u64 temp0;
          u64 c6;
          u64 uu____3;
          mul64(f01, t1, o0, &temp);
          h9 = temp;
          mul64(f1, t1, o1, &temp);
          l9 = o1[0U];
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l9, h9, o1);
          h10 = temp;
          mul64(f2, t1, o2, &temp);
          l10 = o2[0U];
          c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l10, h10, o2);
          h = temp;
          mul64(f3, t1, o3, &temp);
          l = o3[0U];
          c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l, h, o3);
          temp0 = temp;
          c6 = c3 + temp0;
          t22[4U] = c6;
          uu____3 = add8(tempRound0, t22, t3);
          shift8(t3, round4);
          {
            u64 tempBuffer[4U] = { 0U };
            u64 tempBufferForSubborrow = (u64)0U;
            u64 cin = round4[4U];
            u64 *x_ = round4;
            u64 c = sub4_il(x_, prime256_buffer, tempBuffer);
            u64
            carry = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, cin, (u64)0U, &tempBufferForSubborrow);
            cmovznz4(carry, tempBuffer, x_, result);
          }
        }
      }
    }
  }
}

static void montgomery_multiplication_buffer(u64 *a, u64 *b, u64 *result)
{
  u64 t[8U] = { 0U };
  u64 round2[8U] = { 0U };
  u64 round4[8U] = { 0U };
  u64 f0 = a[0U];
  u64 f10 = a[1U];
  u64 f20 = a[2U];
  u64 f30 = a[3U];
  u64 *b0 = t;
  u64 temp2 = (u64)0U;
  u64 f110 = b[1U];
  u64 f210 = b[2U];
  u64 f310 = b[3U];
  u64 *o00 = b0;
  u64 *o10 = b0 + (u32)1U;
  u64 *o20 = b0 + (u32)2U;
  u64 *o30 = b0 + (u32)3U;
  u64 f020 = b[0U];
  u64 h0;
  u64 l0;
  u64 c10;
  u64 h1;
  u64 l1;
  u64 c20;
  u64 h2;
  u64 l2;
  u64 c30;
  u64 temp00;
  u64 c0;
  u64 *b1;
  mul64(f020, f0, o00, &temp2);
  h0 = temp2;
  mul64(f110, f0, o10, &temp2);
  l0 = o10[0U];
  c10 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l0, h0, o10);
  h1 = temp2;
  mul64(f210, f0, o20, &temp2);
  l1 = o20[0U];
  c20 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, l1, h1, o20);
  h2 = temp2;
  mul64(f310, f0, o30, &temp2);
  l2 = o30[0U];
  c30 = Lib_IntTypes_Intrinsics_add_carry_u64(c20, l2, h2, o30);
  temp00 = temp2;
  c0 = c30 + temp00;
  t[4U] = c0;
  b1 = t + (u32)1U;
  {
    u64 temp3[4U] = { 0U };
    u64 temp10 = (u64)0U;
    u64 f111 = b[1U];
    u64 f211 = b[2U];
    u64 f311 = b[3U];
    u64 *o01 = temp3;
    u64 *o11 = temp3 + (u32)1U;
    u64 *o21 = temp3 + (u32)2U;
    u64 *o31 = temp3 + (u32)3U;
    u64 f021 = b[0U];
    u64 h3;
    u64 l3;
    u64 c12;
    u64 h4;
    u64 l4;
    u64 c22;
    u64 h5;
    u64 l5;
    u64 c31;
    u64 temp01;
    u64 c4;
    u64 c32;
    u64 c13;
    u64 *b2;
    mul64(f021, f10, o01, &temp10);
    h3 = temp10;
    mul64(f111, f10, o11, &temp10);
    l3 = o11[0U];
    c12 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l3, h3, o11);
    h4 = temp10;
    mul64(f211, f10, o21, &temp10);
    l4 = o21[0U];
    c22 = Lib_IntTypes_Intrinsics_add_carry_u64(c12, l4, h4, o21);
    h5 = temp10;
    mul64(f311, f10, o31, &temp10);
    l5 = o31[0U];
    c31 = Lib_IntTypes_Intrinsics_add_carry_u64(c22, l5, h5, o31);
    temp01 = temp10;
    c4 = c31 + temp01;
    c32 = add4(temp3, b1, b1);
    c13 = c4 + c32;
    t[5U] = c13;
    b2 = t + (u32)2U;
    {
      u64 temp4[4U] = { 0U };
      u64 temp11 = (u64)0U;
      u64 f112 = b[1U];
      u64 f212 = b[2U];
      u64 f312 = b[3U];
      u64 *o02 = temp4;
      u64 *o12 = temp4 + (u32)1U;
      u64 *o22 = temp4 + (u32)2U;
      u64 *o32 = temp4 + (u32)3U;
      u64 f022 = b[0U];
      u64 h6;
      u64 l6;
      u64 c110;
      u64 h7;
      u64 l7;
      u64 c23;
      u64 h8;
      u64 l8;
      u64 c33;
      u64 temp02;
      u64 c5;
      u64 c34;
      u64 c24;
      u64 *b3;
      mul64(f022, f20, o02, &temp11);
      h6 = temp11;
      mul64(f112, f20, o12, &temp11);
      l6 = o12[0U];
      c110 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l6, h6, o12);
      h7 = temp11;
      mul64(f212, f20, o22, &temp11);
      l7 = o22[0U];
      c23 = Lib_IntTypes_Intrinsics_add_carry_u64(c110, l7, h7, o22);
      h8 = temp11;
      mul64(f312, f20, o32, &temp11);
      l8 = o32[0U];
      c33 = Lib_IntTypes_Intrinsics_add_carry_u64(c23, l8, h8, o32);
      temp02 = temp11;
      c5 = c33 + temp02;
      c34 = add4(temp4, b2, b2);
      c24 = c5 + c34;
      t[6U] = c24;
      b3 = t + (u32)3U;
      {
        u64 temp5[4U] = { 0U };
        u64 temp1 = (u64)0U;
        u64 f11 = b[1U];
        u64 f21 = b[2U];
        u64 f31 = b[3U];
        u64 *o03 = temp5;
        u64 *o13 = temp5 + (u32)1U;
        u64 *o23 = temp5 + (u32)2U;
        u64 *o33 = temp5 + (u32)3U;
        u64 f02 = b[0U];
        u64 h9;
        u64 l9;
        u64 c11;
        u64 h10;
        u64 l10;
        u64 c21;
        u64 h11;
        u64 l11;
        u64 c35;
        u64 temp03;
        u64 c6;
        u64 c36;
        u64 c37;
        mul64(f02, f30, o03, &temp1);
        h9 = temp1;
        mul64(f11, f30, o13, &temp1);
        l9 = o13[0U];
        c11 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l9, h9, o13);
        h10 = temp1;
        mul64(f21, f30, o23, &temp1);
        l10 = o23[0U];
        c21 = Lib_IntTypes_Intrinsics_add_carry_u64(c11, l10, h10, o23);
        h11 = temp1;
        mul64(f31, f30, o33, &temp1);
        l11 = o33[0U];
        c35 = Lib_IntTypes_Intrinsics_add_carry_u64(c21, l11, h11, o33);
        temp03 = temp1;
        c6 = c35 + temp03;
        c36 = add4(temp5, b3, b3);
        c37 = c6 + c36;
        t[7U] = c37;
        {
          u64 tempRound[8U] = { 0U };
          u64 t20[8U] = { 0U };
          u64 t30[8U] = { 0U };
          u64 t10 = t[0U];
          u64 *result040 = t20;
          u64 temp6 = (u64)0U;
          u64 f12 = prime256_buffer[1U];
          u64 f22 = prime256_buffer[2U];
          u64 f32 = prime256_buffer[3U];
          u64 *o04 = result040;
          u64 *o14 = result040 + (u32)1U;
          u64 *o24 = result040 + (u32)2U;
          u64 *o34 = result040 + (u32)3U;
          u64 f010 = prime256_buffer[0U];
          u64 h12;
          u64 l12;
          u64 c14;
          u64 h13;
          u64 l13;
          u64 c25;
          u64 h14;
          u64 l14;
          u64 c38;
          u64 temp04;
          u64 c7;
          u64 uu____0;
          mul64(f010, t10, o04, &temp6);
          h12 = temp6;
          mul64(f12, t10, o14, &temp6);
          l12 = o14[0U];
          c14 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l12, h12, o14);
          h13 = temp6;
          mul64(f22, t10, o24, &temp6);
          l13 = o24[0U];
          c25 = Lib_IntTypes_Intrinsics_add_carry_u64(c14, l13, h13, o24);
          h14 = temp6;
          mul64(f32, t10, o34, &temp6);
          l14 = o34[0U];
          c38 = Lib_IntTypes_Intrinsics_add_carry_u64(c25, l14, h14, o34);
          temp04 = temp6;
          c7 = c38 + temp04;
          t20[4U] = c7;
          uu____0 = add8(t, t20, t30);
          shift8(t30, tempRound);
          {
            u64 t21[8U] = { 0U };
            u64 t31[8U] = { 0U };
            u64 t11 = tempRound[0U];
            u64 *result041 = t21;
            u64 temp7 = (u64)0U;
            u64 f13 = prime256_buffer[1U];
            u64 f23 = prime256_buffer[2U];
            u64 f33 = prime256_buffer[3U];
            u64 *o05 = result041;
            u64 *o15 = result041 + (u32)1U;
            u64 *o25 = result041 + (u32)2U;
            u64 *o35 = result041 + (u32)3U;
            u64 f011 = prime256_buffer[0U];
            u64 h15;
            u64 l15;
            u64 c15;
            u64 h16;
            u64 l16;
            u64 c26;
            u64 h17;
            u64 l17;
            u64 c39;
            u64 temp05;
            u64 c8;
            u64 uu____1;
            mul64(f011, t11, o05, &temp7);
            h15 = temp7;
            mul64(f13, t11, o15, &temp7);
            l15 = o15[0U];
            c15 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l15, h15, o15);
            h16 = temp7;
            mul64(f23, t11, o25, &temp7);
            l16 = o25[0U];
            c26 = Lib_IntTypes_Intrinsics_add_carry_u64(c15, l16, h16, o25);
            h17 = temp7;
            mul64(f33, t11, o35, &temp7);
            l17 = o35[0U];
            c39 = Lib_IntTypes_Intrinsics_add_carry_u64(c26, l17, h17, o35);
            temp05 = temp7;
            c8 = c39 + temp05;
            t21[4U] = c8;
            uu____1 = add8(tempRound, t21, t31);
            shift8(t31, round2);
            {
              u64 tempRound0[8U] = { 0U };
              u64 t2[8U] = { 0U };
              u64 t32[8U] = { 0U };
              u64 t12 = round2[0U];
              u64 *result042 = t2;
              u64 temp8 = (u64)0U;
              u64 f14 = prime256_buffer[1U];
              u64 f24 = prime256_buffer[2U];
              u64 f34 = prime256_buffer[3U];
              u64 *o06 = result042;
              u64 *o16 = result042 + (u32)1U;
              u64 *o26 = result042 + (u32)2U;
              u64 *o36 = result042 + (u32)3U;
              u64 f012 = prime256_buffer[0U];
              u64 h18;
              u64 l18;
              u64 c16;
              u64 h19;
              u64 l19;
              u64 c27;
              u64 h20;
              u64 l20;
              u64 c310;
              u64 temp06;
              u64 c9;
              u64 uu____2;
              mul64(f012, t12, o06, &temp8);
              h18 = temp8;
              mul64(f14, t12, o16, &temp8);
              l18 = o16[0U];
              c16 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l18, h18, o16);
              h19 = temp8;
              mul64(f24, t12, o26, &temp8);
              l19 = o26[0U];
              c27 = Lib_IntTypes_Intrinsics_add_carry_u64(c16, l19, h19, o26);
              h20 = temp8;
              mul64(f34, t12, o36, &temp8);
              l20 = o36[0U];
              c310 = Lib_IntTypes_Intrinsics_add_carry_u64(c27, l20, h20, o36);
              temp06 = temp8;
              c9 = c310 + temp06;
              t2[4U] = c9;
              uu____2 = add8(round2, t2, t32);
              shift8(t32, tempRound0);
              {
                u64 t22[8U] = { 0U };
                u64 t3[8U] = { 0U };
                u64 t1 = tempRound0[0U];
                u64 *result04 = t22;
                u64 temp = (u64)0U;
                u64 f1 = prime256_buffer[1U];
                u64 f2 = prime256_buffer[2U];
                u64 f3 = prime256_buffer[3U];
                u64 *o0 = result04;
                u64 *o1 = result04 + (u32)1U;
                u64 *o2 = result04 + (u32)2U;
                u64 *o3 = result04 + (u32)3U;
                u64 f01 = prime256_buffer[0U];
                u64 h21;
                u64 l21;
                u64 c1;
                u64 h22;
                u64 l22;
                u64 c2;
                u64 h;
                u64 l;
                u64 c3;
                u64 temp0;
                u64 c17;
                u64 uu____3;
                mul64(f01, t1, o0, &temp);
                h21 = temp;
                mul64(f1, t1, o1, &temp);
                l21 = o1[0U];
                c1 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l21, h21, o1);
                h22 = temp;
                mul64(f2, t1, o2, &temp);
                l22 = o2[0U];
                c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l22, h22, o2);
                h = temp;
                mul64(f3, t1, o3, &temp);
                l = o3[0U];
                c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l, h, o3);
                temp0 = temp;
                c17 = c3 + temp0;
                t22[4U] = c17;
                uu____3 = add8(tempRound0, t22, t3);
                shift8(t3, round4);
                {
                  u64 tempBuffer[4U] = { 0U };
                  u64 tempBufferForSubborrow = (u64)0U;
                  u64 cin = round4[4U];
                  u64 *x_ = round4;
                  u64 c = sub4_il(x_, prime256_buffer, tempBuffer);
                  u64
                  carry =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
                      cin,
                      (u64)0U,
                      &tempBufferForSubborrow);
                  cmovznz4(carry, tempBuffer, x_, result);
                }
              }
            }
          }
        }
      }
    }
  }
}

static void montgomery_square_buffer(u64 *a, u64 *result)
{
  u64 t[8U] = { 0U };
  u64 round2[8U] = { 0U };
  u64 round4[8U] = { 0U };
  sq(a, t);
  {
    u64 tempRound[8U] = { 0U };
    u64 t20[8U] = { 0U };
    u64 t30[8U] = { 0U };
    u64 t10 = t[0U];
    u64 *result040 = t20;
    u64 temp1 = (u64)0U;
    u64 f10 = prime256_buffer[1U];
    u64 f20 = prime256_buffer[2U];
    u64 f30 = prime256_buffer[3U];
    u64 *o00 = result040;
    u64 *o10 = result040 + (u32)1U;
    u64 *o20 = result040 + (u32)2U;
    u64 *o30 = result040 + (u32)3U;
    u64 f010 = prime256_buffer[0U];
    u64 h0;
    u64 l0;
    u64 c10;
    u64 h1;
    u64 l1;
    u64 c20;
    u64 h2;
    u64 l2;
    u64 c30;
    u64 temp00;
    u64 c0;
    u64 uu____0;
    mul64(f010, t10, o00, &temp1);
    h0 = temp1;
    mul64(f10, t10, o10, &temp1);
    l0 = o10[0U];
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l0, h0, o10);
    h1 = temp1;
    mul64(f20, t10, o20, &temp1);
    l1 = o20[0U];
    c20 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, l1, h1, o20);
    h2 = temp1;
    mul64(f30, t10, o30, &temp1);
    l2 = o30[0U];
    c30 = Lib_IntTypes_Intrinsics_add_carry_u64(c20, l2, h2, o30);
    temp00 = temp1;
    c0 = c30 + temp00;
    t20[4U] = c0;
    uu____0 = add8(t, t20, t30);
    shift8(t30, tempRound);
    {
      u64 t21[8U] = { 0U };
      u64 t31[8U] = { 0U };
      u64 t11 = tempRound[0U];
      u64 *result041 = t21;
      u64 temp2 = (u64)0U;
      u64 f11 = prime256_buffer[1U];
      u64 f21 = prime256_buffer[2U];
      u64 f31 = prime256_buffer[3U];
      u64 *o01 = result041;
      u64 *o11 = result041 + (u32)1U;
      u64 *o21 = result041 + (u32)2U;
      u64 *o31 = result041 + (u32)3U;
      u64 f011 = prime256_buffer[0U];
      u64 h3;
      u64 l3;
      u64 c11;
      u64 h4;
      u64 l4;
      u64 c21;
      u64 h5;
      u64 l5;
      u64 c31;
      u64 temp01;
      u64 c4;
      u64 uu____1;
      mul64(f011, t11, o01, &temp2);
      h3 = temp2;
      mul64(f11, t11, o11, &temp2);
      l3 = o11[0U];
      c11 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l3, h3, o11);
      h4 = temp2;
      mul64(f21, t11, o21, &temp2);
      l4 = o21[0U];
      c21 = Lib_IntTypes_Intrinsics_add_carry_u64(c11, l4, h4, o21);
      h5 = temp2;
      mul64(f31, t11, o31, &temp2);
      l5 = o31[0U];
      c31 = Lib_IntTypes_Intrinsics_add_carry_u64(c21, l5, h5, o31);
      temp01 = temp2;
      c4 = c31 + temp01;
      t21[4U] = c4;
      uu____1 = add8(tempRound, t21, t31);
      shift8(t31, round2);
      {
        u64 tempRound0[8U] = { 0U };
        u64 t2[8U] = { 0U };
        u64 t32[8U] = { 0U };
        u64 t12 = round2[0U];
        u64 *result042 = t2;
        u64 temp3 = (u64)0U;
        u64 f12 = prime256_buffer[1U];
        u64 f22 = prime256_buffer[2U];
        u64 f32 = prime256_buffer[3U];
        u64 *o02 = result042;
        u64 *o12 = result042 + (u32)1U;
        u64 *o22 = result042 + (u32)2U;
        u64 *o32 = result042 + (u32)3U;
        u64 f012 = prime256_buffer[0U];
        u64 h6;
        u64 l6;
        u64 c12;
        u64 h7;
        u64 l7;
        u64 c22;
        u64 h8;
        u64 l8;
        u64 c32;
        u64 temp02;
        u64 c5;
        u64 uu____2;
        mul64(f012, t12, o02, &temp3);
        h6 = temp3;
        mul64(f12, t12, o12, &temp3);
        l6 = o12[0U];
        c12 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l6, h6, o12);
        h7 = temp3;
        mul64(f22, t12, o22, &temp3);
        l7 = o22[0U];
        c22 = Lib_IntTypes_Intrinsics_add_carry_u64(c12, l7, h7, o22);
        h8 = temp3;
        mul64(f32, t12, o32, &temp3);
        l8 = o32[0U];
        c32 = Lib_IntTypes_Intrinsics_add_carry_u64(c22, l8, h8, o32);
        temp02 = temp3;
        c5 = c32 + temp02;
        t2[4U] = c5;
        uu____2 = add8(round2, t2, t32);
        shift8(t32, tempRound0);
        {
          u64 t22[8U] = { 0U };
          u64 t3[8U] = { 0U };
          u64 t1 = tempRound0[0U];
          u64 *result04 = t22;
          u64 temp = (u64)0U;
          u64 f1 = prime256_buffer[1U];
          u64 f2 = prime256_buffer[2U];
          u64 f3 = prime256_buffer[3U];
          u64 *o0 = result04;
          u64 *o1 = result04 + (u32)1U;
          u64 *o2 = result04 + (u32)2U;
          u64 *o3 = result04 + (u32)3U;
          u64 f01 = prime256_buffer[0U];
          u64 h9;
          u64 l9;
          u64 c1;
          u64 h10;
          u64 l10;
          u64 c2;
          u64 h;
          u64 l;
          u64 c3;
          u64 temp0;
          u64 c6;
          u64 uu____3;
          mul64(f01, t1, o0, &temp);
          h9 = temp;
          mul64(f1, t1, o1, &temp);
          l9 = o1[0U];
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l9, h9, o1);
          h10 = temp;
          mul64(f2, t1, o2, &temp);
          l10 = o2[0U];
          c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l10, h10, o2);
          h = temp;
          mul64(f3, t1, o3, &temp);
          l = o3[0U];
          c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l, h, o3);
          temp0 = temp;
          c6 = c3 + temp0;
          t22[4U] = c6;
          uu____3 = add8(tempRound0, t22, t3);
          shift8(t3, round4);
          {
            u64 tempBuffer[4U] = { 0U };
            u64 tempBufferForSubborrow = (u64)0U;
            u64 cin = round4[4U];
            u64 *x_ = round4;
            u64 c = sub4_il(x_, prime256_buffer, tempBuffer);
            u64
            carry = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, cin, (u64)0U, &tempBufferForSubborrow);
            cmovznz4(carry, tempBuffer, x_, result);
          }
        }
      }
    }
  }
}

static void fsquarePowN(u32 n, u64 *a)
{
  u32 i;
  for (i = (u32)0U; i < n; i++)
    montgomery_square_buffer(a, a);
}

static void fsquarePowNminusOne(u32 n, u64 *a, u64 *b)
{
  u32 i;
  b[0U] = (u64)1U;
  b[1U] = (u64)18446744069414584320U;
  b[2U] = (u64)18446744073709551615U;
  b[3U] = (u64)4294967294U;
  for (i = (u32)0U; i < n; i++)
  {
    montgomery_multiplication_buffer(b, a, b);
    montgomery_square_buffer(a, a);
  }
}

static void exponent(u64 *a, u64 *result, u64 *tempBuffer)
{
  u64 *buffer_norm_1 = tempBuffer;
  u64 *buffer_result1 = tempBuffer + (u32)4U;
  u64 *buffer_result2 = tempBuffer + (u32)8U;
  u64 *buffer_norm_3 = tempBuffer + (u32)12U;
  u64 *buffer_result3 = tempBuffer + (u32)16U;
  u64 *buffer_a0;
  u64 *buffer_b0;
  u64 *buffer_a;
  u64 *buffer_b;
  memcpy(buffer_norm_1, a, (u32)4U * sizeof (u64));
  buffer_a0 = buffer_norm_1;
  buffer_b0 = buffer_norm_1 + (u32)4U;
  fsquarePowNminusOne((u32)32U, buffer_a0, buffer_b0);
  fsquarePowN((u32)224U, buffer_b0);
  memcpy(buffer_result2, a, (u32)4U * sizeof (u64));
  fsquarePowN((u32)192U, buffer_result2);
  memcpy(buffer_norm_3, a, (u32)4U * sizeof (u64));
  buffer_a = buffer_norm_3;
  buffer_b = buffer_norm_3 + (u32)4U;
  fsquarePowNminusOne((u32)94U, buffer_a, buffer_b);
  fsquarePowN((u32)2U, buffer_b);
  montgomery_multiplication_buffer(buffer_result1, buffer_result2, buffer_result1);
  montgomery_multiplication_buffer(buffer_result1, buffer_result3, buffer_result1);
  montgomery_multiplication_buffer(buffer_result1, a, buffer_result1);
  memcpy(result, buffer_result1, (u32)4U * sizeof (u64));
}

static void cube(u64 *a, u64 *result)
{
  montgomery_square_buffer(a, result);
  montgomery_multiplication_buffer(result, a, result);
}

static void multByTwo(u64 *a, u64 *out)
{
  p256_add(a, a, out);
}

static void multByThree(u64 *a, u64 *result)
{
  multByTwo(a, result);
  p256_add(a, result, result);
}

static void multByFour(u64 *a, u64 *result)
{
  multByTwo(a, result);
  multByTwo(result, result);
}

static void multByEight(u64 *a, u64 *result)
{
  multByTwo(a, result);
  multByTwo(result, result);
  multByTwo(result, result);
}

static u64 store_high_low_u(u32 high, u32 low)
{
  u64 as_uint64_high = (u64)high;
  u64 as_uint64_high1 = as_uint64_high << (u32)32U;
  u64 as_uint64_low = (u64)low;
  return as_uint64_low ^ as_uint64_high1;
}

static void solinas_reduction_impl(u64 *i, u64 *o)
{
  u64 tempBuffer[36U] = { 0U };
  u64 i0 = i[0U];
  u64 i1 = i[1U];
  u64 i2 = i[2U];
  u64 i3 = i[3U];
  u64 i4 = i[4U];
  u64 i5 = i[5U];
  u64 i6 = i[6U];
  u64 i7 = i[7U];
  u32 c0 = (u32)i0;
  u32 c1 = (u32)(i0 >> (u32)32U);
  u32 c2 = (u32)i1;
  u32 c3 = (u32)(i1 >> (u32)32U);
  u32 c4 = (u32)i2;
  u32 c5 = (u32)(i2 >> (u32)32U);
  u32 c6 = (u32)i3;
  u32 c7 = (u32)(i3 >> (u32)32U);
  u32 c8 = (u32)i4;
  u32 c9 = (u32)(i4 >> (u32)32U);
  u32 c10 = (u32)i5;
  u32 c11 = (u32)(i5 >> (u32)32U);
  u32 c12 = (u32)i6;
  u32 c13 = (u32)(i6 >> (u32)32U);
  u32 c14 = (u32)i7;
  u32 c15 = (u32)(i7 >> (u32)32U);
  u64 *t010 = tempBuffer;
  u64 *t110 = tempBuffer + (u32)4U;
  u64 *t210 = tempBuffer + (u32)8U;
  u64 *t310 = tempBuffer + (u32)12U;
  u64 *t410 = tempBuffer + (u32)16U;
  u64 *t510 = tempBuffer + (u32)20U;
  u64 *t610 = tempBuffer + (u32)24U;
  u64 *t710 = tempBuffer + (u32)28U;
  u64 *t810 = tempBuffer + (u32)32U;
  u64 b00 = store_high_low_u(c1, c0);
  u64 b10 = store_high_low_u(c3, c2);
  u64 b20 = store_high_low_u(c5, c4);
  u64 b30 = store_high_low_u(c7, c6);
  u64 b01;
  u64 b11;
  u64 b21;
  u64 b31;
  u64 b02;
  u64 b12;
  u64 b22;
  u64 b32;
  u64 b03;
  u64 b13;
  u64 b23;
  u64 b33;
  u64 b04;
  u64 b14;
  u64 b24;
  u64 b34;
  u64 b05;
  u64 b15;
  u64 b25;
  u64 b35;
  u64 b06;
  u64 b16;
  u64 b26;
  u64 b36;
  u64 b07;
  u64 b17;
  u64 b27;
  u64 b37;
  u64 b0;
  u64 b1;
  u64 b2;
  u64 b3;
  u64 *t01;
  u64 *t11;
  u64 *t21;
  u64 *t31;
  u64 *t41;
  u64 *t51;
  u64 *t61;
  u64 *t71;
  u64 *t81;
  t010[0U] = b00;
  t010[1U] = b10;
  t010[2U] = b20;
  t010[3U] = b30;
  reduction_prime_2prime_impl(t010, t010);
  b01 = (u64)0U;
  b11 = store_high_low_u(c11, (u32)0U);
  b21 = store_high_low_u(c13, c12);
  b31 = store_high_low_u(c15, c14);
  t110[0U] = b01;
  t110[1U] = b11;
  t110[2U] = b21;
  t110[3U] = b31;
  reduction_prime_2prime_impl(t110, t110);
  b02 = (u64)0U;
  b12 = store_high_low_u(c12, (u32)0U);
  b22 = store_high_low_u(c14, c13);
  b32 = store_high_low_u((u32)0U, c15);
  t210[0U] = b02;
  t210[1U] = b12;
  t210[2U] = b22;
  t210[3U] = b32;
  b03 = store_high_low_u(c9, c8);
  b13 = store_high_low_u((u32)0U, c10);
  b23 = (u64)0U;
  b33 = store_high_low_u(c15, c14);
  t310[0U] = b03;
  t310[1U] = b13;
  t310[2U] = b23;
  t310[3U] = b33;
  reduction_prime_2prime_impl(t310, t310);
  b04 = store_high_low_u(c10, c9);
  b14 = store_high_low_u(c13, c11);
  b24 = store_high_low_u(c15, c14);
  b34 = store_high_low_u(c8, c13);
  t410[0U] = b04;
  t410[1U] = b14;
  t410[2U] = b24;
  t410[3U] = b34;
  reduction_prime_2prime_impl(t410, t410);
  b05 = store_high_low_u(c12, c11);
  b15 = store_high_low_u((u32)0U, c13);
  b25 = (u64)0U;
  b35 = store_high_low_u(c10, c8);
  t510[0U] = b05;
  t510[1U] = b15;
  t510[2U] = b25;
  t510[3U] = b35;
  reduction_prime_2prime_impl(t510, t510);
  b06 = store_high_low_u(c13, c12);
  b16 = store_high_low_u(c15, c14);
  b26 = (u64)0U;
  b36 = store_high_low_u(c11, c9);
  t610[0U] = b06;
  t610[1U] = b16;
  t610[2U] = b26;
  t610[3U] = b36;
  reduction_prime_2prime_impl(t610, t610);
  b07 = store_high_low_u(c14, c13);
  b17 = store_high_low_u(c8, c15);
  b27 = store_high_low_u(c10, c9);
  b37 = store_high_low_u(c12, (u32)0U);
  t710[0U] = b07;
  t710[1U] = b17;
  t710[2U] = b27;
  t710[3U] = b37;
  reduction_prime_2prime_impl(t710, t710);
  b0 = store_high_low_u(c15, c14);
  b1 = store_high_low_u(c9, (u32)0U);
  b2 = store_high_low_u(c11, c10);
  b3 = store_high_low_u(c13, (u32)0U);
  t810[0U] = b0;
  t810[1U] = b1;
  t810[2U] = b2;
  t810[3U] = b3;
  reduction_prime_2prime_impl(t810, t810);
  t01 = tempBuffer;
  t11 = tempBuffer + (u32)4U;
  t21 = tempBuffer + (u32)8U;
  t31 = tempBuffer + (u32)12U;
  t41 = tempBuffer + (u32)16U;
  t51 = tempBuffer + (u32)20U;
  t61 = tempBuffer + (u32)24U;
  t71 = tempBuffer + (u32)28U;
  t81 = tempBuffer + (u32)32U;
  p256_double(t21, t21);
  p256_double(t11, t11);
  p256_add(t01, t11, o);
  p256_add(t21, o, o);
  p256_add(t31, o, o);
  p256_add(t41, o, o);
  p256_sub(o, t51, o);
  p256_sub(o, t61, o);
  p256_sub(o, t71, o);
  p256_sub(o, t81, o);
}

static void
point_double_a_b_g(u64 *p, u64 *alpha, u64 *beta, u64 *gamma, u64 *delta, u64 *tempBuffer)
{
  u64 *pX = p;
  u64 *pY = p + (u32)4U;
  u64 *pZ = p + (u32)8U;
  u64 *a0 = tempBuffer;
  u64 *a1 = tempBuffer + (u32)4U;
  u64 *alpha0 = tempBuffer + (u32)8U;
  montgomery_square_buffer(pZ, delta);
  montgomery_square_buffer(pY, gamma);
  montgomery_multiplication_buffer(pX, gamma, beta);
  p256_sub(pX, delta, a0);
  p256_add(pX, delta, a1);
  montgomery_multiplication_buffer(a0, a1, alpha0);
  multByThree(alpha0, alpha);
}

static void point_double_x3(u64 *x3, u64 *alpha, u64 *fourBeta, u64 *beta, u64 *eightBeta)
{
  montgomery_square_buffer(alpha, x3);
  multByFour(beta, fourBeta);
  multByTwo(fourBeta, eightBeta);
  p256_sub(x3, eightBeta, x3);
}

static void point_double_z3(u64 *z3, u64 *pY, u64 *pZ, u64 *gamma, u64 *delta)
{
  p256_add(pY, pZ, z3);
  montgomery_square_buffer(z3, z3);
  p256_sub(z3, gamma, z3);
  p256_sub(z3, delta, z3);
}

static void
point_double_y3(u64 *y3, u64 *x3, u64 *alpha, u64 *gamma, u64 *eightGamma, u64 *fourBeta)
{
  p256_sub(fourBeta, x3, y3);
  montgomery_multiplication_buffer(alpha, y3, y3);
  montgomery_square_buffer(gamma, gamma);
  multByEight(gamma, eightGamma);
  p256_sub(y3, eightGamma, y3);
}

static void point_double(u64 *p, u64 *result, u64 *tempBuffer)
{
  u64 *pY = p + (u32)4U;
  u64 *pZ = p + (u32)8U;
  u64 *x3 = result;
  u64 *y3 = result + (u32)4U;
  u64 *z3 = result + (u32)8U;
  u64 *delta = tempBuffer;
  u64 *gamma = tempBuffer + (u32)4U;
  u64 *beta = tempBuffer + (u32)8U;
  u64 *alpha = tempBuffer + (u32)16U;
  u64 *fourBeta = tempBuffer + (u32)20U;
  u64 *eightBeta = tempBuffer + (u32)24U;
  u64 *eightGamma = tempBuffer + (u32)28U;
  u64 *tmp = tempBuffer + (u32)32U;
  point_double_a_b_g(p, alpha, beta, gamma, delta, tmp);
  point_double_x3(x3, alpha, fourBeta, beta, eightBeta);
  point_double_z3(z3, pY, pZ, gamma, delta);
  point_double_y3(y3, x3, alpha, gamma, eightGamma, fourBeta);
}

static void
copy_point_conditional(u64 *x3_out, u64 *y3_out, u64 *z3_out, u64 *p, u64 *maskPoint)
{
  u64 *z = maskPoint + (u32)8U;
  u64 mask = isZero_uint64_CT(z);
  u64 *p_x = p;
  u64 *p_y = p + (u32)4U;
  u64 *p_z = p + (u32)8U;
  copy_conditional(x3_out, p_x, mask);
  copy_conditional(y3_out, p_y, mask);
  copy_conditional(z3_out, p_z, mask);
}

static void point_add(u64 *p, u64 *q, u64 *result, u64 *tempBuffer)
{
  u64 *tempBuffer16 = tempBuffer;
  u64 *u1 = tempBuffer + (u32)16U;
  u64 *u2 = tempBuffer + (u32)20U;
  u64 *s1 = tempBuffer + (u32)24U;
  u64 *s2 = tempBuffer + (u32)28U;
  u64 *h = tempBuffer + (u32)32U;
  u64 *r = tempBuffer + (u32)36U;
  u64 *uh = tempBuffer + (u32)40U;
  u64 *hCube = tempBuffer + (u32)44U;
  u64 *tempBuffer28 = tempBuffer + (u32)60U;
  u64 *pX = p;
  u64 *pY = p + (u32)4U;
  u64 *pZ0 = p + (u32)8U;
  u64 *qX = q;
  u64 *qY = q + (u32)4U;
  u64 *qZ0 = q + (u32)8U;
  u64 *z2Square = tempBuffer16;
  u64 *z1Square = tempBuffer16 + (u32)4U;
  u64 *z2Cube = tempBuffer16 + (u32)8U;
  u64 *z1Cube = tempBuffer16 + (u32)12U;
  u64 *temp;
  u64 *pZ;
  u64 *qZ;
  u64 *tempBuffer161;
  u64 *x3_out1;
  u64 *y3_out1;
  u64 *z3_out1;
  u64 *rSquare;
  u64 *rH;
  u64 *twoUh;
  u64 *s1hCube;
  u64 *u1hx3;
  u64 *ru1hx3;
  u64 *z1z2;
  montgomery_square_buffer(qZ0, z2Square);
  montgomery_square_buffer(pZ0, z1Square);
  montgomery_multiplication_buffer(z2Square, qZ0, z2Cube);
  montgomery_multiplication_buffer(z1Square, pZ0, z1Cube);
  montgomery_multiplication_buffer(z2Square, pX, u1);
  montgomery_multiplication_buffer(z1Square, qX, u2);
  montgomery_multiplication_buffer(z2Cube, pY, s1);
  montgomery_multiplication_buffer(z1Cube, qY, s2);
  temp = tempBuffer16;
  p256_sub(u2, u1, h);
  p256_sub(s2, s1, r);
  montgomery_square_buffer(h, temp);
  montgomery_multiplication_buffer(temp, u1, uh);
  montgomery_multiplication_buffer(temp, h, hCube);
  pZ = p + (u32)8U;
  qZ = q + (u32)8U;
  tempBuffer161 = tempBuffer28;
  x3_out1 = tempBuffer28 + (u32)16U;
  y3_out1 = tempBuffer28 + (u32)20U;
  z3_out1 = tempBuffer28 + (u32)24U;
  rSquare = tempBuffer161;
  rH = tempBuffer161 + (u32)4U;
  twoUh = tempBuffer161 + (u32)8U;
  montgomery_square_buffer(r, rSquare);
  p256_sub(rSquare, hCube, rH);
  multByTwo(uh, twoUh);
  p256_sub(rH, twoUh, x3_out1);
  s1hCube = tempBuffer161;
  u1hx3 = tempBuffer161 + (u32)4U;
  ru1hx3 = tempBuffer161 + (u32)8U;
  montgomery_multiplication_buffer(s1, hCube, s1hCube);
  p256_sub(uh, x3_out1, u1hx3);
  montgomery_multiplication_buffer(u1hx3, r, ru1hx3);
  p256_sub(ru1hx3, s1hCube, y3_out1);
  z1z2 = tempBuffer161;
  montgomery_multiplication_buffer(pZ, qZ, z1z2);
  montgomery_multiplication_buffer(z1z2, h, z3_out1);
  copy_point_conditional(x3_out1, y3_out1, z3_out1, q, p);
  copy_point_conditional(x3_out1, y3_out1, z3_out1, p, q);
  memcpy(result, x3_out1, (u32)4U * sizeof (u64));
  memcpy(result + (u32)4U, y3_out1, (u32)4U * sizeof (u64));
  memcpy(result + (u32)8U, z3_out1, (u32)4U * sizeof (u64));
}

static void pointToDomain(u64 *p, u64 *result)
{
  u64 *p_x = p;
  u64 *p_y = p + (u32)4U;
  u64 *p_z = p + (u32)8U;
  u64 *r_x = result;
  u64 *r_y = result + (u32)4U;
  u64 *r_z = result + (u32)8U;
  u64 multBuffer[8U] = { 0U };
  shift_256_impl(p_x, multBuffer);
  solinas_reduction_impl(multBuffer, r_x);
  {
    u64 multBuffer0[8U] = { 0U };
    shift_256_impl(p_y, multBuffer0);
    solinas_reduction_impl(multBuffer0, r_y);
    {
      u64 multBuffer1[8U] = { 0U };
      shift_256_impl(p_z, multBuffer1);
      solinas_reduction_impl(multBuffer1, r_z);
    }
  }
}

static void copy_point(u64 *p, u64 *result)
{
  memcpy(result, p, (u32)12U * sizeof (u64));
}

static u64 isPointAtInfinityPrivate(u64 *p)
{
  u64 z0 = p[8U];
  u64 z1 = p[9U];
  u64 z2 = p[10U];
  u64 z3 = p[11U];
  u64 z0_zero = FStar_UInt64_eq_mask(z0, (u64)0U);
  u64 z1_zero = FStar_UInt64_eq_mask(z1, (u64)0U);
  u64 z2_zero = FStar_UInt64_eq_mask(z2, (u64)0U);
  u64 z3_zero = FStar_UInt64_eq_mask(z3, (u64)0U);
  return (z0_zero & z1_zero) & (z2_zero & z3_zero);
}

static inline void cswap(u64 bit, u64 *p1, u64 *p2)
{
  u64 mask = (u64)0U - bit;
  u32 i;
  for (i = (u32)0U; i < (u32)12U; i++)
  {
    u64 dummy = mask & (p1[i] ^ p2[i]);
    p1[i] = p1[i] ^ dummy;
    p2[i] = p2[i] ^ dummy;
  }
}

static void norm(u64 *p, u64 *resultPoint, u64 *tempBuffer)
{
  u64 *xf = p;
  u64 *yf = p + (u32)4U;
  u64 *zf = p + (u32)8U;
  u64 *z2f = tempBuffer + (u32)4U;
  u64 *z3f = tempBuffer + (u32)8U;
  u64 *tempBuffer20 = tempBuffer + (u32)12U;
  montgomery_square_buffer(zf, z2f);
  montgomery_multiplication_buffer(z2f, zf, z3f);
  exponent(z2f, z2f, tempBuffer20);
  exponent(z3f, z3f, tempBuffer20);
  montgomery_multiplication_buffer(xf, z2f, z2f);
  montgomery_multiplication_buffer(yf, z3f, z3f);
  {
    u64 zeroBuffer[4U] = { 0U };
    u64 *resultX = resultPoint;
    u64 *resultY = resultPoint + (u32)4U;
    u64 *resultZ = resultPoint + (u32)8U;
    u64 bit = isPointAtInfinityPrivate(p);
    montgomery_multiplication_buffer_by_one(z2f, resultX);
    montgomery_multiplication_buffer_by_one(z3f, resultY);
    uploadOneImpl(resultZ);
    copy_conditional(resultZ, zeroBuffer, bit);
  }
}

static void normX(u64 *p, u64 *result, u64 *tempBuffer)
{
  u64 *xf = p;
  u64 *zf = p + (u32)8U;
  u64 *z2f = tempBuffer + (u32)4U;
  u64 *tempBuffer20 = tempBuffer + (u32)12U;
  montgomery_square_buffer(zf, z2f);
  exponent(z2f, z2f, tempBuffer20);
  montgomery_multiplication_buffer(z2f, xf, z2f);
  montgomery_multiplication_buffer_by_one(z2f, result);
}

static void zero_buffer(u64 *p)
{
  p[0U] = (u64)0U;
  p[1U] = (u64)0U;
  p[2U] = (u64)0U;
  p[3U] = (u64)0U;
  p[4U] = (u64)0U;
  p[5U] = (u64)0U;
  p[6U] = (u64)0U;
  p[7U] = (u64)0U;
  p[8U] = (u64)0U;
  p[9U] = (u64)0U;
  p[10U] = (u64)0U;
  p[11U] = (u64)0U;
}

static void scalarMultiplicationL(u64 *p, u64 *result, u8 *scalar, u64 *tempBuffer)
{
  u64 *q = tempBuffer;
  u64 *buff;
  zero_buffer(q);
  buff = tempBuffer + (u32)12U;
  pointToDomain(p, result);
  {
    u32 i;
    for (i = (u32)0U; i < (u32)256U; i++)
    {
      u32 bit0 = (u32)255U - i;
      u64 bit = (u64)(scalar[(u32)31U - bit0 / (u32)8U] >> bit0 % (u32)8U & (u8)1U);
      cswap(bit, q, result);
      point_add(q, result, result, buff);
      point_double(q, q, buff);
      cswap(bit, q, result);
    }
  }
  norm(q, result, buff);
}

static void scalarMultiplicationC(u64 *p, u64 *result, const u8 *scalar, u64 *tempBuffer)
{
  u64 *q = tempBuffer;
  u64 *buff;
  zero_buffer(q);
  buff = tempBuffer + (u32)12U;
  pointToDomain(p, result);
  {
    u32 i;
    for (i = (u32)0U; i < (u32)256U; i++)
    {
      u32 bit0 = (u32)255U - i;
      u64 bit = (u64)(scalar[(u32)31U - bit0 / (u32)8U] >> bit0 % (u32)8U & (u8)1U);
      cswap(bit, q, result);
      point_add(q, result, result, buff);
      point_double(q, q, buff);
      cswap(bit, q, result);
    }
  }
  norm(q, result, buff);
}

static void uploadBasePoint(u64 *p)
{
  p[0U] = (u64)8784043285714375740U;
  p[1U] = (u64)8483257759279461889U;
  p[2U] = (u64)8789745728267363600U;
  p[3U] = (u64)1770019616739251654U;
  p[4U] = (u64)15992936863339206154U;
  p[5U] = (u64)10037038012062884956U;
  p[6U] = (u64)15197544864945402661U;
  p[7U] = (u64)9615747158586711429U;
  p[8U] = (u64)1U;
  p[9U] = (u64)18446744069414584320U;
  p[10U] = (u64)18446744073709551615U;
  p[11U] = (u64)4294967294U;
}

static void scalarMultiplicationWithoutNorm(u64 *p, u64 *result, u8 *scalar, u64 *tempBuffer)
{
  u64 *q = tempBuffer;
  u64 *buff;
  zero_buffer(q);
  buff = tempBuffer + (u32)12U;
  pointToDomain(p, result);
  {
    u32 i;
    for (i = (u32)0U; i < (u32)256U; i++)
    {
      u32 bit0 = (u32)255U - i;
      u64 bit = (u64)(scalar[(u32)31U - bit0 / (u32)8U] >> bit0 % (u32)8U & (u8)1U);
      cswap(bit, q, result);
      point_add(q, result, result, buff);
      point_double(q, q, buff);
      cswap(bit, q, result);
    }
  }
  copy_point(q, result);
}

static void secretToPublic(u64 *result, u8 *scalar, u64 *tempBuffer)
{
  u64 basePoint[12U] = { 0U };
  u64 *q;
  u64 *buff;
  uploadBasePoint(basePoint);
  q = tempBuffer;
  buff = tempBuffer + (u32)12U;
  zero_buffer(q);
  {
    u32 i;
    for (i = (u32)0U; i < (u32)256U; i++)
    {
      u32 bit0 = (u32)255U - i;
      u64 bit = (u64)(scalar[(u32)31U - bit0 / (u32)8U] >> bit0 % (u32)8U & (u8)1U);
      cswap(bit, q, basePoint);
      point_add(q, basePoint, basePoint, buff);
      point_double(q, q, buff);
      cswap(bit, q, basePoint);
    }
  }
  norm(q, result, buff);
}

static void secretToPublicWithoutNorm(u64 *result, u8 *scalar, u64 *tempBuffer)
{
  u64 basePoint[12U] = { 0U };
  u64 *q;
  u64 *buff;
  uploadBasePoint(basePoint);
  q = tempBuffer;
  buff = tempBuffer + (u32)12U;
  zero_buffer(q);
  {
    u32 i;
    for (i = (u32)0U; i < (u32)256U; i++)
    {
      u32 bit0 = (u32)255U - i;
      u64 bit = (u64)(scalar[(u32)31U - bit0 / (u32)8U] >> bit0 % (u32)8U & (u8)1U);
      cswap(bit, q, basePoint);
      point_add(q, basePoint, basePoint, buff);
      point_double(q, q, buff);
      cswap(bit, q, basePoint);
    }
  }
  copy_point(q, result);
}

static const
u64
prime256order_buffer[4U] =
  {
    (u64)17562291160714782033U,
    (u64)13611842547513532036U,
    (u64)18446744073709551615U,
    (u64)18446744069414584320U
  };

static const
u8
order_inverse_buffer[32U] =
  {
    (u8)79U, (u8)37U, (u8)99U, (u8)252U, (u8)194U, (u8)202U, (u8)185U, (u8)243U, (u8)132U, (u8)158U,
    (u8)23U, (u8)167U, (u8)173U, (u8)250U, (u8)230U, (u8)188U, (u8)255U, (u8)255U, (u8)255U,
    (u8)255U, (u8)255U, (u8)255U, (u8)255U, (u8)255U, (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)255U,
    (u8)255U, (u8)255U, (u8)255U
  };

static const
u8
order_buffer[32U] =
  {
    (u8)255U, (u8)255U, (u8)255U, (u8)255U, (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)255U, (u8)255U,
    (u8)255U, (u8)255U, (u8)255U, (u8)255U, (u8)255U, (u8)255U, (u8)188U, (u8)230U, (u8)250U,
    (u8)173U, (u8)167U, (u8)23U, (u8)158U, (u8)132U, (u8)243U, (u8)185U, (u8)202U, (u8)194U,
    (u8)252U, (u8)99U, (u8)37U, (u8)81U
  };

static void montgomery_multiplication_round(u64 *t, u64 *round, u64 k0)
{
  u64 temp = (u64)0U;
  u64 y = (u64)0U;
  u64 t2[8U] = { 0U };
  u64 t3[8U] = { 0U };
  u64 t1 = t[0U];
  u64 y_;
  u64 *result04;
  mul64(t1, k0, &y, &temp);
  y_ = y;
  result04 = t2;
  {
    u64 temp1 = (u64)0U;
    u64 f1 = prime256order_buffer[1U];
    u64 f2 = prime256order_buffer[2U];
    u64 f3 = prime256order_buffer[3U];
    u64 *o0 = result04;
    u64 *o1 = result04 + (u32)1U;
    u64 *o2 = result04 + (u32)2U;
    u64 *o3 = result04 + (u32)3U;
    u64 f01 = prime256order_buffer[0U];
    u64 h0;
    u64 l0;
    u64 c1;
    u64 h1;
    u64 l1;
    u64 c2;
    u64 h;
    u64 l;
    u64 c3;
    u64 temp0;
    u64 c;
    u64 uu____0;
    mul64(f01, y_, o0, &temp1);
    h0 = temp1;
    mul64(f1, y_, o1, &temp1);
    l0 = o1[0U];
    c1 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l0, h0, o1);
    h1 = temp1;
    mul64(f2, y_, o2, &temp1);
    l1 = o2[0U];
    c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l1, h1, o2);
    h = temp1;
    mul64(f3, y_, o3, &temp1);
    l = o3[0U];
    c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l, h, o3);
    temp0 = temp1;
    c = c3 + temp0;
    t2[4U] = c;
    uu____0 = add8(t, t2, t3);
    shift8(t3, round);
  }
}

static void montgomery_multiplication_round_twice(u64 *t, u64 *result, u64 k0)
{
  u64 tempRound[8U] = { 0U };
  montgomery_multiplication_round(t, tempRound, k0);
  montgomery_multiplication_round(tempRound, result, k0);
}

static void reduction_prime_2prime_with_carry(u64 *x, u64 *result)
{
  u64 tempBuffer[4U] = { 0U };
  u64 tempBufferForSubborrow = (u64)0U;
  u64 cin = x[4U];
  u64 *x_ = x;
  u64 c = sub4_il(x_, prime256order_buffer, tempBuffer);
  u64 carry = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, cin, (u64)0U, &tempBufferForSubborrow);
  cmovznz4(carry, tempBuffer, x_, result);
}

static void reduction_prime_2prime_order(u64 *x, u64 *result)
{
  u64 tempBuffer[4U] = { 0U };
  u64 c = sub4_il(x, prime256order_buffer, tempBuffer);
  cmovznz4(c, tempBuffer, x, result);
}

static void montgomery_multiplication_ecdsa_module(u64 *a, u64 *b, u64 *result)
{
  u64 t[8U] = { 0U };
  u64 round2[8U] = { 0U };
  u64 round4[8U] = { 0U };
  u64 prime_p256_orderBuffer[4U] = { 0U };
  u64 k0 = (u64)14758798090332847183U;
  u64 f0 = a[0U];
  u64 f1 = a[1U];
  u64 f2 = a[2U];
  u64 f3 = a[3U];
  u64 *b0 = t;
  u64 temp2 = (u64)0U;
  u64 f110 = b[1U];
  u64 f210 = b[2U];
  u64 f310 = b[3U];
  u64 *o00 = b0;
  u64 *o10 = b0 + (u32)1U;
  u64 *o20 = b0 + (u32)2U;
  u64 *o30 = b0 + (u32)3U;
  u64 f020 = b[0U];
  u64 h0;
  u64 l0;
  u64 c10;
  u64 h1;
  u64 l1;
  u64 c20;
  u64 h2;
  u64 l2;
  u64 c30;
  u64 temp00;
  u64 c0;
  u64 *b1;
  mul64(f020, f0, o00, &temp2);
  h0 = temp2;
  mul64(f110, f0, o10, &temp2);
  l0 = o10[0U];
  c10 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l0, h0, o10);
  h1 = temp2;
  mul64(f210, f0, o20, &temp2);
  l1 = o20[0U];
  c20 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, l1, h1, o20);
  h2 = temp2;
  mul64(f310, f0, o30, &temp2);
  l2 = o30[0U];
  c30 = Lib_IntTypes_Intrinsics_add_carry_u64(c20, l2, h2, o30);
  temp00 = temp2;
  c0 = c30 + temp00;
  t[4U] = c0;
  b1 = t + (u32)1U;
  {
    u64 temp3[4U] = { 0U };
    u64 temp10 = (u64)0U;
    u64 f111 = b[1U];
    u64 f211 = b[2U];
    u64 f311 = b[3U];
    u64 *o01 = temp3;
    u64 *o11 = temp3 + (u32)1U;
    u64 *o21 = temp3 + (u32)2U;
    u64 *o31 = temp3 + (u32)3U;
    u64 f021 = b[0U];
    u64 h3;
    u64 l3;
    u64 c12;
    u64 h4;
    u64 l4;
    u64 c22;
    u64 h5;
    u64 l5;
    u64 c31;
    u64 temp01;
    u64 c4;
    u64 c32;
    u64 c1;
    u64 *b2;
    mul64(f021, f1, o01, &temp10);
    h3 = temp10;
    mul64(f111, f1, o11, &temp10);
    l3 = o11[0U];
    c12 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l3, h3, o11);
    h4 = temp10;
    mul64(f211, f1, o21, &temp10);
    l4 = o21[0U];
    c22 = Lib_IntTypes_Intrinsics_add_carry_u64(c12, l4, h4, o21);
    h5 = temp10;
    mul64(f311, f1, o31, &temp10);
    l5 = o31[0U];
    c31 = Lib_IntTypes_Intrinsics_add_carry_u64(c22, l5, h5, o31);
    temp01 = temp10;
    c4 = c31 + temp01;
    c32 = add4(temp3, b1, b1);
    c1 = c4 + c32;
    t[5U] = c1;
    b2 = t + (u32)2U;
    {
      u64 temp4[4U] = { 0U };
      u64 temp11 = (u64)0U;
      u64 f112 = b[1U];
      u64 f212 = b[2U];
      u64 f312 = b[3U];
      u64 *o02 = temp4;
      u64 *o12 = temp4 + (u32)1U;
      u64 *o22 = temp4 + (u32)2U;
      u64 *o32 = temp4 + (u32)3U;
      u64 f022 = b[0U];
      u64 h6;
      u64 l6;
      u64 c110;
      u64 h7;
      u64 l7;
      u64 c23;
      u64 h8;
      u64 l8;
      u64 c33;
      u64 temp02;
      u64 c5;
      u64 c34;
      u64 c2;
      u64 *b3;
      mul64(f022, f2, o02, &temp11);
      h6 = temp11;
      mul64(f112, f2, o12, &temp11);
      l6 = o12[0U];
      c110 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l6, h6, o12);
      h7 = temp11;
      mul64(f212, f2, o22, &temp11);
      l7 = o22[0U];
      c23 = Lib_IntTypes_Intrinsics_add_carry_u64(c110, l7, h7, o22);
      h8 = temp11;
      mul64(f312, f2, o32, &temp11);
      l8 = o32[0U];
      c33 = Lib_IntTypes_Intrinsics_add_carry_u64(c23, l8, h8, o32);
      temp02 = temp11;
      c5 = c33 + temp02;
      c34 = add4(temp4, b2, b2);
      c2 = c5 + c34;
      t[6U] = c2;
      b3 = t + (u32)3U;
      {
        u64 temp[4U] = { 0U };
        u64 temp1 = (u64)0U;
        u64 f11 = b[1U];
        u64 f21 = b[2U];
        u64 f31 = b[3U];
        u64 *o0 = temp;
        u64 *o1 = temp + (u32)1U;
        u64 *o2 = temp + (u32)2U;
        u64 *o3 = temp + (u32)3U;
        u64 f02 = b[0U];
        u64 h9;
        u64 l9;
        u64 c11;
        u64 h10;
        u64 l10;
        u64 c21;
        u64 h;
        u64 l;
        u64 c35;
        u64 temp0;
        u64 c;
        u64 c36;
        u64 c3;
        mul64(f02, f3, o0, &temp1);
        h9 = temp1;
        mul64(f11, f3, o1, &temp1);
        l9 = o1[0U];
        c11 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l9, h9, o1);
        h10 = temp1;
        mul64(f21, f3, o2, &temp1);
        l10 = o2[0U];
        c21 = Lib_IntTypes_Intrinsics_add_carry_u64(c11, l10, h10, o2);
        h = temp1;
        mul64(f31, f3, o3, &temp1);
        l = o3[0U];
        c35 = Lib_IntTypes_Intrinsics_add_carry_u64(c21, l, h, o3);
        temp0 = temp1;
        c = c35 + temp0;
        c36 = add4(temp, b3, b3);
        c3 = c + c36;
        t[7U] = c3;
        montgomery_multiplication_round_twice(t, round2, k0);
        montgomery_multiplication_round_twice(round2, round4, k0);
        reduction_prime_2prime_with_carry(round4, result);
      }
    }
  }
}

static void bufferToJac(u64 *p, u64 *result)
{
  u64 *partPoint = result;
  memcpy(partPoint, p, (u32)8U * sizeof (u64));
  result[8U] = (u64)1U;
  result[9U] = (u64)0U;
  result[10U] = (u64)0U;
  result[11U] = (u64)0U;
}

/*
   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.
*/
static bool isPointAtInfinityPublic(u64 *p)
{
  u64 z0 = p[8U];
  u64 z1 = p[9U];
  u64 z2 = p[10U];
  u64 z3 = p[11U];
  bool z0_zero = z0 == (u64)0U;
  bool z1_zero = z1 == (u64)0U;
  bool z2_zero = z2 == (u64)0U;
  bool z3_zero = z3 == (u64)0U;
  return z0_zero && z1_zero && z2_zero && z3_zero;
}

/*
   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.
*/
static bool isPointOnCurvePublic(u64 *p)
{
  u64 y2Buffer[4U] = { 0U };
  u64 xBuffer[4U] = { 0U };
  u64 *x = p;
  u64 *y = p + (u32)4U;
  u64 multBuffer0[8U] = { 0U };
  shift_256_impl(y, multBuffer0);
  solinas_reduction_impl(multBuffer0, y2Buffer);
  montgomery_square_buffer(y2Buffer, y2Buffer);
  {
    u64 xToDomainBuffer[4U] = { 0U };
    u64 minusThreeXBuffer[4U] = { 0U };
    u64 p256_constant[4U] = { 0U };
    u64 multBuffer[8U] = { 0U };
    u64 r;
    shift_256_impl(x, multBuffer);
    solinas_reduction_impl(multBuffer, xToDomainBuffer);
    montgomery_square_buffer(xToDomainBuffer, xBuffer);
    montgomery_multiplication_buffer(xBuffer, xToDomainBuffer, xBuffer);
    multByThree(xToDomainBuffer, minusThreeXBuffer);
    p256_sub(xBuffer, minusThreeXBuffer, xBuffer);
    p256_constant[0U] = (u64)15608596021259845087U;
    p256_constant[1U] = (u64)12461466548982526096U;
    p256_constant[2U] = (u64)16546823903870267094U;
    p256_constant[3U] = (u64)15866188208926050356U;
    p256_add(xBuffer, p256_constant, xBuffer);
    r = compare_felem(y2Buffer, xBuffer);
    return !(r == (u64)0U);
  }
}

static bool isCoordinateValid(u64 *p)
{
  u64 tempBuffer[4U] = { 0U };
  u64 *x = p;
  u64 *y = p + (u32)4U;
  u64 carryX = sub4_il(x, prime256_buffer, tempBuffer);
  u64 carryY = sub4_il(y, prime256_buffer, tempBuffer);
  bool lessX = carryX == (u64)1U;
  bool lessY = carryY == (u64)1U;
  return lessX && lessY;
}

/*
   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.
*/
static bool isOrderCorrect(u64 *p, u64 *tempBuffer)
{
  u64 multResult[12U] = { 0U };
  u64 pBuffer[12U] = { 0U };
  bool result;
  memcpy(pBuffer, p, (u32)12U * sizeof (u64));
  scalarMultiplicationC(pBuffer, multResult, order_buffer, tempBuffer);
  result = isPointAtInfinityPublic(multResult);
  return result;
}

/*
   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.
*/
static bool verifyQValidCurvePoint(u64 *pubKeyAsPoint, u64 *tempBuffer)
{
  bool coordinatesValid = isCoordinateValid(pubKeyAsPoint);
  if (!coordinatesValid)
    return false;
  {
    bool belongsToCurve = isPointOnCurvePublic(pubKeyAsPoint);
    bool orderCorrect = isOrderCorrect(pubKeyAsPoint, tempBuffer);
    return coordinatesValid && belongsToCurve && orderCorrect;
  }
}

static bool isMoreThanZeroLessThanOrder(u8 *x)
{
  u64 xAsFelem[4U] = { 0U };
  toUint64ChangeEndian(x, xAsFelem);
  {
    u64 tempBuffer[4U] = { 0U };
    u64 carry = sub4_il(xAsFelem, prime256order_buffer, tempBuffer);
    u64 less = FStar_UInt64_eq_mask(carry, (u64)1U);
    u64 more = isZero_uint64_CT(xAsFelem);
    u64 notMore = ~more;
    u64 result = less & notMore;
    return ~result == (u64)0U;
  }
}

/*
  The pub(lic)_key input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over this variable.
*/
static u64 _ecp256dh_r(u64 *result, u64 *pubKey, u8 *scalar)
{
  u64 tempBuffer[100U] = { 0U };
  u64 publicKeyBuffer[12U] = { 0U };
  bool publicKeyCorrect;
  u64 ite;
  bufferToJac(pubKey, publicKeyBuffer);
  publicKeyCorrect = verifyQValidCurvePoint(publicKeyBuffer, tempBuffer);
  if (publicKeyCorrect)
  {
    scalarMultiplicationL(publicKeyBuffer, result, scalar, tempBuffer);
    {
      u64 flag = isPointAtInfinityPrivate(result);
      ite = flag;
    }
  }
  else
    ite = (u64)18446744073709551615U;
  return ite;
}

static inline void cswap0(u64 bit, u64 *p1, u64 *p2)
{
  u64 mask = (u64)0U - bit;
  u32 i;
  for (i = (u32)0U; i < (u32)4U; i++)
  {
    u64 dummy = mask & (p1[i] ^ p2[i]);
    p1[i] = p1[i] ^ dummy;
    p2[i] = p2[i] ^ dummy;
  }
}

static void montgomery_ladder_exponent(u64 *r)
{
  u64 p[4U] = { 0U };
  p[0U] = (u64)884452912994769583U;
  p[1U] = (u64)4834901526196019579U;
  p[2U] = (u64)0U;
  p[3U] = (u64)4294967295U;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)256U; i++)
    {
      u32 bit0 = (u32)255U - i;
      u64 bit = (u64)(order_inverse_buffer[bit0 / (u32)8U] >> bit0 % (u32)8U & (u8)1U);
      cswap0(bit, p, r);
      montgomery_multiplication_ecdsa_module(p, r, r);
      montgomery_multiplication_ecdsa_module(p, p, p);
      cswap0(bit, p, r);
    }
  }
  memcpy(r, p, (u32)4U * sizeof (u64));
}

static void fromDomainImpl(u64 *a, u64 *result)
{
  u64 one[4U] = { 0U };
  uploadOneImpl(one);
  montgomery_multiplication_ecdsa_module(one, a, result);
}

static void multPowerPartial(u64 *a, u64 *b, u64 *result)
{
  u64 buffFromDB[4U] = { 0U };
  fromDomainImpl(b, buffFromDB);
  fromDomainImpl(buffFromDB, buffFromDB);
  montgomery_multiplication_ecdsa_module(a, buffFromDB, result);
}

/*
   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.
*/
static bool isMoreThanZeroLessThanOrderMinusOne(u64 *f)
{
  u64 tempBuffer[4U] = { 0U };
  u64 carry = sub4_il(f, prime256order_buffer, tempBuffer);
  bool less = carry == (u64)1U;
  u64 f0 = f[0U];
  u64 f1 = f[1U];
  u64 f2 = f[2U];
  u64 f3 = f[3U];
  bool z0_zero = f0 == (u64)0U;
  bool z1_zero = f1 == (u64)0U;
  bool z2_zero = f2 == (u64)0U;
  bool z3_zero = f3 == (u64)0U;
  bool more = z0_zero && z1_zero && z2_zero && z3_zero;
  return less && !more;
}

/*
   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.
*/
static bool compare_felem_bool(u64 *a, u64 *b)
{
  u64 a_0 = a[0U];
  u64 a_1 = a[1U];
  u64 a_2 = a[2U];
  u64 a_3 = a[3U];
  u64 b_0 = b[0U];
  u64 b_1 = b[1U];
  u64 b_2 = b[2U];
  u64 b_3 = b[3U];
  return a_0 == b_0 && a_1 == b_1 && a_2 == b_2 && a_3 == b_3;
}

/*
   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.
*/
static bool
ecdsa_verification_(
  Spec_ECDSA_hash_alg_ecdsa alg,
  u64 *pubKey,
  u64 *r,
  u64 *s,
  u32 mLen,
  u8 *m
)
{
  u64 tempBufferU64[120U] = { 0U };
  u64 *publicKeyBuffer = tempBufferU64;
  u64 *hashAsFelem = tempBufferU64 + (u32)12U;
  u64 *tempBuffer = tempBufferU64 + (u32)16U;
  u64 *xBuffer = tempBufferU64 + (u32)116U;
  bool publicKeyCorrect;
  bool ite;
  bufferToJac(pubKey, publicKeyBuffer);
  publicKeyCorrect = verifyQValidCurvePoint(publicKeyBuffer, tempBuffer);
  if (publicKeyCorrect == false)
    ite = false;
  else
  {
    bool isRCorrect = isMoreThanZeroLessThanOrderMinusOne(r);
    bool isSCorrect = isMoreThanZeroLessThanOrderMinusOne(s);
    bool step1 = isRCorrect && isSCorrect;
    if (step1 == false)
      ite = false;
    else
    {
      u8 tempBufferU8[64U] = { 0U };
      u8 *bufferU1 = tempBufferU8;
      u8 *bufferU2 = tempBufferU8 + (u32)32U;
      u32 sz;
      if (alg.tag == Spec_ECDSA_NoHash)
        sz = mLen;
      else if (alg.tag == Spec_ECDSA_Hash)
      {
        Spec_Hash_Definitions_hash_alg a = alg._0;
        switch (a)
        {
          case Spec_Hash_Definitions_MD5:
            {
              sz = (u32)16U;
              break;
            }
          case Spec_Hash_Definitions_SHA1:
            {
              sz = (u32)20U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_224:
            {
              sz = (u32)28U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_256:
            {
              sz = (u32)32U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_384:
            {
              sz = (u32)48U;
              break;
            }
          case Spec_Hash_Definitions_SHA2_512:
            {
              sz = (u32)64U;
              break;
            }
          case Spec_Hash_Definitions_Blake2S:
            {
              sz = (u32)32U;
              break;
            }
          case Spec_Hash_Definitions_Blake2B:
            {
              sz = (u32)64U;
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
        sz = KRML_EABORT(u32, "unreachable (pattern matches are exhaustive in F*)");
      KRML_CHECK_SIZE(sizeof (u8), sz);
      {
        u8 mHash[sz];
        memset(mHash, 0U, sz * sizeof (u8));
        if (alg.tag == Spec_ECDSA_NoHash)
          memcpy(mHash, m, sz * sizeof (u8));
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
        {
          u8 *cutHash = mHash;
          toUint64ChangeEndian(cutHash, hashAsFelem);
          reduction_prime_2prime_order(hashAsFelem, hashAsFelem);
          {
            u64 tempBuffer1[12U] = { 0U };
            u64 *inverseS = tempBuffer1;
            u64 *u1 = tempBuffer1 + (u32)4U;
            u64 *u2 = tempBuffer1 + (u32)8U;
            fromDomainImpl(s, inverseS);
            montgomery_ladder_exponent(inverseS);
            multPowerPartial(inverseS, hashAsFelem, u1);
            multPowerPartial(inverseS, r, u2);
            changeEndian(u1);
            changeEndian(u2);
            toUint8(u1, bufferU1);
            toUint8(u2, bufferU2);
            {
              u64 pointSum[12U] = { 0U };
              u64 points[24U] = { 0U };
              u64 *buff = tempBuffer + (u32)12U;
              u64 *pointU1G = points;
              u64 *pointU2Q0 = points + (u32)12U;
              secretToPublicWithoutNorm(pointU1G, bufferU1, tempBuffer);
              scalarMultiplicationWithoutNorm(publicKeyBuffer, pointU2Q0, bufferU2, tempBuffer);
              {
                u64 *pointU1G0 = points;
                u64 *pointU2Q = points + (u32)12U;
                u64 tmp[112U] = { 0U };
                u64 *tmpForNorm = tmp;
                u64 *result0Norm = tmp + (u32)88U;
                u64 *result1Norm = tmp + (u32)100U;
                u64 *pointU1G1 = points;
                u64 *pointU2Q1 = points + (u32)12U;
                norm(pointU1G1, result0Norm, tmpForNorm);
                norm(pointU2Q1, result1Norm, tmpForNorm);
                {
                  u64 *x0 = result0Norm;
                  u64 *y0 = result0Norm + (u32)4U;
                  u64 *z0 = result0Norm + (u32)8U;
                  u64 *x1 = result1Norm;
                  u64 *y1 = result1Norm + (u32)4U;
                  u64 *z1 = result1Norm + (u32)8U;
                  bool xEqual = compare_felem_bool(x0, x1);
                  bool yEqual = compare_felem_bool(y0, y1);
                  bool zEqual = compare_felem_bool(z0, z1);
                  bool equalX = xEqual && yEqual && zEqual;
                  bool equalX0 = equalX;
                  if (equalX0)
                    point_double(pointU1G0, pointSum, buff);
                  else
                    point_add(pointU1G0, pointU2Q, pointSum, buff);
                  norm(pointSum, pointSum, buff);
                  {
                    bool resultIsPAI = isPointAtInfinityPublic(pointSum);
                    u64 *xCoordinateSum = pointSum;
                    memcpy(xBuffer, xCoordinateSum, (u32)4U * sizeof (u64));
                    reduction_prime_2prime_order(xBuffer, xBuffer);
                    {
                      bool r1 = !resultIsPAI;
                      bool state = r1;
                      if (state == false)
                        ite = false;
                      else
                      {
                        bool result = compare_felem_bool(xBuffer, r);
                        ite = result;
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
  return ite;
}

static u64
ecdsa_signature_core(
  Spec_ECDSA_hash_alg_ecdsa alg,
  u64 *r,
  u64 *s,
  u32 mLen,
  u8 *m,
  u64 *privKeyAsFelem,
  u8 *k
)
{
  u64 hashAsFelem[4U] = { 0U };
  u64 tempBuffer[100U] = { 0U };
  u64 kAsFelem[4U] = { 0U };
  toUint64ChangeEndian(k, kAsFelem);
  {
    u32 sz;
    if (alg.tag == Spec_ECDSA_NoHash)
      sz = mLen;
    else if (alg.tag == Spec_ECDSA_Hash)
    {
      Spec_Hash_Definitions_hash_alg a = alg._0;
      switch (a)
      {
        case Spec_Hash_Definitions_MD5:
          {
            sz = (u32)16U;
            break;
          }
        case Spec_Hash_Definitions_SHA1:
          {
            sz = (u32)20U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_224:
          {
            sz = (u32)28U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_256:
          {
            sz = (u32)32U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_384:
          {
            sz = (u32)48U;
            break;
          }
        case Spec_Hash_Definitions_SHA2_512:
          {
            sz = (u32)64U;
            break;
          }
        case Spec_Hash_Definitions_Blake2S:
          {
            sz = (u32)32U;
            break;
          }
        case Spec_Hash_Definitions_Blake2B:
          {
            sz = (u32)64U;
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
      sz = KRML_EABORT(u32, "unreachable (pattern matches are exhaustive in F*)");
    KRML_CHECK_SIZE(sizeof (u8), sz);
    {
      u8 mHash[sz];
      memset(mHash, 0U, sz * sizeof (u8));
      {
        u8 *cutHash;
        if (alg.tag == Spec_ECDSA_NoHash)
          memcpy(mHash, m, sz * sizeof (u8));
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
        cutHash = mHash;
        toUint64ChangeEndian(cutHash, hashAsFelem);
        reduction_prime_2prime_order(hashAsFelem, hashAsFelem);
        {
          u64 result[12U] = { 0U };
          u64 *tempForNorm = tempBuffer;
          u64 step5Flag;
          secretToPublicWithoutNorm(result, k, tempBuffer);
          normX(result, r, tempForNorm);
          reduction_prime_2prime_order(r, r);
          step5Flag = isZero_uint64_CT(r);
          {
            u64 rda[4U] = { 0U };
            u64 zBuffer[4U] = { 0U };
            u64 kInv[4U] = { 0U };
            u64 t;
            montgomery_multiplication_ecdsa_module(r, privKeyAsFelem, rda);
            fromDomainImpl(hashAsFelem, zBuffer);
            t = add4(rda, zBuffer, zBuffer);
            {
              u64 tempBuffer1[4U] = { 0U };
              u64 tempBufferForSubborrow = (u64)0U;
              u64 c = sub4_il(zBuffer, prime256order_buffer, tempBuffer1);
              u64
              carry = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t, (u64)0U, &tempBufferForSubborrow);
              u64 sIsZero;
              cmovznz4(carry, tempBuffer1, zBuffer, zBuffer);
              memcpy(kInv, kAsFelem, (u32)4U * sizeof (u64));
              montgomery_ladder_exponent(kInv);
              montgomery_multiplication_ecdsa_module(zBuffer, kInv, s);
              sIsZero = isZero_uint64_CT(s);
              return step5Flag | sIsZero;
            }
          }
        }
      }
    }
  }
}

static inline void cswap1(u64 bit, u64 *p1, u64 *p2)
{
  u64 mask = (u64)0U - bit;
  u32 i;
  for (i = (u32)0U; i < (u32)4U; i++)
  {
    u64 dummy = mask & (p1[i] ^ p2[i]);
    p1[i] = p1[i] ^ dummy;
    p2[i] = p2[i] ^ dummy;
  }
}

static void montgomery_ladder_power(u64 *a, const u8 *scalar, u64 *result)
{
  u64 p[4U] = { 0U };
  p[0U] = (u64)1U;
  p[1U] = (u64)18446744069414584320U;
  p[2U] = (u64)18446744073709551615U;
  p[3U] = (u64)4294967294U;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)256U; i++)
    {
      u32 bit0 = (u32)255U - i;
      u64 bit = (u64)(scalar[bit0 / (u32)8U] >> bit0 % (u32)8U & (u8)1U);
      cswap1(bit, p, a);
      montgomery_multiplication_buffer(p, a, a);
      montgomery_square_buffer(p, p);
      cswap1(bit, p, a);
    }
  }
  memcpy(result, p, (u32)4U * sizeof (u64));
}

static const
u8
sqPower_buffer[32U] =
  {
    (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)64U,
    (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)64U,
    (u8)0U, (u8)0U, (u8)0U, (u8)192U, (u8)255U, (u8)255U, (u8)255U, (u8)63U
  };

static void computeYFromX(u64 *x, u64 *result, u64 sign)
{
  u64 aCoordinateBuffer[4U] = { 0U };
  u64 bCoordinateBuffer[4U] = { 0U };
  u64 word;
  u64 bitToCheck;
  u64 flag;
  aCoordinateBuffer[0U] = (u64)18446744073709551612U;
  aCoordinateBuffer[1U] = (u64)17179869183U;
  aCoordinateBuffer[2U] = (u64)0U;
  aCoordinateBuffer[3U] = (u64)18446744056529682436U;
  bCoordinateBuffer[0U] = (u64)15608596021259845087U;
  bCoordinateBuffer[1U] = (u64)12461466548982526096U;
  bCoordinateBuffer[2U] = (u64)16546823903870267094U;
  bCoordinateBuffer[3U] = (u64)15866188208926050356U;
  montgomery_multiplication_buffer(aCoordinateBuffer, x, aCoordinateBuffer);
  cube(x, result);
  p256_add(result, aCoordinateBuffer, result);
  p256_add(result, bCoordinateBuffer, result);
  uploadZeroImpl(aCoordinateBuffer);
  montgomery_ladder_power(result, sqPower_buffer, result);
  montgomery_multiplication_buffer_by_one(result, result);
  p256_sub(aCoordinateBuffer, result, bCoordinateBuffer);
  word = result[0U];
  bitToCheck = word & (u64)1U;
  flag = FStar_UInt64_eq_mask(bitToCheck, sign);
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
bool Hacl_P256_ecdsa_sign_p256_sha2(u8 *result, u32 mLen, u8 *m, u8 *privKey, u8 *k)
{
  u64 privKeyAsFelem[4U] = { 0U };
  u64 r[4U] = { 0U };
  u64 s[4U] = { 0U };
  u8 *resultR = result;
  u8 *resultS = result + (u32)32U;
  u64 flag;
  toUint64ChangeEndian(privKey, privKeyAsFelem);
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
  changeEndian(r);
  toUint8(r, resultR);
  changeEndian(s);
  toUint8(s, resultS);
  return flag == (u64)0U;
}

/*
 Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
 priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: bool, where True stands for the correct signature generation. False value means that an error has occurred. 
  
 The private key and the nonce are expected to be more than 0 and less than the curve order.
*/
bool Hacl_P256_ecdsa_sign_p256_sha384(u8 *result, u32 mLen, u8 *m, u8 *privKey, u8 *k)
{
  u64 privKeyAsFelem[4U] = { 0U };
  u64 r[4U] = { 0U };
  u64 s[4U] = { 0U };
  u8 *resultR = result;
  u8 *resultS = result + (u32)32U;
  u64 flag;
  toUint64ChangeEndian(privKey, privKeyAsFelem);
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
  changeEndian(r);
  toUint8(r, resultR);
  changeEndian(s);
  toUint8(s, resultS);
  return flag == (u64)0U;
}

/*
 Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
 priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: bool, where True stands for the correct signature generation. False value means that an error has occurred. 
  
 The private key and the nonce are expected to be more than 0 and less than the curve order.
*/
bool Hacl_P256_ecdsa_sign_p256_sha512(u8 *result, u32 mLen, u8 *m, u8 *privKey, u8 *k)
{
  u64 privKeyAsFelem[4U] = { 0U };
  u64 r[4U] = { 0U };
  u64 s[4U] = { 0U };
  u8 *resultR = result;
  u8 *resultS = result + (u32)32U;
  u64 flag;
  toUint64ChangeEndian(privKey, privKeyAsFelem);
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
  changeEndian(r);
  toUint8(r, resultR);
  changeEndian(s);
  toUint8(s, resultS);
  return flag == (u64)0U;
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
bool Hacl_P256_ecdsa_sign_p256_without_hash(u8 *result, u32 mLen, u8 *m, u8 *privKey, u8 *k)
{
  u64 privKeyAsFelem[4U] = { 0U };
  u64 r[4U] = { 0U };
  u64 s[4U] = { 0U };
  u8 *resultR = result;
  u8 *resultS = result + (u32)32U;
  u64 flag;
  toUint64ChangeEndian(privKey, privKeyAsFelem);
  flag =
    ecdsa_signature_core(((Spec_ECDSA_hash_alg_ecdsa){ .tag = Spec_ECDSA_NoHash }),
      r,
      s,
      mLen,
      m,
      privKeyAsFelem,
      k);
  changeEndian(r);
  toUint8(r, resultR);
  changeEndian(s);
  toUint8(s, resultS);
  return flag == (u64)0U;
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
bool Hacl_P256_ecdsa_verif_p256_sha2(u32 mLen, u8 *m, u8 *pubKey, u8 *r, u8 *s)
{
  u64 publicKeyAsFelem[8U] = { 0U };
  u64 *publicKeyFelemX = publicKeyAsFelem;
  u64 *publicKeyFelemY = publicKeyAsFelem + (u32)4U;
  u64 rAsFelem[4U] = { 0U };
  u64 sAsFelem[4U] = { 0U };
  u8 *pubKeyX = pubKey;
  u8 *pubKeyY = pubKey + (u32)32U;
  bool result;
  toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  toUint64ChangeEndian(r, rAsFelem);
  toUint64ChangeEndian(s, sAsFelem);
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
bool Hacl_P256_ecdsa_verif_p256_sha384(u32 mLen, u8 *m, u8 *pubKey, u8 *r, u8 *s)
{
  u64 publicKeyAsFelem[8U] = { 0U };
  u64 *publicKeyFelemX = publicKeyAsFelem;
  u64 *publicKeyFelemY = publicKeyAsFelem + (u32)4U;
  u64 rAsFelem[4U] = { 0U };
  u64 sAsFelem[4U] = { 0U };
  u8 *pubKeyX = pubKey;
  u8 *pubKeyY = pubKey + (u32)32U;
  bool result;
  toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  toUint64ChangeEndian(r, rAsFelem);
  toUint64ChangeEndian(s, sAsFelem);
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
bool Hacl_P256_ecdsa_verif_p256_sha512(u32 mLen, u8 *m, u8 *pubKey, u8 *r, u8 *s)
{
  u64 publicKeyAsFelem[8U] = { 0U };
  u64 *publicKeyFelemX = publicKeyAsFelem;
  u64 *publicKeyFelemY = publicKeyAsFelem + (u32)4U;
  u64 rAsFelem[4U] = { 0U };
  u64 sAsFelem[4U] = { 0U };
  u8 *pubKeyX = pubKey;
  u8 *pubKeyY = pubKey + (u32)32U;
  bool result;
  toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  toUint64ChangeEndian(r, rAsFelem);
  toUint64ChangeEndian(s, sAsFelem);
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
bool Hacl_P256_ecdsa_verif_without_hash(u32 mLen, u8 *m, u8 *pubKey, u8 *r, u8 *s)
{
  u64 publicKeyAsFelem[8U] = { 0U };
  u64 *publicKeyFelemX = publicKeyAsFelem;
  u64 *publicKeyFelemY = publicKeyAsFelem + (u32)4U;
  u64 rAsFelem[4U] = { 0U };
  u64 sAsFelem[4U] = { 0U };
  u8 *pubKeyX = pubKey;
  u8 *pubKeyY = pubKey + (u32)32U;
  bool result;
  toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  toUint64ChangeEndian(r, rAsFelem);
  toUint64ChangeEndian(s, sAsFelem);
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
bool Hacl_P256_verify_q(u8 *pubKey)
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
  toUint64ChangeEndian(pubKeyX, publicKeyX);
  toUint64ChangeEndian(pubKeyY, publicKeyY);
  bufferToJac(publicKeyB, publicKeyJ);
  r = verifyQValidCurvePoint(publicKeyJ, tempBufferV);
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
bool Hacl_P256_decompression_not_compressed_form(u8 *b, u8 *result)
{
  u8 compressionIdentifier = b[0U];
  bool correctIdentifier = (u8)4U == compressionIdentifier;
  if (correctIdentifier)
    memcpy(result, b + (u32)1U, (u32)64U * sizeof (u8));
  return correctIdentifier;
}

/*
 Input: a point in compressed form (uint8[33]), 
 result: uint8[64] (internal point representation).
  
 Output: bool, where true stands for the correct decompression.
 
*/
bool Hacl_P256_decompression_compressed_form(u8 *b, u8 *result)
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
    memcpy(result, x, (u32)32U * sizeof (u8));
    toUint64ChangeEndian(x, t0);
    {
      u64 tempBuffer[4U] = { 0U };
      u64 carry = sub4_il(t0, prime256_buffer, tempBuffer);
      bool lessThanPrimeXCoordinate = carry == (u64)1U;
      if (!lessThanPrimeXCoordinate)
        return false;
      {
        u64 multBuffer[8U] = { 0U };
        shift_256_impl(t0, multBuffer);
        solinas_reduction_impl(multBuffer, t0);
        {
          u64 identifierBit = (u64)(compressedIdentifier & (u8)1U);
          computeYFromX(t0, t1, identifierBit);
          changeEndian(t1);
          toUint8(t1, result + (u32)32U);
          return true;
        }
      }
    }
  }
  return false;
}

/*
 Input: a point buffer (internal representation: uint8[64]), 
 result: a point in not compressed form (uint8[65]).
*/
void Hacl_P256_compression_not_compressed_form(u8 *b, u8 *result)
{
  u8 *to = result + (u32)1U;
  memcpy(to, b, (u32)64U * sizeof (u8));
  result[0U] = (u8)4U;
}

/*
 Input: a point buffer (internal representation: uint8[64]), 
 result: a point in not compressed form (uint8[33]).
*/
void Hacl_P256_compression_compressed_form(u8 *b, u8 *result)
{
  u8 *y = b + (u32)32U;
  u8 lastWordY = y[31U];
  u8 lastBitY = lastWordY & (u8)1U;
  u8 identifier = lastBitY + (u8)2U;
  memcpy(result + (u32)1U, b, (u32)32U * sizeof (u8));
  result[0U] = identifier;
}

/*
 Input: result: uint8[64], 
 scalar: uint8[32].
  
 Output: bool, where True stands for the correct key generation. 
  
 False means that an error has occurred (possibly that the result respresents point at infinity). 
  
*/
bool Hacl_P256_ecp256dh_i(u8 *result, u8 *scalar)
{
  u64 tempBuffer[100U] = { 0U };
  u64 resultBuffer[12U] = { 0U };
  u64 *resultBufferX = resultBuffer;
  u64 *resultBufferY = resultBuffer + (u32)4U;
  u8 *resultX = result;
  u8 *resultY = result + (u32)32U;
  u64 flag;
  secretToPublic(resultBuffer, scalar, tempBuffer);
  flag = isPointAtInfinityPrivate(resultBuffer);
  changeEndian(resultBufferX);
  changeEndian(resultBufferY);
  toUint8(resultBufferX, resultX);
  toUint8(resultBufferY, resultY);
  return flag == (u64)0U;
}

/*
 
   The pub(lic)_key input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over this variable.
  
 Input: result: uint8[64], 
 pub(lic)Key: uint8[64], 
 scalar: uint8[32].
  
 Output: bool, where True stands for the correct key generation. False value means that an error has occurred (possibly the provided public key was incorrect or the result represents point at infinity). 
  
*/
bool Hacl_P256_ecp256dh_r(u8 *result, u8 *pubKey, u8 *scalar)
{
  u64 resultBufferFelem[12U] = { 0U };
  u64 *resultBufferFelemX = resultBufferFelem;
  u64 *resultBufferFelemY = resultBufferFelem + (u32)4U;
  u8 *resultX = result;
  u8 *resultY = result + (u32)32U;
  u64 publicKeyAsFelem[8U] = { 0U };
  u64 *publicKeyFelemX = publicKeyAsFelem;
  u64 *publicKeyFelemY = publicKeyAsFelem + (u32)4U;
  u8 *pubKeyX = pubKey;
  u8 *pubKeyY = pubKey + (u32)32U;
  u64 flag;
  toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  flag = _ecp256dh_r(resultBufferFelem, publicKeyAsFelem, scalar);
  changeEndian(resultBufferFelemX);
  changeEndian(resultBufferFelemY);
  toUint8(resultBufferFelemX, resultX);
  toUint8(resultBufferFelemY, resultY);
  return flag == (u64)0U;
}

/*
 Input: scalar: uint8[32].
  
 Output: bool, where true stands for the scalar to be more than 0 and less than order.
*/
bool Hacl_P256_is_more_than_zero_less_than_order(u8 *x)
{
  return isMoreThanZeroLessThanOrder(x);
}

