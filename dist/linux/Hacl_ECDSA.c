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


#include "Hacl_ECDSA.h"

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

static u64 sub4_il(u64 *x, u64 *y, u64 *result)
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

static void mult64_0(u64 *x, u64 u, u64 *result, u64 *temp)
{
  u64 f0 = x[0U];
  mul64(f0, u, result, temp);
}

static void mult64_0il(u64 *x, u64 u, u64 *result, u64 *temp)
{
  u64 f0 = x[0U];
  mul64(f0, u, result, temp);
}

static u64 mult64_c(u64 x, u64 u, u64 cin, u64 *result, u64 *temp)
{
  u64 h = temp[0U];
  u64 l;
  mul64(x, u, result, temp);
  l = result[0U];
  return Lib_IntTypes_Intrinsics_add_carry_u64(cin, l, h, result);
}

static u64 mul1_il(u64 *f, u64 u, u64 *result)
{
  u64 temp = (u64)0U;
  u64 f1 = f[1U];
  u64 f2 = f[2U];
  u64 f3 = f[3U];
  u64 *o0 = result;
  u64 *o1 = result + (u32)1U;
  u64 *o2 = result + (u32)2U;
  u64 *o3 = result + (u32)3U;
  u64 c1;
  u64 c2;
  u64 c3;
  u64 temp0;
  mult64_0il(f, u, o0, &temp);
  c1 = mult64_c(f1, u, (u64)0U, o1, &temp);
  c2 = mult64_c(f2, u, c1, o2, &temp);
  c3 = mult64_c(f3, u, c2, o3, &temp);
  temp0 = temp;
  return c3 + temp0;
}

static u64 mul1(u64 *f, u64 u, u64 *result)
{
  u64 temp = (u64)0U;
  u64 f1 = f[1U];
  u64 f2 = f[2U];
  u64 f3 = f[3U];
  u64 *o0 = result;
  u64 *o1 = result + (u32)1U;
  u64 *o2 = result + (u32)2U;
  u64 *o3 = result + (u32)3U;
  u64 c1;
  u64 c2;
  u64 c3;
  u64 temp0;
  mult64_0(f, u, o0, &temp);
  c1 = mult64_c(f1, u, (u64)0U, o1, &temp);
  c2 = mult64_c(f2, u, c1, o2, &temp);
  c3 = mult64_c(f3, u, c2, o3, &temp);
  temp0 = temp;
  return c3 + temp0;
}

static u64 mul1_add(u64 *f1, u64 u2, u64 *f3, u64 *result)
{
  u64 temp[4U] = { 0U };
  u64 c = mul1(f1, u2, temp);
  u64 c3 = add4(temp, f3, result);
  return c + c3;
}

static void mul(u64 *f, u64 *r, u64 *out)
{
  u64 temp[8U] = { 0U };
  u64 f0 = f[0U];
  u64 f1 = f[1U];
  u64 f2 = f[2U];
  u64 f3 = f[3U];
  u64 *b0 = temp;
  u64 c0 = mul1(r, f0, b0);
  u64 *b1;
  u64 c1;
  u64 *b2;
  u64 c2;
  u64 *b3;
  u64 c3;
  temp[4U] = c0;
  b1 = temp + (u32)1U;
  c1 = mul1_add(r, f1, b1, b1);
  temp[5U] = c1;
  b2 = temp + (u32)2U;
  c2 = mul1_add(r, f2, b2, b2);
  temp[6U] = c2;
  b3 = temp + (u32)3U;
  c3 = mul1_add(r, f3, b3, b3);
  temp[7U] = c3;
  memcpy(out, temp, (u32)8U * sizeof (temp[0U]));
}

static u64 sq0(u64 *f, u64 *result, u64 *memory, u64 *temp)
{
  u64 f0 = f[0U];
  u64 f1 = f[1U];
  u64 f2 = f[2U];
  u64 f3 = f[3U];
  u64 *o0 = result;
  u64 *o1 = result + (u32)1U;
  u64 *o2 = result + (u32)2U;
  u64 *o3 = result + (u32)3U;
  u64 *temp1 = temp;
  u64 h_0;
  u64 l;
  u64 c1;
  u64 h_1;
  u64 l1;
  u64 c2;
  u64 h_2;
  u64 l2;
  u64 c3;
  u64 temp0;
  mul64(f0, f0, o0, temp1);
  h_0 = temp1[0U];
  mul64(f0, f1, o1, temp1);
  l = o1[0U];
  memory[0U] = l;
  memory[1U] = temp1[0U];
  c1 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l, h_0, o1);
  h_1 = temp1[0U];
  mul64(f0, f2, o2, temp1);
  l1 = o2[0U];
  memory[2U] = l1;
  memory[3U] = temp1[0U];
  c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l1, h_1, o2);
  h_2 = temp1[0U];
  mul64(f0, f3, o3, temp1);
  l2 = o3[0U];
  memory[4U] = l2;
  memory[5U] = temp1[0U];
  c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l2, h_2, o3);
  temp0 = temp1[0U];
  return c3 + temp0;
}

static u64 sq1(u64 *f, u64 *f4, u64 *result, u64 *memory, u64 *tempBuffer)
{
  u64 *temp = tempBuffer;
  u64 *tempBufferResult = tempBuffer + (u32)1U;
  u64 f1 = f[1U];
  u64 f2 = f[2U];
  u64 f3 = f[3U];
  u64 *o0 = tempBufferResult;
  u64 *o1 = tempBufferResult + (u32)1U;
  u64 *o2 = tempBufferResult + (u32)2U;
  u64 *o3 = tempBufferResult + (u32)3U;
  u64 h_0;
  u64 l;
  u64 c1;
  u64 h_1;
  u64 l1;
  u64 c2;
  u64 h_2;
  u64 l2;
  u64 c3;
  u64 h_3;
  u64 c4;
  o0[0U] = memory[0U];
  h_0 = memory[1U];
  mul64(f1, f1, o1, temp);
  l = o1[0U];
  c1 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l, h_0, o1);
  h_1 = temp[0U];
  mul64(f1, f2, o2, temp);
  l1 = o2[0U];
  memory[6U] = l1;
  memory[7U] = temp[0U];
  c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l1, h_1, o2);
  h_2 = temp[0U];
  mul64(f1, f3, o3, temp);
  l2 = o3[0U];
  memory[8U] = l2;
  memory[9U] = temp[0U];
  c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l2, h_2, o3);
  h_3 = temp[0U];
  c4 = add4(tempBufferResult, f4, result);
  return c3 + h_3 + c4;
}

static u64 sq2(u64 *f, u64 *f4, u64 *result, u64 *memory, u64 *tempBuffer)
{
  u64 *temp = tempBuffer;
  u64 *tempBufferResult = tempBuffer + (u32)1U;
  u64 f2 = f[2U];
  u64 f3 = f[3U];
  u64 *o0 = tempBufferResult;
  u64 *o1 = tempBufferResult + (u32)1U;
  u64 *o2 = tempBufferResult + (u32)2U;
  u64 *o3 = tempBufferResult + (u32)3U;
  u64 h_0;
  u64 l;
  u64 c1;
  u64 h_1;
  u64 l1;
  u64 c2;
  u64 h_2;
  u64 l2;
  u64 c3;
  u64 h_3;
  u64 c4;
  o0[0U] = memory[2U];
  h_0 = memory[3U];
  o1[0U] = memory[6U];
  l = o1[0U];
  c1 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l, h_0, o1);
  h_1 = memory[7U];
  mul64(f2, f2, o2, temp);
  l1 = o2[0U];
  c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l1, h_1, o2);
  h_2 = temp[0U];
  mul64(f2, f3, o3, temp);
  l2 = o3[0U];
  memory[10U] = l2;
  memory[11U] = temp[0U];
  c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l2, h_2, o3);
  h_3 = temp[0U];
  c4 = add4(tempBufferResult, f4, result);
  return c3 + h_3 + c4;
}

static u64 sq3(u64 *f, u64 *f4, u64 *result, u64 *memory, u64 *tempBuffer)
{
  u64 *temp = tempBuffer;
  u64 *tempBufferResult = tempBuffer + (u32)1U;
  u64 f3 = f[3U];
  u64 *o0 = tempBufferResult;
  u64 *o1 = tempBufferResult + (u32)1U;
  u64 *o2 = tempBufferResult + (u32)2U;
  u64 *o3 = tempBufferResult + (u32)3U;
  u64 h;
  u64 l;
  u64 c1;
  u64 h1;
  u64 l1;
  u64 c2;
  u64 h2;
  u64 l2;
  u64 c3;
  u64 h_3;
  u64 c4;
  o0[0U] = memory[4U];
  h = memory[5U];
  o1[0U] = memory[8U];
  l = o1[0U];
  c1 = Lib_IntTypes_Intrinsics_add_carry_u64((u64)0U, l, h, o1);
  h1 = memory[9U];
  o2[0U] = memory[10U];
  l1 = o2[0U];
  c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l1, h1, o2);
  h2 = memory[11U];
  mul64(f3, f3, o3, temp);
  l2 = o3[0U];
  c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l2, h2, o3);
  h_3 = temp[0U];
  c4 = add4(tempBufferResult, f4, result);
  return c3 + h_3 + c4;
}

static void sq(u64 *f, u64 *out)
{
  u64 wb[25U] = { 0U };
  u64 *temp = wb;
  u64 *tb = wb + (u32)8U;
  u64 *memory = wb + (u32)13U;
  u64 *b0 = temp;
  u64 c0 = sq0(f, b0, memory, tb);
  u64 *b1;
  u64 c1;
  u64 *b2;
  u64 c2;
  u64 *b3;
  u64 c3;
  temp[4U] = c0;
  b1 = temp + (u32)1U;
  c1 = sq1(f, b1, b1, memory, tb);
  temp[5U] = c1;
  b2 = temp + (u32)2U;
  c2 = sq2(f, b2, b2, memory, tb);
  temp[6U] = c2;
  b3 = temp + (u32)3U;
  c3 = sq3(f, b3, b3, memory, tb);
  temp[7U] = c3;
  memcpy(out, temp, (u32)8U * sizeof (temp[0U]));
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

static void shortened_mul(u64 *a, u64 b, u64 *result)
{
  u64 *result04 = result;
  u64 c = mul1_il(a, b, result04);
  result[4U] = c;
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

static u64
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
  memcpy(t_low, a, (u32)4U * sizeof (a[0U]));
  {
    u64 tempRound[8U] = { 0U };
    u64 t20[8U] = { 0U };
    u64 t30[8U] = { 0U };
    u64 t10 = t[0U];
    u64 uu____0;
    shortened_mul(prime256_buffer, t10, t20);
    uu____0 = add8(t, t20, t30);
    shift8(t30, tempRound);
    {
      u64 t21[8U] = { 0U };
      u64 t31[8U] = { 0U };
      u64 t11 = tempRound[0U];
      u64 uu____1;
      shortened_mul(prime256_buffer, t11, t21);
      uu____1 = add8(tempRound, t21, t31);
      shift8(t31, round2);
      {
        u64 tempRound0[8U] = { 0U };
        u64 t2[8U] = { 0U };
        u64 t32[8U] = { 0U };
        u64 t12 = round2[0U];
        u64 uu____2;
        shortened_mul(prime256_buffer, t12, t2);
        uu____2 = add8(round2, t2, t32);
        shift8(t32, tempRound0);
        {
          u64 t22[8U] = { 0U };
          u64 t3[8U] = { 0U };
          u64 t1 = tempRound0[0U];
          u64 uu____3;
          shortened_mul(prime256_buffer, t1, t22);
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
  mul(a, b, t);
  {
    u64 tempRound[8U] = { 0U };
    u64 t20[8U] = { 0U };
    u64 t30[8U] = { 0U };
    u64 t10 = t[0U];
    u64 uu____0;
    shortened_mul(prime256_buffer, t10, t20);
    uu____0 = add8(t, t20, t30);
    shift8(t30, tempRound);
    {
      u64 t21[8U] = { 0U };
      u64 t31[8U] = { 0U };
      u64 t11 = tempRound[0U];
      u64 uu____1;
      shortened_mul(prime256_buffer, t11, t21);
      uu____1 = add8(tempRound, t21, t31);
      shift8(t31, round2);
      {
        u64 tempRound0[8U] = { 0U };
        u64 t2[8U] = { 0U };
        u64 t32[8U] = { 0U };
        u64 t12 = round2[0U];
        u64 uu____2;
        shortened_mul(prime256_buffer, t12, t2);
        uu____2 = add8(round2, t2, t32);
        shift8(t32, tempRound0);
        {
          u64 t22[8U] = { 0U };
          u64 t3[8U] = { 0U };
          u64 t1 = tempRound0[0U];
          u64 uu____3;
          shortened_mul(prime256_buffer, t1, t22);
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
    u64 uu____0;
    shortened_mul(prime256_buffer, t10, t20);
    uu____0 = add8(t, t20, t30);
    shift8(t30, tempRound);
    {
      u64 t21[8U] = { 0U };
      u64 t31[8U] = { 0U };
      u64 t11 = tempRound[0U];
      u64 uu____1;
      shortened_mul(prime256_buffer, t11, t21);
      uu____1 = add8(tempRound, t21, t31);
      shift8(t31, round2);
      {
        u64 tempRound0[8U] = { 0U };
        u64 t2[8U] = { 0U };
        u64 t32[8U] = { 0U };
        u64 t12 = round2[0U];
        u64 uu____2;
        shortened_mul(prime256_buffer, t12, t2);
        uu____2 = add8(round2, t2, t32);
        shift8(t32, tempRound0);
        {
          u64 t22[8U] = { 0U };
          u64 t3[8U] = { 0U };
          u64 t1 = tempRound0[0U];
          u64 uu____3;
          shortened_mul(prime256_buffer, t1, t22);
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

static void fsquarePowN(u32 n1, u64 *a)
{
  u32 i;
  for (i = (u32)0U; i < n1; i++)
    montgomery_multiplication_buffer(a, a, a);
}

static void fsquarePowNminusOne(u32 n1, u64 *a, u64 *b)
{
  u32 i;
  b[0U] = (u64)1U;
  b[1U] = (u64)18446744069414584320U;
  b[2U] = (u64)18446744073709551615U;
  b[3U] = (u64)4294967294U;
  for (i = (u32)0U; i < n1; i++)
  {
    montgomery_multiplication_buffer(b, a, b);
    montgomery_multiplication_buffer(a, a, a);
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
  memcpy(buffer_norm_1, a, (u32)4U * sizeof (a[0U]));
  buffer_a0 = buffer_norm_1;
  buffer_b0 = buffer_norm_1 + (u32)4U;
  fsquarePowNminusOne((u32)32U, buffer_a0, buffer_b0);
  fsquarePowN((u32)224U, buffer_b0);
  memcpy(buffer_result2, a, (u32)4U * sizeof (a[0U]));
  fsquarePowN((u32)192U, buffer_result2);
  memcpy(buffer_norm_3, a, (u32)4U * sizeof (a[0U]));
  buffer_a = buffer_norm_3;
  buffer_b = buffer_norm_3 + (u32)4U;
  fsquarePowNminusOne((u32)94U, buffer_a, buffer_b);
  fsquarePowN((u32)2U, buffer_b);
  montgomery_multiplication_buffer(buffer_result1, buffer_result2, buffer_result1);
  montgomery_multiplication_buffer(buffer_result1, buffer_result3, buffer_result1);
  montgomery_multiplication_buffer(buffer_result1, a, buffer_result1);
  memcpy(result, buffer_result1, (u32)4U * sizeof (buffer_result1[0U]));
}

static void quatre(u64 *a, u64 *result)
{
  montgomery_multiplication_buffer(a, a, result);
  montgomery_multiplication_buffer(result, result, result);
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

static void multByMinusThree(u64 *a, u64 *result)
{
  multByThree(a, result);
  {
    u64 zeros1[4U] = { 0U };
    p256_sub(zeros1, result, result);
  }
}

static u64 store_high_low_u(u32 high, u32 low)
{
  u64 as_uint64_high = (u64)high;
  u64 as_uint64_high1 = as_uint64_high << (u32)32U;
  u64 as_uint64_low = (u64)low;
  return as_uint64_low ^ as_uint64_high1;
}

static void
upl_zer_buffer(u32 c0, u32 c1, u32 c2, u32 c3, u32 c4, u32 c5, u32 c6, u32 c7, u64 *o)
{
  u64 b0 = store_high_low_u(c1, c0);
  u64 b1 = store_high_low_u(c3, c2);
  u64 b2 = store_high_low_u(c5, c4);
  u64 b3 = store_high_low_u(c7, c6);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  reduction_prime_2prime_impl(o, o);
}

static void upl_fir_buffer(u32 c11, u32 c12, u32 c13, u32 c14, u32 c15, u64 *o)
{
  u64 b0 = (u64)0U;
  u64 b1 = store_high_low_u(c11, (u32)0U);
  u64 b2 = store_high_low_u(c13, c12);
  u64 b3 = store_high_low_u(c15, c14);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  reduction_prime_2prime_impl(o, o);
}

static void upl_sec_buffer(u32 c12, u32 c13, u32 c14, u32 c15, u64 *o)
{
  u64 b0 = (u64)0U;
  u64 b1 = store_high_low_u(c12, (u32)0U);
  u64 b2 = store_high_low_u(c14, c13);
  u64 b3 = store_high_low_u((u32)0U, c15);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
}

static void upl_thi_buffer(u32 c8, u32 c9, u32 c10, u32 c14, u32 c15, u64 *o)
{
  u64 b0 = store_high_low_u(c9, c8);
  u64 b1 = store_high_low_u((u32)0U, c10);
  u64 b2 = (u64)0U;
  u64 b3 = store_high_low_u(c15, c14);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  reduction_prime_2prime_impl(o, o);
}

static void upl_for_buffer(u32 c8, u32 c9, u32 c10, u32 c11, u32 c13, u32 c14, u32 c15, u64 *o)
{
  u64 b0 = store_high_low_u(c10, c9);
  u64 b1 = store_high_low_u(c13, c11);
  u64 b2 = store_high_low_u(c15, c14);
  u64 b3 = store_high_low_u(c8, c13);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  reduction_prime_2prime_impl(o, o);
}

static void upl_fif_buffer(u32 c8, u32 c10, u32 c11, u32 c12, u32 c13, u64 *o)
{
  u64 b0 = store_high_low_u(c12, c11);
  u64 b1 = store_high_low_u((u32)0U, c13);
  u64 b2 = (u64)0U;
  u64 b3 = store_high_low_u(c10, c8);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  reduction_prime_2prime_impl(o, o);
}

static void upl_six_buffer(u32 c9, u32 c11, u32 c12, u32 c13, u32 c14, u32 c15, u64 *o)
{
  u64 b0 = store_high_low_u(c13, c12);
  u64 b1 = store_high_low_u(c15, c14);
  u64 b2 = (u64)0U;
  u64 b3 = store_high_low_u(c11, c9);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  reduction_prime_2prime_impl(o, o);
}

static void upl_sev_buffer(u32 c8, u32 c9, u32 c10, u32 c12, u32 c13, u32 c14, u32 c15, u64 *o)
{
  u64 b0 = store_high_low_u(c14, c13);
  u64 b1 = store_high_low_u(c8, c15);
  u64 b2 = store_high_low_u(c10, c9);
  u64 b3 = store_high_low_u(c12, (u32)0U);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  reduction_prime_2prime_impl(o, o);
}

static void upl_eig_buffer(u32 c9, u32 c10, u32 c11, u32 c13, u32 c14, u32 c15, u64 *o)
{
  u64 b0 = store_high_low_u(c15, c14);
  u64 b1 = store_high_low_u(c9, (u32)0U);
  u64 b2 = store_high_low_u(c11, c10);
  u64 b3 = store_high_low_u(c13, (u32)0U);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  reduction_prime_2prime_impl(o, o);
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
  u64 *t01;
  u64 *t11;
  u64 *t21;
  u64 *t31;
  u64 *t41;
  u64 *t51;
  u64 *t61;
  u64 *t71;
  u64 *t81;
  upl_zer_buffer(c0, c1, c2, c3, c4, c5, c6, c7, t010);
  upl_fir_buffer(c11, c12, c13, c14, c15, t110);
  upl_sec_buffer(c12, c13, c14, c15, t210);
  upl_thi_buffer(c8, c9, c10, c14, c15, t310);
  upl_for_buffer(c8, c9, c10, c11, c13, c14, c15, t410);
  upl_fif_buffer(c8, c10, c11, c12, c13, t510);
  upl_six_buffer(c9, c11, c12, c13, c14, c15, t610);
  upl_sev_buffer(c8, c9, c10, c12, c13, c14, c15, t710);
  upl_eig_buffer(c9, c10, c11, c13, c14, c15, t810);
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

static void point_double_compute_s_m(u64 *p, u64 *s1, u64 *m, u64 *tempBuffer)
{
  u64 *px = p;
  u64 *py = p + (u32)4U;
  u64 *pz = p + (u32)8U;
  u64 *yy = tempBuffer;
  u64 *xyy = tempBuffer + (u32)4U;
  u64 *zzzz = tempBuffer + (u32)8U;
  u64 *minThreeZzzz = tempBuffer + (u32)12U;
  u64 *xx = tempBuffer + (u32)16U;
  u64 *threeXx = tempBuffer + (u32)20U;
  montgomery_square_buffer(py, yy);
  montgomery_multiplication_buffer(px, yy, xyy);
  quatre(pz, zzzz);
  multByMinusThree(zzzz, minThreeZzzz);
  montgomery_square_buffer(px, xx);
  multByThree(xx, threeXx);
  p256_add(minThreeZzzz, threeXx, m);
  multByFour(xyy, s1);
}

static void
point_double_compute_y3(u64 *pY, u64 *y3, u64 *x3, u64 *s1, u64 *m, u64 *tempBuffer)
{
  u64 *yyyy = tempBuffer;
  u64 *eightYyyy = tempBuffer + (u32)4U;
  u64 *sx3 = tempBuffer + (u32)8U;
  u64 *msx3 = tempBuffer + (u32)12U;
  quatre(pY, yyyy);
  multByEight(yyyy, eightYyyy);
  p256_sub(s1, x3, sx3);
  montgomery_multiplication_buffer(m, sx3, msx3);
  p256_sub(msx3, eightYyyy, y3);
}

static void point_double(u64 *p, u64 *result, u64 *tempBuffer)
{
  u64 *s1 = tempBuffer;
  u64 *m = tempBuffer + (u32)4U;
  u64 *buffer_for_s_m = tempBuffer + (u32)8U;
  u64 *buffer_for_x3 = tempBuffer + (u32)32U;
  u64 *buffer_for_y3 = tempBuffer + (u32)40U;
  u64 *pypz = tempBuffer + (u32)56U;
  u64 *x3 = tempBuffer + (u32)60U;
  u64 *y3 = tempBuffer + (u32)64U;
  u64 *z3 = tempBuffer + (u32)68U;
  u64 *pY = p + (u32)4U;
  u64 *pZ = p + (u32)8U;
  u64 *twoS;
  u64 *mm;
  point_double_compute_s_m(p, s1, m, buffer_for_s_m);
  twoS = buffer_for_x3;
  mm = buffer_for_x3 + (u32)4U;
  multByTwo(s1, twoS);
  montgomery_square_buffer(m, mm);
  p256_sub(mm, twoS, x3);
  point_double_compute_y3(pY, y3, x3, s1, m, buffer_for_y3);
  montgomery_multiplication_buffer(pY, pZ, pypz);
  multByTwo(pypz, z3);
  memcpy(result, x3, (u32)4U * sizeof (x3[0U]));
  memcpy(result + (u32)4U, y3, (u32)4U * sizeof (y3[0U]));
  memcpy(result + (u32)8U, z3, (u32)4U * sizeof (z3[0U]));
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
  u64 *u11 = tempBuffer + (u32)16U;
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
  montgomery_multiplication_buffer(z2Square, pX, u11);
  montgomery_multiplication_buffer(z1Square, qX, u2);
  montgomery_multiplication_buffer(z2Cube, pY, s1);
  montgomery_multiplication_buffer(z1Cube, qY, s2);
  temp = tempBuffer16;
  p256_sub(u2, u11, h);
  p256_sub(s2, s1, r);
  montgomery_square_buffer(h, temp);
  montgomery_multiplication_buffer(temp, u11, uh);
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
  memcpy(result, x3_out1, (u32)4U * sizeof (x3_out1[0U]));
  memcpy(result + (u32)4U, y3_out1, (u32)4U * sizeof (y3_out1[0U]));
  memcpy(result + (u32)8U, z3_out1, (u32)4U * sizeof (z3_out1[0U]));
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

static void fromDomain(u64 *f, u64 *result)
{
  montgomery_multiplication_buffer_by_one(f, result);
}

static void copy_point(u64 *p, u64 *result)
{
  memcpy(result, p, (u32)12U * sizeof (p[0U]));
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
  montgomery_multiplication_buffer(zf, zf, z2f);
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
    fromDomain(z2f, resultX);
    fromDomain(z3f, resultY);
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
  montgomery_multiplication_buffer(zf, zf, z2f);
  exponent(z2f, z2f, tempBuffer20);
  montgomery_multiplication_buffer(z2f, xf, z2f);
  fromDomain(z2f, result);
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

static void scalarMultiplicationI(u64 *p, u64 *result, u8 *scalar, u64 *tempBuffer)
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

static void secretToPublicWithoutNorm(u64 *result, u8 *scalar, u64 *tempBuffer)
{
  u64 basePoint1[12U] = { 0U };
  u64 *q;
  u64 *buff;
  uploadBasePoint(basePoint1);
  q = tempBuffer;
  buff = tempBuffer + (u32)12U;
  zero_buffer(q);
  {
    u32 i;
    for (i = (u32)0U; i < (u32)256U; i++)
    {
      u32 bit0 = (u32)255U - i;
      u64 bit = (u64)(scalar[(u32)31U - bit0 / (u32)8U] >> bit0 % (u32)8U & (u8)1U);
      cswap(bit, q, basePoint1);
      point_add(q, basePoint1, basePoint1, buff);
      point_double(q, q, buff);
      cswap(bit, q, basePoint1);
    }
  }
  copy_point(q, result);
}

static u64
prime256order_buffer[4U] =
  {
    (u64)17562291160714782033U,
    (u64)13611842547513532036U,
    (u64)18446744073709551615U,
    (u64)18446744069414584320U
  };

static u8
order_inverse_buffer[32U] =
  {
    (u8)79U, (u8)37U, (u8)99U, (u8)252U, (u8)194U, (u8)202U, (u8)185U, (u8)243U, (u8)132U, (u8)158U,
    (u8)23U, (u8)167U, (u8)173U, (u8)250U, (u8)230U, (u8)188U, (u8)255U, (u8)255U, (u8)255U,
    (u8)255U, (u8)255U, (u8)255U, (u8)255U, (u8)255U, (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)255U,
    (u8)255U, (u8)255U, (u8)255U
  };

static u8
order_buffer[32U] =
  {
    (u8)255U, (u8)255U, (u8)255U, (u8)255U, (u8)0U, (u8)0U, (u8)0U, (u8)0U, (u8)255U, (u8)255U,
    (u8)255U, (u8)255U, (u8)255U, (u8)255U, (u8)255U, (u8)255U, (u8)188U, (u8)230U, (u8)250U,
    (u8)173U, (u8)167U, (u8)23U, (u8)158U, (u8)132U, (u8)243U, (u8)185U, (u8)202U, (u8)194U,
    (u8)252U, (u8)99U, (u8)37U, (u8)81U
  };

static void add8_without_carry1(u64 *t, u64 *t1, u64 *result)
{
  u64 uu____0 = add8(t, t1, result);
}

static void montgomery_multiplication_round(u64 *t, u64 *round, u64 k0)
{
  u64 temp = (u64)0U;
  u64 y = (u64)0U;
  u64 t2[8U] = { 0U };
  u64 t3[8U] = { 0U };
  u64 t1 = t[0U];
  u64 y_;
  mul64(t1, k0, &y, &temp);
  y_ = y;
  shortened_mul(prime256order_buffer, y_, t2);
  add8_without_carry1(t, t2, t3);
  shift8(t3, round);
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

static void reduction_prime_2prime_with_carry2(u64 cin, u64 *x, u64 *result)
{
  u64 tempBuffer[4U] = { 0U };
  u64 tempBufferForSubborrow = (u64)0U;
  u64 c = sub4_il(x, prime256order_buffer, tempBuffer);
  u64 carry = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, cin, (u64)0U, &tempBufferForSubborrow);
  cmovznz4(carry, tempBuffer, x, result);
}

static void reduction_prime_2prime_order(u64 *x, u64 *result)
{
  u64 tempBuffer[4U] = { 0U };
  u64 c = sub4_il(x, prime256order_buffer, tempBuffer);
  cmovznz4(c, tempBuffer, x, result);
}

static u64 upload_k0()
{
  return (u64)14758798090332847183U;
}

static void montgomery_multiplication_ecdsa_module(u64 *a, u64 *b, u64 *result)
{
  u64 t[8U] = { 0U };
  u64 round2[8U] = { 0U };
  u64 round4[8U] = { 0U };
  u64 prime_p256_orderBuffer[4U] = { 0U };
  u64 k0 = upload_k0();
  mul(a, b, t);
  montgomery_multiplication_round_twice(t, round2, k0);
  montgomery_multiplication_round_twice(round2, round4, k0);
  reduction_prime_2prime_with_carry(round4, result);
}

static void felem_add(u64 *arg1, u64 *arg2, u64 *out)
{
  u64 t = add4(arg1, arg2, out);
  reduction_prime_2prime_with_carry2(t, out, out);
}

static bool eq_u64_nCT(u64 a, u64 b)
{
  return a == b;
}

static bool eq_0_u64(u64 a)
{
  return eq_u64_nCT(a, (u64)0U);
}

static void changeEndian(u64 *i)
{
  u64 zero1 = i[0U];
  u64 one1 = i[1U];
  u64 two = i[2U];
  u64 three = i[3U];
  i[0U] = three;
  i[1U] = two;
  i[2U] = one1;
  i[3U] = zero1;
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

static void bufferToJac(u64 *p, u64 *result)
{
  u64 *partPoint = result;
  memcpy(partPoint, p, (u32)8U * sizeof (p[0U]));
  result[8U] = (u64)1U;
  result[9U] = (u64)0U;
  result[10U] = (u64)0U;
  result[11U] = (u64)0U;
}

static bool isPointAtInfinityPublic(u64 *p)
{
  u64 z0 = p[8U];
  u64 z1 = p[9U];
  u64 z2 = p[10U];
  u64 z3 = p[11U];
  bool z0_zero = eq_0_u64(z0);
  bool z1_zero = eq_0_u64(z1);
  bool z2_zero = eq_0_u64(z2);
  bool z3_zero = eq_0_u64(z3);
  return z0_zero && z1_zero && z2_zero && z3_zero;
}

static bool isPointOnCurvePublic(u64 *p)
{
  u64 y2Buffer[4U] = { 0U };
  u64 xBuffer[4U] = { 0U };
  u64 *x = p;
  u64 *y = p + (u32)4U;
  u64 multBuffer0[8U] = { 0U };
  shift_256_impl(y, multBuffer0);
  solinas_reduction_impl(multBuffer0, y2Buffer);
  montgomery_multiplication_buffer(y2Buffer, y2Buffer, y2Buffer);
  {
    u64 xToDomainBuffer[4U] = { 0U };
    u64 minusThreeXBuffer[4U] = { 0U };
    u64 p256_constant[4U] = { 0U };
    u64 multBuffer[8U] = { 0U };
    u64 r;
    bool z;
    shift_256_impl(x, multBuffer);
    solinas_reduction_impl(multBuffer, xToDomainBuffer);
    montgomery_multiplication_buffer(xToDomainBuffer, xToDomainBuffer, xBuffer);
    montgomery_multiplication_buffer(xBuffer, xToDomainBuffer, xBuffer);
    multByThree(xToDomainBuffer, minusThreeXBuffer);
    p256_sub(xBuffer, minusThreeXBuffer, xBuffer);
    p256_constant[0U] = (u64)15608596021259845087U;
    p256_constant[1U] = (u64)12461466548982526096U;
    p256_constant[2U] = (u64)16546823903870267094U;
    p256_constant[3U] = (u64)15866188208926050356U;
    p256_add(xBuffer, p256_constant, xBuffer);
    r = compare_felem(y2Buffer, xBuffer);
    z = !eq_0_u64(r);
    return z;
  }
}

static bool isCoordinateValid(u64 *p)
{
  u64 tempBuffer[4U] = { 0U };
  u64 *x = p;
  u64 *y = p + (u32)4U;
  u64 carryX = sub4_il(x, prime256_buffer, tempBuffer);
  u64 carryY = sub4_il(y, prime256_buffer, tempBuffer);
  bool lessX = eq_u64_nCT(carryX, (u64)1U);
  bool lessY = eq_u64_nCT(carryY, (u64)1U);
  return lessX && lessY;
}

static bool isOrderCorrect(u64 *p, u64 *tempBuffer)
{
  u64 multResult[12U] = { 0U };
  u64 pBuffer[12U] = { 0U };
  bool result;
  memcpy(pBuffer, p, (u32)12U * sizeof (p[0U]));
  scalarMultiplicationI(pBuffer, multResult, order_buffer, tempBuffer);
  result = isPointAtInfinityPublic(multResult);
  return result;
}

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
  memcpy(r, p, (u32)4U * sizeof (p[0U]));
}

static void fromDomainImpl(u64 *a, u64 *result)
{
  u64 one1[4U] = { 0U };
  uploadOneImpl(one1);
  montgomery_multiplication_ecdsa_module(one1, a, result);
}

static void multPowerPartial(u64 *a, u64 *b, u64 *result)
{
  u64 buffFromDB[4U] = { 0U };
  fromDomainImpl(b, buffFromDB);
  fromDomainImpl(buffFromDB, buffFromDB);
  montgomery_multiplication_ecdsa_module(a, buffFromDB, result);
}

static void ecdsa_signature_step12(u64 *hashAsFelem, u32 mLen, u8 *m)
{
  u8 mHash[32U] = { 0U };
  Hacl_Hash_SHA2_hash_256(m, mLen, mHash);
  toUint64ChangeEndian(mHash, hashAsFelem);
  reduction_prime_2prime_order(hashAsFelem, hashAsFelem);
}

static u64 ecdsa_signature_step45(u64 *x, u8 *k, u64 *tempBuffer)
{
  u64 result[12U] = { 0U };
  u64 *tempForNorm = tempBuffer;
  secretToPublicWithoutNorm(result, k, tempBuffer);
  normX(result, x, tempForNorm);
  reduction_prime_2prime_order(x, x);
  return isZero_uint64_CT(x);
}

static void ecdsa_signature_step6(u64 *result, u64 *kFelem, u64 *z, u64 *r, u64 *da)
{
  u64 rda[4U] = { 0U };
  u64 zBuffer[4U] = { 0U };
  u64 kInv[4U] = { 0U };
  montgomery_multiplication_ecdsa_module(r, da, rda);
  fromDomainImpl(z, zBuffer);
  felem_add(rda, zBuffer, zBuffer);
  memcpy(kInv, kFelem, (u32)4U * sizeof (kFelem[0U]));
  montgomery_ladder_exponent(kInv);
  montgomery_multiplication_ecdsa_module(zBuffer, kInv, result);
}

static u64 ecdsa_signature_core(u64 *r, u64 *s1, u32 mLen, u8 *m, u64 *privKeyAsFelem, u8 *k)
{
  u64 hashAsFelem[4U] = { 0U };
  u64 tempBuffer[100U] = { 0U };
  u64 kAsFelem[4U] = { 0U };
  u64 step5Flag;
  u64 sIsZero;
  toUint64ChangeEndian(k, kAsFelem);
  ecdsa_signature_step12(hashAsFelem, mLen, m);
  step5Flag = ecdsa_signature_step45(r, k, tempBuffer);
  ecdsa_signature_step6(s1, kAsFelem, hashAsFelem, r, privKeyAsFelem);
  sIsZero = isZero_uint64_CT(s1);
  return step5Flag | sIsZero;
}

static u64 ecdsa_signature(u8 *result, u32 mLen, u8 *m, u8 *privKey, u8 *k)
{
  u64 privKeyAsFelem[4U] = { 0U };
  u64 r[4U] = { 0U };
  u64 s1[4U] = { 0U };
  u8 *resultR = result;
  u8 *resultS = result + (u32)32U;
  u64 flag;
  toUint64ChangeEndian(privKey, privKeyAsFelem);
  flag = ecdsa_signature_core(r, s1, mLen, m, privKeyAsFelem, k);
  changeEndian(r);
  toUint8(r, resultR);
  changeEndian(s1);
  toUint8(s1, resultS);
  return flag;
}

static bool isMoreThanZeroLessThanOrderMinusOne(u64 *f)
{
  u64 tempBuffer[4U] = { 0U };
  u64 carry = sub4_il(f, prime256order_buffer, tempBuffer);
  bool less = eq_u64_nCT(carry, (u64)1U);
  u64 f0 = f[0U];
  u64 f1 = f[1U];
  u64 f2 = f[2U];
  u64 f3 = f[3U];
  bool z0_zero = eq_0_u64(f0);
  bool z1_zero = eq_0_u64(f1);
  bool z2_zero = eq_0_u64(f2);
  bool z3_zero = eq_0_u64(f3);
  bool more = z0_zero && z1_zero && z2_zero && z3_zero;
  return less && !more;
}

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
  return
    eq_u64_nCT(a_0,
      b_0)
    && eq_u64_nCT(a_1, b_1)
    && eq_u64_nCT(a_2, b_2)
    && eq_u64_nCT(a_3, b_3);
}

static bool
ecdsa_verification_core(
  u64 *publicKeyBuffer,
  u64 *hashAsFelem,
  u64 *r,
  u64 *s1,
  u32 mLen,
  u8 *m,
  u64 *xBuffer,
  u64 *tempBuffer
)
{
  u8 tempBufferU8[64U] = { 0U };
  u8 *bufferU1 = tempBufferU8;
  u8 *bufferU2 = tempBufferU8 + (u32)32U;
  u8 mHash[32U] = { 0U };
  Hacl_Hash_SHA2_hash_256(m, mLen, mHash);
  toUint64ChangeEndian(mHash, hashAsFelem);
  reduction_prime_2prime_order(hashAsFelem, hashAsFelem);
  {
    u64 tempBuffer1[12U] = { 0U };
    u64 *inverseS = tempBuffer1;
    u64 *u11 = tempBuffer1 + (u32)4U;
    u64 *u2 = tempBuffer1 + (u32)8U;
    fromDomainImpl(s1, inverseS);
    montgomery_ladder_exponent(inverseS);
    multPowerPartial(inverseS, hashAsFelem, u11);
    multPowerPartial(inverseS, r, u2);
    changeEndian(u11);
    changeEndian(u2);
    toUint8(u11, bufferU1);
    toUint8(u2, bufferU2);
    {
      u64 pointSum[12U] = { 0U };
      u64 points[24U] = { 0U };
      u64 *buff = tempBuffer + (u32)12U;
      u64 *pointU1G0 = points;
      u64 *pointU2Q0 = points + (u32)12U;
      u64 *pointU1G;
      u64 *pointU2Q;
      bool resultIsPAI;
      u64 *xCoordinateSum;
      bool r1;
      secretToPublicWithoutNorm(pointU1G0, bufferU1, tempBuffer);
      scalarMultiplicationWithoutNorm(publicKeyBuffer, pointU2Q0, bufferU2, tempBuffer);
      pointU1G = points;
      pointU2Q = points + (u32)12U;
      point_add(pointU1G, pointU2Q, pointSum, buff);
      norm(pointSum, pointSum, buff);
      resultIsPAI = isPointAtInfinityPublic(pointSum);
      xCoordinateSum = pointSum;
      memcpy(xBuffer, xCoordinateSum, (u32)4U * sizeof (xCoordinateSum[0U]));
      r1 = !resultIsPAI;
      return r1;
    }
  }
}

static bool ecdsa_verification_(u64 *pubKey, u64 *r, u64 *s1, u32 mLen, u8 *m)
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
    bool isSCorrect = isMoreThanZeroLessThanOrderMinusOne(s1);
    bool step1 = isRCorrect && isSCorrect;
    if (step1 == false)
      ite = false;
    else
    {
      bool
      state =
        ecdsa_verification_core(publicKeyBuffer,
          hashAsFelem,
          r,
          s1,
          mLen,
          m,
          xBuffer,
          tempBuffer);
      if (state == false)
        ite = false;
      else
      {
        bool result = compare_felem_bool(xBuffer, r);
        ite = result;
      }
    }
  }
  return ite;
}

static bool ecdsa_verification(u8 *pubKey, u8 *r, u8 *s1, u32 mLen, u8 *m)
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
  toUint64ChangeEndian(s1, sAsFelem);
  result = ecdsa_verification_(publicKeyAsFelem, rAsFelem, sAsFelem, mLen, m);
  return result;
}

u64 Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign(u8 *result, u32 mLen, u8 *m, u8 *privKey, u8 *k)
{
  return ecdsa_signature(result, mLen, m, privKey, k);
}

bool Hacl_Impl_ECDSA_ecdsa_p256_sha2_verify(u32 mLen, u8 *m, u8 *pubKey, u8 *r, u8 *s1)
{
  return ecdsa_verification(pubKey, r, s1, mLen, m);
}

