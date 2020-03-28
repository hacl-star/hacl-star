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

static uint64_t sub4_il(uint64_t *x, uint64_t *y, uint64_t *result)
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
  uint128_t res = (uint128_t)x * y;
  uint64_t l0 = (uint64_t)res;
  uint64_t h0 = (uint64_t)(res >> (uint32_t)64U);
  result[0U] = l0;
  temp[0U] = h0;
}

static void mult64_0(uint64_t *x, uint64_t u, uint64_t *result, uint64_t *temp)
{
  uint64_t f0 = x[0U];
  mul64(f0, u, result, temp);
}

static void mult64_0il(uint64_t *x, uint64_t u, uint64_t *result, uint64_t *temp)
{
  uint64_t f0 = x[0U];
  mul64(f0, u, result, temp);
}

static uint64_t
mult64_c(uint64_t x, uint64_t u, uint64_t cin, uint64_t *result, uint64_t *temp)
{
  uint64_t h = temp[0U];
  mul64(x, u, result, temp);
  uint64_t l = result[0U];
  return Lib_IntTypes_Intrinsics_add_carry_u64(cin, l, h, result);
}

static uint64_t mul1_il(uint64_t *f, uint64_t u, uint64_t *result)
{
  uint64_t temp = (uint64_t)0U;
  uint64_t f1 = f[1U];
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  uint64_t *o0 = result;
  uint64_t *o1 = result + (uint32_t)1U;
  uint64_t *o2 = result + (uint32_t)2U;
  uint64_t *o3 = result + (uint32_t)3U;
  mult64_0il(f, u, o0, &temp);
  uint64_t c1 = mult64_c(f1, u, (uint64_t)0U, o1, &temp);
  uint64_t c2 = mult64_c(f2, u, c1, o2, &temp);
  uint64_t c3 = mult64_c(f3, u, c2, o3, &temp);
  uint64_t temp0 = temp;
  return c3 + temp0;
}

static uint64_t mul1(uint64_t *f, uint64_t u, uint64_t *result)
{
  uint64_t temp = (uint64_t)0U;
  uint64_t f1 = f[1U];
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  uint64_t *o0 = result;
  uint64_t *o1 = result + (uint32_t)1U;
  uint64_t *o2 = result + (uint32_t)2U;
  uint64_t *o3 = result + (uint32_t)3U;
  mult64_0(f, u, o0, &temp);
  uint64_t c1 = mult64_c(f1, u, (uint64_t)0U, o1, &temp);
  uint64_t c2 = mult64_c(f2, u, c1, o2, &temp);
  uint64_t c3 = mult64_c(f3, u, c2, o3, &temp);
  uint64_t temp0 = temp;
  return c3 + temp0;
}

static uint64_t mul1_add(uint64_t *f1, uint64_t u2, uint64_t *f3, uint64_t *result)
{
  uint64_t temp[4U] = { 0U };
  uint64_t c = mul1(f1, u2, temp);
  uint64_t c3 = add4(temp, f3, result);
  return c + c3;
}

static void mul(uint64_t *f, uint64_t *r, uint64_t *out)
{
  uint64_t temp[8U] = { 0U };
  uint64_t f0 = f[0U];
  uint64_t f1 = f[1U];
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  uint64_t *b0 = temp;
  uint64_t c0 = mul1(r, f0, b0);
  temp[4U] = c0;
  uint64_t *b1 = temp + (uint32_t)1U;
  uint64_t c1 = mul1_add(r, f1, b1, b1);
  temp[5U] = c1;
  uint64_t *b2 = temp + (uint32_t)2U;
  uint64_t c2 = mul1_add(r, f2, b2, b2);
  temp[6U] = c2;
  uint64_t *b3 = temp + (uint32_t)3U;
  uint64_t c3 = mul1_add(r, f3, b3, b3);
  temp[7U] = c3;
  memcpy(out, temp, (uint32_t)8U * sizeof (temp[0U]));
}

static uint64_t sq0(uint64_t *f, uint64_t *result, uint64_t *memory, uint64_t *temp)
{
  uint64_t f0 = f[0U];
  uint64_t f1 = f[1U];
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  uint64_t *o0 = result;
  uint64_t *o1 = result + (uint32_t)1U;
  uint64_t *o2 = result + (uint32_t)2U;
  uint64_t *o3 = result + (uint32_t)3U;
  uint64_t *temp1 = temp;
  mul64(f0, f0, o0, temp1);
  uint64_t h_0 = temp1[0U];
  mul64(f0, f1, o1, temp1);
  uint64_t l = o1[0U];
  memory[0U] = l;
  memory[1U] = temp1[0U];
  uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h_0, o1);
  uint64_t h_1 = temp1[0U];
  mul64(f0, f2, o2, temp1);
  uint64_t l1 = o2[0U];
  memory[2U] = l1;
  memory[3U] = temp1[0U];
  uint64_t c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l1, h_1, o2);
  uint64_t h_2 = temp1[0U];
  mul64(f0, f3, o3, temp1);
  uint64_t l2 = o3[0U];
  memory[4U] = l2;
  memory[5U] = temp1[0U];
  uint64_t c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l2, h_2, o3);
  uint64_t temp0 = temp1[0U];
  return c3 + temp0;
}

static uint64_t
sq1(uint64_t *f, uint64_t *f4, uint64_t *result, uint64_t *memory, uint64_t *tempBuffer)
{
  uint64_t *temp = tempBuffer;
  uint64_t *tempBufferResult = tempBuffer + (uint32_t)1U;
  uint64_t f1 = f[1U];
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  uint64_t *o0 = tempBufferResult;
  uint64_t *o1 = tempBufferResult + (uint32_t)1U;
  uint64_t *o2 = tempBufferResult + (uint32_t)2U;
  uint64_t *o3 = tempBufferResult + (uint32_t)3U;
  o0[0U] = memory[0U];
  uint64_t h_0 = memory[1U];
  mul64(f1, f1, o1, temp);
  uint64_t l = o1[0U];
  uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h_0, o1);
  uint64_t h_1 = temp[0U];
  mul64(f1, f2, o2, temp);
  uint64_t l1 = o2[0U];
  memory[6U] = l1;
  memory[7U] = temp[0U];
  uint64_t c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l1, h_1, o2);
  uint64_t h_2 = temp[0U];
  mul64(f1, f3, o3, temp);
  uint64_t l2 = o3[0U];
  memory[8U] = l2;
  memory[9U] = temp[0U];
  uint64_t c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l2, h_2, o3);
  uint64_t h_3 = temp[0U];
  uint64_t c4 = add4(tempBufferResult, f4, result);
  return c3 + h_3 + c4;
}

static uint64_t
sq2(uint64_t *f, uint64_t *f4, uint64_t *result, uint64_t *memory, uint64_t *tempBuffer)
{
  uint64_t *temp = tempBuffer;
  uint64_t *tempBufferResult = tempBuffer + (uint32_t)1U;
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  uint64_t *o0 = tempBufferResult;
  uint64_t *o1 = tempBufferResult + (uint32_t)1U;
  uint64_t *o2 = tempBufferResult + (uint32_t)2U;
  uint64_t *o3 = tempBufferResult + (uint32_t)3U;
  o0[0U] = memory[2U];
  uint64_t h_0 = memory[3U];
  o1[0U] = memory[6U];
  uint64_t l = o1[0U];
  uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h_0, o1);
  uint64_t h_1 = memory[7U];
  mul64(f2, f2, o2, temp);
  uint64_t l1 = o2[0U];
  uint64_t c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l1, h_1, o2);
  uint64_t h_2 = temp[0U];
  mul64(f2, f3, o3, temp);
  uint64_t l2 = o3[0U];
  memory[10U] = l2;
  memory[11U] = temp[0U];
  uint64_t c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l2, h_2, o3);
  uint64_t h_3 = temp[0U];
  uint64_t c4 = add4(tempBufferResult, f4, result);
  return c3 + h_3 + c4;
}

static uint64_t
sq3(uint64_t *f, uint64_t *f4, uint64_t *result, uint64_t *memory, uint64_t *tempBuffer)
{
  uint64_t *temp = tempBuffer;
  uint64_t *tempBufferResult = tempBuffer + (uint32_t)1U;
  uint64_t f3 = f[3U];
  uint64_t *o0 = tempBufferResult;
  uint64_t *o1 = tempBufferResult + (uint32_t)1U;
  uint64_t *o2 = tempBufferResult + (uint32_t)2U;
  uint64_t *o3 = tempBufferResult + (uint32_t)3U;
  o0[0U] = memory[4U];
  uint64_t h = memory[5U];
  o1[0U] = memory[8U];
  uint64_t l = o1[0U];
  uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h, o1);
  uint64_t h1 = memory[9U];
  o2[0U] = memory[10U];
  uint64_t l1 = o2[0U];
  uint64_t c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l1, h1, o2);
  uint64_t h2 = memory[11U];
  mul64(f3, f3, o3, temp);
  uint64_t l2 = o3[0U];
  uint64_t c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l2, h2, o3);
  uint64_t h_3 = temp[0U];
  uint64_t c4 = add4(tempBufferResult, f4, result);
  return c3 + h_3 + c4;
}

static void sq(uint64_t *f, uint64_t *out)
{
  uint64_t wb[25U] = { 0U };
  uint64_t *temp = wb;
  uint64_t *tb = wb + (uint32_t)8U;
  uint64_t *memory = wb + (uint32_t)13U;
  uint64_t *b0 = temp;
  uint64_t c0 = sq0(f, b0, memory, tb);
  temp[4U] = c0;
  uint64_t *b1 = temp + (uint32_t)1U;
  uint64_t c1 = sq1(f, b1, b1, memory, tb);
  temp[5U] = c1;
  uint64_t *b2 = temp + (uint32_t)2U;
  uint64_t c2 = sq2(f, b2, b2, memory, tb);
  temp[6U] = c2;
  uint64_t *b3 = temp + (uint32_t)3U;
  uint64_t c3 = sq3(f, b3, b3, memory, tb);
  temp[7U] = c3;
  memcpy(out, temp, (uint32_t)8U * sizeof (temp[0U]));
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

static void shortened_mul(uint64_t *a, uint64_t b, uint64_t *result)
{
  uint64_t *result04 = result;
  uint64_t c = mul1_il(a, b, result04);
  result[4U] = c;
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

static void uploadOneImpl(uint64_t *f)
{
  f[0U] = (uint64_t)1U;
  f[1U] = (uint64_t)0U;
  f[2U] = (uint64_t)0U;
  f[3U] = (uint64_t)0U;
}

static void toUint8(uint64_t *i, uint8_t *o)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    store64_be(o + i0 * (uint32_t)8U, i[i0]);
  }
}

static uint64_t
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
  memcpy(t_low, a, (uint32_t)4U * sizeof (a[0U]));
  uint64_t tempRound[8U] = { 0U };
  uint64_t t20[8U] = { 0U };
  uint64_t t30[8U] = { 0U };
  uint64_t t10 = t[0U];
  shortened_mul(prime256_buffer, t10, t20);
  uint64_t uu____0 = add8(t, t20, t30);
  shift8(t30, tempRound);
  uint64_t t21[8U] = { 0U };
  uint64_t t31[8U] = { 0U };
  uint64_t t11 = tempRound[0U];
  shortened_mul(prime256_buffer, t11, t21);
  uint64_t uu____1 = add8(tempRound, t21, t31);
  shift8(t31, round2);
  uint64_t tempRound0[8U] = { 0U };
  uint64_t t2[8U] = { 0U };
  uint64_t t32[8U] = { 0U };
  uint64_t t12 = round2[0U];
  shortened_mul(prime256_buffer, t12, t2);
  uint64_t uu____2 = add8(round2, t2, t32);
  shift8(t32, tempRound0);
  uint64_t t22[8U] = { 0U };
  uint64_t t3[8U] = { 0U };
  uint64_t t1 = tempRound0[0U];
  shortened_mul(prime256_buffer, t1, t22);
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
  mul(a, b, t);
  uint64_t tempRound[8U] = { 0U };
  uint64_t t20[8U] = { 0U };
  uint64_t t30[8U] = { 0U };
  uint64_t t10 = t[0U];
  shortened_mul(prime256_buffer, t10, t20);
  uint64_t uu____0 = add8(t, t20, t30);
  shift8(t30, tempRound);
  uint64_t t21[8U] = { 0U };
  uint64_t t31[8U] = { 0U };
  uint64_t t11 = tempRound[0U];
  shortened_mul(prime256_buffer, t11, t21);
  uint64_t uu____1 = add8(tempRound, t21, t31);
  shift8(t31, round2);
  uint64_t tempRound0[8U] = { 0U };
  uint64_t t2[8U] = { 0U };
  uint64_t t32[8U] = { 0U };
  uint64_t t12 = round2[0U];
  shortened_mul(prime256_buffer, t12, t2);
  uint64_t uu____2 = add8(round2, t2, t32);
  shift8(t32, tempRound0);
  uint64_t t22[8U] = { 0U };
  uint64_t t3[8U] = { 0U };
  uint64_t t1 = tempRound0[0U];
  shortened_mul(prime256_buffer, t1, t22);
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
  shortened_mul(prime256_buffer, t10, t20);
  uint64_t uu____0 = add8(t, t20, t30);
  shift8(t30, tempRound);
  uint64_t t21[8U] = { 0U };
  uint64_t t31[8U] = { 0U };
  uint64_t t11 = tempRound[0U];
  shortened_mul(prime256_buffer, t11, t21);
  uint64_t uu____1 = add8(tempRound, t21, t31);
  shift8(t31, round2);
  uint64_t tempRound0[8U] = { 0U };
  uint64_t t2[8U] = { 0U };
  uint64_t t32[8U] = { 0U };
  uint64_t t12 = round2[0U];
  shortened_mul(prime256_buffer, t12, t2);
  uint64_t uu____2 = add8(round2, t2, t32);
  shift8(t32, tempRound0);
  uint64_t t22[8U] = { 0U };
  uint64_t t3[8U] = { 0U };
  uint64_t t1 = tempRound0[0U];
  shortened_mul(prime256_buffer, t1, t22);
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

static void fsquarePowN(uint32_t n1, uint64_t *a)
{
  for (uint32_t i = (uint32_t)0U; i < n1; i++)
  {
    montgomery_multiplication_buffer(a, a, a);
  }
}

static void fsquarePowNminusOne(uint32_t n1, uint64_t *a, uint64_t *b)
{
  b[0U] = (uint64_t)1U;
  b[1U] = (uint64_t)18446744069414584320U;
  b[2U] = (uint64_t)18446744073709551615U;
  b[3U] = (uint64_t)4294967294U;
  for (uint32_t i = (uint32_t)0U; i < n1; i++)
  {
    montgomery_multiplication_buffer(b, a, b);
    montgomery_multiplication_buffer(a, a, a);
  }
}

static void exponent(uint64_t *a, uint64_t *result, uint64_t *tempBuffer)
{
  uint64_t *buffer_norm_1 = tempBuffer;
  uint64_t *buffer_result1 = tempBuffer + (uint32_t)4U;
  uint64_t *buffer_result2 = tempBuffer + (uint32_t)8U;
  uint64_t *buffer_norm_3 = tempBuffer + (uint32_t)12U;
  uint64_t *buffer_result3 = tempBuffer + (uint32_t)16U;
  memcpy(buffer_norm_1, a, (uint32_t)4U * sizeof (a[0U]));
  uint64_t *buffer_a = buffer_norm_1;
  uint64_t *buffer_b0 = buffer_norm_1 + (uint32_t)4U;
  fsquarePowNminusOne((uint32_t)32U, buffer_a, buffer_b0);
  fsquarePowN((uint32_t)224U, buffer_b0);
  memcpy(buffer_result2, a, (uint32_t)4U * sizeof (a[0U]));
  fsquarePowN((uint32_t)192U, buffer_result2);
  memcpy(buffer_norm_3, a, (uint32_t)4U * sizeof (a[0U]));
  uint64_t *buffer_a0 = buffer_norm_3;
  uint64_t *buffer_b = buffer_norm_3 + (uint32_t)4U;
  fsquarePowNminusOne((uint32_t)94U, buffer_a0, buffer_b);
  fsquarePowN((uint32_t)2U, buffer_b);
  montgomery_multiplication_buffer(buffer_result1, buffer_result2, buffer_result1);
  montgomery_multiplication_buffer(buffer_result1, buffer_result3, buffer_result1);
  montgomery_multiplication_buffer(buffer_result1, a, buffer_result1);
  memcpy(result, buffer_result1, (uint32_t)4U * sizeof (buffer_result1[0U]));
}

static void quatre(uint64_t *a, uint64_t *result)
{
  montgomery_multiplication_buffer(a, a, result);
  montgomery_multiplication_buffer(result, result, result);
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

static void multByMinusThree(uint64_t *a, uint64_t *result)
{
  multByThree(a, result);
  uint64_t zeros1[4U] = { 0U };
  p256_sub(zeros1, result, result);
}

static uint64_t store_high_low_u(uint32_t high, uint32_t low)
{
  uint64_t as_uint64_high = (uint64_t)high;
  uint64_t as_uint64_high1 = as_uint64_high << (uint32_t)32U;
  uint64_t as_uint64_low = (uint64_t)low;
  return as_uint64_low ^ as_uint64_high1;
}

static void
upl_zer_buffer(
  uint32_t c0,
  uint32_t c1,
  uint32_t c2,
  uint32_t c3,
  uint32_t c4,
  uint32_t c5,
  uint32_t c6,
  uint32_t c7,
  uint64_t *o
)
{
  uint64_t b0 = store_high_low_u(c1, c0);
  uint64_t b1 = store_high_low_u(c3, c2);
  uint64_t b2 = store_high_low_u(c5, c4);
  uint64_t b3 = store_high_low_u(c7, c6);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  reduction_prime_2prime_impl(o, o);
}

static void
upl_fir_buffer(
  uint32_t c11,
  uint32_t c12,
  uint32_t c13,
  uint32_t c14,
  uint32_t c15,
  uint64_t *o
)
{
  uint64_t b0 = (uint64_t)0U;
  uint64_t b1 = store_high_low_u(c11, (uint32_t)0U);
  uint64_t b2 = store_high_low_u(c13, c12);
  uint64_t b3 = store_high_low_u(c15, c14);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  reduction_prime_2prime_impl(o, o);
}

static void upl_sec_buffer(uint32_t c12, uint32_t c13, uint32_t c14, uint32_t c15, uint64_t *o)
{
  uint64_t b0 = (uint64_t)0U;
  uint64_t b1 = store_high_low_u(c12, (uint32_t)0U);
  uint64_t b2 = store_high_low_u(c14, c13);
  uint64_t b3 = store_high_low_u((uint32_t)0U, c15);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
}

static void
upl_thi_buffer(uint32_t c8, uint32_t c9, uint32_t c10, uint32_t c14, uint32_t c15, uint64_t *o)
{
  uint64_t b0 = store_high_low_u(c9, c8);
  uint64_t b1 = store_high_low_u((uint32_t)0U, c10);
  uint64_t b2 = (uint64_t)0U;
  uint64_t b3 = store_high_low_u(c15, c14);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  reduction_prime_2prime_impl(o, o);
}

static void
upl_for_buffer(
  uint32_t c8,
  uint32_t c9,
  uint32_t c10,
  uint32_t c11,
  uint32_t c13,
  uint32_t c14,
  uint32_t c15,
  uint64_t *o
)
{
  uint64_t b0 = store_high_low_u(c10, c9);
  uint64_t b1 = store_high_low_u(c13, c11);
  uint64_t b2 = store_high_low_u(c15, c14);
  uint64_t b3 = store_high_low_u(c8, c13);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  reduction_prime_2prime_impl(o, o);
}

static void
upl_fif_buffer(
  uint32_t c8,
  uint32_t c10,
  uint32_t c11,
  uint32_t c12,
  uint32_t c13,
  uint64_t *o
)
{
  uint64_t b0 = store_high_low_u(c12, c11);
  uint64_t b1 = store_high_low_u((uint32_t)0U, c13);
  uint64_t b2 = (uint64_t)0U;
  uint64_t b3 = store_high_low_u(c10, c8);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  reduction_prime_2prime_impl(o, o);
}

static void
upl_six_buffer(
  uint32_t c9,
  uint32_t c11,
  uint32_t c12,
  uint32_t c13,
  uint32_t c14,
  uint32_t c15,
  uint64_t *o
)
{
  uint64_t b0 = store_high_low_u(c13, c12);
  uint64_t b1 = store_high_low_u(c15, c14);
  uint64_t b2 = (uint64_t)0U;
  uint64_t b3 = store_high_low_u(c11, c9);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  reduction_prime_2prime_impl(o, o);
}

static void
upl_sev_buffer(
  uint32_t c8,
  uint32_t c9,
  uint32_t c10,
  uint32_t c12,
  uint32_t c13,
  uint32_t c14,
  uint32_t c15,
  uint64_t *o
)
{
  uint64_t b0 = store_high_low_u(c14, c13);
  uint64_t b1 = store_high_low_u(c8, c15);
  uint64_t b2 = store_high_low_u(c10, c9);
  uint64_t b3 = store_high_low_u(c12, (uint32_t)0U);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  reduction_prime_2prime_impl(o, o);
}

static void
upl_eig_buffer(
  uint32_t c9,
  uint32_t c10,
  uint32_t c11,
  uint32_t c13,
  uint32_t c14,
  uint32_t c15,
  uint64_t *o
)
{
  uint64_t b0 = store_high_low_u(c15, c14);
  uint64_t b1 = store_high_low_u(c9, (uint32_t)0U);
  uint64_t b2 = store_high_low_u(c11, c10);
  uint64_t b3 = store_high_low_u(c13, (uint32_t)0U);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  reduction_prime_2prime_impl(o, o);
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
  upl_zer_buffer(c0, c1, c2, c3, c4, c5, c6, c7, t01);
  upl_fir_buffer(c11, c12, c13, c14, c15, t110);
  upl_sec_buffer(c12, c13, c14, c15, t210);
  upl_thi_buffer(c8, c9, c10, c14, c15, t310);
  upl_for_buffer(c8, c9, c10, c11, c13, c14, c15, t410);
  upl_fif_buffer(c8, c10, c11, c12, c13, t510);
  upl_six_buffer(c9, c11, c12, c13, c14, c15, t610);
  upl_sev_buffer(c8, c9, c10, c12, c13, c14, c15, t710);
  upl_eig_buffer(c9, c10, c11, c13, c14, c15, t810);
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
point_double_compute_s_m(uint64_t *p, uint64_t *s1, uint64_t *m, uint64_t *tempBuffer)
{
  uint64_t *px = p;
  uint64_t *py = p + (uint32_t)4U;
  uint64_t *pz = p + (uint32_t)8U;
  uint64_t *yy = tempBuffer;
  uint64_t *xyy = tempBuffer + (uint32_t)4U;
  uint64_t *zzzz = tempBuffer + (uint32_t)8U;
  uint64_t *minThreeZzzz = tempBuffer + (uint32_t)12U;
  uint64_t *xx = tempBuffer + (uint32_t)16U;
  uint64_t *threeXx = tempBuffer + (uint32_t)20U;
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
point_double_compute_y3(
  uint64_t *pY,
  uint64_t *y3,
  uint64_t *x3,
  uint64_t *s1,
  uint64_t *m,
  uint64_t *tempBuffer
)
{
  uint64_t *yyyy = tempBuffer;
  uint64_t *eightYyyy = tempBuffer + (uint32_t)4U;
  uint64_t *sx3 = tempBuffer + (uint32_t)8U;
  uint64_t *msx3 = tempBuffer + (uint32_t)12U;
  quatre(pY, yyyy);
  multByEight(yyyy, eightYyyy);
  p256_sub(s1, x3, sx3);
  montgomery_multiplication_buffer(m, sx3, msx3);
  p256_sub(msx3, eightYyyy, y3);
}

static void point_double(uint64_t *p, uint64_t *result, uint64_t *tempBuffer)
{
  uint64_t *s1 = tempBuffer;
  uint64_t *m = tempBuffer + (uint32_t)4U;
  uint64_t *buffer_for_s_m = tempBuffer + (uint32_t)8U;
  uint64_t *buffer_for_x3 = tempBuffer + (uint32_t)32U;
  uint64_t *buffer_for_y3 = tempBuffer + (uint32_t)40U;
  uint64_t *pypz = tempBuffer + (uint32_t)56U;
  uint64_t *x3 = tempBuffer + (uint32_t)60U;
  uint64_t *y3 = tempBuffer + (uint32_t)64U;
  uint64_t *z3 = tempBuffer + (uint32_t)68U;
  uint64_t *pY = p + (uint32_t)4U;
  uint64_t *pZ = p + (uint32_t)8U;
  point_double_compute_s_m(p, s1, m, buffer_for_s_m);
  uint64_t *twoS = buffer_for_x3;
  uint64_t *mm = buffer_for_x3 + (uint32_t)4U;
  multByTwo(s1, twoS);
  montgomery_square_buffer(m, mm);
  p256_sub(mm, twoS, x3);
  point_double_compute_y3(pY, y3, x3, s1, m, buffer_for_y3);
  montgomery_multiplication_buffer(pY, pZ, pypz);
  multByTwo(pypz, z3);
  memcpy(result, x3, (uint32_t)4U * sizeof (x3[0U]));
  memcpy(result + (uint32_t)4U, y3, (uint32_t)4U * sizeof (y3[0U]));
  memcpy(result + (uint32_t)8U, z3, (uint32_t)4U * sizeof (z3[0U]));
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
  uint64_t *u11 = tempBuffer + (uint32_t)16U;
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
  montgomery_multiplication_buffer(z2Square, pX, u11);
  montgomery_multiplication_buffer(z1Square, qX, u2);
  montgomery_multiplication_buffer(z2Cube, pY, s1);
  montgomery_multiplication_buffer(z1Cube, qY, s2);
  uint64_t *temp = tempBuffer16;
  p256_sub(u2, u11, h);
  p256_sub(s2, s1, r);
  montgomery_square_buffer(h, temp);
  montgomery_multiplication_buffer(temp, u11, uh);
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
  memcpy(result, x3_out1, (uint32_t)4U * sizeof (x3_out1[0U]));
  memcpy(result + (uint32_t)4U, y3_out1, (uint32_t)4U * sizeof (y3_out1[0U]));
  memcpy(result + (uint32_t)8U, z3_out1, (uint32_t)4U * sizeof (z3_out1[0U]));
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

static void fromDomain(uint64_t *f, uint64_t *result)
{
  montgomery_multiplication_buffer_by_one(f, result);
}

static void copy_point(uint64_t *p, uint64_t *result)
{
  memcpy(result, p, (uint32_t)12U * sizeof (p[0U]));
}

static uint64_t isPointAtInfinityPrivate(uint64_t *p)
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
  montgomery_multiplication_buffer(zf, zf, z2f);
  montgomery_multiplication_buffer(z2f, zf, z3f);
  exponent(z2f, z2f, tempBuffer20);
  exponent(z3f, z3f, tempBuffer20);
  montgomery_multiplication_buffer(xf, z2f, z2f);
  montgomery_multiplication_buffer(yf, z3f, z3f);
  uint64_t zeroBuffer[4U] = { 0U };
  uint64_t *resultX = resultPoint;
  uint64_t *resultY = resultPoint + (uint32_t)4U;
  uint64_t *resultZ = resultPoint + (uint32_t)8U;
  uint64_t bit = isPointAtInfinityPrivate(p);
  fromDomain(z2f, resultX);
  fromDomain(z3f, resultY);
  uploadOneImpl(resultZ);
  copy_conditional(resultZ, zeroBuffer, bit);
}

static void normX(uint64_t *p, uint64_t *result, uint64_t *tempBuffer)
{
  uint64_t *xf = p;
  uint64_t *zf = p + (uint32_t)8U;
  uint64_t *z2f = tempBuffer + (uint32_t)4U;
  uint64_t *tempBuffer20 = tempBuffer + (uint32_t)12U;
  montgomery_multiplication_buffer(zf, zf, z2f);
  exponent(z2f, z2f, tempBuffer20);
  montgomery_multiplication_buffer(z2f, xf, z2f);
  fromDomain(z2f, result);
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
scalarMultiplicationI(uint64_t *p, uint64_t *result, uint8_t *scalar, uint64_t *tempBuffer)
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

static void secretToPublic(uint64_t *result, uint8_t *scalar, uint64_t *tempBuffer)
{
  uint64_t basePoint1[12U] = { 0U };
  uploadBasePoint(basePoint1);
  uint64_t *q = tempBuffer;
  uint64_t *buff = tempBuffer + (uint32_t)12U;
  zero_buffer(q);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)256U; i++)
  {
    uint32_t bit0 = (uint32_t)255U - i;
    uint64_t
    bit =
      (uint64_t)(scalar[(uint32_t)31U - bit0 / (uint32_t)8U] >> bit0 % (uint32_t)8U & (uint8_t)1U);
    cswap(bit, q, basePoint1);
    point_add(q, basePoint1, basePoint1, buff);
    point_double(q, q, buff);
    cswap(bit, q, basePoint1);
  }
  norm(q, result, buff);
}

static void secretToPublicWithoutNorm(uint64_t *result, uint8_t *scalar, uint64_t *tempBuffer)
{
  uint64_t basePoint1[12U] = { 0U };
  uploadBasePoint(basePoint1);
  uint64_t *q = tempBuffer;
  uint64_t *buff = tempBuffer + (uint32_t)12U;
  zero_buffer(q);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)256U; i++)
  {
    uint32_t bit0 = (uint32_t)255U - i;
    uint64_t
    bit =
      (uint64_t)(scalar[(uint32_t)31U - bit0 / (uint32_t)8U] >> bit0 % (uint32_t)8U & (uint8_t)1U);
    cswap(bit, q, basePoint1);
    point_add(q, basePoint1, basePoint1, buff);
    point_double(q, q, buff);
    cswap(bit, q, basePoint1);
  }
  copy_point(q, result);
}

static uint64_t
prime256order_buffer[4U] =
  {
    (uint64_t)17562291160714782033U,
    (uint64_t)13611842547513532036U,
    (uint64_t)18446744073709551615U,
    (uint64_t)18446744069414584320U
  };

static uint8_t
order_inverse_buffer[32U] =
  {
    (uint8_t)79U, (uint8_t)37U, (uint8_t)99U, (uint8_t)252U, (uint8_t)194U, (uint8_t)202U,
    (uint8_t)185U, (uint8_t)243U, (uint8_t)132U, (uint8_t)158U, (uint8_t)23U, (uint8_t)167U,
    (uint8_t)173U, (uint8_t)250U, (uint8_t)230U, (uint8_t)188U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U
  };

static uint8_t
order_buffer[32U] =
  {
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)188U, (uint8_t)230U,
    (uint8_t)250U, (uint8_t)173U, (uint8_t)167U, (uint8_t)23U, (uint8_t)158U, (uint8_t)132U,
    (uint8_t)243U, (uint8_t)185U, (uint8_t)202U, (uint8_t)194U, (uint8_t)252U, (uint8_t)99U,
    (uint8_t)37U, (uint8_t)81U
  };

static void add8_without_carry1(uint64_t *t, uint64_t *t1, uint64_t *result)
{
  uint64_t uu____0 = add8(t, t1, result);
}

static void montgomery_multiplication_round(uint64_t *t, uint64_t *round, uint64_t k0)
{
  uint64_t temp = (uint64_t)0U;
  uint64_t y = (uint64_t)0U;
  uint64_t t2[8U] = { 0U };
  uint64_t t3[8U] = { 0U };
  uint64_t t1 = t[0U];
  mul64(t1, k0, &y, &temp);
  uint64_t y_ = y;
  shortened_mul(prime256order_buffer, y_, t2);
  add8_without_carry1(t, t2, t3);
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

static void reduction_prime_2prime_with_carry2(uint64_t cin, uint64_t *x, uint64_t *result)
{
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t c = sub4_il(x, prime256order_buffer, tempBuffer);
  uint64_t
  carry = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, cin, (uint64_t)0U, &tempBufferForSubborrow);
  cmovznz4(carry, tempBuffer, x, result);
}

static void reduction_prime_2prime_order(uint64_t *x, uint64_t *result)
{
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t c = sub4_il(x, prime256order_buffer, tempBuffer);
  cmovznz4(c, tempBuffer, x, result);
}

static uint64_t upload_k0()
{
  return (uint64_t)14758798090332847183U;
}

static void montgomery_multiplication_ecdsa_module(uint64_t *a, uint64_t *b, uint64_t *result)
{
  uint64_t t[8U] = { 0U };
  uint64_t round2[8U] = { 0U };
  uint64_t round4[8U] = { 0U };
  uint64_t prime_p256_orderBuffer[4U] = { 0U };
  uint64_t k0 = upload_k0();
  mul(a, b, t);
  montgomery_multiplication_round_twice(t, round2, k0);
  montgomery_multiplication_round_twice(round2, round4, k0);
  reduction_prime_2prime_with_carry(round4, result);
}

static void felem_add(uint64_t *arg1, uint64_t *arg2, uint64_t *out)
{
  uint64_t t = add4(arg1, arg2, out);
  reduction_prime_2prime_with_carry2(t, out, out);
}

static bool eq_u64_nCT(uint64_t a, uint64_t b)
{
  return a == b;
}

static bool eq_0_u64(uint64_t a)
{
  return eq_u64_nCT(a, (uint64_t)0U);
}

static void changeEndian(uint64_t *i)
{
  uint64_t zero1 = i[0U];
  uint64_t one1 = i[1U];
  uint64_t two = i[2U];
  uint64_t three = i[3U];
  i[0U] = three;
  i[1U] = two;
  i[2U] = one1;
  i[3U] = zero1;
}

static void toUint64ChangeEndian(uint8_t *i, uint64_t *o)
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
  changeEndian(o);
}

static void bufferToJac(uint64_t *p, uint64_t *result)
{
  uint64_t *partPoint = result;
  memcpy(partPoint, p, (uint32_t)8U * sizeof (p[0U]));
  result[8U] = (uint64_t)1U;
  result[9U] = (uint64_t)0U;
  result[10U] = (uint64_t)0U;
  result[11U] = (uint64_t)0U;
}

static bool isPointAtInfinityPublic(uint64_t *p)
{
  uint64_t z0 = p[8U];
  uint64_t z1 = p[9U];
  uint64_t z2 = p[10U];
  uint64_t z3 = p[11U];
  bool z0_zero = eq_0_u64(z0);
  bool z1_zero = eq_0_u64(z1);
  bool z2_zero = eq_0_u64(z2);
  bool z3_zero = eq_0_u64(z3);
  return z0_zero && z1_zero && z2_zero && z3_zero;
}

static bool isPointOnCurvePublic(uint64_t *p)
{
  uint64_t y2Buffer[4U] = { 0U };
  uint64_t xBuffer[4U] = { 0U };
  uint64_t *x = p;
  uint64_t *y = p + (uint32_t)4U;
  uint64_t multBuffer0[8U] = { 0U };
  shift_256_impl(y, multBuffer0);
  solinas_reduction_impl(multBuffer0, y2Buffer);
  montgomery_multiplication_buffer(y2Buffer, y2Buffer, y2Buffer);
  uint64_t xToDomainBuffer[4U] = { 0U };
  uint64_t minusThreeXBuffer[4U] = { 0U };
  uint64_t p256_constant[4U] = { 0U };
  uint64_t multBuffer[8U] = { 0U };
  shift_256_impl(x, multBuffer);
  solinas_reduction_impl(multBuffer, xToDomainBuffer);
  montgomery_multiplication_buffer(xToDomainBuffer, xToDomainBuffer, xBuffer);
  montgomery_multiplication_buffer(xBuffer, xToDomainBuffer, xBuffer);
  multByThree(xToDomainBuffer, minusThreeXBuffer);
  p256_sub(xBuffer, minusThreeXBuffer, xBuffer);
  p256_constant[0U] = (uint64_t)15608596021259845087U;
  p256_constant[1U] = (uint64_t)12461466548982526096U;
  p256_constant[2U] = (uint64_t)16546823903870267094U;
  p256_constant[3U] = (uint64_t)15866188208926050356U;
  p256_add(xBuffer, p256_constant, xBuffer);
  uint64_t r = compare_felem(y2Buffer, xBuffer);
  bool z = !eq_0_u64(r);
  return z;
}

static bool isCoordinateValid(uint64_t *p)
{
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t *x = p;
  uint64_t *y = p + (uint32_t)4U;
  uint64_t carryX = sub4_il(x, prime256_buffer, tempBuffer);
  uint64_t carryY = sub4_il(y, prime256_buffer, tempBuffer);
  bool lessX = eq_u64_nCT(carryX, (uint64_t)1U);
  bool lessY = eq_u64_nCT(carryY, (uint64_t)1U);
  return lessX && lessY;
}

static bool isOrderCorrect(uint64_t *p, uint64_t *tempBuffer)
{
  uint64_t multResult[12U] = { 0U };
  uint64_t pBuffer[12U] = { 0U };
  memcpy(pBuffer, p, (uint32_t)12U * sizeof (p[0U]));
  scalarMultiplicationI(pBuffer, multResult, order_buffer, tempBuffer);
  bool result = isPointAtInfinityPublic(multResult);
  return result;
}

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

uint64_t Hacl_Impl_P256_DH_ecp256dh_i(uint8_t *result, uint8_t *scalar)
{
  uint64_t tempBuffer[100U] = { 0U };
  uint64_t resultBuffer[12U] = { 0U };
  uint64_t *resultBufferX = resultBuffer;
  uint64_t *resultBufferY = resultBuffer + (uint32_t)4U;
  uint8_t *resultX = result;
  uint8_t *resultY = result + (uint32_t)32U;
  secretToPublic(resultBuffer, scalar, tempBuffer);
  uint64_t flag = isPointAtInfinityPrivate(resultBuffer);
  changeEndian(resultBufferX);
  changeEndian(resultBufferY);
  toUint8(resultBufferX, resultX);
  toUint8(resultBufferY, resultY);
  return flag;
}

static uint64_t _ecp256dh_r(uint64_t *result, uint64_t *pubKey, uint8_t *scalar)
{
  uint64_t tempBuffer[100U] = { 0U };
  uint64_t publicKeyBuffer[12U] = { 0U };
  bufferToJac(pubKey, publicKeyBuffer);
  bool publicKeyCorrect = verifyQValidCurvePoint(publicKeyBuffer, tempBuffer);
  if (publicKeyCorrect)
  {
    scalarMultiplicationL(publicKeyBuffer, result, scalar, tempBuffer);
    uint64_t flag = isPointAtInfinityPrivate(result);
    return flag;
  }
  return (uint64_t)18446744073709551615U;
}

uint64_t Hacl_Impl_P256_DH_ecp256dh_r(uint8_t *result, uint8_t *pubKey, uint8_t *scalar)
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
  toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  uint64_t flag = _ecp256dh_r(resultBufferFelem, publicKeyAsFelem, scalar);
  changeEndian(resultBufferFelemX);
  changeEndian(resultBufferFelemY);
  toUint8(resultBufferFelemX, resultX);
  toUint8(resultBufferFelemY, resultY);
  return flag;
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
  memcpy(r, p, (uint32_t)4U * sizeof (p[0U]));
}

static void fromDomainImpl(uint64_t *a, uint64_t *result)
{
  uint64_t one1[4U] = { 0U };
  uploadOneImpl(one1);
  montgomery_multiplication_ecdsa_module(one1, a, result);
}

static void multPowerPartial(uint64_t *a, uint64_t *b, uint64_t *result)
{
  uint64_t buffFromDB[4U] = { 0U };
  fromDomainImpl(b, buffFromDB);
  fromDomainImpl(buffFromDB, buffFromDB);
  montgomery_multiplication_ecdsa_module(a, buffFromDB, result);
}

static void ecdsa_signature_step12(uint64_t *hashAsFelem, uint32_t mLen, uint8_t *m)
{
  uint8_t mHash[32U] = { 0U };
  Hacl_Hash_SHA2_hash_256(m, mLen, mHash);
  toUint64ChangeEndian(mHash, hashAsFelem);
  reduction_prime_2prime_order(hashAsFelem, hashAsFelem);
}

static uint64_t ecdsa_signature_step45(uint64_t *x, uint8_t *k, uint64_t *tempBuffer)
{
  uint64_t result[12U] = { 0U };
  uint64_t *tempForNorm = tempBuffer;
  secretToPublicWithoutNorm(result, k, tempBuffer);
  normX(result, x, tempForNorm);
  reduction_prime_2prime_order(x, x);
  return isZero_uint64_CT(x);
}

static void
ecdsa_signature_step6(
  uint64_t *result,
  uint64_t *kFelem,
  uint64_t *z,
  uint64_t *r,
  uint64_t *da
)
{
  uint64_t rda[4U] = { 0U };
  uint64_t zBuffer[4U] = { 0U };
  uint64_t kInv[4U] = { 0U };
  montgomery_multiplication_ecdsa_module(r, da, rda);
  fromDomainImpl(z, zBuffer);
  felem_add(rda, zBuffer, zBuffer);
  memcpy(kInv, kFelem, (uint32_t)4U * sizeof (kFelem[0U]));
  montgomery_ladder_exponent(kInv);
  montgomery_multiplication_ecdsa_module(zBuffer, kInv, result);
}

static uint64_t
ecdsa_signature_core(
  uint64_t *r,
  uint64_t *s1,
  uint32_t mLen,
  uint8_t *m,
  uint64_t *privKeyAsFelem,
  uint8_t *k
)
{
  uint64_t hashAsFelem[4U] = { 0U };
  uint64_t tempBuffer[100U] = { 0U };
  uint64_t kAsFelem[4U] = { 0U };
  toUint64ChangeEndian(k, kAsFelem);
  ecdsa_signature_step12(hashAsFelem, mLen, m);
  uint64_t step5Flag = ecdsa_signature_step45(r, k, tempBuffer);
  ecdsa_signature_step6(s1, kAsFelem, hashAsFelem, r, privKeyAsFelem);
  uint64_t sIsZero = isZero_uint64_CT(s1);
  return step5Flag | sIsZero;
}

static uint64_t
ecdsa_signature(uint8_t *result, uint32_t mLen, uint8_t *m, uint8_t *privKey, uint8_t *k)
{
  uint64_t privKeyAsFelem[4U] = { 0U };
  uint64_t r[4U] = { 0U };
  uint64_t s1[4U] = { 0U };
  uint8_t *resultR = result;
  uint8_t *resultS = result + (uint32_t)32U;
  toUint64ChangeEndian(privKey, privKeyAsFelem);
  uint64_t flag = ecdsa_signature_core(r, s1, mLen, m, privKeyAsFelem, k);
  changeEndian(r);
  toUint8(r, resultR);
  changeEndian(s1);
  toUint8(s1, resultS);
  return flag;
}

static bool isMoreThanZeroLessThanOrderMinusOne(uint64_t *f)
{
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t carry = sub4_il(f, prime256order_buffer, tempBuffer);
  bool less = eq_u64_nCT(carry, (uint64_t)1U);
  uint64_t f0 = f[0U];
  uint64_t f1 = f[1U];
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  bool z0_zero = eq_0_u64(f0);
  bool z1_zero = eq_0_u64(f1);
  bool z2_zero = eq_0_u64(f2);
  bool z3_zero = eq_0_u64(f3);
  bool more = z0_zero && z1_zero && z2_zero && z3_zero;
  return less && !more;
}

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
  return
    eq_u64_nCT(a_0,
      b_0)
    && eq_u64_nCT(a_1, b_1)
    && eq_u64_nCT(a_2, b_2)
    && eq_u64_nCT(a_3, b_3);
}

static bool
ecdsa_verification_core(
  uint64_t *publicKeyBuffer,
  uint64_t *hashAsFelem,
  uint64_t *r,
  uint64_t *s1,
  uint32_t mLen,
  uint8_t *m,
  uint64_t *xBuffer,
  uint64_t *tempBuffer
)
{
  uint8_t tempBufferU8[64U] = { 0U };
  uint8_t *bufferU1 = tempBufferU8;
  uint8_t *bufferU2 = tempBufferU8 + (uint32_t)32U;
  uint8_t mHash[32U] = { 0U };
  Hacl_Hash_SHA2_hash_256(m, mLen, mHash);
  toUint64ChangeEndian(mHash, hashAsFelem);
  reduction_prime_2prime_order(hashAsFelem, hashAsFelem);
  uint64_t tempBuffer1[12U] = { 0U };
  uint64_t *inverseS = tempBuffer1;
  uint64_t *u11 = tempBuffer1 + (uint32_t)4U;
  uint64_t *u2 = tempBuffer1 + (uint32_t)8U;
  fromDomainImpl(s1, inverseS);
  montgomery_ladder_exponent(inverseS);
  multPowerPartial(inverseS, hashAsFelem, u11);
  multPowerPartial(inverseS, r, u2);
  changeEndian(u11);
  changeEndian(u2);
  toUint8(u11, bufferU1);
  toUint8(u2, bufferU2);
  uint64_t pointSum[12U] = { 0U };
  uint64_t points[24U] = { 0U };
  uint64_t *buff = tempBuffer + (uint32_t)12U;
  uint64_t *pointU1G = points;
  uint64_t *pointU2Q0 = points + (uint32_t)12U;
  secretToPublicWithoutNorm(pointU1G, bufferU1, tempBuffer);
  scalarMultiplicationWithoutNorm(publicKeyBuffer, pointU2Q0, bufferU2, tempBuffer);
  uint64_t *pointU1G0 = points;
  uint64_t *pointU2Q = points + (uint32_t)12U;
  point_add(pointU1G0, pointU2Q, pointSum, buff);
  norm(pointSum, pointSum, buff);
  bool resultIsPAI = isPointAtInfinityPublic(pointSum);
  uint64_t *xCoordinateSum = pointSum;
  memcpy(xBuffer, xCoordinateSum, (uint32_t)4U * sizeof (xCoordinateSum[0U]));
  bool r1 = !resultIsPAI;
  return r1;
}

static bool
ecdsa_verification_(uint64_t *pubKey, uint64_t *r, uint64_t *s1, uint32_t mLen, uint8_t *m)
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
  bool isSCorrect = isMoreThanZeroLessThanOrderMinusOne(s1);
  bool step1 = isRCorrect && isSCorrect;
  if (step1 == false)
  {
    return false;
  }
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
  {
    return false;
  }
  bool result = compare_felem_bool(xBuffer, r);
  return result;
}

static bool
ecdsa_verification(uint8_t *pubKey, uint8_t *r, uint8_t *s1, uint32_t mLen, uint8_t *m)
{
  uint64_t publicKeyAsFelem[8U] = { 0U };
  uint64_t *publicKeyFelemX = publicKeyAsFelem;
  uint64_t *publicKeyFelemY = publicKeyAsFelem + (uint32_t)4U;
  uint64_t rAsFelem[4U] = { 0U };
  uint64_t sAsFelem[4U] = { 0U };
  uint8_t *pubKeyX = pubKey;
  uint8_t *pubKeyY = pubKey + (uint32_t)32U;
  toUint64ChangeEndian(pubKeyX, publicKeyFelemX);
  toUint64ChangeEndian(pubKeyY, publicKeyFelemY);
  toUint64ChangeEndian(r, rAsFelem);
  toUint64ChangeEndian(s1, sAsFelem);
  bool result = ecdsa_verification_(publicKeyAsFelem, rAsFelem, sAsFelem, mLen, m);
  return result;
}

uint64_t
Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
)
{
  return ecdsa_signature(result, mLen, m, privKey, k);
}

bool
Hacl_Impl_ECDSA_ecdsa_p256_sha2_verify(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s1
)
{
  return ecdsa_verification(pubKey, r, s1, mLen, m);
}

