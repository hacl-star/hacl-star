#include "Hacl_EC_Curve25519_recursive.h"

uint8_t Hacl_EC_Curve25519_recursive_zero_8 = (uint8_t )0;

uint64_t Hacl_EC_Curve25519_recursive_zero_64 = (uint64_t )0;

FStar_UInt128_t
Hacl_EC_Curve25519_recursive_zero_128 = FStar_Int_Cast_uint64_to_uint128((uint64_t )0);

uint8_t Hacl_EC_Curve25519_recursive_one_8 = (uint8_t )1;

uint64_t Hacl_EC_Curve25519_recursive_one_64 = (uint64_t )1;

uint32_t Hacl_EC_Curve25519_recursive_len = (uint32_t )5;

uint32_t Hacl_EC_Curve25519_recursive_limb_size = (uint32_t )51;

uint64_t Hacl_EC_Curve25519_recursive_two54m152 = (uint64_t )0x3fffffffffff68;

uint64_t Hacl_EC_Curve25519_recursive_two54m8 = (uint64_t )0x3ffffffffffff8;

uint64_t Hacl_EC_Curve25519_recursive_nineteen = (uint64_t )19;

uint64_t Hacl_EC_Curve25519_recursive_mask_51 = (uint64_t )0x7ffffffffffff;

void Hacl_EC_Curve25519_recursive_fsum(uint64_t *a, uint64_t *b)
{
  uint64_t a0 = a[(uint32_t )0];
  uint64_t b0 = b[(uint32_t )0];
  uint64_t a1 = a[(uint32_t )1];
  uint64_t b1 = b[(uint32_t )1];
  uint64_t a2 = a[(uint32_t )2];
  uint64_t b2 = b[(uint32_t )2];
  uint64_t a3 = a[(uint32_t )3];
  uint64_t b3 = b[(uint32_t )3];
  uint64_t a4 = a[(uint32_t )4];
  uint64_t b4 = b[(uint32_t )4];
  a[(uint32_t )0] = a0 + b0;
  a[(uint32_t )1] = a1 + b1;
  a[(uint32_t )2] = a2 + b2;
  a[(uint32_t )3] = a3 + b3;
  a[(uint32_t )4] = a4 + b4;
}

void Hacl_EC_Curve25519_recursive_fdifference(uint64_t *a, uint64_t *b)
{
  uint64_t a0 = a[(uint32_t )0];
  uint64_t b0 = b[(uint32_t )0];
  uint64_t a1 = a[(uint32_t )1];
  uint64_t b1 = b[(uint32_t )1];
  uint64_t a2 = a[(uint32_t )2];
  uint64_t b2 = b[(uint32_t )2];
  uint64_t a3 = a[(uint32_t )3];
  uint64_t b3 = b[(uint32_t )3];
  uint64_t a4 = a[(uint32_t )4];
  uint64_t b4 = b[(uint32_t )4];
  a[(uint32_t )0] = b0 + (uint64_t )0x3fffffffffff68 - a0;
  a[(uint32_t )1] = b1 + (uint64_t )0x3ffffffffffff8 - a1;
  a[(uint32_t )2] = b2 + (uint64_t )0x3ffffffffffff8 - a2;
  a[(uint32_t )3] = b3 + (uint64_t )0x3ffffffffffff8 - a3;
  a[(uint32_t )4] = b4 + (uint64_t )0x3ffffffffffff8 - a4;
}

void
Hacl_EC_Curve25519_recursive_fscalar_(
  FStar_UInt128_t *output,
  uint64_t *a,
  uint64_t s,
  uint32_t ctr
)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    uint64_t ai = a[i];
    output[i] = FStar_UInt128_mul_wide(ai, s);
    Hacl_EC_Curve25519_recursive_fscalar_(output, a, s, i);
    return;
  }
}

void Hacl_EC_Curve25519_recursive_carry_wide_(FStar_UInt128_t *t, uint32_t ctr)
{
  if (ctr == (uint32_t )4)
    return;
  else
  {
    FStar_UInt128_t tctr = t[ctr];
    FStar_UInt128_t tctrp1 = t[ctr + (uint32_t )1];
    uint64_t r0 = FStar_Int_Cast_uint128_to_uint64(tctr) & (uint64_t )0x7ffffffffffff;
    uint64_t c = FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(tctr, (uint32_t )51));
    t[ctr] = FStar_Int_Cast_uint64_to_uint128(r0);
    t[ctr + (uint32_t )1] = FStar_UInt128_add(tctrp1, FStar_Int_Cast_uint64_to_uint128(c));
    Hacl_EC_Curve25519_recursive_carry_wide_(t, ctr + (uint32_t )1);
    return;
  }
}

void
Hacl_EC_Curve25519_recursive_copy_from_wide_(
  uint64_t *output,
  FStar_UInt128_t *input,
  uint32_t ctr
)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    FStar_UInt128_t inputi = input[i];
    output[i] = FStar_Int_Cast_uint128_to_uint64(inputi);
    Hacl_EC_Curve25519_recursive_copy_from_wide_(output, input, i);
    return;
  }
}

void Hacl_EC_Curve25519_recursive_fscalar_product(uint64_t *output, uint64_t *a, uint64_t s)
{
  FStar_UInt128_t t[5];
  for (uintmax_t i = 0; i < (uint32_t )5; ++i)
    t[i] = FStar_Int_Cast_uint64_to_uint128((uint64_t )0);
  Hacl_EC_Curve25519_recursive_fscalar_(t, a, s, (uint32_t )5);
  Hacl_EC_Curve25519_recursive_carry_wide_(t, (uint32_t )0);
  FStar_UInt128_t tnm1 = t[(uint32_t )4];
  FStar_UInt128_t t0 = t[(uint32_t )0];
  uint64_t c = FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(tnm1, (uint32_t )51));
  t[(uint32_t )4] =
    FStar_UInt128_logand(tnm1,
      FStar_Int_Cast_uint64_to_uint128((uint64_t )0x7ffffffffffff));
  t[(uint32_t )0] = FStar_UInt128_add(t0, FStar_UInt128_mul_wide(c, (uint64_t )19));
  Hacl_EC_Curve25519_recursive_copy_from_wide_(output, t, (uint32_t )5);
}

void Hacl_EC_Curve25519_recursive_shift_(uint64_t *output, uint64_t tmp, uint32_t ctr)
{
  uint64_t tmp0;
  if (ctr == (uint32_t )5)
    tmp0 = output[(uint32_t )0];
  else
    tmp0 = tmp;
  if (ctr == (uint32_t )1)
    output[(uint32_t )1] = tmp0;
  else
  {
    uint64_t z = output[ctr - (uint32_t )1];
    output[ctr % (uint32_t )5] = z;
    Hacl_EC_Curve25519_recursive_shift_(output, tmp0, ctr - (uint32_t )1);
    return;
  }
}

void Hacl_EC_Curve25519_recursive_shift_reduce(uint64_t *output)
{
  Hacl_EC_Curve25519_recursive_shift_(output, (uint64_t )0, (uint32_t )5);
  uint64_t o0 = output[(uint32_t )0];
  output[(uint32_t )0] = o0 * (uint64_t )19;
}

void
Hacl_EC_Curve25519_recursive_sum_scalar_multiplication_(
  FStar_UInt128_t *output,
  uint64_t *input,
  uint64_t s,
  uint32_t ctr
)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    FStar_UInt128_t oi = output[i];
    uint64_t ii = input[i];
    output[i] = FStar_UInt128_add(oi, FStar_UInt128_mul_wide(ii, s));
    Hacl_EC_Curve25519_recursive_sum_scalar_multiplication_(output, input, s, i);
    return;
  }
}

void
Hacl_EC_Curve25519_recursive_mul_shift_reduce_(
  FStar_UInt128_t *output,
  uint64_t *input,
  uint64_t *input2,
  uint32_t ctr
)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    uint64_t input2i = input2[(uint32_t )4 - i];
    Hacl_EC_Curve25519_recursive_sum_scalar_multiplication_(output, input, input2i, (uint32_t )5);
    if (ctr > (uint32_t )1)
      Hacl_EC_Curve25519_recursive_shift_reduce(input);
    Hacl_EC_Curve25519_recursive_mul_shift_reduce_(output, input, input2, i);
    return;
  }
}

void Hacl_EC_Curve25519_recursive_fmul(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  uint64_t tmp[5] = { 0 };
  FStar_UInt128_t t[5];
  for (uintmax_t i = 0; i < (uint32_t )5; ++i)
    t[i] = FStar_Int_Cast_uint64_to_uint128((uint64_t )0);
  memcpy(tmp, input, (uint32_t )5 * sizeof input[0]);
  Hacl_EC_Curve25519_recursive_mul_shift_reduce_(t, tmp, input2, (uint32_t )5);
  Hacl_EC_Curve25519_recursive_carry_wide_(t, (uint32_t )0);
  FStar_UInt128_t tnm1 = t[(uint32_t )4];
  FStar_UInt128_t t0 = t[(uint32_t )0];
  uint64_t c0 = FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(tnm1, (uint32_t )51));
  t[(uint32_t )4] =
    FStar_UInt128_logand(tnm1,
      FStar_Int_Cast_uint64_to_uint128((uint64_t )0x7ffffffffffff));
  t[(uint32_t )0] = FStar_UInt128_add(t0, FStar_UInt128_mul_wide(c0, (uint64_t )19));
  Hacl_EC_Curve25519_recursive_copy_from_wide_(output, t, (uint32_t )5);
  uint64_t output0 = output[(uint32_t )0];
  uint64_t output1 = output[(uint32_t )1];
  uint64_t c = output0 >> (uint32_t )51;
  output[(uint32_t )0] = output0 & (uint64_t )0x7ffffffffffff;
  output[(uint32_t )1] = output1 + c;
}

void Hacl_EC_Curve25519_recursive_fsquare_(uint64_t *output, FStar_UInt128_t *t)
{
  uint64_t r0 = output[(uint32_t )0];
  uint64_t r1 = output[(uint32_t )1];
  uint64_t r2 = output[(uint32_t )2];
  uint64_t r3 = output[(uint32_t )3];
  uint64_t r4 = output[(uint32_t )4];
  uint64_t d0 = r0 * (uint64_t )2;
  uint64_t d1 = r1 * (uint64_t )2;
  uint64_t d2 = r2 * (uint64_t )2 * (uint64_t )19;
  uint64_t d419 = r4 * (uint64_t )19;
  uint64_t d4 = d419 * (uint64_t )2;
  t[(uint32_t )0] =
    FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(r0, r0),
        FStar_UInt128_mul_wide(d4, r1)),
      FStar_UInt128_mul_wide(d2, r3));
  t[(uint32_t )1] =
    FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(d0, r1),
        FStar_UInt128_mul_wide(d4, r2)),
      FStar_UInt128_mul_wide(r3, r3 * (uint64_t )19));
  t[(uint32_t )2] =
    FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(d0, r2),
        FStar_UInt128_mul_wide(r1, r1)),
      FStar_UInt128_mul_wide(d4, r3));
  t[(uint32_t )3] =
    FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(d0, r3),
        FStar_UInt128_mul_wide(d1, r2)),
      FStar_UInt128_mul_wide(r4, d419));
  t[(uint32_t )4] =
    FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(d0, r4),
        FStar_UInt128_mul_wide(d1, r3)),
      FStar_UInt128_mul_wide(r2, r2));
  Hacl_EC_Curve25519_recursive_carry_wide_(t, (uint32_t )0);
  FStar_UInt128_t tnm1 = t[(uint32_t )4];
  FStar_UInt128_t t0 = t[(uint32_t )0];
  uint64_t c0 = FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(tnm1, (uint32_t )51));
  t[(uint32_t )4] =
    FStar_UInt128_logand(tnm1,
      FStar_Int_Cast_uint64_to_uint128((uint64_t )0x7ffffffffffff));
  t[(uint32_t )0] = FStar_UInt128_add(t0, FStar_UInt128_mul_wide(c0, (uint64_t )19));
  Hacl_EC_Curve25519_recursive_copy_from_wide_(output, t, (uint32_t )5);
  uint64_t output0 = output[(uint32_t )0];
  uint64_t output1 = output[(uint32_t )1];
  uint64_t c = output0 >> (uint32_t )51;
  output[(uint32_t )0] = output0 & (uint64_t )0x7ffffffffffff;
  output[(uint32_t )1] = output1 + c;
}

void
Hacl_EC_Curve25519_recursive_fsquare_times_(
  uint64_t *output,
  FStar_UInt128_t *tmp,
  uint32_t count
)
{
  if (count == (uint32_t )0)
    return;
  else
  {
    Hacl_EC_Curve25519_recursive_fsquare_(output, tmp);
    Hacl_EC_Curve25519_recursive_fsquare_times_(output, tmp, count - (uint32_t )1);
    return;
  }
}

void
Hacl_EC_Curve25519_recursive_fsquare_times(uint64_t *output, uint64_t *input, uint32_t count)
{
  uint64_t tmp[5] = { 0 };
  FStar_UInt128_t t[5];
  for (uintmax_t i = 0; i < (uint32_t )5; ++i)
    t[i] = FStar_Int_Cast_uint64_to_uint128((uint64_t )0);
  memcpy(tmp, input, (uint32_t )5 * sizeof input[0]);
  Hacl_EC_Curve25519_recursive_fsquare_times_(tmp, t, count);
  memcpy(output, tmp, (uint32_t )5 * sizeof tmp[0]);
}

uint64_t Hacl_EC_Curve25519_recursive_load64_le(uint8_t *b)
{
  uint8_t b0 = b[(uint32_t )0];
  uint8_t b1 = b[(uint32_t )1];
  uint8_t b2 = b[(uint32_t )2];
  uint8_t b3 = b[(uint32_t )3];
  uint8_t b4 = b[(uint32_t )4];
  uint8_t b5 = b[(uint32_t )5];
  uint8_t b6 = b[(uint32_t )6];
  uint8_t b7 = b[(uint32_t )7];
  return
    (uint64_t )b0
    | (uint64_t )b1 << (uint32_t )8
    | (uint64_t )b2 << (uint32_t )16
    | (uint64_t )b3 << (uint32_t )24
    | (uint64_t )b4 << (uint32_t )32
    | (uint64_t )b5 << (uint32_t )40
    | (uint64_t )b6 << (uint32_t )48
    | (uint64_t )b7 << (uint32_t )56;
}

void Hacl_EC_Curve25519_recursive_store64_le(uint8_t *b, uint64_t z)
{
  b[(uint32_t )0] = (uint8_t )z;
  b[(uint32_t )1] = (uint8_t )(z >> (uint32_t )8);
  b[(uint32_t )2] = (uint8_t )(z >> (uint32_t )16);
  b[(uint32_t )3] = (uint8_t )(z >> (uint32_t )24);
  b[(uint32_t )4] = (uint8_t )(z >> (uint32_t )32);
  b[(uint32_t )5] = (uint8_t )(z >> (uint32_t )40);
  b[(uint32_t )6] = (uint8_t )(z >> (uint32_t )48);
  b[(uint32_t )7] = (uint8_t )(z >> (uint32_t )56);
}

void Hacl_EC_Curve25519_recursive_fexpand(uint64_t *output, uint8_t *input)
{
  uint64_t mask_51 = (uint64_t )0x7ffffffffffff;
  uint64_t i0 = Hacl_EC_Curve25519_recursive_load64_le(input + (uint32_t )0);
  uint64_t i1 = Hacl_EC_Curve25519_recursive_load64_le(input + (uint32_t )6);
  uint64_t i2 = Hacl_EC_Curve25519_recursive_load64_le(input + (uint32_t )12);
  uint64_t i3 = Hacl_EC_Curve25519_recursive_load64_le(input + (uint32_t )19);
  uint64_t i4 = Hacl_EC_Curve25519_recursive_load64_le(input + (uint32_t )24);
  uint64_t output0 = i0 & mask_51;
  uint64_t output1 = i1 >> (uint32_t )3 & mask_51;
  uint64_t output2 = i2 >> (uint32_t )6 & mask_51;
  uint64_t output3 = i3 >> (uint32_t )1 & mask_51;
  uint64_t output4 = i4 >> (uint32_t )12 & mask_51;
  output[(uint32_t )0] = output0;
  output[(uint32_t )1] = output1;
  output[(uint32_t )2] = output2;
  output[(uint32_t )3] = output3;
  output[(uint32_t )4] = output4;
}

void Hacl_EC_Curve25519_recursive_fcontract(uint8_t *output, uint64_t *input)
{
  uint64_t mask_51 = (uint64_t )0x7ffffffffffff;
  uint64_t nineteen = (uint64_t )19;
  uint64_t t00 = input[(uint32_t )0];
  uint64_t t10 = input[(uint32_t )1];
  uint64_t t20 = input[(uint32_t )2];
  uint64_t t30 = input[(uint32_t )3];
  uint64_t t40 = input[(uint32_t )4];
  uint64_t t11 = t10 + (t00 >> (uint32_t )51);
  uint64_t t01 = t00 & mask_51;
  uint64_t t21 = t20 + (t11 >> (uint32_t )51);
  uint64_t t12 = t11 & mask_51;
  uint64_t t31 = t30 + (t21 >> (uint32_t )51);
  uint64_t t22 = t21 & mask_51;
  uint64_t t41 = t40 + (t31 >> (uint32_t )51);
  uint64_t t32 = t31 & mask_51;
  uint64_t t02 = t01 + nineteen * (t41 >> (uint32_t )51);
  uint64_t t42 = t41 & mask_51;
  uint64_t t13 = t12 + (t02 >> (uint32_t )51);
  uint64_t t03 = t02 & mask_51;
  uint64_t t23 = t22 + (t13 >> (uint32_t )51);
  uint64_t t14 = t13 & mask_51;
  uint64_t t33 = t32 + (t23 >> (uint32_t )51);
  uint64_t t24 = t23 & mask_51;
  uint64_t t43 = t42 + (t33 >> (uint32_t )51);
  uint64_t t34 = t33 & mask_51;
  uint64_t t04 = t03 + nineteen * (t43 >> (uint32_t )51);
  uint64_t t44 = t43 & mask_51;
  uint64_t t05 = t04 + nineteen;
  uint64_t t15 = t14 + (t05 >> (uint32_t )51);
  uint64_t t06 = t05 & mask_51;
  uint64_t t25 = t24 + (t15 >> (uint32_t )51);
  uint64_t t16 = t15 & mask_51;
  uint64_t t35 = t34 + (t25 >> (uint32_t )51);
  uint64_t t26 = t25 & mask_51;
  uint64_t t45 = t44 + (t35 >> (uint32_t )51);
  uint64_t t36 = t35 & mask_51;
  uint64_t t07 = t06 + nineteen * (t45 >> (uint32_t )51);
  uint64_t t46 = t45 & mask_51;
  uint64_t two52 = (uint64_t )0x8000000000000;
  uint64_t t08 = t07 + two52 - nineteen;
  uint64_t t17 = t16 + two52 - (uint64_t )1;
  uint64_t t27 = t26 + two52 - (uint64_t )1;
  uint64_t t37 = t36 + two52 - (uint64_t )1;
  uint64_t t47 = t46 + two52 - (uint64_t )1;
  uint64_t t18 = t17 + (t08 >> (uint32_t )51);
  uint64_t t0 = t08 & mask_51;
  uint64_t t28 = t27 + (t18 >> (uint32_t )51);
  uint64_t t1 = t18 & mask_51;
  uint64_t t38 = t37 + (t28 >> (uint32_t )51);
  uint64_t t2 = t28 & mask_51;
  uint64_t t48 = t47 + (t38 >> (uint32_t )51);
  uint64_t t3 = t38 & mask_51;
  uint64_t t4 = t48 & mask_51;
  uint64_t o0 = t0 | t1 << (uint32_t )51;
  uint64_t o1 = t1 >> (uint32_t )13 | t2 << (uint32_t )38;
  uint64_t o2 = t2 >> (uint32_t )26 | t3 << (uint32_t )25;
  uint64_t o3 = t3 >> (uint32_t )39 | t4 << (uint32_t )12;
  Hacl_EC_Curve25519_recursive_store64_le(output + (uint32_t )0, o0);
  Hacl_EC_Curve25519_recursive_store64_le(output + (uint32_t )8, o1);
  Hacl_EC_Curve25519_recursive_store64_le(output + (uint32_t )16, o2);
  Hacl_EC_Curve25519_recursive_store64_le(output + (uint32_t )24, o3);
  return;
}

void
Hacl_EC_Curve25519_recursive_fmonty(
  uint64_t *x2,
  uint64_t *z2,
  uint64_t *x3,
  uint64_t *z3,
  uint64_t *x,
  uint64_t *z,
  uint64_t *xprime,
  uint64_t *zprime,
  uint64_t *qmqp
)
{
  uint64_t buf[40] = { 0 };
  uint64_t *origx = buf + (uint32_t )0;
  uint64_t *origxprime = buf + (uint32_t )5;
  uint64_t *zzz = buf + (uint32_t )10;
  uint64_t *xx = buf + (uint32_t )15;
  uint64_t *zz = buf + (uint32_t )20;
  uint64_t *xxprime = buf + (uint32_t )25;
  uint64_t *zzprime = buf + (uint32_t )30;
  uint64_t *zzzprime = buf + (uint32_t )35;
  memcpy(origx, x, (uint32_t )5 * sizeof x[0]);
  Hacl_EC_Curve25519_recursive_fsum(x, z);
  Hacl_EC_Curve25519_recursive_fdifference(z, origx);
  memcpy(origxprime, xprime, (uint32_t )5 * sizeof xprime[0]);
  Hacl_EC_Curve25519_recursive_fsum(xprime, zprime);
  Hacl_EC_Curve25519_recursive_fdifference(zprime, origxprime);
  Hacl_EC_Curve25519_recursive_fmul(xxprime, xprime, z);
  Hacl_EC_Curve25519_recursive_fmul(zzprime, x, zprime);
  memcpy(origxprime, xxprime, (uint32_t )5 * sizeof xxprime[0]);
  Hacl_EC_Curve25519_recursive_fsum(xxprime, zzprime);
  Hacl_EC_Curve25519_recursive_fdifference(zzprime, origxprime);
  Hacl_EC_Curve25519_recursive_fsquare_times(x3, xxprime, (uint32_t )1);
  Hacl_EC_Curve25519_recursive_fsquare_times(zzzprime, zzprime, (uint32_t )1);
  Hacl_EC_Curve25519_recursive_fmul(z3, zzzprime, qmqp);
  Hacl_EC_Curve25519_recursive_fsquare_times(xx, x, (uint32_t )1);
  Hacl_EC_Curve25519_recursive_fsquare_times(zz, z, (uint32_t )1);
  Hacl_EC_Curve25519_recursive_fmul(x2, xx, zz);
  Hacl_EC_Curve25519_recursive_fdifference(zz, xx);
  Hacl_EC_Curve25519_recursive_fscalar_product(zzz, zz, (uint64_t )121665);
  Hacl_EC_Curve25519_recursive_fsum(zzz, xx);
  Hacl_EC_Curve25519_recursive_fmul(z2, zz, zzz);
}

void
Hacl_EC_Curve25519_recursive_swap_conditional_(
  uint64_t *a,
  uint64_t *b,
  uint64_t swap,
  uint32_t ctr
)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    uint64_t ai0 = a[i];
    uint64_t bi0 = b[i];
    uint64_t x = swap & (ai0 ^ bi0);
    uint64_t ai = ai0 ^ x;
    uint64_t bi = bi0 ^ x;
    a[i] = ai;
    b[i] = bi;
    Hacl_EC_Curve25519_recursive_swap_conditional_(a, b, swap, i);
    return;
  }
}

void Hacl_EC_Curve25519_recursive_swap_conditional(uint64_t *a, uint64_t *b, uint64_t iswap)
{
  uint64_t swap = (uint64_t )0 - iswap;
  Hacl_EC_Curve25519_recursive_swap_conditional_(a, b, swap, (uint32_t )5);
  return;
}

void
Hacl_EC_Curve25519_recursive_cmult_small_loop(
  uint64_t *nqx,
  uint64_t *nqz,
  uint64_t *nqpqx,
  uint64_t *nqpqz,
  uint64_t *nqx2,
  uint64_t *nqz2,
  uint64_t *nqpqx2,
  uint64_t *nqpqz2,
  uint64_t *q,
  uint8_t byte,
  uint32_t i
)
{
  if (i == (uint32_t )0)
    return;
  else
  {
    uint64_t bit = (uint64_t )(byte >> (uint32_t )7);
    Hacl_EC_Curve25519_recursive_swap_conditional(nqx, nqpqx, bit);
    Hacl_EC_Curve25519_recursive_swap_conditional(nqz, nqpqz, bit);
    Hacl_EC_Curve25519_recursive_fmonty(nqx2, nqz2, nqpqx2, nqpqz2, nqx, nqz, nqpqx, nqpqz, q);
    Hacl_EC_Curve25519_recursive_swap_conditional(nqx2, nqpqx2, bit);
    Hacl_EC_Curve25519_recursive_swap_conditional(nqz2, nqpqz2, bit);
    uint64_t *t0 = nqx;
    uint64_t *nqx = nqx2;
    uint64_t *nqx2 = t0;
    uint64_t *t1 = nqz;
    uint64_t *nqz = nqz2;
    uint64_t *nqz2 = t1;
    uint64_t *t2 = nqpqx;
    uint64_t *nqpqx = nqpqx2;
    uint64_t *nqpqx2 = t2;
    uint64_t *t = nqpqz;
    uint64_t *nqpqz = nqpqz2;
    uint64_t *nqpqz2 = t;
    uint8_t byte0 = byte << (uint32_t )1;
    Hacl_EC_Curve25519_recursive_cmult_small_loop(nqx,
      nqz,
      nqpqx,
      nqpqz,
      nqx2,
      nqz2,
      nqpqx2,
      nqpqz2,
      q,
      byte0,
      i - (uint32_t )1);
    return;
  }
}

void
Hacl_EC_Curve25519_recursive_cmult_big_loop(
  uint8_t *n,
  uint64_t *nqx,
  uint64_t *nqz,
  uint64_t *nqpqx,
  uint64_t *nqpqz,
  uint64_t *nqx2,
  uint64_t *nqz2,
  uint64_t *nqpqx2,
  uint64_t *nqpqz2,
  uint64_t *q,
  uint32_t i
)
{
  if (i == (uint32_t )0)
    return;
  else
  {
    uint32_t i0 = i - (uint32_t )1;
    uint8_t byte = n[i0];
    Hacl_EC_Curve25519_recursive_cmult_small_loop(nqx,
      nqz,
      nqpqx,
      nqpqz,
      nqx2,
      nqz2,
      nqpqx2,
      nqpqz2,
      q,
      byte,
      (uint32_t )8);
    Hacl_EC_Curve25519_recursive_cmult_big_loop(n,
      nqx,
      nqz,
      nqpqx,
      nqpqz,
      nqx2,
      nqz2,
      nqpqx2,
      nqpqz2,
      q,
      i0);
    return;
  }
}

void
Hacl_EC_Curve25519_recursive_cmult(
  uint64_t *resultx,
  uint64_t *resultz,
  uint8_t *n,
  uint64_t *q
)
{
  uint64_t buf[40] = { 0 };
  uint64_t *nqpqx = buf + (uint32_t )0;
  uint64_t *nqpqz = buf + (uint32_t )5;
  uint64_t *nqx = buf + (uint32_t )10;
  uint64_t *nqz = buf + (uint32_t )15;
  uint64_t *nqpqx2 = buf + (uint32_t )20;
  uint64_t *nqpqz2 = buf + (uint32_t )25;
  uint64_t *nqx2 = buf + (uint32_t )30;
  uint64_t *nqz2 = buf + (uint32_t )35;
  nqpqz[(uint32_t )0] = (uint64_t )1;
  nqx[(uint32_t )0] = (uint64_t )1;
  nqpqz2[(uint32_t )0] = (uint64_t )1;
  nqz2[(uint32_t )0] = (uint64_t )1;
  memcpy(nqpqx, q, (uint32_t )5 * sizeof q[0]);
  Hacl_EC_Curve25519_recursive_cmult_big_loop(n,
    nqx,
    nqz,
    nqpqx,
    nqpqz,
    nqx2,
    nqz2,
    nqpqx2,
    nqpqz2,
    q,
    (uint32_t )32);
  memcpy(resultx, nqx, (uint32_t )5 * sizeof nqx[0]);
  memcpy(resultz, nqz, (uint32_t )5 * sizeof nqz[0]);
}

void Hacl_EC_Curve25519_recursive_crecip(uint64_t *out, uint64_t *z)
{
  uint64_t buf[20] = { 0 };
  uint64_t *a = buf + (uint32_t )0;
  uint64_t *t0 = buf + (uint32_t )5;
  uint64_t *b = buf + (uint32_t )10;
  uint64_t *c = buf + (uint32_t )15;
  Hacl_EC_Curve25519_recursive_fsquare_times(a, z, (uint32_t )1);
  Hacl_EC_Curve25519_recursive_fsquare_times(t0, a, (uint32_t )2);
  Hacl_EC_Curve25519_recursive_fmul(b, t0, z);
  Hacl_EC_Curve25519_recursive_fmul(a, b, a);
  Hacl_EC_Curve25519_recursive_fsquare_times(t0, a, (uint32_t )1);
  Hacl_EC_Curve25519_recursive_fmul(b, t0, b);
  Hacl_EC_Curve25519_recursive_fsquare_times(t0, b, (uint32_t )5);
  Hacl_EC_Curve25519_recursive_fmul(b, t0, b);
  Hacl_EC_Curve25519_recursive_fsquare_times(t0, b, (uint32_t )10);
  Hacl_EC_Curve25519_recursive_fmul(c, t0, b);
  Hacl_EC_Curve25519_recursive_fsquare_times(t0, c, (uint32_t )20);
  Hacl_EC_Curve25519_recursive_fmul(t0, t0, c);
  Hacl_EC_Curve25519_recursive_fsquare_times(t0, t0, (uint32_t )10);
  Hacl_EC_Curve25519_recursive_fmul(b, t0, b);
  Hacl_EC_Curve25519_recursive_fsquare_times(t0, b, (uint32_t )50);
  Hacl_EC_Curve25519_recursive_fmul(c, t0, b);
  Hacl_EC_Curve25519_recursive_fsquare_times(t0, c, (uint32_t )100);
  Hacl_EC_Curve25519_recursive_fmul(t0, t0, c);
  Hacl_EC_Curve25519_recursive_fsquare_times(t0, t0, (uint32_t )50);
  Hacl_EC_Curve25519_recursive_fmul(t0, t0, b);
  Hacl_EC_Curve25519_recursive_fsquare_times(t0, t0, (uint32_t )5);
  Hacl_EC_Curve25519_recursive_fmul(out, t0, a);
}

void
Hacl_EC_Curve25519_recursive_crypto_scalarmult_curve25519_donna_c64(
  uint8_t *mypublic,
  uint8_t *secret,
  uint8_t *basepoint
)
{
  uint64_t buf[20] = { 0 };
  uint8_t e[32] = { 0 };
  uint64_t *bp = buf + (uint32_t )0;
  uint64_t *x = buf + (uint32_t )5;
  uint64_t *z = buf + (uint32_t )10;
  uint64_t *zmone = buf + (uint32_t )15;
  memcpy(e, secret, (uint32_t )32 * sizeof secret[0]);
  uint8_t e00 = e[(uint32_t )0];
  uint8_t e310 = e[(uint32_t )31];
  uint8_t e0 = e00 & (uint8_t )248;
  uint8_t e31 = e310 & (uint8_t )127;
  uint8_t e311 = e31 | (uint8_t )64;
  e[(uint32_t )0] = e0;
  e[(uint32_t )31] = e311;
  Hacl_EC_Curve25519_recursive_fexpand(bp, basepoint);
  Hacl_EC_Curve25519_recursive_cmult(x, z, e, bp);
  Hacl_EC_Curve25519_recursive_crecip(zmone, z);
  Hacl_EC_Curve25519_recursive_fmul(z, x, zmone);
  Hacl_EC_Curve25519_recursive_fcontract(mypublic, z);
}

