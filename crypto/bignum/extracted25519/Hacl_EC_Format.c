#include "Hacl_EC_Format.h"

uint8_t Hacl_EC_Format_zero_8 = (uint8_t )0;

uint64_t Hacl_EC_Format_load64_le(uint8_t *b)
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

void Hacl_EC_Format_store64_le(uint8_t *b, uint64_t z)
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

void Hacl_EC_Format_fexpand(uint64_t *output, uint8_t *input)
{
  uint64_t mask_51 = (uint64_t )0x7ffffffffffff;
  uint64_t i0 = Hacl_EC_Format_load64_le(input + (uint32_t )0);
  uint64_t i1 = Hacl_EC_Format_load64_le(input + (uint32_t )6);
  uint64_t i2 = Hacl_EC_Format_load64_le(input + (uint32_t )12);
  uint64_t i3 = Hacl_EC_Format_load64_le(input + (uint32_t )19);
  uint64_t i4 = Hacl_EC_Format_load64_le(input + (uint32_t )24);
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

void Hacl_EC_Format_fcontract(uint8_t *output, uint64_t *input)
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
  Hacl_EC_Format_store64_le(output + (uint32_t )0, o0);
  Hacl_EC_Format_store64_le(output + (uint32_t )8, o1);
  Hacl_EC_Format_store64_le(output + (uint32_t )16, o2);
  Hacl_EC_Format_store64_le(output + (uint32_t )24, o3);
  return;
}

void Hacl_EC_Format_scalar_of_point(uint8_t *scalar, uint64_t *point)
{
  uint64_t *x = Hacl_EC_Point_getx(point);
  uint64_t *z = Hacl_EC_Point_getz(point);
  uint64_t zmone[5] = { 0 };
  Hacl_Bignum_crecip(zmone, z);
  Hacl_Bignum_fmul(z, x, zmone);
  Hacl_EC_Format_fcontract(scalar, z);
}

