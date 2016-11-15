#include "Hacl_EC_Curve25519.h"

void Hacl_EC_Curve25519_format_scalar(uint8_t *scalar)
{
  uint8_t _0_53 = scalar[(uint32_t )0];
  uint8_t _0_54 = Hacl_UInt8_op_Amp_Hat(_0_53, Hacl_Cast_uint8_to_sint8((uint8_t )248));
  scalar[(uint32_t )0] = _0_54;
  uint8_t _0_55 = scalar[(uint32_t )31];
  uint8_t _0_56 = Hacl_UInt8_op_Amp_Hat(_0_55, Hacl_Cast_uint8_to_sint8((uint8_t )127));
  scalar[(uint32_t )31] = _0_56;
  uint8_t _0_57 = scalar[(uint32_t )31];
  uint8_t _0_58 = Hacl_UInt8_op_Bar_Hat(_0_57, Hacl_Cast_uint8_to_sint8((uint8_t )64));
  scalar[(uint32_t )31] = _0_58;
}

void Hacl_EC_Curve25519_expand_0(uint64_t *output, uint8_t *input)
{
  uint64_t mask = (uint64_t )0x7ffffffffffff;
  uint8_t i00 = input[(uint32_t )0];
  uint8_t i10 = input[(uint32_t )1];
  uint8_t i20 = input[(uint32_t )2];
  uint8_t i30 = input[(uint32_t )3];
  uint8_t i40 = input[(uint32_t )4];
  uint8_t i50 = input[(uint32_t )5];
  uint8_t i60 = input[(uint32_t )6];
  uint64_t i0 = (uint64_t )i00;
  uint64_t i1 = (uint64_t )i10;
  uint64_t i2 = (uint64_t )i20;
  uint64_t i3 = (uint64_t )i30;
  uint64_t i4 = (uint64_t )i40;
  uint64_t i5 = (uint64_t )i50;
  uint64_t i6 = (uint64_t )i60;
  uint64_t
  o0 =
    i0
    + (i1 << (uint32_t )8)
    + (i2 << (uint32_t )16)
    + (i3 << (uint32_t )24)
    + (i4 << (uint32_t )32)
    + (i5 << (uint32_t )40)
    + (i6 << (uint32_t )48 & mask);
  output[(uint32_t )0] = o0;
}

void Hacl_EC_Curve25519_expand_1(uint64_t *output, uint8_t *input)
{
  uint64_t mask = (uint64_t )0x7ffffffffffff;
  uint8_t i60 = input[(uint32_t )6];
  uint8_t i70 = input[(uint32_t )7];
  uint8_t i80 = input[(uint32_t )8];
  uint8_t i90 = input[(uint32_t )9];
  uint8_t i100 = input[(uint32_t )10];
  uint8_t i110 = input[(uint32_t )11];
  uint8_t i120 = input[(uint32_t )12];
  uint64_t i6 = (uint64_t )i60;
  uint64_t i7 = (uint64_t )i70;
  uint64_t i8 = (uint64_t )i80;
  uint64_t i9 = (uint64_t )i90;
  uint64_t i10 = (uint64_t )i100;
  uint64_t i11 = (uint64_t )i110;
  uint64_t i12 = (uint64_t )i120;
  uint64_t
  o1 =
    (i6 >> (uint32_t )3)
    + (i7 << (uint32_t )5)
    + (i8 << (uint32_t )13)
    + (i9 << (uint32_t )21)
    + (i10 << (uint32_t )29)
    + (i11 << (uint32_t )37)
    + (i12 << (uint32_t )45 & mask);
  output[(uint32_t )1] = o1;
}

void Hacl_EC_Curve25519_expand_2(uint64_t *output, uint8_t *input)
{
  uint64_t mask = (uint64_t )0x7ffffffffffff;
  uint8_t i120 = input[(uint32_t )12];
  uint8_t i130 = input[(uint32_t )13];
  uint8_t i140 = input[(uint32_t )14];
  uint8_t i150 = input[(uint32_t )15];
  uint8_t i160 = input[(uint32_t )16];
  uint8_t i170 = input[(uint32_t )17];
  uint8_t i180 = input[(uint32_t )18];
  uint8_t i190 = input[(uint32_t )19];
  uint64_t i12 = (uint64_t )i120;
  uint64_t i13 = (uint64_t )i130;
  uint64_t i14 = (uint64_t )i140;
  uint64_t i15 = (uint64_t )i150;
  uint64_t i16 = (uint64_t )i160;
  uint64_t i17 = (uint64_t )i170;
  uint64_t i18 = (uint64_t )i180;
  uint64_t i19 = (uint64_t )i190;
  uint64_t
  o2 =
    (i12 >> (uint32_t )6)
    + (i13 << (uint32_t )2)
    + (i14 << (uint32_t )10)
    + (i15 << (uint32_t )18)
    + (i16 << (uint32_t )26)
    + (i17 << (uint32_t )34)
    + (i18 << (uint32_t )42)
    + (i19 << (uint32_t )50 & mask);
  output[(uint32_t )2] = o2;
}

void Hacl_EC_Curve25519_expand_3(uint64_t *output, uint8_t *input)
{
  uint64_t mask = (uint64_t )0x7ffffffffffff;
  uint8_t i190 = input[(uint32_t )19];
  uint8_t i200 = input[(uint32_t )20];
  uint8_t i210 = input[(uint32_t )21];
  uint8_t i220 = input[(uint32_t )22];
  uint8_t i230 = input[(uint32_t )23];
  uint8_t i240 = input[(uint32_t )24];
  uint8_t i250 = input[(uint32_t )25];
  uint64_t i19 = (uint64_t )i190;
  uint64_t i20 = (uint64_t )i200;
  uint64_t i21 = (uint64_t )i210;
  uint64_t i22 = (uint64_t )i220;
  uint64_t i23 = (uint64_t )i230;
  uint64_t i24 = (uint64_t )i240;
  uint64_t i25 = (uint64_t )i250;
  uint64_t
  o3 =
    (i19 >> (uint32_t )1)
    + (i20 << (uint32_t )7)
    + (i21 << (uint32_t )15)
    + (i22 << (uint32_t )23)
    + (i23 << (uint32_t )31)
    + (i24 << (uint32_t )39)
    + (i25 << (uint32_t )47 & mask);
  output[(uint32_t )3] = o3;
}

void Hacl_EC_Curve25519_expand_4(uint64_t *output, uint8_t *input)
{
  uint64_t mask = (uint64_t )0x7ffffffffffff;
  uint8_t i250 = input[(uint32_t )25];
  uint8_t i260 = input[(uint32_t )26];
  uint8_t i270 = input[(uint32_t )27];
  uint8_t i280 = input[(uint32_t )28];
  uint8_t i290 = input[(uint32_t )29];
  uint8_t i300 = input[(uint32_t )30];
  uint8_t i310 = input[(uint32_t )31];
  uint64_t i25 = (uint64_t )i250;
  uint64_t i26 = (uint64_t )i260;
  uint64_t i27 = (uint64_t )i270;
  uint64_t i28 = (uint64_t )i280;
  uint64_t i29 = (uint64_t )i290;
  uint64_t i30 = (uint64_t )i300;
  uint64_t i31 = (uint64_t )i310;
  uint64_t
  o4 =
    (i25 >> (uint32_t )4)
    + (i26 << (uint32_t )4)
    + (i27 << (uint32_t )12)
    + (i28 << (uint32_t )20)
    + (i29 << (uint32_t )28)
    + (i30 << (uint32_t )36)
    + (i31 << (uint32_t )44 & mask);
  output[(uint32_t )4] = o4;
}

void Hacl_EC_Curve25519_expand(uint64_t *output, uint8_t *input)
{
  Hacl_EC_Curve25519_expand_0(output, input);
  Hacl_EC_Curve25519_expand_1(output, input);
  Hacl_EC_Curve25519_expand_2(output, input);
  Hacl_EC_Curve25519_expand_3(output, input);
  Hacl_EC_Curve25519_expand_4(output, input);
  return;
}

void Hacl_EC_Curve25519_contract_0(uint8_t *output, uint64_t *input)
{
  uint64_t i0 = input[(uint32_t )0];
  uint64_t i1 = input[(uint32_t )1];
  output[(uint32_t )0] = (uint8_t )(i0 >> (uint32_t )0);
  output[(uint32_t )1] = (uint8_t )(i0 >> (uint32_t )8);
  output[(uint32_t )2] = (uint8_t )(i0 >> (uint32_t )16);
  output[(uint32_t )3] = (uint8_t )(i0 >> (uint32_t )24);
  output[(uint32_t )4] = (uint8_t )(i0 >> (uint32_t )32);
  output[(uint32_t )5] = (uint8_t )(i0 >> (uint32_t )40);
  output[(uint32_t )6] = (uint8_t )((i0 >> (uint32_t )48) + (i1 << (uint32_t )3));
}

void Hacl_EC_Curve25519_contract_1(uint8_t *output, uint64_t *input)
{
  uint64_t i1 = input[(uint32_t )1];
  uint64_t i2 = input[(uint32_t )2];
  output[(uint32_t )7] = (uint8_t )(i1 >> (uint32_t )5);
  output[(uint32_t )8] = (uint8_t )(i1 >> (uint32_t )13);
  output[(uint32_t )9] = (uint8_t )(i1 >> (uint32_t )21);
  output[(uint32_t )10] = (uint8_t )(i1 >> (uint32_t )29);
  output[(uint32_t )11] = (uint8_t )(i1 >> (uint32_t )37);
  output[(uint32_t )12] = (uint8_t )((i1 >> (uint32_t )45) + (i2 << (uint32_t )6));
}

void Hacl_EC_Curve25519_contract_2(uint8_t *output, uint64_t *input)
{
  uint64_t i2 = input[(uint32_t )2];
  uint64_t i3 = input[(uint32_t )3];
  output[(uint32_t )13] = (uint8_t )(i2 >> (uint32_t )2);
  output[(uint32_t )14] = (uint8_t )(i2 >> (uint32_t )10);
  output[(uint32_t )15] = (uint8_t )(i2 >> (uint32_t )18);
  output[(uint32_t )16] = (uint8_t )(i2 >> (uint32_t )26);
  output[(uint32_t )17] = (uint8_t )(i2 >> (uint32_t )34);
  output[(uint32_t )18] = (uint8_t )(i2 >> (uint32_t )42);
  output[(uint32_t )19] = (uint8_t )((i2 >> (uint32_t )50) + (i3 << (uint32_t )1));
}

void Hacl_EC_Curve25519_contract_3(uint8_t *output, uint64_t *input)
{
  uint64_t i3 = input[(uint32_t )3];
  uint64_t i4 = input[(uint32_t )4];
  output[(uint32_t )20] = (uint8_t )(i3 >> (uint32_t )7);
  output[(uint32_t )21] = (uint8_t )(i3 >> (uint32_t )15);
  output[(uint32_t )22] = (uint8_t )(i3 >> (uint32_t )23);
  output[(uint32_t )23] = (uint8_t )(i3 >> (uint32_t )31);
  output[(uint32_t )24] = (uint8_t )(i3 >> (uint32_t )39);
  output[(uint32_t )25] = (uint8_t )((i3 >> (uint32_t )47) + (i4 << (uint32_t )4));
}

void Hacl_EC_Curve25519_contract_4(uint8_t *output, uint64_t *input)
{
  uint64_t i4 = input[(uint32_t )4];
  output[(uint32_t )26] = (uint8_t )(i4 >> (uint32_t )4);
  output[(uint32_t )27] = (uint8_t )(i4 >> (uint32_t )12);
  output[(uint32_t )28] = (uint8_t )(i4 >> (uint32_t )20);
  output[(uint32_t )29] = (uint8_t )(i4 >> (uint32_t )28);
  output[(uint32_t )30] = (uint8_t )(i4 >> (uint32_t )36);
  output[(uint32_t )31] = (uint8_t )(i4 >> (uint32_t )44);
}

void Hacl_EC_Curve25519_contract(uint8_t *output, uint64_t *input)
{
  Hacl_EC_Curve25519_contract_0(output, input);
  Hacl_EC_Curve25519_contract_1(output, input);
  Hacl_EC_Curve25519_contract_2(output, input);
  Hacl_EC_Curve25519_contract_3(output, input);
  Hacl_EC_Curve25519_contract_4(output, input);
  return;
}

void
Hacl_EC_Curve25519_mk_q(
  uint8_t *output,
  uint8_t *q_x,
  uint8_t *pk,
  Hacl_EC_Curve25519_PPoint_point q
)
{
  uint64_t one = (uint64_t )1;
  uint64_t *qx = Hacl_EC_Curve25519_PPoint_get_x(q);
  uint64_t *qy = Hacl_EC_Curve25519_PPoint_get_y(q);
  uint64_t *qz = Hacl_EC_Curve25519_PPoint_get_z(q);
  Hacl_EC_Curve25519_expand(qx, q_x);
  qz[(uint32_t )0] = one;
}

void
Hacl_EC_Curve25519_exp_2(
  uint8_t *output,
  uint8_t *q_x,
  uint8_t *scalar,
  Hacl_EC_Curve25519_PPoint_point basepoint
)
{
  uint64_t zero = (uint64_t )0;
  uint64_t tmp[22];
  for (uintmax_t i = 0; i < (uint32_t )22; ++i)
    tmp[i] = zero;
  uint64_t *resx = tmp + (uint32_t )0;
  uint64_t *resy = tmp + (uint32_t )6;
  uint64_t *resz = tmp + (uint32_t )11;
  uint64_t *zrecip = tmp + (uint32_t )17;
  Hacl_EC_Curve25519_PPoint_point res = Hacl_EC_Curve25519_PPoint_make(resx, resy, resz);
  Hacl_EC_Curve25519_Ladder_montgomery_ladder(res, scalar, basepoint);
  Hacl_EC_Curve25519_Crecip_crecip_(zrecip, Hacl_EC_Curve25519_PPoint_get_z(res));
  Hacl_EC_Curve25519_Bignum_fmul(resy, resx, zrecip);
  Hacl_EC_Curve25519_contract(output, resy);
}

void Hacl_EC_Curve25519_exp_1(uint8_t *output, uint8_t *q_x, uint8_t *scalar)
{
  uint64_t zero = (uint64_t )0;
  uint64_t tmp[17];
  for (uintmax_t i = 0; i < (uint32_t )17; ++i)
    tmp[i] = zero;
  uint64_t *qx = tmp + (uint32_t )0;
  uint64_t *qy = tmp + (uint32_t )6;
  uint64_t *qz = tmp + (uint32_t )11;
  Hacl_EC_Curve25519_PPoint_point q = Hacl_EC_Curve25519_PPoint_make(qx, qy, qz);
  Hacl_EC_Curve25519_mk_q(output, q_x, scalar, q);
  Hacl_EC_Curve25519_exp_2(output, q_x, scalar, q);
}

void Hacl_EC_Curve25519_exp(uint8_t *output, uint8_t *q_x, uint8_t *scalar)
{
  uint8_t scalar_cpy[32] = { 0 };
  memcpy(scalar_cpy, scalar, (uint32_t )32 * sizeof scalar[0]);
  Hacl_EC_Curve25519_format_scalar(scalar_cpy);
  Hacl_EC_Curve25519_exp_1(output, q_x, scalar_cpy);
}

