#include "Ed25519.h"

static void
Hacl_Lib_Create64_make_h64_5(
  uint64_t *b,
  uint64_t s0,
  uint64_t s1,
  uint64_t s2,
  uint64_t s3,
  uint64_t s4
)
{
  b[0] = s0;
  b[1] = s1;
  b[2] = s2;
  b[3] = s3;
  b[4] = s4;
}

static void
Hacl_Lib_Create64_make_h64_10(
  uint64_t *b,
  uint64_t s0,
  uint64_t s1,
  uint64_t s2,
  uint64_t s3,
  uint64_t s4,
  uint64_t s5,
  uint64_t s6,
  uint64_t s7,
  uint64_t s8,
  uint64_t s9
)
{
  b[0] = s0;
  b[1] = s1;
  b[2] = s2;
  b[3] = s3;
  b[4] = s4;
  b[5] = s5;
  b[6] = s6;
  b[7] = s7;
  b[8] = s8;
  b[9] = s9;
}

static void Hacl_Bignum_Modulo_carry_top(uint64_t *b)
{
  uint64_t b4 = b[4];
  uint64_t b0 = b[0];
  uint64_t mask = ((uint64_t )1 << (uint32_t )51) - (uint64_t )1;
  uint64_t b4_ = b4 & mask;
  uint64_t b0_ = b0 + (uint64_t )19 * (b4 >> (uint32_t )51);
  b[4] = b4_;
  b[0] = b0_;
}

inline static void
Hacl_Bignum_Fproduct_copy_from_wide_(uint64_t *output, FStar_UInt128_t *input)
{
  {
    FStar_UInt128_t uu____429 = input[0];
    uint64_t uu____428 = FStar_Int_Cast_Full_uint128_to_uint64(uu____429);
    output[0] = uu____428;
  }
  {
    FStar_UInt128_t uu____429 = input[1];
    uint64_t uu____428 = FStar_Int_Cast_Full_uint128_to_uint64(uu____429);
    output[1] = uu____428;
  }
  {
    FStar_UInt128_t uu____429 = input[2];
    uint64_t uu____428 = FStar_Int_Cast_Full_uint128_to_uint64(uu____429);
    output[2] = uu____428;
  }
  {
    FStar_UInt128_t uu____429 = input[3];
    uint64_t uu____428 = FStar_Int_Cast_Full_uint128_to_uint64(uu____429);
    output[3] = uu____428;
  }
  {
    FStar_UInt128_t uu____429 = input[4];
    uint64_t uu____428 = FStar_Int_Cast_Full_uint128_to_uint64(uu____429);
    output[4] = uu____428;
  }
}

inline static void Hacl_Bignum_Fproduct_shift(uint64_t *output)
{
  uint64_t tmp = output[4];
  {
    uint32_t ctr = (uint32_t )5 - (uint32_t )0 - (uint32_t )1;
    uint64_t z = output[ctr - (uint32_t )1];
    output[ctr] = z;
  }
  {
    uint32_t ctr = (uint32_t )5 - (uint32_t )1 - (uint32_t )1;
    uint64_t z = output[ctr - (uint32_t )1];
    output[ctr] = z;
  }
  {
    uint32_t ctr = (uint32_t )5 - (uint32_t )2 - (uint32_t )1;
    uint64_t z = output[ctr - (uint32_t )1];
    output[ctr] = z;
  }
  {
    uint32_t ctr = (uint32_t )5 - (uint32_t )3 - (uint32_t )1;
    uint64_t z = output[ctr - (uint32_t )1];
    output[ctr] = z;
  }
  output[0] = tmp;
}

inline static void
Hacl_Bignum_Fproduct_sum_scalar_multiplication_(
  FStar_UInt128_t *output,
  uint64_t *input,
  uint64_t s
)
{
  {
    FStar_UInt128_t uu____871 = output[0];
    uint64_t uu____874 = input[0];
    FStar_UInt128_t
    uu____870 = FStar_UInt128_add_mod(uu____871, FStar_UInt128_mul_wide(uu____874, s));
    output[0] = uu____870;
  }
  {
    FStar_UInt128_t uu____871 = output[1];
    uint64_t uu____874 = input[1];
    FStar_UInt128_t
    uu____870 = FStar_UInt128_add_mod(uu____871, FStar_UInt128_mul_wide(uu____874, s));
    output[1] = uu____870;
  }
  {
    FStar_UInt128_t uu____871 = output[2];
    uint64_t uu____874 = input[2];
    FStar_UInt128_t
    uu____870 = FStar_UInt128_add_mod(uu____871, FStar_UInt128_mul_wide(uu____874, s));
    output[2] = uu____870;
  }
  {
    FStar_UInt128_t uu____871 = output[3];
    uint64_t uu____874 = input[3];
    FStar_UInt128_t
    uu____870 = FStar_UInt128_add_mod(uu____871, FStar_UInt128_mul_wide(uu____874, s));
    output[3] = uu____870;
  }
  {
    FStar_UInt128_t uu____871 = output[4];
    uint64_t uu____874 = input[4];
    FStar_UInt128_t
    uu____870 = FStar_UInt128_add_mod(uu____871, FStar_UInt128_mul_wide(uu____874, s));
    output[4] = uu____870;
  }
}

inline static void Hacl_Bignum_Fproduct_carry_wide_(FStar_UInt128_t *tmp)
{
  {
    uint32_t ctr = (uint32_t )0;
    FStar_UInt128_t tctr = tmp[ctr];
    FStar_UInt128_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint64_t
    r0 =
      FStar_Int_Cast_Full_uint128_to_uint64(tctr)
      & ((uint64_t )1 << (uint32_t )51) - (uint64_t )1;
    FStar_UInt128_t c = FStar_UInt128_shift_right(tctr, (uint32_t )51);
    tmp[ctr] = FStar_Int_Cast_Full_uint64_to_uint128(r0);
    tmp[ctr + (uint32_t )1] = FStar_UInt128_add(tctrp1, c);
  }
  {
    uint32_t ctr = (uint32_t )1;
    FStar_UInt128_t tctr = tmp[ctr];
    FStar_UInt128_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint64_t
    r0 =
      FStar_Int_Cast_Full_uint128_to_uint64(tctr)
      & ((uint64_t )1 << (uint32_t )51) - (uint64_t )1;
    FStar_UInt128_t c = FStar_UInt128_shift_right(tctr, (uint32_t )51);
    tmp[ctr] = FStar_Int_Cast_Full_uint64_to_uint128(r0);
    tmp[ctr + (uint32_t )1] = FStar_UInt128_add(tctrp1, c);
  }
  {
    uint32_t ctr = (uint32_t )2;
    FStar_UInt128_t tctr = tmp[ctr];
    FStar_UInt128_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint64_t
    r0 =
      FStar_Int_Cast_Full_uint128_to_uint64(tctr)
      & ((uint64_t )1 << (uint32_t )51) - (uint64_t )1;
    FStar_UInt128_t c = FStar_UInt128_shift_right(tctr, (uint32_t )51);
    tmp[ctr] = FStar_Int_Cast_Full_uint64_to_uint128(r0);
    tmp[ctr + (uint32_t )1] = FStar_UInt128_add(tctrp1, c);
  }
  {
    uint32_t ctr = (uint32_t )3;
    FStar_UInt128_t tctr = tmp[ctr];
    FStar_UInt128_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint64_t
    r0 =
      FStar_Int_Cast_Full_uint128_to_uint64(tctr)
      & ((uint64_t )1 << (uint32_t )51) - (uint64_t )1;
    FStar_UInt128_t c = FStar_UInt128_shift_right(tctr, (uint32_t )51);
    tmp[ctr] = FStar_Int_Cast_Full_uint64_to_uint128(r0);
    tmp[ctr + (uint32_t )1] = FStar_UInt128_add(tctrp1, c);
  }
}

inline static void Hacl_Bignum_Fmul_shift_reduce(uint64_t *output)
{
  Hacl_Bignum_Fproduct_shift(output);
  uint64_t b0 = output[0];
  output[0] = (uint64_t )19 * b0;
}

static void
Hacl_Bignum_Fmul_mul_shift_reduce_(FStar_UInt128_t *output, uint64_t *input, uint64_t *input21)
{
  {
    uint64_t input2i = input21[0];
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i);
    Hacl_Bignum_Fmul_shift_reduce(input);
  }
  {
    uint64_t input2i = input21[1];
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i);
    Hacl_Bignum_Fmul_shift_reduce(input);
  }
  {
    uint64_t input2i = input21[2];
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i);
    Hacl_Bignum_Fmul_shift_reduce(input);
  }
  {
    uint64_t input2i = input21[3];
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i);
    Hacl_Bignum_Fmul_shift_reduce(input);
  }
  uint32_t i = (uint32_t )4;
  uint64_t input2i = input21[i];
  Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i);
}

inline static void Hacl_Bignum_Fmul_fmul_(uint64_t *output, uint64_t *input, uint64_t *input21)
{
  KRML_CHECK_SIZE(FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )0), (uint32_t )5);
  FStar_UInt128_t t[5];
  for (uintmax_t _i = 0; _i < (uint32_t )5; ++_i)
    t[_i] = FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )0);
  Hacl_Bignum_Fmul_mul_shift_reduce_(t, input, input21);
  Hacl_Bignum_Fproduct_carry_wide_(t);
  FStar_UInt128_t b4 = t[4];
  FStar_UInt128_t b0 = t[0];
  FStar_UInt128_t
  mask =
    FStar_UInt128_sub(FStar_UInt128_shift_left(FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )1),
        (uint32_t )51),
      FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )1));
  FStar_UInt128_t b4_ = FStar_UInt128_logand(b4, mask);
  FStar_UInt128_t
  b0_ =
    FStar_UInt128_add(b0,
      FStar_UInt128_mul_wide((uint64_t )19,
        FStar_Int_Cast_Full_uint128_to_uint64(FStar_UInt128_shift_right(b4, (uint32_t )51))));
  t[4] = b4_;
  t[0] = b0_;
  Hacl_Bignum_Fproduct_copy_from_wide_(output, t);
  uint64_t i0 = output[0];
  uint64_t i1 = output[1];
  uint64_t i0_ = i0 & ((uint64_t )1 << (uint32_t )51) - (uint64_t )1;
  uint64_t i1_ = i1 + (i0 >> (uint32_t )51);
  output[0] = i0_;
  output[1] = i1_;
}

inline static void Hacl_Bignum_Fmul_fmul(uint64_t *output, uint64_t *input, uint64_t *input21)
{
  uint64_t tmp[5] = { 0 };
  memcpy(tmp, input, (uint32_t )5 * sizeof input[0]);
  Hacl_Bignum_Fmul_fmul_(output, tmp, input21);
}

inline static void
Hacl_Bignum_Fsquare_upd_5(
  FStar_UInt128_t *tmp,
  FStar_UInt128_t s0,
  FStar_UInt128_t s1,
  FStar_UInt128_t s2,
  FStar_UInt128_t s3,
  FStar_UInt128_t s4
)
{
  tmp[0] = s0;
  tmp[1] = s1;
  tmp[2] = s2;
  tmp[3] = s3;
  tmp[4] = s4;
}

inline static void Hacl_Bignum_Fsquare_fsquare__(FStar_UInt128_t *tmp, uint64_t *output)
{
  uint64_t r0 = output[0];
  uint64_t r1 = output[1];
  uint64_t r2 = output[2];
  uint64_t r3 = output[3];
  uint64_t r4 = output[4];
  uint64_t d0 = r0 * (uint64_t )2;
  uint64_t d1 = r1 * (uint64_t )2;
  uint64_t d2 = r2 * (uint64_t )2 * (uint64_t )19;
  uint64_t d419 = r4 * (uint64_t )19;
  uint64_t d4 = d419 * (uint64_t )2;
  FStar_UInt128_t
  s0 =
    FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(r0, r0),
        FStar_UInt128_mul_wide(d4, r1)),
      FStar_UInt128_mul_wide(d2, r3));
  FStar_UInt128_t
  s1 =
    FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(d0, r1),
        FStar_UInt128_mul_wide(d4, r2)),
      FStar_UInt128_mul_wide(r3 * (uint64_t )19, r3));
  FStar_UInt128_t
  s2 =
    FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(d0, r2),
        FStar_UInt128_mul_wide(r1, r1)),
      FStar_UInt128_mul_wide(d4, r3));
  FStar_UInt128_t
  s3 =
    FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(d0, r3),
        FStar_UInt128_mul_wide(d1, r2)),
      FStar_UInt128_mul_wide(r4, d419));
  FStar_UInt128_t
  s4 =
    FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(d0, r4),
        FStar_UInt128_mul_wide(d1, r3)),
      FStar_UInt128_mul_wide(r2, r2));
  Hacl_Bignum_Fsquare_upd_5(tmp, s0, s1, s2, s3, s4);
}

inline static void Hacl_Bignum_Fsquare_fsquare_(FStar_UInt128_t *tmp, uint64_t *output)
{
  Hacl_Bignum_Fsquare_fsquare__(tmp, output);
  Hacl_Bignum_Fproduct_carry_wide_(tmp);
  FStar_UInt128_t b4 = tmp[4];
  FStar_UInt128_t b0 = tmp[0];
  FStar_UInt128_t
  mask =
    FStar_UInt128_sub(FStar_UInt128_shift_left(FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )1),
        (uint32_t )51),
      FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )1));
  FStar_UInt128_t b4_ = FStar_UInt128_logand(b4, mask);
  FStar_UInt128_t
  b0_ =
    FStar_UInt128_add(b0,
      FStar_UInt128_mul_wide((uint64_t )19,
        FStar_Int_Cast_Full_uint128_to_uint64(FStar_UInt128_shift_right(b4, (uint32_t )51))));
  tmp[4] = b4_;
  tmp[0] = b0_;
  Hacl_Bignum_Fproduct_copy_from_wide_(output, tmp);
  uint64_t i0 = output[0];
  uint64_t i1 = output[1];
  uint64_t i0_ = i0 & ((uint64_t )1 << (uint32_t )51) - (uint64_t )1;
  uint64_t i1_ = i1 + (i0 >> (uint32_t )51);
  output[0] = i0_;
  output[1] = i1_;
}

static void
Hacl_Bignum_Fsquare_fsquare_times_(uint64_t *input, FStar_UInt128_t *tmp, uint32_t count1)
{
  Hacl_Bignum_Fsquare_fsquare_(tmp, input);
  for (uint32_t i = (uint32_t )1; i < count1; i = i + (uint32_t )1)
    Hacl_Bignum_Fsquare_fsquare_(tmp, input);
}

inline static void
Hacl_Bignum_Fsquare_fsquare_times(uint64_t *output, uint64_t *input, uint32_t count1)
{
  KRML_CHECK_SIZE(FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )0), (uint32_t )5);
  FStar_UInt128_t t[5];
  for (uintmax_t _i = 0; _i < (uint32_t )5; ++_i)
    t[_i] = FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )0);
  memcpy(output, input, (uint32_t )5 * sizeof input[0]);
  Hacl_Bignum_Fsquare_fsquare_times_(output, t, count1);
}

inline static void Hacl_Bignum_Fsquare_fsquare_times_inplace(uint64_t *output, uint32_t count1)
{
  KRML_CHECK_SIZE(FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )0), (uint32_t )5);
  FStar_UInt128_t t[5];
  for (uintmax_t _i = 0; _i < (uint32_t )5; ++_i)
    t[_i] = FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )0);
  Hacl_Bignum_Fsquare_fsquare_times_(output, t, count1);
}

inline static void Hacl_Bignum_Crecip_crecip(uint64_t *out, uint64_t *z)
{
  uint64_t buf[20] = { 0 };
  uint64_t *a = buf;
  uint64_t *t00 = buf + (uint32_t )5;
  uint64_t *b0 = buf + (uint32_t )10;
  (void )(buf + (uint32_t )15);
  Hacl_Bignum_Fsquare_fsquare_times(a, z, (uint32_t )1);
  Hacl_Bignum_Fsquare_fsquare_times(t00, a, (uint32_t )2);
  Hacl_Bignum_Fmul_fmul(b0, t00, z);
  Hacl_Bignum_Fmul_fmul(a, b0, a);
  Hacl_Bignum_Fsquare_fsquare_times(t00, a, (uint32_t )1);
  Hacl_Bignum_Fmul_fmul(b0, t00, b0);
  Hacl_Bignum_Fsquare_fsquare_times(t00, b0, (uint32_t )5);
  uint64_t *t01 = buf + (uint32_t )5;
  uint64_t *b1 = buf + (uint32_t )10;
  uint64_t *c0 = buf + (uint32_t )15;
  Hacl_Bignum_Fmul_fmul(b1, t01, b1);
  Hacl_Bignum_Fsquare_fsquare_times(t01, b1, (uint32_t )10);
  Hacl_Bignum_Fmul_fmul(c0, t01, b1);
  Hacl_Bignum_Fsquare_fsquare_times(t01, c0, (uint32_t )20);
  Hacl_Bignum_Fmul_fmul(t01, t01, c0);
  Hacl_Bignum_Fsquare_fsquare_times_inplace(t01, (uint32_t )10);
  Hacl_Bignum_Fmul_fmul(b1, t01, b1);
  Hacl_Bignum_Fsquare_fsquare_times(t01, b1, (uint32_t )50);
  uint64_t *a0 = buf;
  uint64_t *t0 = buf + (uint32_t )5;
  uint64_t *b = buf + (uint32_t )10;
  uint64_t *c = buf + (uint32_t )15;
  Hacl_Bignum_Fmul_fmul(c, t0, b);
  Hacl_Bignum_Fsquare_fsquare_times(t0, c, (uint32_t )100);
  Hacl_Bignum_Fmul_fmul(t0, t0, c);
  Hacl_Bignum_Fsquare_fsquare_times_inplace(t0, (uint32_t )50);
  Hacl_Bignum_Fmul_fmul(t0, t0, b);
  Hacl_Bignum_Fsquare_fsquare_times_inplace(t0, (uint32_t )5);
  Hacl_Bignum_Fmul_fmul(out, t0, a0);
}

inline static void Hacl_Bignum_Crecip_crecip_(uint64_t *out, uint64_t *z)
{
  uint64_t buf[20] = { 0 };
  uint64_t *a = buf;
  uint64_t *t00 = buf + (uint32_t )5;
  uint64_t *b0 = buf + (uint32_t )10;
  (void )(buf + (uint32_t )15);
  Hacl_Bignum_Fsquare_fsquare_times(a, z, (uint32_t )1);
  Hacl_Bignum_Fsquare_fsquare_times(t00, a, (uint32_t )2);
  Hacl_Bignum_Fmul_fmul(b0, t00, z);
  Hacl_Bignum_Fmul_fmul(a, b0, a);
  Hacl_Bignum_Fsquare_fsquare_times(t00, a, (uint32_t )1);
  Hacl_Bignum_Fmul_fmul(b0, t00, b0);
  Hacl_Bignum_Fsquare_fsquare_times(t00, b0, (uint32_t )5);
  uint64_t *t01 = buf + (uint32_t )5;
  uint64_t *b1 = buf + (uint32_t )10;
  uint64_t *c0 = buf + (uint32_t )15;
  Hacl_Bignum_Fmul_fmul(b1, t01, b1);
  Hacl_Bignum_Fsquare_fsquare_times(t01, b1, (uint32_t )10);
  Hacl_Bignum_Fmul_fmul(c0, t01, b1);
  Hacl_Bignum_Fsquare_fsquare_times(t01, c0, (uint32_t )20);
  Hacl_Bignum_Fmul_fmul(t01, t01, c0);
  Hacl_Bignum_Fsquare_fsquare_times_inplace(t01, (uint32_t )10);
  Hacl_Bignum_Fmul_fmul(b1, t01, b1);
  Hacl_Bignum_Fsquare_fsquare_times(t01, b1, (uint32_t )50);
  uint64_t *a0 = buf;
  (void )(buf + (uint32_t )5);
  (void )(buf + (uint32_t )10);
  (void )(buf + (uint32_t )15);
  Hacl_Bignum_Fsquare_fsquare_times(a0, z, (uint32_t )1);
  uint64_t *a1 = buf;
  uint64_t *t0 = buf + (uint32_t )5;
  uint64_t *b = buf + (uint32_t )10;
  uint64_t *c = buf + (uint32_t )15;
  Hacl_Bignum_Fmul_fmul(c, t0, b);
  Hacl_Bignum_Fsquare_fsquare_times(t0, c, (uint32_t )100);
  Hacl_Bignum_Fmul_fmul(t0, t0, c);
  Hacl_Bignum_Fsquare_fsquare_times_inplace(t0, (uint32_t )50);
  Hacl_Bignum_Fmul_fmul(t0, t0, b);
  Hacl_Bignum_Fsquare_fsquare_times_inplace(t0, (uint32_t )2);
  Hacl_Bignum_Fmul_fmul(out, t0, a1);
}

inline static void Hacl_Bignum_fsum(uint64_t *a, uint64_t *b)
{
  {
    uint64_t uu____871 = a[0];
    uint64_t uu____874 = b[0];
    uint64_t uu____870 = uu____871 + uu____874;
    a[0] = uu____870;
  }
  {
    uint64_t uu____871 = a[1];
    uint64_t uu____874 = b[1];
    uint64_t uu____870 = uu____871 + uu____874;
    a[1] = uu____870;
  }
  {
    uint64_t uu____871 = a[2];
    uint64_t uu____874 = b[2];
    uint64_t uu____870 = uu____871 + uu____874;
    a[2] = uu____870;
  }
  {
    uint64_t uu____871 = a[3];
    uint64_t uu____874 = b[3];
    uint64_t uu____870 = uu____871 + uu____874;
    a[3] = uu____870;
  }
  {
    uint64_t uu____871 = a[4];
    uint64_t uu____874 = b[4];
    uint64_t uu____870 = uu____871 + uu____874;
    a[4] = uu____870;
  }
}

inline static void Hacl_Bignum_fdifference(uint64_t *a, uint64_t *b)
{
  uint64_t tmp[5] = { 0 };
  memcpy(tmp, b, (uint32_t )5 * sizeof b[0]);
  uint64_t b0 = tmp[0];
  uint64_t b1 = tmp[1];
  uint64_t b2 = tmp[2];
  uint64_t b3 = tmp[3];
  uint64_t b4 = tmp[4];
  tmp[0] = b0 + (uint64_t )0x3fffffffffff68;
  tmp[1] = b1 + (uint64_t )0x3ffffffffffff8;
  tmp[2] = b2 + (uint64_t )0x3ffffffffffff8;
  tmp[3] = b3 + (uint64_t )0x3ffffffffffff8;
  tmp[4] = b4 + (uint64_t )0x3ffffffffffff8;
  {
    uint64_t uu____871 = a[0];
    uint64_t uu____874 = tmp[0];
    uint64_t uu____870 = uu____874 - uu____871;
    a[0] = uu____870;
  }
  {
    uint64_t uu____871 = a[1];
    uint64_t uu____874 = tmp[1];
    uint64_t uu____870 = uu____874 - uu____871;
    a[1] = uu____870;
  }
  {
    uint64_t uu____871 = a[2];
    uint64_t uu____874 = tmp[2];
    uint64_t uu____870 = uu____874 - uu____871;
    a[2] = uu____870;
  }
  {
    uint64_t uu____871 = a[3];
    uint64_t uu____874 = tmp[3];
    uint64_t uu____870 = uu____874 - uu____871;
    a[3] = uu____870;
  }
  {
    uint64_t uu____871 = a[4];
    uint64_t uu____874 = tmp[4];
    uint64_t uu____870 = uu____874 - uu____871;
    a[4] = uu____870;
  }
}

inline static void Hacl_Bignum_fmul(uint64_t *output, uint64_t *a, uint64_t *b)
{
  Hacl_Bignum_Fmul_fmul(output, a, b);
}

static void
Hacl_EC_Format_upd_5(
  uint64_t *output,
  uint64_t output0,
  uint64_t output1,
  uint64_t output2,
  uint64_t output3,
  uint64_t output4
)
{
  output[0] = output0;
  output[1] = output1;
  output[2] = output2;
  output[3] = output3;
  output[4] = output4;
}

static void
Hacl_EC_Format_upd_5_(
  uint64_t *output,
  uint64_t output0,
  uint64_t output1,
  uint64_t output2,
  uint64_t output3,
  uint64_t output4
)
{
  output[0] = output0;
  output[1] = output1;
  output[2] = output2;
  output[3] = output3;
  output[4] = output4;
}

static void Hacl_EC_Format_fexpand(uint64_t *output, uint8_t *input)
{
  uint64_t mask_511 = (uint64_t )0x7ffffffffffff;
  uint64_t i0 = load64_le(input);
  uint8_t *x00 = input + (uint32_t )6;
  uint64_t i1 = load64_le(x00);
  uint8_t *x01 = input + (uint32_t )12;
  uint64_t i2 = load64_le(x01);
  uint8_t *x02 = input + (uint32_t )19;
  uint64_t i3 = load64_le(x02);
  uint8_t *x0 = input + (uint32_t )24;
  uint64_t i4 = load64_le(x0);
  uint64_t output0 = i0 & mask_511;
  uint64_t output1 = i1 >> (uint32_t )3 & mask_511;
  uint64_t output2 = i2 >> (uint32_t )6 & mask_511;
  uint64_t output3 = i3 >> (uint32_t )1 & mask_511;
  uint64_t output4 = i4 >> (uint32_t )12 & mask_511;
  Hacl_EC_Format_upd_5(output, output0, output1, output2, output3, output4);
}

static void Hacl_EC_Format_fcontract_first_carry_pass(uint64_t *input)
{
  uint64_t t0 = input[0];
  uint64_t t1 = input[1];
  uint64_t t2 = input[2];
  uint64_t t3 = input[3];
  uint64_t t4 = input[4];
  uint64_t t1_ = t1 + (t0 >> (uint32_t )51);
  uint64_t t0_ = t0 & (uint64_t )0x7ffffffffffff;
  uint64_t t2_ = t2 + (t1_ >> (uint32_t )51);
  uint64_t t1__ = t1_ & (uint64_t )0x7ffffffffffff;
  uint64_t t3_ = t3 + (t2_ >> (uint32_t )51);
  uint64_t t2__ = t2_ & (uint64_t )0x7ffffffffffff;
  uint64_t t4_ = t4 + (t3_ >> (uint32_t )51);
  uint64_t t3__ = t3_ & (uint64_t )0x7ffffffffffff;
  Hacl_EC_Format_upd_5_(input, t0_, t1__, t2__, t3__, t4_);
}

static void Hacl_EC_Format_fcontract_first_carry_full(uint64_t *input)
{
  Hacl_EC_Format_fcontract_first_carry_pass(input);
  Hacl_Bignum_Modulo_carry_top(input);
}

static void Hacl_EC_Format_fcontract_second_carry_pass(uint64_t *input)
{
  uint64_t t0 = input[0];
  uint64_t t1 = input[1];
  uint64_t t2 = input[2];
  uint64_t t3 = input[3];
  uint64_t t4 = input[4];
  uint64_t t1_ = t1 + (t0 >> (uint32_t )51);
  uint64_t t0_ = t0 & (uint64_t )0x7ffffffffffff;
  uint64_t t2_ = t2 + (t1_ >> (uint32_t )51);
  uint64_t t1__ = t1_ & (uint64_t )0x7ffffffffffff;
  uint64_t t3_ = t3 + (t2_ >> (uint32_t )51);
  uint64_t t2__ = t2_ & (uint64_t )0x7ffffffffffff;
  uint64_t t4_ = t4 + (t3_ >> (uint32_t )51);
  uint64_t t3__ = t3_ & (uint64_t )0x7ffffffffffff;
  Hacl_EC_Format_upd_5_(input, t0_, t1__, t2__, t3__, t4_);
}

static void Hacl_EC_Format_fcontract_second_carry_full(uint64_t *input)
{
  Hacl_EC_Format_fcontract_second_carry_pass(input);
  Hacl_Bignum_Modulo_carry_top(input);
  uint64_t i0 = input[0];
  uint64_t i1 = input[1];
  uint64_t i0_ = i0 & ((uint64_t )1 << (uint32_t )51) - (uint64_t )1;
  uint64_t i1_ = i1 + (i0 >> (uint32_t )51);
  input[0] = i0_;
  input[1] = i1_;
}

static void Hacl_EC_Format_fcontract_trim(uint64_t *input)
{
  uint64_t a0 = input[0];
  uint64_t a1 = input[1];
  uint64_t a2 = input[2];
  uint64_t a3 = input[3];
  uint64_t a4 = input[4];
  uint64_t mask0 = FStar_UInt64_gte_mask(a0, (uint64_t )0x7ffffffffffed);
  uint64_t mask1 = FStar_UInt64_eq_mask(a1, (uint64_t )0x7ffffffffffff);
  uint64_t mask2 = FStar_UInt64_eq_mask(a2, (uint64_t )0x7ffffffffffff);
  uint64_t mask3 = FStar_UInt64_eq_mask(a3, (uint64_t )0x7ffffffffffff);
  uint64_t mask4 = FStar_UInt64_eq_mask(a4, (uint64_t )0x7ffffffffffff);
  uint64_t mask = mask0 & mask1 & mask2 & mask3 & mask4;
  uint64_t a0_ = a0 - ((uint64_t )0x7ffffffffffed & mask);
  uint64_t a1_ = a1 - ((uint64_t )0x7ffffffffffff & mask);
  uint64_t a2_ = a2 - ((uint64_t )0x7ffffffffffff & mask);
  uint64_t a3_ = a3 - ((uint64_t )0x7ffffffffffff & mask);
  uint64_t a4_ = a4 - ((uint64_t )0x7ffffffffffff & mask);
  Hacl_EC_Format_upd_5_(input, a0_, a1_, a2_, a3_, a4_);
}

static void Hacl_EC_Format_reduce(uint64_t *out)
{
  Hacl_EC_Format_fcontract_first_carry_full(out);
  Hacl_EC_Format_fcontract_second_carry_full(out);
  Hacl_EC_Format_fcontract_trim(out);
}

static void Hacl_Bignum25519_fsum(uint64_t *a, uint64_t *b)
{
  Hacl_Bignum_fsum(a, b);
}

static void Hacl_Bignum25519_fdifference(uint64_t *a, uint64_t *b)
{
  Hacl_Bignum_fdifference(a, b);
}

static void Hacl_Bignum25519_reduce_513(uint64_t *a)
{
  uint64_t t0 = a[0];
  uint64_t t1 = a[1];
  uint64_t t2 = a[2];
  uint64_t t3 = a[3];
  uint64_t t4 = a[4];
  uint64_t t1_ = t1 + (t0 >> (uint32_t )51);
  uint64_t t0_ = t0 & (uint64_t )0x7ffffffffffff;
  uint64_t t2_ = t2 + (t1_ >> (uint32_t )51);
  uint64_t t1__ = t1_ & (uint64_t )0x7ffffffffffff;
  uint64_t t3_ = t3 + (t2_ >> (uint32_t )51);
  uint64_t t2__ = t2_ & (uint64_t )0x7ffffffffffff;
  uint64_t t4_ = t4 + (t3_ >> (uint32_t )51);
  uint64_t t3__ = t3_ & (uint64_t )0x7ffffffffffff;
  Hacl_Lib_Create64_make_h64_5(a, t0_, t1__, t2__, t3__, t4_);
  Hacl_Bignum_Modulo_carry_top(a);
  uint64_t i0 = a[0];
  uint64_t i1 = a[1];
  uint64_t i0_ = i0 & ((uint64_t )1 << (uint32_t )51) - (uint64_t )1;
  uint64_t i1_ = i1 + (i0 >> (uint32_t )51);
  a[0] = i0_;
  a[1] = i1_;
}

static void Hacl_Bignum25519_fdifference_reduced(uint64_t *a, uint64_t *b)
{
  Hacl_Bignum25519_fdifference(a, b);
  Hacl_Bignum25519_reduce_513(a);
}

static void Hacl_Bignum25519_fmul(uint64_t *out, uint64_t *a, uint64_t *b)
{
  Hacl_Bignum_fmul(out, a, b);
}

static void Hacl_Bignum25519_times_2(uint64_t *out, uint64_t *a)
{
  uint64_t a0 = a[0];
  uint64_t a1 = a[1];
  uint64_t a2 = a[2];
  uint64_t a3 = a[3];
  uint64_t a4 = a[4];
  uint64_t o0 = (uint64_t )2 * a0;
  uint64_t o1 = (uint64_t )2 * a1;
  uint64_t o2 = (uint64_t )2 * a2;
  uint64_t o3 = (uint64_t )2 * a3;
  uint64_t o4 = (uint64_t )2 * a4;
  Hacl_Lib_Create64_make_h64_5(out, o0, o1, o2, o3, o4);
}

static void Hacl_Bignum25519_times_d(uint64_t *out, uint64_t *a)
{
  uint64_t d1[5] = { 0 };
  Hacl_Lib_Create64_make_h64_5(d1,
    (uint64_t )0x00034dca135978a3,
    (uint64_t )0x0001a8283b156ebd,
    (uint64_t )0x0005e7a26001c029,
    (uint64_t )0x000739c663a03cbb,
    (uint64_t )0x00052036cee2b6ff);
  Hacl_Bignum25519_fmul(out, d1, a);
}

static void Hacl_Bignum25519_times_2d(uint64_t *out, uint64_t *a)
{
  uint64_t d2[5] = { 0 };
  Hacl_Lib_Create64_make_h64_5(d2,
    (uint64_t )0x00069b9426b2f159,
    (uint64_t )0x00035050762add7a,
    (uint64_t )0x0003cf44c0038052,
    (uint64_t )0x0006738cc7407977,
    (uint64_t )0x0002406d9dc56dff);
  Hacl_Bignum25519_fmul(out, a, d2);
}

static void Hacl_Bignum25519_fsquare(uint64_t *out, uint64_t *a)
{
  KRML_CHECK_SIZE(FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )0), (uint32_t )5);
  FStar_UInt128_t tmp[5];
  for (uintmax_t _i = 0; _i < (uint32_t )5; ++_i)
    tmp[_i] = FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )0);
  memcpy(out, a, (uint32_t )5 * sizeof a[0]);
  Hacl_Bignum_Fsquare_fsquare_(tmp, out);
}

static void Hacl_Bignum25519_inverse(uint64_t *out, uint64_t *a)
{
  Hacl_Bignum_Crecip_crecip(out, a);
}

static void Hacl_Bignum25519_reduce(uint64_t *out)
{
  Hacl_EC_Format_reduce(out);
}

static uint64_t *Hacl_Impl_Ed25519_ExtPoint_getx(uint64_t *p)
{
  return p;
}

static uint64_t *Hacl_Impl_Ed25519_ExtPoint_gety(uint64_t *p)
{
  return p + (uint32_t )5;
}

static uint64_t *Hacl_Impl_Ed25519_ExtPoint_getz(uint64_t *p)
{
  return p + (uint32_t )10;
}

static uint64_t *Hacl_Impl_Ed25519_ExtPoint_gett(uint64_t *p)
{
  return p + (uint32_t )15;
}

static void Hacl_Impl_Ed25519_G_make_g(uint64_t *g1)
{
  uint64_t *gx = Hacl_Impl_Ed25519_ExtPoint_getx(g1);
  uint64_t *gy = Hacl_Impl_Ed25519_ExtPoint_gety(g1);
  uint64_t *gz = Hacl_Impl_Ed25519_ExtPoint_getz(g1);
  uint64_t *gt1 = Hacl_Impl_Ed25519_ExtPoint_gett(g1);
  Hacl_Lib_Create64_make_h64_5(gx,
    (uint64_t )0x00062d608f25d51a,
    (uint64_t )0x000412a4b4f6592a,
    (uint64_t )0x00075b7171a4b31d,
    (uint64_t )0x0001ff60527118fe,
    (uint64_t )0x000216936d3cd6e5);
  Hacl_Lib_Create64_make_h64_5(gy,
    (uint64_t )0x0006666666666658,
    (uint64_t )0x0004cccccccccccc,
    (uint64_t )0x0001999999999999,
    (uint64_t )0x0003333333333333,
    (uint64_t )0x0006666666666666);
  Hacl_Lib_Create64_make_h64_5(gz,
    (uint64_t )0x0000000000000001,
    (uint64_t )0x0000000000000000,
    (uint64_t )0x0000000000000000,
    (uint64_t )0x0000000000000000,
    (uint64_t )0x0000000000000000);
  Hacl_Lib_Create64_make_h64_5(gt1,
    (uint64_t )0x00068ab3a5b7dda3,
    (uint64_t )0x00000eea2a5eadbb,
    (uint64_t )0x0002af8df483c27e,
    (uint64_t )0x000332b375274732,
    (uint64_t )0x00067875f0fd78b7);
}

static void Hacl_Impl_Store51_store_51_(uint8_t *output, uint64_t *input)
{
  uint64_t t0 = input[0];
  uint64_t t1 = input[1];
  uint64_t t2 = input[2];
  uint64_t t3 = input[3];
  uint64_t t4 = input[4];
  uint64_t o0 = t1 << (uint32_t )51 | t0;
  uint64_t o1 = t2 << (uint32_t )38 | t1 >> (uint32_t )13;
  uint64_t o2 = t3 << (uint32_t )25 | t2 >> (uint32_t )26;
  uint64_t o3 = t4 << (uint32_t )12 | t3 >> (uint32_t )39;
  uint8_t *b0 = output;
  uint8_t *b1 = output + (uint32_t )8;
  uint8_t *b2 = output + (uint32_t )16;
  uint8_t *b3 = output + (uint32_t )24;
  store64_le(b0, o0);
  store64_le(b1, o1);
  store64_le(b2, o2);
  store64_le(b3, o3);
}

static uint64_t Hacl_Impl_Ed25519_PointCompress_x_mod_2(uint64_t *x)
{
  uint64_t x0 = x[0];
  return x0 & (uint64_t )1;
}

static void Hacl_Impl_Ed25519_PointCompress_point_compress(uint8_t *z, uint64_t *p)
{
  uint64_t tmp[15] = { 0 };
  uint64_t *x0 = tmp + (uint32_t )5;
  uint64_t *out0 = tmp + (uint32_t )10;
  uint64_t *zinv = tmp;
  uint64_t *x = tmp + (uint32_t )5;
  uint64_t *out = tmp + (uint32_t )10;
  uint64_t *px = Hacl_Impl_Ed25519_ExtPoint_getx(p);
  uint64_t *py = Hacl_Impl_Ed25519_ExtPoint_gety(p);
  uint64_t *pz = Hacl_Impl_Ed25519_ExtPoint_getz(p);
  Hacl_Bignum25519_inverse(zinv, pz);
  Hacl_Bignum25519_fmul(x, px, zinv);
  Hacl_Bignum25519_reduce(x);
  Hacl_Bignum25519_fmul(out, py, zinv);
  Hacl_Bignum25519_reduce(out);
  uint64_t b = Hacl_Impl_Ed25519_PointCompress_x_mod_2(x0);
  Hacl_Impl_Store51_store_51_(z, out0);
  uint8_t xbyte = (uint8_t )b;
  uint8_t o31 = z[31];
  z[31] = o31 + (xbyte << (uint32_t )7);
}

static void
Hacl_Impl_Ed25519_SwapConditional_swap_conditional_step(
  uint64_t *a_,
  uint64_t *b_,
  uint64_t *a,
  uint64_t *b,
  uint64_t swap1
)
{
  uint64_t a0 = a[0];
  uint64_t a1 = a[1];
  uint64_t a2 = a[2];
  uint64_t a3 = a[3];
  uint64_t a4 = a[4];
  uint64_t b0 = b[0];
  uint64_t b1 = b[1];
  uint64_t b2 = b[2];
  uint64_t b3 = b[3];
  uint64_t b4 = b[4];
  uint64_t x0 = swap1 & (a0 ^ b0);
  uint64_t x1 = swap1 & (a1 ^ b1);
  uint64_t x2 = swap1 & (a2 ^ b2);
  uint64_t x3 = swap1 & (a3 ^ b3);
  uint64_t x4 = swap1 & (a4 ^ b4);
  uint64_t a0_ = a0 ^ x0;
  uint64_t b0_ = b0 ^ x0;
  uint64_t a1_ = a1 ^ x1;
  uint64_t b1_ = b1 ^ x1;
  uint64_t a2_ = a2 ^ x2;
  uint64_t b2_ = b2 ^ x2;
  uint64_t a3_ = a3 ^ x3;
  uint64_t b3_ = b3 ^ x3;
  uint64_t a4_ = a4 ^ x4;
  uint64_t b4_ = b4 ^ x4;
  Hacl_Lib_Create64_make_h64_5(a_, a0_, a1_, a2_, a3_, a4_);
  Hacl_Lib_Create64_make_h64_5(b_, b0_, b1_, b2_, b3_, b4_);
}

static void
Hacl_Impl_Ed25519_SwapConditional_swap_conditional(
  uint64_t *a_,
  uint64_t *b_,
  uint64_t *a,
  uint64_t *b,
  uint64_t iswap
)
{
  uint64_t swap1 = (uint64_t )0 - iswap;
  Hacl_Impl_Ed25519_SwapConditional_swap_conditional_step(Hacl_Impl_Ed25519_ExtPoint_getx(a_),
    Hacl_Impl_Ed25519_ExtPoint_getx(b_),
    Hacl_Impl_Ed25519_ExtPoint_getx(a),
    Hacl_Impl_Ed25519_ExtPoint_getx(b),
    swap1);
  Hacl_Impl_Ed25519_SwapConditional_swap_conditional_step(Hacl_Impl_Ed25519_ExtPoint_gety(a_),
    Hacl_Impl_Ed25519_ExtPoint_gety(b_),
    Hacl_Impl_Ed25519_ExtPoint_gety(a),
    Hacl_Impl_Ed25519_ExtPoint_gety(b),
    swap1);
  Hacl_Impl_Ed25519_SwapConditional_swap_conditional_step(Hacl_Impl_Ed25519_ExtPoint_getz(a_),
    Hacl_Impl_Ed25519_ExtPoint_getz(b_),
    Hacl_Impl_Ed25519_ExtPoint_getz(a),
    Hacl_Impl_Ed25519_ExtPoint_getz(b),
    swap1);
  Hacl_Impl_Ed25519_SwapConditional_swap_conditional_step(Hacl_Impl_Ed25519_ExtPoint_gett(a_),
    Hacl_Impl_Ed25519_ExtPoint_gett(b_),
    Hacl_Impl_Ed25519_ExtPoint_gett(a),
    Hacl_Impl_Ed25519_ExtPoint_gett(b),
    swap1);
}

static void
Hacl_Impl_Ed25519_SwapConditional_swap_conditional_inplace(
  uint64_t *a,
  uint64_t *b,
  uint64_t iswap
)
{
  uint64_t swap1 = (uint64_t )0 - iswap;
  Hacl_Impl_Ed25519_SwapConditional_swap_conditional_step(Hacl_Impl_Ed25519_ExtPoint_getx(a),
    Hacl_Impl_Ed25519_ExtPoint_getx(b),
    Hacl_Impl_Ed25519_ExtPoint_getx(a),
    Hacl_Impl_Ed25519_ExtPoint_getx(b),
    swap1);
  Hacl_Impl_Ed25519_SwapConditional_swap_conditional_step(Hacl_Impl_Ed25519_ExtPoint_gety(a),
    Hacl_Impl_Ed25519_ExtPoint_gety(b),
    Hacl_Impl_Ed25519_ExtPoint_gety(a),
    Hacl_Impl_Ed25519_ExtPoint_gety(b),
    swap1);
  Hacl_Impl_Ed25519_SwapConditional_swap_conditional_step(Hacl_Impl_Ed25519_ExtPoint_getz(a),
    Hacl_Impl_Ed25519_ExtPoint_getz(b),
    Hacl_Impl_Ed25519_ExtPoint_getz(a),
    Hacl_Impl_Ed25519_ExtPoint_getz(b),
    swap1);
  Hacl_Impl_Ed25519_SwapConditional_swap_conditional_step(Hacl_Impl_Ed25519_ExtPoint_gett(a),
    Hacl_Impl_Ed25519_ExtPoint_gett(b),
    Hacl_Impl_Ed25519_ExtPoint_gett(a),
    Hacl_Impl_Ed25519_ExtPoint_gett(b),
    swap1);
}

static void Hacl_Impl_Ed25519_SwapConditional_copy(uint64_t *output, uint64_t *input)
{
  memcpy(output, input, (uint32_t )20 * sizeof input[0]);
}

static void Hacl_Impl_Ed25519_PointAdd_point_add(uint64_t *out, uint64_t *p, uint64_t *q1)
{
  uint64_t tmp[30] = { 0 };
  uint64_t *tmp1 = tmp;
  uint64_t *tmp20 = tmp + (uint32_t )5;
  uint64_t *tmp30 = tmp + (uint32_t )10;
  uint64_t *tmp40 = tmp + (uint32_t )15;
  (void )(tmp + (uint32_t )20);
  (void )(tmp + (uint32_t )25);
  uint64_t *x1 = Hacl_Impl_Ed25519_ExtPoint_getx(p);
  uint64_t *y1 = Hacl_Impl_Ed25519_ExtPoint_gety(p);
  (void )Hacl_Impl_Ed25519_ExtPoint_getz(p);
  (void )Hacl_Impl_Ed25519_ExtPoint_gett(p);
  uint64_t *x2 = Hacl_Impl_Ed25519_ExtPoint_getx(q1);
  uint64_t *y2 = Hacl_Impl_Ed25519_ExtPoint_gety(q1);
  (void )Hacl_Impl_Ed25519_ExtPoint_getz(q1);
  (void )Hacl_Impl_Ed25519_ExtPoint_gett(q1);
  memcpy(tmp1, x1, (uint32_t )5 * sizeof x1[0]);
  memcpy(tmp20, x2, (uint32_t )5 * sizeof x2[0]);
  Hacl_Bignum25519_fdifference_reduced(tmp1, y1);
  Hacl_Bignum25519_fdifference(tmp20, y2);
  Hacl_Bignum25519_fmul(tmp30, tmp1, tmp20);
  memcpy(tmp1, y1, (uint32_t )5 * sizeof y1[0]);
  memcpy(tmp20, y2, (uint32_t )5 * sizeof y2[0]);
  Hacl_Bignum25519_fsum(tmp1, x1);
  Hacl_Bignum25519_fsum(tmp20, x2);
  Hacl_Bignum25519_fmul(tmp40, tmp1, tmp20);
  uint64_t *tmp10 = tmp;
  uint64_t *tmp21 = tmp + (uint32_t )5;
  uint64_t *tmp31 = tmp + (uint32_t )10;
  (void )(tmp + (uint32_t )15);
  uint64_t *tmp50 = tmp + (uint32_t )20;
  uint64_t *tmp60 = tmp + (uint32_t )25;
  (void )Hacl_Impl_Ed25519_ExtPoint_getx(p);
  (void )Hacl_Impl_Ed25519_ExtPoint_gety(p);
  uint64_t *z1 = Hacl_Impl_Ed25519_ExtPoint_getz(p);
  uint64_t *t1 = Hacl_Impl_Ed25519_ExtPoint_gett(p);
  (void )Hacl_Impl_Ed25519_ExtPoint_getx(q1);
  (void )Hacl_Impl_Ed25519_ExtPoint_gety(q1);
  uint64_t *z2 = Hacl_Impl_Ed25519_ExtPoint_getz(q1);
  uint64_t *t2 = Hacl_Impl_Ed25519_ExtPoint_gett(q1);
  Hacl_Bignum25519_times_2d(tmp10, t1);
  Hacl_Bignum25519_fmul(tmp21, tmp10, t2);
  Hacl_Bignum25519_times_2(tmp10, z1);
  Hacl_Bignum25519_fmul(tmp50, tmp10, z2);
  memcpy(tmp10, tmp31, (uint32_t )5 * sizeof tmp31[0]);
  memcpy(tmp60, tmp21, (uint32_t )5 * sizeof tmp21[0]);
  uint64_t *tmp11 = tmp;
  uint64_t *tmp2 = tmp + (uint32_t )5;
  uint64_t *tmp3 = tmp + (uint32_t )10;
  uint64_t *tmp41 = tmp + (uint32_t )15;
  uint64_t *tmp51 = tmp + (uint32_t )20;
  uint64_t *tmp61 = tmp + (uint32_t )25;
  (void )Hacl_Impl_Ed25519_ExtPoint_getx(p);
  (void )Hacl_Impl_Ed25519_ExtPoint_gety(p);
  (void )Hacl_Impl_Ed25519_ExtPoint_getz(p);
  (void )Hacl_Impl_Ed25519_ExtPoint_gett(p);
  (void )Hacl_Impl_Ed25519_ExtPoint_getx(q1);
  (void )Hacl_Impl_Ed25519_ExtPoint_gety(q1);
  (void )Hacl_Impl_Ed25519_ExtPoint_getz(q1);
  (void )Hacl_Impl_Ed25519_ExtPoint_gett(q1);
  Hacl_Bignum25519_fdifference_reduced(tmp11, tmp41);
  Hacl_Bignum25519_fdifference(tmp61, tmp51);
  Hacl_Bignum25519_fsum(tmp51, tmp2);
  Hacl_Bignum25519_fsum(tmp41, tmp3);
  uint64_t *tmp12 = tmp;
  (void )(tmp + (uint32_t )5);
  (void )(tmp + (uint32_t )10);
  uint64_t *tmp4 = tmp + (uint32_t )15;
  uint64_t *tmp5 = tmp + (uint32_t )20;
  uint64_t *tmp6 = tmp + (uint32_t )25;
  uint64_t *x3 = Hacl_Impl_Ed25519_ExtPoint_getx(out);
  uint64_t *y3 = Hacl_Impl_Ed25519_ExtPoint_gety(out);
  uint64_t *z3 = Hacl_Impl_Ed25519_ExtPoint_getz(out);
  uint64_t *t3 = Hacl_Impl_Ed25519_ExtPoint_gett(out);
  Hacl_Bignum25519_fmul(x3, tmp12, tmp6);
  Hacl_Bignum25519_fmul(y3, tmp5, tmp4);
  Hacl_Bignum25519_fmul(t3, tmp12, tmp4);
  Hacl_Bignum25519_fmul(z3, tmp5, tmp6);
}

static void Hacl_Impl_Ed25519_PointDouble_point_double_step_1(uint64_t *p, uint64_t *tmp)
{
  uint64_t *tmp1 = tmp;
  uint64_t *tmp2 = tmp + (uint32_t )5;
  uint64_t *tmp3 = tmp + (uint32_t )10;
  uint64_t *tmp4 = tmp + (uint32_t )15;
  (void )(tmp + (uint32_t )20);
  (void )(tmp + (uint32_t )25);
  uint64_t *x1 = Hacl_Impl_Ed25519_ExtPoint_getx(p);
  uint64_t *y1 = Hacl_Impl_Ed25519_ExtPoint_gety(p);
  uint64_t *z1 = Hacl_Impl_Ed25519_ExtPoint_getz(p);
  (void )Hacl_Impl_Ed25519_ExtPoint_gett(p);
  Hacl_Bignum25519_fsquare(tmp1, x1);
  Hacl_Bignum25519_fsquare(tmp2, y1);
  Hacl_Bignum25519_fsquare(tmp3, z1);
  Hacl_Bignum25519_times_2(tmp4, tmp3);
  memcpy(tmp3, tmp1, (uint32_t )5 * sizeof tmp1[0]);
  Hacl_Bignum25519_fsum(tmp3, tmp2);
  Hacl_Bignum25519_reduce_513(tmp3);
}

static void Hacl_Impl_Ed25519_PointDouble_point_double_step_2(uint64_t *p, uint64_t *tmp)
{
  uint64_t *tmp1 = tmp;
  uint64_t *tmp2 = tmp + (uint32_t )5;
  uint64_t *tmp3 = tmp + (uint32_t )10;
  uint64_t *tmp4 = tmp + (uint32_t )15;
  uint64_t *tmp5 = tmp + (uint32_t )20;
  uint64_t *tmp6 = tmp + (uint32_t )25;
  uint64_t *x1 = Hacl_Impl_Ed25519_ExtPoint_getx(p);
  uint64_t *y1 = Hacl_Impl_Ed25519_ExtPoint_gety(p);
  (void )Hacl_Impl_Ed25519_ExtPoint_getz(p);
  (void )Hacl_Impl_Ed25519_ExtPoint_gett(p);
  memcpy(tmp5, x1, (uint32_t )5 * sizeof x1[0]);
  Hacl_Bignum25519_fsum(tmp5, y1);
  Hacl_Bignum25519_fsquare(tmp6, tmp5);
  memcpy(tmp5, tmp3, (uint32_t )5 * sizeof tmp3[0]);
  Hacl_Bignum25519_fdifference(tmp6, tmp5);
  Hacl_Bignum25519_fdifference_reduced(tmp2, tmp1);
  Hacl_Bignum25519_reduce_513(tmp4);
  Hacl_Bignum25519_fsum(tmp4, tmp2);
}

static void
Hacl_Impl_Ed25519_PointDouble_point_double_(uint64_t *out, uint64_t *p, uint64_t *tmp)
{
  uint64_t *tmp2 = tmp + (uint32_t )5;
  uint64_t *tmp3 = tmp + (uint32_t )10;
  uint64_t *tmp4 = tmp + (uint32_t )15;
  (void )(tmp + (uint32_t )20);
  uint64_t *tmp6 = tmp + (uint32_t )25;
  uint64_t *x3 = Hacl_Impl_Ed25519_ExtPoint_getx(out);
  uint64_t *y3 = Hacl_Impl_Ed25519_ExtPoint_gety(out);
  uint64_t *z3 = Hacl_Impl_Ed25519_ExtPoint_getz(out);
  uint64_t *t3 = Hacl_Impl_Ed25519_ExtPoint_gett(out);
  Hacl_Impl_Ed25519_PointDouble_point_double_step_1(p, tmp);
  Hacl_Impl_Ed25519_PointDouble_point_double_step_2(p, tmp);
  Hacl_Bignum25519_fmul(x3, tmp4, tmp6);
  Hacl_Bignum25519_fmul(y3, tmp2, tmp3);
  Hacl_Bignum25519_fmul(t3, tmp3, tmp6);
  Hacl_Bignum25519_fmul(z3, tmp4, tmp2);
}

static void Hacl_Impl_Ed25519_PointDouble_point_double(uint64_t *out, uint64_t *p)
{
  uint64_t tmp[30] = { 0 };
  Hacl_Impl_Ed25519_PointDouble_point_double_(out, p, tmp);
}

static uint8_t Hacl_Impl_Ed25519_Ladder_Step_ith_bit(uint8_t *k1, uint32_t i)
{
  uint32_t q1 = i >> (uint32_t )3;
  uint32_t r = i & (uint32_t )7;
  uint8_t kq = k1[q1];
  return kq >> r & (uint8_t )1;
}

static void
Hacl_Impl_Ed25519_Ladder_Step_swap_cond_inplace(uint64_t *p, uint64_t *q1, uint64_t iswap)
{
  Hacl_Impl_Ed25519_SwapConditional_swap_conditional_inplace(p, q1, iswap);
}

static void
Hacl_Impl_Ed25519_Ladder_Step_swap_cond(
  uint64_t *p_,
  uint64_t *q_,
  uint64_t *p,
  uint64_t *q1,
  uint64_t iswap
)
{
  Hacl_Impl_Ed25519_SwapConditional_swap_conditional(p_, q_, p, q1, iswap);
}

static void
Hacl_Impl_Ed25519_Ladder_Step_loop_step_1(uint64_t *b, uint8_t *k1, uint32_t ctr, uint8_t i)
{
  uint64_t *nq = b;
  uint64_t *nqpq = b + (uint32_t )20;
  (void )(b + (uint32_t )40);
  (void )(b + (uint32_t )60);
  uint64_t bit = (uint64_t )i;
  Hacl_Impl_Ed25519_Ladder_Step_swap_cond_inplace(nq, nqpq, bit);
}

static void Hacl_Impl_Ed25519_Ladder_Step_loop_step_2(uint64_t *b, uint8_t *k1, uint32_t ctr)
{
  uint64_t *nq = b;
  uint64_t *nqpq = b + (uint32_t )20;
  uint64_t *nq2 = b + (uint32_t )40;
  uint64_t *nqpq2 = b + (uint32_t )60;
  Hacl_Impl_Ed25519_PointDouble_point_double(nq2, nq);
  (void )Hacl_Impl_Ed25519_ExtPoint_getx(nq);
  (void )Hacl_Impl_Ed25519_ExtPoint_gety(nq);
  (void )Hacl_Impl_Ed25519_ExtPoint_getz(nq);
  (void )Hacl_Impl_Ed25519_ExtPoint_gett(nq);
  (void )Hacl_Impl_Ed25519_ExtPoint_getx(nqpq);
  (void )Hacl_Impl_Ed25519_ExtPoint_gety(nqpq);
  (void )Hacl_Impl_Ed25519_ExtPoint_getz(nqpq);
  (void )Hacl_Impl_Ed25519_ExtPoint_gett(nqpq);
  Hacl_Impl_Ed25519_PointAdd_point_add(nqpq2, nq, nqpq);
}

static void
Hacl_Impl_Ed25519_Ladder_Step_loop_step_3(uint64_t *b, uint8_t *k1, uint32_t ctr, uint8_t i)
{
  uint64_t *nq = b;
  uint64_t *nqpq = b + (uint32_t )20;
  uint64_t *nq2 = b + (uint32_t )40;
  uint64_t *nqpq2 = b + (uint32_t )60;
  uint64_t bit = (uint64_t )i;
  Hacl_Impl_Ed25519_Ladder_Step_swap_cond(nq, nqpq, nq2, nqpq2, bit);
}

static void Hacl_Impl_Ed25519_Ladder_Step_loop_step(uint64_t *b, uint8_t *k1, uint32_t ctr)
{
  (void )(b + (uint32_t )20);
  (void )(b + (uint32_t )40);
  (void )(b + (uint32_t )60);
  uint8_t bit = Hacl_Impl_Ed25519_Ladder_Step_ith_bit(k1, ctr);
  Hacl_Impl_Ed25519_Ladder_Step_loop_step_1(b, k1, ctr, bit);
  Hacl_Impl_Ed25519_Ladder_Step_loop_step_2(b, k1, ctr);
  Hacl_Impl_Ed25519_Ladder_Step_loop_step_3(b, k1, ctr, bit);
}

static void Hacl_Impl_Ed25519_Ladder_point_mul_(uint64_t *b, uint8_t *k1)
{
  (void )(b + (uint32_t )20);
  for (uint32_t i = (uint32_t )0; i < (uint32_t )256; i = i + (uint32_t )1)
  {
    (void )(b + (uint32_t )20);
    Hacl_Impl_Ed25519_Ladder_Step_loop_step(b, k1, (uint32_t )256 - i - (uint32_t )1);
  }
}

static void Hacl_Impl_Ed25519_Ladder_make_point_inf(uint64_t *b)
{
  uint64_t *x = b;
  uint64_t *y = b + (uint32_t )5;
  uint64_t *z = b + (uint32_t )10;
  uint64_t *t = b + (uint32_t )15;
  uint64_t zero1 = (uint64_t )0;
  Hacl_Lib_Create64_make_h64_5(x, zero1, zero1, zero1, zero1, zero1);
  uint64_t zero10 = (uint64_t )0;
  uint64_t one10 = (uint64_t )1;
  Hacl_Lib_Create64_make_h64_5(y, one10, zero10, zero10, zero10, zero10);
  uint64_t zero11 = (uint64_t )0;
  uint64_t one1 = (uint64_t )1;
  Hacl_Lib_Create64_make_h64_5(z, one1, zero11, zero11, zero11, zero11);
  uint64_t zero12 = (uint64_t )0;
  Hacl_Lib_Create64_make_h64_5(t, zero12, zero12, zero12, zero12, zero12);
}

static void Hacl_Impl_Ed25519_Ladder_point_mul(uint64_t *result, uint8_t *scalar, uint64_t *q1)
{
  uint64_t b[80] = { 0 };
  uint64_t *nq = b;
  uint64_t *nqpq = b + (uint32_t )20;
  Hacl_Impl_Ed25519_Ladder_make_point_inf(nq);
  Hacl_Impl_Ed25519_SwapConditional_copy(nqpq, q1);
  Hacl_Impl_Ed25519_Ladder_point_mul_(b, scalar);
  Hacl_Impl_Ed25519_SwapConditional_copy(result, nq);
}

static void
Hacl_Hash_Lib_LoadStore_uint64s_from_be_bytes(uint64_t *output, uint8_t *input, uint32_t len1)
{
  for (uint32_t i = (uint32_t )0; i < len1; i = i + (uint32_t )1)
  {
    uint8_t *x0 = input + (uint32_t )8 * i;
    uint64_t inputi = load64_be(x0);
    output[i] = inputi;
  }
}

static void
Hacl_Hash_Lib_LoadStore_uint64s_to_be_bytes(uint8_t *output, uint64_t *input, uint32_t len1)
{
  for (uint32_t i = (uint32_t )0; i < len1; i = i + (uint32_t )1)
  {
    uint64_t hd1 = input[i];
    uint8_t *x0 = output + (uint32_t )8 * i;
    store64_be(x0, hd1);
  }
}

static void Hacl_Hash_SHA2_512_init(uint64_t *state)
{
  (void )(state + (uint32_t )168);
  uint64_t *k1 = state;
  uint64_t *h_01 = state + (uint32_t )160;
  uint64_t *p10 = k1;
  uint64_t *p20 = k1 + (uint32_t )16;
  uint64_t *p3 = k1 + (uint32_t )32;
  uint64_t *p4 = k1 + (uint32_t )48;
  uint64_t *p5 = k1 + (uint32_t )64;
  uint64_t *p11 = p10;
  uint64_t *p21 = p10 + (uint32_t )8;
  uint64_t *p12 = p11;
  uint64_t *p22 = p11 + (uint32_t )4;
  p12[0] = (uint64_t )0x428a2f98d728ae22;
  p12[1] = (uint64_t )0x7137449123ef65cd;
  p12[2] = (uint64_t )0xb5c0fbcfec4d3b2f;
  p12[3] = (uint64_t )0xe9b5dba58189dbbc;
  p22[0] = (uint64_t )0x3956c25bf348b538;
  p22[1] = (uint64_t )0x59f111f1b605d019;
  p22[2] = (uint64_t )0x923f82a4af194f9b;
  p22[3] = (uint64_t )0xab1c5ed5da6d8118;
  uint64_t *p13 = p21;
  uint64_t *p23 = p21 + (uint32_t )4;
  p13[0] = (uint64_t )0xd807aa98a3030242;
  p13[1] = (uint64_t )0x12835b0145706fbe;
  p13[2] = (uint64_t )0x243185be4ee4b28c;
  p13[3] = (uint64_t )0x550c7dc3d5ffb4e2;
  p23[0] = (uint64_t )0x72be5d74f27b896f;
  p23[1] = (uint64_t )0x80deb1fe3b1696b1;
  p23[2] = (uint64_t )0x9bdc06a725c71235;
  p23[3] = (uint64_t )0xc19bf174cf692694;
  uint64_t *p14 = p20;
  uint64_t *p24 = p20 + (uint32_t )8;
  uint64_t *p15 = p14;
  uint64_t *p25 = p14 + (uint32_t )4;
  p15[0] = (uint64_t )0xe49b69c19ef14ad2;
  p15[1] = (uint64_t )0xefbe4786384f25e3;
  p15[2] = (uint64_t )0x0fc19dc68b8cd5b5;
  p15[3] = (uint64_t )0x240ca1cc77ac9c65;
  p25[0] = (uint64_t )0x2de92c6f592b0275;
  p25[1] = (uint64_t )0x4a7484aa6ea6e483;
  p25[2] = (uint64_t )0x5cb0a9dcbd41fbd4;
  p25[3] = (uint64_t )0x76f988da831153b5;
  uint64_t *p16 = p24;
  uint64_t *p26 = p24 + (uint32_t )4;
  p16[0] = (uint64_t )0x983e5152ee66dfab;
  p16[1] = (uint64_t )0xa831c66d2db43210;
  p16[2] = (uint64_t )0xb00327c898fb213f;
  p16[3] = (uint64_t )0xbf597fc7beef0ee4;
  p26[0] = (uint64_t )0xc6e00bf33da88fc2;
  p26[1] = (uint64_t )0xd5a79147930aa725;
  p26[2] = (uint64_t )0x06ca6351e003826f;
  p26[3] = (uint64_t )0x142929670a0e6e70;
  uint64_t *p17 = p3;
  uint64_t *p27 = p3 + (uint32_t )8;
  uint64_t *p18 = p17;
  uint64_t *p28 = p17 + (uint32_t )4;
  p18[0] = (uint64_t )0x27b70a8546d22ffc;
  p18[1] = (uint64_t )0x2e1b21385c26c926;
  p18[2] = (uint64_t )0x4d2c6dfc5ac42aed;
  p18[3] = (uint64_t )0x53380d139d95b3df;
  p28[0] = (uint64_t )0x650a73548baf63de;
  p28[1] = (uint64_t )0x766a0abb3c77b2a8;
  p28[2] = (uint64_t )0x81c2c92e47edaee6;
  p28[3] = (uint64_t )0x92722c851482353b;
  uint64_t *p19 = p27;
  uint64_t *p29 = p27 + (uint32_t )4;
  p19[0] = (uint64_t )0xa2bfe8a14cf10364;
  p19[1] = (uint64_t )0xa81a664bbc423001;
  p19[2] = (uint64_t )0xc24b8b70d0f89791;
  p19[3] = (uint64_t )0xc76c51a30654be30;
  p29[0] = (uint64_t )0xd192e819d6ef5218;
  p29[1] = (uint64_t )0xd69906245565a910;
  p29[2] = (uint64_t )0xf40e35855771202a;
  p29[3] = (uint64_t )0x106aa07032bbd1b8;
  uint64_t *p110 = p4;
  uint64_t *p210 = p4 + (uint32_t )8;
  uint64_t *p111 = p110;
  uint64_t *p211 = p110 + (uint32_t )4;
  p111[0] = (uint64_t )0x19a4c116b8d2d0c8;
  p111[1] = (uint64_t )0x1e376c085141ab53;
  p111[2] = (uint64_t )0x2748774cdf8eeb99;
  p111[3] = (uint64_t )0x34b0bcb5e19b48a8;
  p211[0] = (uint64_t )0x391c0cb3c5c95a63;
  p211[1] = (uint64_t )0x4ed8aa4ae3418acb;
  p211[2] = (uint64_t )0x5b9cca4f7763e373;
  p211[3] = (uint64_t )0x682e6ff3d6b2b8a3;
  uint64_t *p112 = p210;
  uint64_t *p212 = p210 + (uint32_t )4;
  p112[0] = (uint64_t )0x748f82ee5defb2fc;
  p112[1] = (uint64_t )0x78a5636f43172f60;
  p112[2] = (uint64_t )0x84c87814a1f0ab72;
  p112[3] = (uint64_t )0x8cc702081a6439ec;
  p212[0] = (uint64_t )0x90befffa23631e28;
  p212[1] = (uint64_t )0xa4506cebde82bde9;
  p212[2] = (uint64_t )0xbef9a3f7b2c67915;
  p212[3] = (uint64_t )0xc67178f2e372532b;
  uint64_t *p113 = p5;
  uint64_t *p213 = p5 + (uint32_t )8;
  uint64_t *p1 = p113;
  uint64_t *p214 = p113 + (uint32_t )4;
  p1[0] = (uint64_t )0xca273eceea26619c;
  p1[1] = (uint64_t )0xd186b8c721c0c207;
  p1[2] = (uint64_t )0xeada7dd6cde0eb1e;
  p1[3] = (uint64_t )0xf57d4f7fee6ed178;
  p214[0] = (uint64_t )0x06f067aa72176fba;
  p214[1] = (uint64_t )0x0a637dc5a2c898a6;
  p214[2] = (uint64_t )0x113f9804bef90dae;
  p214[3] = (uint64_t )0x1b710b35131c471b;
  uint64_t *p114 = p213;
  uint64_t *p215 = p213 + (uint32_t )4;
  p114[0] = (uint64_t )0x28db77f523047d84;
  p114[1] = (uint64_t )0x32caab7b40c72493;
  p114[2] = (uint64_t )0x3c9ebe0a15c9bebc;
  p114[3] = (uint64_t )0x431d67c49c100d4c;
  p215[0] = (uint64_t )0x4cc5d4becb3e42b6;
  p215[1] = (uint64_t )0x597f299cfc657e2a;
  p215[2] = (uint64_t )0x5fcb6fab3ad6faec;
  p215[3] = (uint64_t )0x6c44198c4a475817;
  uint64_t *p115 = h_01;
  uint64_t *p2 = h_01 + (uint32_t )4;
  p115[0] = (uint64_t )0x6a09e667f3bcc908;
  p115[1] = (uint64_t )0xbb67ae8584caa73b;
  p115[2] = (uint64_t )0x3c6ef372fe94f82b;
  p115[3] = (uint64_t )0xa54ff53a5f1d36f1;
  p2[0] = (uint64_t )0x510e527fade682d1;
  p2[1] = (uint64_t )0x9b05688c2b3e6c1f;
  p2[2] = (uint64_t )0x1f83d9abfb41bd6b;
  p2[3] = (uint64_t )0x5be0cd19137e2179;
}

static void Hacl_Hash_SHA2_512_update(uint64_t *state, uint8_t *data)
{
  KRML_CHECK_SIZE((uint64_t )(uint32_t )0, (uint32_t )16);
  uint64_t data_w[16];
  for (uintmax_t _i = 0; _i < (uint32_t )16; ++_i)
    data_w[_i] = (uint64_t )(uint32_t )0;
  Hacl_Hash_Lib_LoadStore_uint64s_from_be_bytes(data_w, data, (uint32_t )16);
  uint64_t *hash_w = state + (uint32_t )160;
  uint64_t *ws_w = state + (uint32_t )80;
  uint64_t *k_w = state;
  uint64_t *counter_w = state + (uint32_t )168;
  for (uint32_t i = (uint32_t )0; i < (uint32_t )16; i = i + (uint32_t )1)
  {
    uint64_t uu____242 = data_w[i];
    ws_w[i] = uu____242;
  }
  for (uint32_t i = (uint32_t )16; i < (uint32_t )80; i = i + (uint32_t )1)
  {
    uint64_t t16 = ws_w[i - (uint32_t )16];
    uint64_t t15 = ws_w[i - (uint32_t )15];
    uint64_t t7 = ws_w[i - (uint32_t )7];
    uint64_t t2 = ws_w[i - (uint32_t )2];
    ws_w[i] =
      ((t2 >> (uint32_t )19 | t2 << (uint32_t )64 - (uint32_t )19)
      ^ (t2 >> (uint32_t )61 | t2 << (uint32_t )64 - (uint32_t )61) ^ t2 >> (uint32_t )6)
      +
        t7
        +
          ((t15 >> (uint32_t )1 | t15 << (uint32_t )64 - (uint32_t )1)
          ^ (t15 >> (uint32_t )8 | t15 << (uint32_t )64 - (uint32_t )8) ^ t15 >> (uint32_t )7)
          + t16;
  }
  uint64_t hash_0[8] = { 0 };
  memcpy(hash_0, hash_w, (uint32_t )8 * sizeof hash_w[0]);
  for (uint32_t i = (uint32_t )0; i < (uint32_t )80; i = i + (uint32_t )1)
  {
    uint64_t a = hash_0[0];
    uint64_t b = hash_0[1];
    uint64_t c = hash_0[2];
    uint64_t d1 = hash_0[3];
    uint64_t e = hash_0[4];
    uint64_t f1 = hash_0[5];
    uint64_t g1 = hash_0[6];
    uint64_t h = hash_0[7];
    uint64_t k_t = k_w[i];
    uint64_t ws_t = ws_w[i];
    uint64_t
    t1 =
      h
      +
        ((e >> (uint32_t )14 | e << (uint32_t )64 - (uint32_t )14)
        ^
          (e >> (uint32_t )18 | e << (uint32_t )64 - (uint32_t )18)
          ^ (e >> (uint32_t )41 | e << (uint32_t )64 - (uint32_t )41))
      + (e & f1 ^ ~e & g1)
      + k_t
      + ws_t;
    uint64_t
    t2 =
      ((a >> (uint32_t )28 | a << (uint32_t )64 - (uint32_t )28)
      ^
        (a >> (uint32_t )34 | a << (uint32_t )64 - (uint32_t )34)
        ^ (a >> (uint32_t )39 | a << (uint32_t )64 - (uint32_t )39))
      + (a & b ^ a & c ^ b & c);
    uint64_t x1 = t1 + t2;
    uint64_t x5 = d1 + t1;
    uint64_t *p1 = hash_0;
    uint64_t *p2 = hash_0 + (uint32_t )4;
    p1[0] = x1;
    p1[1] = a;
    p1[2] = b;
    p1[3] = c;
    p2[0] = x5;
    p2[1] = e;
    p2[2] = f1;
    p2[3] = g1;
  }
  for (uint32_t i = (uint32_t )0; i < (uint32_t )8; i = i + (uint32_t )1)
  {
    uint64_t uu____871 = hash_w[i];
    uint64_t uu____874 = hash_0[i];
    uint64_t uu____870 = uu____871 + uu____874;
    hash_w[i] = uu____870;
  }
  uint64_t c0 = counter_w[0];
  uint64_t one1 = (uint64_t )(uint32_t )1;
  counter_w[0] = c0 + one1;
}

static void Hacl_Hash_SHA2_512_update_multi(uint64_t *state, uint8_t *data, uint32_t n1)
{
  for (uint32_t i = (uint32_t )0; i < n1; i = i + (uint32_t )1)
  {
    uint8_t *b = data + i * (uint32_t )128;
    Hacl_Hash_SHA2_512_update(state, b);
  }
}

static void Hacl_Hash_SHA2_512_update_last(uint64_t *state, uint8_t *data, uint64_t len1)
{
  uint8_t blocks[256] = { 0 };
  uint32_t nb;
  if (len1 < (uint64_t )112)
    nb = (uint32_t )1;
  else
    nb = (uint32_t )2;
  uint8_t *final_blocks;
  if (len1 < (uint64_t )112)
    final_blocks = blocks + (uint32_t )128;
  else
    final_blocks = blocks;
  memcpy(final_blocks, data, (uint32_t )len1 * sizeof data[0]);
  uint64_t n1 = state[168];
  uint8_t *padding = final_blocks + (uint32_t )len1;
  FStar_UInt128_t
  encodedlen =
    FStar_UInt128_shift_left(FStar_UInt128_add(FStar_UInt128_mul_wide(n1,
          (uint64_t )(uint32_t )128),
        FStar_Int_Cast_Full_uint64_to_uint128(len1)),
      (uint32_t )3);
  uint32_t
  pad0len = ((uint32_t )256 - ((uint32_t )len1 + (uint32_t )16 + (uint32_t )1)) % (uint32_t )128;
  uint8_t *buf1 = padding;
  (void )(padding + (uint32_t )1);
  uint8_t *buf2 = padding + (uint32_t )1 + pad0len;
  buf1[0] = (uint8_t )0x80;
  store128_be(buf2, encodedlen);
  Hacl_Hash_SHA2_512_update_multi(state, final_blocks, nb);
}

static void Hacl_Hash_SHA2_512_finish(uint64_t *state, uint8_t *hash1)
{
  uint64_t *hash_w = state + (uint32_t )160;
  Hacl_Hash_Lib_LoadStore_uint64s_to_be_bytes(hash1, hash_w, (uint32_t )8);
}

static void Hacl_Hash_SHA2_512_hash(uint8_t *hash1, uint8_t *input, uint32_t len1)
{
  KRML_CHECK_SIZE((uint64_t )(uint32_t )0, (uint32_t )169);
  uint64_t state[169];
  for (uintmax_t _i = 0; _i < (uint32_t )169; ++_i)
    state[_i] = (uint64_t )(uint32_t )0;
  uint32_t n1 = len1 / (uint32_t )128;
  uint32_t r = len1 % (uint32_t )128;
  uint8_t *input_blocks = input;
  uint8_t *input_last = input + n1 * (uint32_t )128;
  Hacl_Hash_SHA2_512_init(state);
  Hacl_Hash_SHA2_512_update_multi(state, input_blocks, n1);
  Hacl_Hash_SHA2_512_update_last(state, input_last, (uint64_t )r);
  Hacl_Hash_SHA2_512_finish(state, hash1);
}

static void SHA2_512_hash(uint8_t *hash1, uint8_t *input, uint32_t len1)
{
  Hacl_Hash_SHA2_512_hash(hash1, input, len1);
}

static void Hacl_Impl_Ed25519_SecretExpand_secret_expand(uint8_t *expanded, uint8_t *secret)
{
  SHA2_512_hash(expanded, secret, (uint32_t )32);
  uint8_t *h_low = expanded;
  (void )(expanded + (uint32_t )32);
  uint8_t h_low0 = h_low[0];
  uint8_t h_low31 = h_low[31];
  h_low[0] = h_low0 & (uint8_t )0xf8;
  h_low[31] = h_low31 & (uint8_t )127 | (uint8_t )64;
}

static void Hacl_Impl_Ed25519_SecretToPublic_point_mul_g(uint64_t *result, uint8_t *scalar)
{
  uint64_t g1[20] = { 0 };
  Hacl_Impl_Ed25519_G_make_g(g1);
  Hacl_Impl_Ed25519_Ladder_point_mul(result, scalar, g1);
}

static void
Hacl_Impl_Ed25519_SecretToPublic_secret_to_public_(
  uint8_t *out,
  uint8_t *secret,
  uint8_t *expanded_secret
)
{
  uint8_t *a = expanded_secret;
  uint64_t res[20] = { 0 };
  Hacl_Impl_Ed25519_SecretToPublic_point_mul_g(res, a);
  Hacl_Impl_Ed25519_PointCompress_point_compress(out, res);
}

static void Hacl_Impl_Ed25519_SecretToPublic_secret_to_public(uint8_t *out, uint8_t *secret)
{
  uint8_t expanded[64] = { 0 };
  Hacl_Impl_Ed25519_SecretExpand_secret_expand(expanded, secret);
  Hacl_Impl_Ed25519_SecretToPublic_secret_to_public_(out, secret, expanded);
}

static bool Hacl_Impl_Ed25519_PointEqual_gte_q(uint64_t *s)
{
  uint64_t s0 = s[0];
  uint64_t s1 = s[1];
  uint64_t s2 = s[2];
  uint64_t s3 = s[3];
  uint64_t s4 = s[4];
  if (s4 > (uint64_t )0x00000010000000)
    return true;
  else if (s4 < (uint64_t )0x00000010000000)
    return false;
  else if (s3 > (uint64_t )0x00000000000000)
    return true;
  else if (s2 > (uint64_t )0x000000000014de)
    return true;
  else if (s2 < (uint64_t )0x000000000014de)
    return false;
  else if (s1 > (uint64_t )0xf9dea2f79cd658)
    return true;
  else if (s1 < (uint64_t )0xf9dea2f79cd658)
    return false;
  else if (s0 >= (uint64_t )0x12631a5cf5d3ed)
    return true;
  else
    return false;
}

static bool Hacl_Impl_Ed25519_PointEqual_eq(uint64_t *a, uint64_t *b)
{
  uint64_t a0 = a[0];
  uint64_t a1 = a[1];
  uint64_t a2 = a[2];
  uint64_t a3 = a[3];
  uint64_t a4 = a[4];
  uint64_t b0 = b[0];
  uint64_t b1 = b[1];
  uint64_t b2 = b[2];
  uint64_t b3 = b[3];
  uint64_t b4 = b[4];
  bool z = a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3 && a4 == b4;
  return z;
}

static bool
Hacl_Impl_Ed25519_PointEqual_point_equal_1(uint64_t *p, uint64_t *q1, uint64_t *tmp)
{
  uint64_t *pxqz = tmp;
  uint64_t *qxpz = tmp + (uint32_t )5;
  (void )(tmp + (uint32_t )10);
  (void )(tmp + (uint32_t )15);
  Hacl_Bignum25519_fmul(pxqz,
    Hacl_Impl_Ed25519_ExtPoint_getx(p),
    Hacl_Impl_Ed25519_ExtPoint_getz(q1));
  Hacl_Bignum25519_reduce(pxqz);
  Hacl_Bignum25519_fmul(qxpz,
    Hacl_Impl_Ed25519_ExtPoint_getx(q1),
    Hacl_Impl_Ed25519_ExtPoint_getz(p));
  Hacl_Bignum25519_reduce(qxpz);
  bool b = Hacl_Impl_Ed25519_PointEqual_eq(pxqz, qxpz);
  return b;
}

static bool
Hacl_Impl_Ed25519_PointEqual_point_equal_2(uint64_t *p, uint64_t *q1, uint64_t *tmp)
{
  (void )(tmp + (uint32_t )5);
  uint64_t *pyqz = tmp + (uint32_t )10;
  uint64_t *qypz = tmp + (uint32_t )15;
  Hacl_Bignum25519_fmul(pyqz,
    Hacl_Impl_Ed25519_ExtPoint_gety(p),
    Hacl_Impl_Ed25519_ExtPoint_getz(q1));
  Hacl_Bignum25519_reduce(pyqz);
  Hacl_Bignum25519_fmul(qypz,
    Hacl_Impl_Ed25519_ExtPoint_gety(q1),
    Hacl_Impl_Ed25519_ExtPoint_getz(p));
  Hacl_Bignum25519_reduce(qypz);
  bool b = Hacl_Impl_Ed25519_PointEqual_eq(pyqz, qypz);
  return b;
}

static bool Hacl_Impl_Ed25519_PointEqual_point_equal_(uint64_t *p, uint64_t *q1, uint64_t *tmp)
{
  bool b = Hacl_Impl_Ed25519_PointEqual_point_equal_1(p, q1, tmp);
  if (b == true)
    return Hacl_Impl_Ed25519_PointEqual_point_equal_2(p, q1, tmp);
  else
    return false;
}

static bool Hacl_Impl_Ed25519_PointEqual_point_equal(uint64_t *p, uint64_t *q1)
{
  uint64_t tmp[20] = { 0 };
  bool res = Hacl_Impl_Ed25519_PointEqual_point_equal_(p, q1, tmp);
  return res;
}

static void Hacl_Impl_Load56_load_64_bytes(uint64_t *out, uint8_t *b)
{
  uint8_t *b80 = b;
  uint64_t z = load64_le(b80);
  uint64_t z_ = z & (uint64_t )0xffffffffffffff;
  uint64_t b0 = z_;
  uint8_t *b81 = b + (uint32_t )7;
  uint64_t z0 = load64_le(b81);
  uint64_t z_0 = z0 & (uint64_t )0xffffffffffffff;
  uint64_t b1 = z_0;
  uint8_t *b82 = b + (uint32_t )14;
  uint64_t z1 = load64_le(b82);
  uint64_t z_1 = z1 & (uint64_t )0xffffffffffffff;
  uint64_t b2 = z_1;
  uint8_t *b83 = b + (uint32_t )21;
  uint64_t z2 = load64_le(b83);
  uint64_t z_2 = z2 & (uint64_t )0xffffffffffffff;
  uint64_t b3 = z_2;
  uint8_t *b84 = b + (uint32_t )28;
  uint64_t z3 = load64_le(b84);
  uint64_t z_3 = z3 & (uint64_t )0xffffffffffffff;
  uint64_t b4 = z_3;
  uint8_t *b85 = b + (uint32_t )35;
  uint64_t z4 = load64_le(b85);
  uint64_t z_4 = z4 & (uint64_t )0xffffffffffffff;
  uint64_t b5 = z_4;
  uint8_t *b86 = b + (uint32_t )42;
  uint64_t z5 = load64_le(b86);
  uint64_t z_5 = z5 & (uint64_t )0xffffffffffffff;
  uint64_t b6 = z_5;
  uint8_t *b87 = b + (uint32_t )49;
  uint64_t z6 = load64_le(b87);
  uint64_t z_6 = z6 & (uint64_t )0xffffffffffffff;
  uint64_t b7 = z_6;
  uint8_t *b8 = b + (uint32_t )56;
  uint64_t z7 = load64_le(b8);
  uint64_t z_7 = z7 & (uint64_t )0xffffffffffffff;
  uint64_t b88 = z_7;
  uint8_t b63 = b[63];
  uint64_t b9 = (uint64_t )b63;
  Hacl_Lib_Create64_make_h64_10(out, b0, b1, b2, b3, b4, b5, b6, b7, b88, b9);
}

static void Hacl_Impl_Load56_load_32_bytes(uint64_t *out, uint8_t *b)
{
  uint8_t *b80 = b;
  uint64_t z = load64_le(b80);
  uint64_t z_ = z & (uint64_t )0xffffffffffffff;
  uint64_t b0 = z_;
  uint8_t *b81 = b + (uint32_t )7;
  uint64_t z0 = load64_le(b81);
  uint64_t z_0 = z0 & (uint64_t )0xffffffffffffff;
  uint64_t b1 = z_0;
  uint8_t *b82 = b + (uint32_t )14;
  uint64_t z1 = load64_le(b82);
  uint64_t z_1 = z1 & (uint64_t )0xffffffffffffff;
  uint64_t b2 = z_1;
  uint8_t *b8 = b + (uint32_t )21;
  uint64_t z2 = load64_le(b8);
  uint64_t z_2 = z2 & (uint64_t )0xffffffffffffff;
  uint64_t b3 = z_2;
  uint8_t *x0 = b + (uint32_t )28;
  uint32_t b4 = load32_le(x0);
  uint64_t b41 = (uint64_t )b4;
  Hacl_Lib_Create64_make_h64_5(out, b0, b1, b2, b3, b41);
}

inline static void Hacl_Impl_Ed25519_Pow2_252m2_pow2_252m2(uint64_t *out, uint64_t *z)
{
  Hacl_Bignum_Crecip_crecip_(out, z);
}

static bool Hacl_Impl_Ed25519_RecoverX_is_0(uint64_t *x)
{
  uint64_t x0 = x[0];
  uint64_t x1 = x[1];
  uint64_t x2 = x[2];
  uint64_t x3 = x[3];
  uint64_t x4 = x[4];
  return
    x0
    == (uint64_t )0
    && x1 == (uint64_t )0
    && x2 == (uint64_t )0
    && x3 == (uint64_t )0
    && x4 == (uint64_t )0;
}

static void
Hacl_Impl_Ed25519_RecoverX_recover_x_step_5(uint64_t *x, uint64_t sign1, uint64_t *tmp)
{
  uint64_t *x3 = tmp + (uint32_t )5;
  uint64_t *t0 = tmp + (uint32_t )10;
  uint64_t x0 = x3[0];
  uint64_t x00 = x0 & (uint64_t )1;
  if (!(x00 == sign1))
  {
    uint64_t zero1 = (uint64_t )0;
    Hacl_Lib_Create64_make_h64_5(t0, zero1, zero1, zero1, zero1, zero1);
    Hacl_Bignum25519_fdifference(x3, t0);
    Hacl_Bignum25519_reduce_513(x3);
    Hacl_Bignum25519_reduce(x3);
  }
  memcpy(x, x3, (uint32_t )5 * sizeof x3[0]);
}

static bool
Hacl_Impl_Ed25519_RecoverX_recover_x_(uint64_t *x, uint64_t *y, uint64_t sign1, uint64_t *tmp)
{
  uint64_t *x20 = tmp;
  uint64_t x0 = y[0];
  uint64_t x1 = y[1];
  uint64_t x2 = y[2];
  uint64_t x30 = y[3];
  uint64_t x4 = y[4];
  bool
  b =
    x0
    >= (uint64_t )0x7ffffffffffed
    && x1 == (uint64_t )0x7ffffffffffff
    && x2 == (uint64_t )0x7ffffffffffff
    && x30 == (uint64_t )0x7ffffffffffff
    && x4 == (uint64_t )0x7ffffffffffff;
  if (b)
    return false;
  else
  {
    uint64_t tmp0[25] = { 0 };
    uint64_t *one10 = tmp0;
    uint64_t *y2 = tmp0 + (uint32_t )5;
    uint64_t *dyyi = tmp0 + (uint32_t )10;
    uint64_t *dyy = tmp0 + (uint32_t )15;
    uint64_t zero10 = (uint64_t )0;
    uint64_t one1 = (uint64_t )1;
    Hacl_Lib_Create64_make_h64_5(one10, one1, zero10, zero10, zero10, zero10);
    Hacl_Bignum25519_fsquare(y2, y);
    Hacl_Bignum25519_times_d(dyy, y2);
    Hacl_Bignum25519_fsum(dyy, one10);
    Hacl_Bignum25519_reduce_513(dyy);
    Hacl_Bignum25519_inverse(dyyi, dyy);
    Hacl_Bignum25519_fdifference(one10, y2);
    Hacl_Bignum25519_fmul(x20, dyyi, one10);
    Hacl_Bignum25519_reduce(x20);
    bool x2_is_0 = Hacl_Impl_Ed25519_RecoverX_is_0(x20);
    uint8_t z;
    if (x2_is_0)
    {
      uint8_t ite;
      if (sign1 == (uint64_t )0)
      {
        uint64_t zero1 = (uint64_t )0;
        Hacl_Lib_Create64_make_h64_5(x, zero1, zero1, zero1, zero1, zero1);
        ite = (uint8_t )1;
      }
      else
        ite = (uint8_t )0;
      z = ite;
    }
    else
      z = (uint8_t )2;
    if (z == (uint8_t )0)
      return false;
    else if (z == (uint8_t )1)
      return true;
    else
    {
      uint64_t *x2 = tmp;
      uint64_t *x30 = tmp + (uint32_t )5;
      uint64_t *t00 = tmp + (uint32_t )10;
      uint64_t *t10 = tmp + (uint32_t )15;
      Hacl_Impl_Ed25519_Pow2_252m2_pow2_252m2(x30, x2);
      Hacl_Bignum25519_fsquare(t00, x30);
      memcpy(t10, x2, (uint32_t )5 * sizeof x2[0]);
      Hacl_Bignum25519_fdifference(t10, t00);
      Hacl_Bignum25519_reduce_513(t10);
      Hacl_Bignum25519_reduce(t10);
      bool t1_is_0 = Hacl_Impl_Ed25519_RecoverX_is_0(t10);
      if (t1_is_0)
      {
        
      }
      else
      {
        uint64_t sqrt_m1[5] = { 0 };
        Hacl_Lib_Create64_make_h64_5(sqrt_m1,
          (uint64_t )0x00061b274a0ea0b0,
          (uint64_t )0x0000d5a5fc8f189d,
          (uint64_t )0x0007ef5e9cbd0c60,
          (uint64_t )0x00078595a6804c9e,
          (uint64_t )0x0002b8324804fc1d);
        Hacl_Bignum25519_fmul(x30, x30, sqrt_m1);
      }
      Hacl_Bignum25519_reduce(x30);
      uint64_t *x20 = tmp;
      uint64_t *x3 = tmp + (uint32_t )5;
      uint64_t *t0 = tmp + (uint32_t )10;
      uint64_t *t1 = tmp + (uint32_t )15;
      Hacl_Bignum25519_fsquare(t0, x3);
      memcpy(t1, x20, (uint32_t )5 * sizeof x20[0]);
      Hacl_Bignum25519_fdifference(t1, t0);
      Hacl_Bignum25519_reduce_513(t1);
      Hacl_Bignum25519_reduce(t1);
      bool z1 = Hacl_Impl_Ed25519_RecoverX_is_0(t1);
      if (z1 == false)
        return false;
      else
      {
        Hacl_Impl_Ed25519_RecoverX_recover_x_step_5(x, sign1, tmp);
        return true;
      }
    }
  }
}

static bool Hacl_Impl_Ed25519_RecoverX_recover_x(uint64_t *x, uint64_t *y, uint64_t sign1)
{
  uint64_t tmp[20] = { 0 };
  bool res = Hacl_Impl_Ed25519_RecoverX_recover_x_(x, y, sign1, tmp);
  return res;
}

static void Hacl_Impl_Load51_load_51(uint64_t *output, uint8_t *input)
{
  Hacl_EC_Format_fexpand(output, input);
}

static bool Hacl_Impl_Ed25519_PointDecompress_point_decompress(uint64_t *out, uint8_t *s)
{
  uint64_t tmp[10] = { 0 };
  uint64_t *y0 = tmp;
  uint64_t *x0 = tmp + (uint32_t )5;
  uint64_t *y = tmp;
  uint64_t *x = tmp + (uint32_t )5;
  uint8_t s31 = s[31];
  uint64_t sign1 = (uint64_t )(s31 >> (uint32_t )7);
  Hacl_Impl_Load51_load_51(y, s);
  bool z = Hacl_Impl_Ed25519_RecoverX_recover_x(x, y, sign1);
  bool z0 = z;
  bool res;
  if (z0 == false)
    res = false;
  else
  {
    uint64_t *outx = Hacl_Impl_Ed25519_ExtPoint_getx(out);
    uint64_t *outy = Hacl_Impl_Ed25519_ExtPoint_gety(out);
    uint64_t *outz = Hacl_Impl_Ed25519_ExtPoint_getz(out);
    uint64_t *outt = Hacl_Impl_Ed25519_ExtPoint_gett(out);
    memcpy(outx, x0, (uint32_t )5 * sizeof x0[0]);
    memcpy(outy, y0, (uint32_t )5 * sizeof y0[0]);
    uint64_t zero1 = (uint64_t )0;
    uint64_t one1 = (uint64_t )1;
    Hacl_Lib_Create64_make_h64_5(outz, one1, zero1, zero1, zero1, zero1);
    Hacl_Bignum25519_fmul(outt, x0, y0);
    res = true;
  }
  return res;
}

static void Hacl_Impl_Store56_store_56(uint8_t *out, uint64_t *b)
{
  uint64_t b0 = b[0];
  uint64_t b1 = b[1];
  uint64_t b2 = b[2];
  uint64_t b3 = b[3];
  uint64_t b4 = b[4];
  uint32_t b41 = (uint32_t )b4;
  uint8_t *b8 = out;
  store64_le(b8, b0);
  uint8_t *b80 = out + (uint32_t )7;
  store64_le(b80, b1);
  uint8_t *b81 = out + (uint32_t )14;
  store64_le(b81, b2);
  uint8_t *b82 = out + (uint32_t )21;
  store64_le(b82, b3);
  uint8_t *x0 = out + (uint32_t )28;
  store32_le(x0, b41);
}

static void
Hacl_Impl_SHA512_Ed25519_2_hash_block_and_rest(
  uint8_t *out,
  uint8_t *block,
  uint8_t *msg,
  uint32_t len1
)
{
  uint32_t nblocks = len1 >> (uint32_t )7;
  uint64_t rest = (uint64_t )(len1 & (uint32_t )127);
  uint64_t st[169] = { 0 };
  Hacl_Hash_SHA2_512_init(st);
  Hacl_Hash_SHA2_512_update(st, block);
  Hacl_Hash_SHA2_512_update_multi(st, msg, nblocks);
  Hacl_Hash_SHA2_512_update_last(st, msg + (uint32_t )128 * nblocks, rest);
  Hacl_Hash_SHA2_512_finish(st, out);
}

static void
Hacl_Impl_SHA512_Ed25519_1_copy_bytes(uint8_t *output, uint8_t *input, uint32_t len1)
{
  memcpy(output, input, len1 * sizeof input[0]);
}

static void
Hacl_Impl_SHA512_Ed25519_1_concat_2(uint8_t *out, uint8_t *pre, uint8_t *msg, uint32_t len1)
{
  Hacl_Impl_SHA512_Ed25519_1_copy_bytes(out, pre, (uint32_t )32);
  Hacl_Impl_SHA512_Ed25519_1_copy_bytes(out + (uint32_t )32, msg, len1);
}

static void
Hacl_Impl_SHA512_Ed25519_1_concat_3(
  uint8_t *out,
  uint8_t *pre,
  uint8_t *pre2,
  uint8_t *msg,
  uint32_t len1
)
{
  Hacl_Impl_SHA512_Ed25519_1_copy_bytes(out, pre, (uint32_t )32);
  Hacl_Impl_SHA512_Ed25519_1_copy_bytes(out + (uint32_t )32, pre2, (uint32_t )32);
  Hacl_Impl_SHA512_Ed25519_1_copy_bytes(out + (uint32_t )64, msg, len1);
}

static void
Hacl_Impl_SHA512_Ed25519_1_sha512_pre_msg_1(
  uint8_t *h,
  uint8_t *prefix,
  uint8_t *input,
  uint32_t len1
)
{
  uint8_t block[128] = { 0 };
  uint8_t *block_ = block;
  Hacl_Impl_SHA512_Ed25519_1_concat_2(block_, prefix, input, len1);
  Hacl_Hash_SHA2_512_hash(h, block_, len1 + (uint32_t )32);
}

static void
Hacl_Impl_SHA512_Ed25519_1_sha512_pre_pre2_msg_1(
  uint8_t *h,
  uint8_t *prefix,
  uint8_t *prefix2,
  uint8_t *input,
  uint32_t len1
)
{
  uint8_t block[128] = { 0 };
  uint8_t *block_ = block;
  Hacl_Impl_SHA512_Ed25519_1_concat_3(block_, prefix, prefix2, input, len1);
  Hacl_Hash_SHA2_512_hash(h, block_, len1 + (uint32_t )64);
}

static void
Hacl_Impl_SHA512_Ed25519_3_sha512_pre_msg_2(
  uint8_t *h,
  uint8_t *prefix,
  uint8_t *input,
  uint32_t len1
)
{
  uint8_t *input11 = input;
  uint8_t *input21 = input + (uint32_t )96;
  uint8_t block[128] = { 0 };
  Hacl_Impl_SHA512_Ed25519_1_concat_2(block, prefix, input11, (uint32_t )96);
  Hacl_Impl_SHA512_Ed25519_2_hash_block_and_rest(h, block, input21, len1 - (uint32_t )96);
}

static void
Hacl_Impl_SHA512_Ed25519_3_sha512_pre_msg(
  uint8_t *h,
  uint8_t *prefix,
  uint8_t *input,
  uint32_t len1
)
{
  if (len1 <= (uint32_t )96)
    Hacl_Impl_SHA512_Ed25519_1_sha512_pre_msg_1(h, prefix, input, len1);
  else
    Hacl_Impl_SHA512_Ed25519_3_sha512_pre_msg_2(h, prefix, input, len1);
}

static void
Hacl_Impl_SHA512_Ed25519_3_sha512_pre_pre2_msg_2(
  uint8_t *h,
  uint8_t *prefix,
  uint8_t *prefix2,
  uint8_t *input,
  uint32_t len1
)
{
  uint8_t *input11 = input;
  uint8_t *input21 = input + (uint32_t )64;
  uint8_t block[128] = { 0 };
  Hacl_Impl_SHA512_Ed25519_1_concat_3(block, prefix, prefix2, input11, (uint32_t )64);
  Hacl_Impl_SHA512_Ed25519_2_hash_block_and_rest(h, block, input21, len1 - (uint32_t )64);
}

static void
Hacl_Impl_SHA512_Ed25519_3_sha512_pre_pre2_msg(
  uint8_t *h,
  uint8_t *prefix,
  uint8_t *prefix2,
  uint8_t *input,
  uint32_t len1
)
{
  if (len1 <= (uint32_t )64)
    Hacl_Impl_SHA512_Ed25519_1_sha512_pre_pre2_msg_1(h, prefix, prefix2, input, len1);
  else
    Hacl_Impl_SHA512_Ed25519_3_sha512_pre_pre2_msg_2(h, prefix, prefix2, input, len1);
}

static void
Hacl_Impl_SHA512_Ed25519_sha512_pre_msg(
  uint8_t *h,
  uint8_t *prefix,
  uint8_t *input,
  uint32_t len1
)
{
  Hacl_Impl_SHA512_Ed25519_3_sha512_pre_msg(h, prefix, input, len1);
}

static void
Hacl_Impl_SHA512_Ed25519_sha512_pre_pre2_msg(
  uint8_t *h,
  uint8_t *prefix,
  uint8_t *prefix2,
  uint8_t *input,
  uint32_t len1
)
{
  Hacl_Impl_SHA512_Ed25519_3_sha512_pre_pre2_msg(h, prefix, prefix2, input, len1);
}

static void
Hacl_Impl_Sha512_sha512_pre_msg(uint8_t *h, uint8_t *prefix, uint8_t *input, uint32_t len1)
{
  Hacl_Impl_SHA512_Ed25519_sha512_pre_msg(h, prefix, input, len1);
}

static void
Hacl_Impl_Sha512_sha512_pre_pre2_msg(
  uint8_t *h,
  uint8_t *prefix,
  uint8_t *prefix2,
  uint8_t *input,
  uint32_t len1
)
{
  Hacl_Impl_SHA512_Ed25519_sha512_pre_pre2_msg(h, prefix, prefix2, input, len1);
}

static void
Hacl_Lib_Create128_make_h128_9(
  FStar_UInt128_t *b,
  FStar_UInt128_t s0,
  FStar_UInt128_t s1,
  FStar_UInt128_t s2,
  FStar_UInt128_t s3,
  FStar_UInt128_t s4,
  FStar_UInt128_t s5,
  FStar_UInt128_t s6,
  FStar_UInt128_t s7,
  FStar_UInt128_t s8
)
{
  b[0] = s0;
  b[1] = s1;
  b[2] = s2;
  b[3] = s3;
  b[4] = s4;
  b[5] = s5;
  b[6] = s6;
  b[7] = s7;
  b[8] = s8;
}

static void Hacl_Impl_BignumQ_Mul_make_m(uint64_t *m1)
{
  Hacl_Lib_Create64_make_h64_5(m1,
    (uint64_t )0x12631a5cf5d3ed,
    (uint64_t )0xf9dea2f79cd658,
    (uint64_t )0x000000000014de,
    (uint64_t )0x00000000000000,
    (uint64_t )0x00000010000000);
}

static void Hacl_Impl_BignumQ_Mul_make_mu(uint64_t *m1)
{
  Hacl_Lib_Create64_make_h64_5(m1,
    (uint64_t )0x9ce5a30a2c131b,
    (uint64_t )0x215d086329a7ed,
    (uint64_t )0xffffffffeb2106,
    (uint64_t )0xffffffffffffff,
    (uint64_t )0x00000fffffffff);
}

static void Hacl_Impl_BignumQ_Mul_choose(uint64_t *z, uint64_t *x, uint64_t *y, uint64_t b)
{
  uint64_t mask = b - (uint64_t )1;
  uint64_t x0 = x[0];
  uint64_t x1 = x[1];
  uint64_t x2 = x[2];
  uint64_t x3 = x[3];
  uint64_t x4 = x[4];
  uint64_t y0 = y[0];
  uint64_t y1 = y[1];
  uint64_t y2 = y[2];
  uint64_t y3 = y[3];
  uint64_t y4 = y[4];
  uint64_t z0 = (y0 ^ x0) & mask ^ x0;
  uint64_t z1 = (y1 ^ x1) & mask ^ x1;
  uint64_t z2 = (y2 ^ x2) & mask ^ x2;
  uint64_t z3 = (y3 ^ x3) & mask ^ x3;
  uint64_t z4 = (y4 ^ x4) & mask ^ x4;
  Hacl_Lib_Create64_make_h64_5(z, z0, z1, z2, z3, z4);
}

static uint64_t Hacl_Impl_BignumQ_Mul_lt(uint64_t a, uint64_t b)
{
  return a - b >> (uint32_t )63;
}

static uint64_t Hacl_Impl_BignumQ_Mul_shiftl_56(uint64_t b)
{
  return b << (uint32_t )56;
}

static void Hacl_Impl_BignumQ_Mul_sub_mod_264(uint64_t *z, uint64_t *x, uint64_t *y)
{
  uint64_t x0 = x[0];
  uint64_t x1 = x[1];
  uint64_t x2 = x[2];
  uint64_t x3 = x[3];
  uint64_t x4 = x[4];
  uint64_t y0 = y[0];
  uint64_t y1 = y[1];
  uint64_t y2 = y[2];
  uint64_t y3 = y[3];
  uint64_t y4 = y[4];
  uint64_t b = Hacl_Impl_BignumQ_Mul_lt(x0, y0);
  uint64_t t0 = Hacl_Impl_BignumQ_Mul_shiftl_56(b) + x0 - y0;
  uint64_t y11 = y1 + b;
  uint64_t b1 = Hacl_Impl_BignumQ_Mul_lt(x1, y11);
  uint64_t t1 = Hacl_Impl_BignumQ_Mul_shiftl_56(b1) + x1 - y11;
  uint64_t y21 = y2 + b1;
  uint64_t b2 = Hacl_Impl_BignumQ_Mul_lt(x2, y21);
  uint64_t t2 = Hacl_Impl_BignumQ_Mul_shiftl_56(b2) + x2 - y21;
  uint64_t y31 = y3 + b2;
  uint64_t b3 = Hacl_Impl_BignumQ_Mul_lt(x3, y31);
  uint64_t t3 = Hacl_Impl_BignumQ_Mul_shiftl_56(b3) + x3 - y31;
  uint64_t y41 = y4 + b3;
  uint64_t b4 = Hacl_Impl_BignumQ_Mul_lt(x4, y41);
  uint64_t t4 = (b4 << (uint32_t )40) + x4 - y41;
  Hacl_Lib_Create64_make_h64_5(z, t0, t1, t2, t3, t4);
}

static void Hacl_Impl_BignumQ_Mul_subm_conditional(uint64_t *z, uint64_t *x)
{
  uint64_t tmp[5] = { 0 };
  uint64_t x0 = x[0];
  uint64_t x1 = x[1];
  uint64_t x2 = x[2];
  uint64_t x3 = x[3];
  uint64_t x4 = x[4];
  Hacl_Lib_Create64_make_h64_5(tmp, x0, x1, x2, x3, x4);
  uint64_t y0 = (uint64_t )0x12631a5cf5d3ed;
  uint64_t y1 = (uint64_t )0xf9dea2f79cd658;
  uint64_t y2 = (uint64_t )0x000000000014de;
  uint64_t y3 = (uint64_t )0x00000000000000;
  uint64_t y4 = (uint64_t )0x00000010000000;
  uint64_t b = Hacl_Impl_BignumQ_Mul_lt(x0, y0);
  uint64_t t0 = Hacl_Impl_BignumQ_Mul_shiftl_56(b) + x0 - y0;
  uint64_t y11 = y1 + b;
  uint64_t b1 = Hacl_Impl_BignumQ_Mul_lt(x1, y11);
  uint64_t t1 = Hacl_Impl_BignumQ_Mul_shiftl_56(b1) + x1 - y11;
  uint64_t y21 = y2 + b1;
  uint64_t b2 = Hacl_Impl_BignumQ_Mul_lt(x2, y21);
  uint64_t t2 = Hacl_Impl_BignumQ_Mul_shiftl_56(b2) + x2 - y21;
  uint64_t y31 = y3 + b2;
  uint64_t b3 = Hacl_Impl_BignumQ_Mul_lt(x3, y31);
  uint64_t t3 = Hacl_Impl_BignumQ_Mul_shiftl_56(b3) + x3 - y31;
  uint64_t y41 = y4 + b3;
  uint64_t b4 = Hacl_Impl_BignumQ_Mul_lt(x4, y41);
  uint64_t t4 = Hacl_Impl_BignumQ_Mul_shiftl_56(b4) + x4 - y41;
  Hacl_Lib_Create64_make_h64_5(z, t0, t1, t2, t3, t4);
  Hacl_Impl_BignumQ_Mul_choose(z, tmp, z, b4);
}

static void Hacl_Impl_BignumQ_Mul_low_mul_5(uint64_t *z, uint64_t *x, uint64_t *y)
{
  uint64_t x0 = x[0];
  uint64_t x1 = x[1];
  uint64_t x2 = x[2];
  uint64_t x3 = x[3];
  uint64_t x4 = x[4];
  uint64_t y0 = y[0];
  uint64_t y1 = y[1];
  uint64_t y2 = y[2];
  uint64_t y3 = y[3];
  uint64_t y4 = y[4];
  FStar_UInt128_t xy00 = FStar_UInt128_mul_wide(x0, y0);
  FStar_UInt128_t xy01 = FStar_UInt128_mul_wide(x0, y1);
  FStar_UInt128_t xy02 = FStar_UInt128_mul_wide(x0, y2);
  FStar_UInt128_t xy03 = FStar_UInt128_mul_wide(x0, y3);
  FStar_UInt128_t xy04 = FStar_UInt128_mul_wide(x0, y4);
  FStar_UInt128_t xy10 = FStar_UInt128_mul_wide(x1, y0);
  FStar_UInt128_t xy11 = FStar_UInt128_mul_wide(x1, y1);
  FStar_UInt128_t xy12 = FStar_UInt128_mul_wide(x1, y2);
  FStar_UInt128_t xy13 = FStar_UInt128_mul_wide(x1, y3);
  FStar_UInt128_t xy20 = FStar_UInt128_mul_wide(x2, y0);
  FStar_UInt128_t xy21 = FStar_UInt128_mul_wide(x2, y1);
  FStar_UInt128_t xy22 = FStar_UInt128_mul_wide(x2, y2);
  FStar_UInt128_t xy30 = FStar_UInt128_mul_wide(x3, y0);
  FStar_UInt128_t xy31 = FStar_UInt128_mul_wide(x3, y1);
  FStar_UInt128_t xy40 = FStar_UInt128_mul_wide(x4, y0);
  FStar_UInt128_t x5 = xy00;
  FStar_UInt128_t carry1 = FStar_UInt128_shift_right(x5, (uint32_t )56);
  uint64_t t = FStar_Int_Cast_Full_uint128_to_uint64(x5) & (uint64_t )0xffffffffffffff;
  uint64_t t0 = t;
  FStar_UInt128_t x6 = FStar_UInt128_add(FStar_UInt128_add(xy01, xy10), carry1);
  FStar_UInt128_t carry2 = FStar_UInt128_shift_right(x6, (uint32_t )56);
  uint64_t t1 = FStar_Int_Cast_Full_uint128_to_uint64(x6) & (uint64_t )0xffffffffffffff;
  uint64_t t11 = t1;
  FStar_UInt128_t
  x7 = FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_add(xy02, xy11), xy20), carry2);
  FStar_UInt128_t carry3 = FStar_UInt128_shift_right(x7, (uint32_t )56);
  uint64_t t2 = FStar_Int_Cast_Full_uint128_to_uint64(x7) & (uint64_t )0xffffffffffffff;
  uint64_t t21 = t2;
  FStar_UInt128_t
  x8 =
    FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_add(xy03, xy12), xy21),
        xy30),
      carry3);
  FStar_UInt128_t carry4 = FStar_UInt128_shift_right(x8, (uint32_t )56);
  uint64_t t3 = FStar_Int_Cast_Full_uint128_to_uint64(x8) & (uint64_t )0xffffffffffffff;
  uint64_t t31 = t3;
  uint64_t
  t4 =
    FStar_Int_Cast_Full_uint128_to_uint64(FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_add(xy04,
                xy13),
              xy22),
            xy31),
          xy40),
        carry4))
    & (uint64_t )0xffffffffff;
  Hacl_Lib_Create64_make_h64_5(z, t0, t11, t21, t31, t4);
}

static void Hacl_Impl_BignumQ_Mul_mul_5(FStar_UInt128_t *z, uint64_t *x, uint64_t *y)
{
  uint64_t x0 = x[0];
  uint64_t x1 = x[1];
  uint64_t x2 = x[2];
  uint64_t x3 = x[3];
  uint64_t x4 = x[4];
  uint64_t y0 = y[0];
  uint64_t y1 = y[1];
  uint64_t y2 = y[2];
  uint64_t y3 = y[3];
  uint64_t y4 = y[4];
  FStar_UInt128_t xy00 = FStar_UInt128_mul_wide(x0, y0);
  FStar_UInt128_t xy01 = FStar_UInt128_mul_wide(x0, y1);
  FStar_UInt128_t xy02 = FStar_UInt128_mul_wide(x0, y2);
  FStar_UInt128_t xy03 = FStar_UInt128_mul_wide(x0, y3);
  FStar_UInt128_t xy04 = FStar_UInt128_mul_wide(x0, y4);
  FStar_UInt128_t xy10 = FStar_UInt128_mul_wide(x1, y0);
  FStar_UInt128_t xy11 = FStar_UInt128_mul_wide(x1, y1);
  FStar_UInt128_t xy12 = FStar_UInt128_mul_wide(x1, y2);
  FStar_UInt128_t xy13 = FStar_UInt128_mul_wide(x1, y3);
  FStar_UInt128_t xy14 = FStar_UInt128_mul_wide(x1, y4);
  FStar_UInt128_t xy20 = FStar_UInt128_mul_wide(x2, y0);
  FStar_UInt128_t xy21 = FStar_UInt128_mul_wide(x2, y1);
  FStar_UInt128_t xy22 = FStar_UInt128_mul_wide(x2, y2);
  FStar_UInt128_t xy23 = FStar_UInt128_mul_wide(x2, y3);
  FStar_UInt128_t xy24 = FStar_UInt128_mul_wide(x2, y4);
  FStar_UInt128_t xy30 = FStar_UInt128_mul_wide(x3, y0);
  FStar_UInt128_t xy31 = FStar_UInt128_mul_wide(x3, y1);
  FStar_UInt128_t xy32 = FStar_UInt128_mul_wide(x3, y2);
  FStar_UInt128_t xy33 = FStar_UInt128_mul_wide(x3, y3);
  FStar_UInt128_t xy34 = FStar_UInt128_mul_wide(x3, y4);
  FStar_UInt128_t xy40 = FStar_UInt128_mul_wide(x4, y0);
  FStar_UInt128_t xy41 = FStar_UInt128_mul_wide(x4, y1);
  FStar_UInt128_t xy42 = FStar_UInt128_mul_wide(x4, y2);
  FStar_UInt128_t xy43 = FStar_UInt128_mul_wide(x4, y3);
  FStar_UInt128_t xy44 = FStar_UInt128_mul_wide(x4, y4);
  FStar_UInt128_t z0 = xy00;
  FStar_UInt128_t z1 = FStar_UInt128_add(xy01, xy10);
  FStar_UInt128_t z2 = FStar_UInt128_add(FStar_UInt128_add(xy02, xy11), xy20);
  FStar_UInt128_t
  z3 = FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_add(xy03, xy12), xy21), xy30);
  FStar_UInt128_t
  z4 =
    FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_add(xy04, xy13), xy22),
        xy31),
      xy40);
  FStar_UInt128_t
  z5 = FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_add(xy14, xy23), xy32), xy41);
  FStar_UInt128_t z6 = FStar_UInt128_add(FStar_UInt128_add(xy24, xy33), xy42);
  FStar_UInt128_t z7 = FStar_UInt128_add(xy34, xy43);
  FStar_UInt128_t z8 = xy44;
  Hacl_Lib_Create128_make_h128_9(z, z0, z1, z2, z3, z4, z5, z6, z7, z8);
}

static void Hacl_Impl_BignumQ_Mul_carry(uint64_t *out, FStar_UInt128_t *z)
{
  FStar_UInt128_t z0 = z[0];
  FStar_UInt128_t z1 = z[1];
  FStar_UInt128_t z2 = z[2];
  FStar_UInt128_t z3 = z[3];
  FStar_UInt128_t z4 = z[4];
  FStar_UInt128_t z5 = z[5];
  FStar_UInt128_t z6 = z[6];
  FStar_UInt128_t z7 = z[7];
  FStar_UInt128_t z8 = z[8];
  FStar_UInt128_t x = z0;
  FStar_UInt128_t y = z1;
  FStar_UInt128_t carry1 = FStar_UInt128_shift_right(x, (uint32_t )56);
  uint64_t t = FStar_Int_Cast_Full_uint128_to_uint64(x) & (uint64_t )0xffffffffffffff;
  uint64_t x0 = t;
  FStar_UInt128_t z1_ = FStar_UInt128_add(y, carry1);
  FStar_UInt128_t x1 = z1_;
  FStar_UInt128_t y1 = z2;
  FStar_UInt128_t carry2 = FStar_UInt128_shift_right(x1, (uint32_t )56);
  uint64_t t1 = FStar_Int_Cast_Full_uint128_to_uint64(x1) & (uint64_t )0xffffffffffffff;
  uint64_t x11 = t1;
  FStar_UInt128_t z2_ = FStar_UInt128_add(y1, carry2);
  FStar_UInt128_t x2 = z2_;
  FStar_UInt128_t y2 = z3;
  FStar_UInt128_t carry3 = FStar_UInt128_shift_right(x2, (uint32_t )56);
  uint64_t t2 = FStar_Int_Cast_Full_uint128_to_uint64(x2) & (uint64_t )0xffffffffffffff;
  uint64_t x21 = t2;
  FStar_UInt128_t z3_ = FStar_UInt128_add(y2, carry3);
  FStar_UInt128_t x3 = z3_;
  FStar_UInt128_t y3 = z4;
  FStar_UInt128_t carry4 = FStar_UInt128_shift_right(x3, (uint32_t )56);
  uint64_t t3 = FStar_Int_Cast_Full_uint128_to_uint64(x3) & (uint64_t )0xffffffffffffff;
  uint64_t x31 = t3;
  FStar_UInt128_t z4_ = FStar_UInt128_add(y3, carry4);
  FStar_UInt128_t x4 = z4_;
  FStar_UInt128_t y4 = z5;
  FStar_UInt128_t carry5 = FStar_UInt128_shift_right(x4, (uint32_t )56);
  uint64_t t4 = FStar_Int_Cast_Full_uint128_to_uint64(x4) & (uint64_t )0xffffffffffffff;
  uint64_t x41 = t4;
  FStar_UInt128_t z5_ = FStar_UInt128_add(y4, carry5);
  FStar_UInt128_t x5 = z5_;
  FStar_UInt128_t y5 = z6;
  FStar_UInt128_t carry6 = FStar_UInt128_shift_right(x5, (uint32_t )56);
  uint64_t t5 = FStar_Int_Cast_Full_uint128_to_uint64(x5) & (uint64_t )0xffffffffffffff;
  uint64_t x51 = t5;
  FStar_UInt128_t z6_ = FStar_UInt128_add(y5, carry6);
  FStar_UInt128_t x6 = z6_;
  FStar_UInt128_t y6 = z7;
  FStar_UInt128_t carry7 = FStar_UInt128_shift_right(x6, (uint32_t )56);
  uint64_t t6 = FStar_Int_Cast_Full_uint128_to_uint64(x6) & (uint64_t )0xffffffffffffff;
  uint64_t x61 = t6;
  FStar_UInt128_t z7_ = FStar_UInt128_add(y6, carry7);
  FStar_UInt128_t x7 = z7_;
  FStar_UInt128_t y7 = z8;
  FStar_UInt128_t carry8 = FStar_UInt128_shift_right(x7, (uint32_t )56);
  uint64_t t7 = FStar_Int_Cast_Full_uint128_to_uint64(x7) & (uint64_t )0xffffffffffffff;
  uint64_t x71 = t7;
  FStar_UInt128_t z8_ = FStar_UInt128_add(y7, carry8);
  FStar_UInt128_t x8 = z8_;
  FStar_UInt128_t y8 = FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )0);
  FStar_UInt128_t carry9 = FStar_UInt128_shift_right(x8, (uint32_t )56);
  uint64_t t8 = FStar_Int_Cast_Full_uint128_to_uint64(x8) & (uint64_t )0xffffffffffffff;
  uint64_t x81 = t8;
  FStar_UInt128_t z9_ = FStar_UInt128_add(y8, carry9);
  uint64_t x9 = FStar_Int_Cast_Full_uint128_to_uint64(z9_);
  Hacl_Lib_Create64_make_h64_10(out, x0, x11, x21, x31, x41, x51, x61, x71, x81, x9);
}

static void Hacl_Impl_BignumQ_Mul_mod_264(uint64_t *r, uint64_t *t)
{
  uint64_t x0 = t[0];
  uint64_t x1 = t[1];
  uint64_t x2 = t[2];
  uint64_t x3 = t[3];
  uint64_t x4 = t[4];
  uint64_t x4_ = x4 & (uint64_t )0xffffffffff;
  Hacl_Lib_Create64_make_h64_5(r, x0, x1, x2, x3, x4_);
}

static void Hacl_Impl_BignumQ_Mul_div_248(uint64_t *out, uint64_t *t)
{
  (void )t[0];
  (void )t[1];
  (void )t[2];
  (void )t[3];
  uint64_t x4 = t[4];
  uint64_t x5 = t[5];
  uint64_t x6 = t[6];
  uint64_t x7 = t[7];
  uint64_t x8 = t[8];
  uint64_t x9 = t[9];
  uint64_t z0 = (x5 & (uint64_t )0xffffff) << (uint32_t )32 | x4 >> (uint32_t )24;
  uint64_t z1 = (x6 & (uint64_t )0xffffff) << (uint32_t )32 | x5 >> (uint32_t )24;
  uint64_t z2 = (x7 & (uint64_t )0xffffff) << (uint32_t )32 | x6 >> (uint32_t )24;
  uint64_t z3 = (x8 & (uint64_t )0xffffff) << (uint32_t )32 | x7 >> (uint32_t )24;
  uint64_t z4 = (x9 & (uint64_t )0xffffff) << (uint32_t )32 | x8 >> (uint32_t )24;
  Hacl_Lib_Create64_make_h64_5(out, z0, z1, z2, z3, z4);
}

static void Hacl_Impl_BignumQ_Mul_div_264(uint64_t *out, uint64_t *t)
{
  (void )t[0];
  (void )t[1];
  (void )t[2];
  (void )t[3];
  uint64_t x4 = t[4];
  uint64_t x5 = t[5];
  uint64_t x6 = t[6];
  uint64_t x7 = t[7];
  uint64_t x8 = t[8];
  uint64_t x9 = t[9];
  uint64_t z0 = (x5 & (uint64_t )0xffffffffff) << (uint32_t )16 | x4 >> (uint32_t )40;
  uint64_t z1 = (x6 & (uint64_t )0xffffffffff) << (uint32_t )16 | x5 >> (uint32_t )40;
  uint64_t z2 = (x7 & (uint64_t )0xffffffffff) << (uint32_t )16 | x6 >> (uint32_t )40;
  uint64_t z3 = (x8 & (uint64_t )0xffffffffff) << (uint32_t )16 | x7 >> (uint32_t )40;
  uint64_t z4 = (x9 & (uint64_t )0xffffffffff) << (uint32_t )16 | x8 >> (uint32_t )40;
  Hacl_Lib_Create64_make_h64_5(out, z0, z1, z2, z3, z4);
}

static void
Hacl_Impl_BignumQ_Mul_barrett_reduction__1(
  FStar_UInt128_t *qmu,
  uint64_t *t,
  uint64_t *mu1,
  uint64_t *tmp
)
{
  uint64_t *q1 = tmp;
  uint64_t *qmu_ = tmp + (uint32_t )10;
  uint64_t *qmu_264 = tmp + (uint32_t )20;
  Hacl_Impl_BignumQ_Mul_div_248(q1, t);
  Hacl_Impl_BignumQ_Mul_mul_5(qmu, q1, mu1);
  Hacl_Impl_BignumQ_Mul_carry(qmu_, qmu);
  Hacl_Impl_BignumQ_Mul_div_264(qmu_264, qmu_);
}

static void
Hacl_Impl_BignumQ_Mul_barrett_reduction__2(uint64_t *t, uint64_t *m1, uint64_t *tmp)
{
  uint64_t *qmul = tmp;
  uint64_t *r = tmp + (uint32_t )5;
  uint64_t *qmu_264 = tmp + (uint32_t )20;
  uint64_t *s = tmp + (uint32_t )25;
  Hacl_Impl_BignumQ_Mul_mod_264(r, t);
  Hacl_Impl_BignumQ_Mul_low_mul_5(qmul, qmu_264, m1);
  Hacl_Impl_BignumQ_Mul_sub_mod_264(s, r, qmul);
}

static void
Hacl_Impl_BignumQ_Mul_barrett_reduction__(
  uint64_t *z,
  uint64_t *t,
  uint64_t *m1,
  uint64_t *mu1,
  uint64_t *tmp
)
{
  uint64_t *s = tmp + (uint32_t )25;
  KRML_CHECK_SIZE(FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )0), (uint32_t )9);
  FStar_UInt128_t qmu[9];
  for (uintmax_t _i = 0; _i < (uint32_t )9; ++_i)
    qmu[_i] = FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )0);
  Hacl_Impl_BignumQ_Mul_barrett_reduction__1(qmu, t, mu1, tmp);
  Hacl_Impl_BignumQ_Mul_barrett_reduction__2(t, m1, tmp);
  Hacl_Impl_BignumQ_Mul_subm_conditional(z, s);
}

static void Hacl_Impl_BignumQ_Mul_barrett_reduction_(uint64_t *z, uint64_t *t)
{
  uint64_t tmp[40] = { 0 };
  uint64_t *m1 = tmp;
  uint64_t *mu1 = tmp + (uint32_t )5;
  uint64_t *tmp1 = tmp + (uint32_t )10;
  Hacl_Impl_BignumQ_Mul_make_m(m1);
  Hacl_Impl_BignumQ_Mul_make_mu(mu1);
  Hacl_Impl_BignumQ_Mul_barrett_reduction__(z, t, m1, mu1, tmp1);
}

static void Hacl_Impl_BignumQ_Mul_barrett_reduction(uint64_t *z, uint64_t *t)
{
  Hacl_Impl_BignumQ_Mul_barrett_reduction_(z, t);
}

static void Hacl_Impl_BignumQ_Mul_mul_modq(uint64_t *out, uint64_t *x, uint64_t *y)
{
  uint64_t z_[10] = { 0 };
  KRML_CHECK_SIZE(FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )0), (uint32_t )9);
  FStar_UInt128_t z[9];
  for (uintmax_t _i = 0; _i < (uint32_t )9; ++_i)
    z[_i] = FStar_Int_Cast_Full_uint64_to_uint128((uint64_t )0);
  Hacl_Impl_BignumQ_Mul_mul_5(z, x, y);
  Hacl_Impl_BignumQ_Mul_carry(z_, z);
  Hacl_Impl_BignumQ_Mul_barrett_reduction_(out, z_);
}

static void Hacl_Impl_BignumQ_Mul_add_modq_(uint64_t *out, uint64_t *x, uint64_t *y)
{
  uint64_t tmp[5] = { 0 };
  uint64_t x0 = x[0];
  uint64_t x1 = x[1];
  uint64_t x2 = x[2];
  uint64_t x3 = x[3];
  uint64_t x4 = x[4];
  uint64_t y0 = y[0];
  uint64_t y1 = y[1];
  uint64_t y2 = y[2];
  uint64_t y3 = y[3];
  uint64_t y4 = y[4];
  uint64_t z0 = x0 + y0;
  uint64_t z1 = x1 + y1;
  uint64_t z2 = x2 + y2;
  uint64_t z3 = x3 + y3;
  uint64_t z4 = x4 + y4;
  uint64_t x5 = z0;
  uint64_t y5 = z1;
  uint64_t carry1 = x5 >> (uint32_t )56;
  uint64_t t = x5 & (uint64_t )0xffffffffffffff;
  uint64_t x01 = t;
  uint64_t z1_ = y5 + carry1;
  uint64_t x6 = z1_;
  uint64_t y6 = z2;
  uint64_t carry2 = x6 >> (uint32_t )56;
  uint64_t t1 = x6 & (uint64_t )0xffffffffffffff;
  uint64_t x11 = t1;
  uint64_t z2_ = y6 + carry2;
  uint64_t x7 = z2_;
  uint64_t y7 = z3;
  uint64_t carry3 = x7 >> (uint32_t )56;
  uint64_t t2 = x7 & (uint64_t )0xffffffffffffff;
  uint64_t x21 = t2;
  uint64_t z3_ = y7 + carry3;
  uint64_t x8 = z3_;
  uint64_t y8 = z4;
  uint64_t carry4 = x8 >> (uint32_t )56;
  uint64_t t3 = x8 & (uint64_t )0xffffffffffffff;
  uint64_t x31 = t3;
  uint64_t x41 = y8 + carry4;
  Hacl_Lib_Create64_make_h64_5(tmp, x01, x11, x21, x31, x41);
  Hacl_Impl_BignumQ_Mul_subm_conditional(out, tmp);
}

static void Hacl_Impl_BignumQ_Mul_add_modq(uint64_t *out, uint64_t *x, uint64_t *y)
{
  Hacl_Impl_BignumQ_Mul_add_modq_(out, x, y);
}

static void
Hacl_Impl_SHA512_ModQ_sha512_modq_pre_(
  uint64_t *out,
  uint8_t *prefix,
  uint8_t *input,
  uint32_t len1,
  uint64_t *tmp
)
{
  uint8_t hash1[64] = { 0 };
  Hacl_Impl_Sha512_sha512_pre_msg(hash1, prefix, input, len1);
  Hacl_Impl_Load56_load_64_bytes(tmp, hash1);
  Hacl_Impl_BignumQ_Mul_barrett_reduction(out, tmp);
}

static void
Hacl_Impl_SHA512_ModQ_sha512_modq_pre(
  uint64_t *out,
  uint8_t *prefix,
  uint8_t *input,
  uint32_t len1
)
{
  uint64_t tmp[10] = { 0 };
  Hacl_Impl_SHA512_ModQ_sha512_modq_pre_(out, prefix, input, len1, tmp);
}

static void
Hacl_Impl_SHA512_ModQ_sha512_modq_pre_pre2_(
  uint64_t *out,
  uint8_t *prefix,
  uint8_t *prefix2,
  uint8_t *input,
  uint32_t len1,
  uint64_t *tmp
)
{
  uint8_t hash1[64] = { 0 };
  Hacl_Impl_Sha512_sha512_pre_pre2_msg(hash1, prefix, prefix2, input, len1);
  Hacl_Impl_Load56_load_64_bytes(tmp, hash1);
  Hacl_Impl_BignumQ_Mul_barrett_reduction(out, tmp);
}

static void
Hacl_Impl_SHA512_ModQ_sha512_modq_pre_pre2(
  uint64_t *out,
  uint8_t *prefix,
  uint8_t *prefix2,
  uint8_t *input,
  uint32_t len1
)
{
  uint64_t tmp[10] = { 0 };
  Hacl_Impl_SHA512_ModQ_sha512_modq_pre_pre2_(out, prefix, prefix2, input, len1, tmp);
}

static bool Hacl_Impl_Ed25519_Verify_Steps_verify_step_1(uint64_t *r_, uint8_t *signature)
{
  uint8_t *rs = signature;
  bool b_ = Hacl_Impl_Ed25519_PointDecompress_point_decompress(r_, rs);
  return b_;
}

static void
Hacl_Impl_Ed25519_Verify_Steps_verify_step_2(
  uint8_t *r,
  uint8_t *msg,
  uint32_t len1,
  uint8_t *rs,
  uint8_t *public
)
{
  uint64_t r_[5] = { 0 };
  Hacl_Impl_SHA512_ModQ_sha512_modq_pre_pre2(r_, rs, public, msg, len1);
  Hacl_Impl_Store56_store_56(r, r_);
}

static void Hacl_Impl_Ed25519_Verify_Steps_point_mul_g(uint64_t *result, uint8_t *scalar)
{
  uint64_t g1[20] = { 0 };
  Hacl_Impl_Ed25519_G_make_g(g1);
  Hacl_Impl_Ed25519_Ladder_point_mul(result, scalar, g1);
}

static bool
Hacl_Impl_Ed25519_Verify_Steps_verify_step_4(
  uint8_t *s,
  uint8_t *h_,
  uint64_t *a_,
  uint64_t *r_
)
{
  uint64_t tmp[60] = { 0 };
  uint64_t *hA = tmp;
  uint64_t *rhA = tmp + (uint32_t )20;
  uint64_t *sB = tmp + (uint32_t )40;
  Hacl_Impl_Ed25519_Verify_Steps_point_mul_g(sB, s);
  Hacl_Impl_Ed25519_Ladder_point_mul(hA, h_, a_);
  Hacl_Impl_Ed25519_PointAdd_point_add(rhA, r_, hA);
  bool b = Hacl_Impl_Ed25519_PointEqual_point_equal(sB, rhA);
  return b;
}

static bool
Hacl_Impl_Ed25519_Verify_verify__(
  uint8_t *public,
  uint8_t *msg,
  uint32_t len1,
  uint8_t *signature,
  uint64_t *tmp,
  uint8_t *tmp_
)
{
  uint64_t *a_ = tmp;
  uint64_t *r_ = tmp + (uint32_t )20;
  uint64_t *s = tmp + (uint32_t )40;
  uint8_t *h_ = tmp_;
  bool b = Hacl_Impl_Ed25519_PointDecompress_point_decompress(a_, public);
  bool res;
  if (b)
  {
    uint8_t *rs = signature;
    bool b_ = Hacl_Impl_Ed25519_Verify_Steps_verify_step_1(r_, signature);
    bool ite0;
    if (b_)
    {
      Hacl_Impl_Load56_load_32_bytes(s, signature + (uint32_t )32);
      bool b__ = Hacl_Impl_Ed25519_PointEqual_gte_q(s);
      bool ite;
      if (b__)
        ite = false;
      else
      {
        Hacl_Impl_Ed25519_Verify_Steps_verify_step_2(h_, msg, len1, rs, public);
        bool
        b1 = Hacl_Impl_Ed25519_Verify_Steps_verify_step_4(signature + (uint32_t )32, h_, a_, r_);
        ite = b1;
      }
      ite0 = ite;
    }
    else
      ite0 = false;
    res = ite0;
  }
  else
    res = false;
  return res;
}

static bool
Hacl_Impl_Ed25519_Verify_verify_(
  uint8_t *public,
  uint8_t *msg,
  uint32_t len1,
  uint8_t *signature
)
{
  uint64_t tmp[45] = { 0 };
  uint8_t tmp_[32] = { 0 };
  bool res = Hacl_Impl_Ed25519_Verify_verify__(public, msg, len1, signature, tmp, tmp_);
  return res;
}

static bool
Hacl_Impl_Ed25519_Verify_verify(
  uint8_t *public,
  uint8_t *msg,
  uint32_t len1,
  uint8_t *signature
)
{
  return Hacl_Impl_Ed25519_Verify_verify_(public, msg, len1, signature);
}

static void Hacl_Impl_Ed25519_Sign_Steps_point_mul_g(uint64_t *result, uint8_t *scalar)
{
  uint64_t g1[20] = { 0 };
  Hacl_Impl_Ed25519_G_make_g(g1);
  Hacl_Impl_Ed25519_Ladder_point_mul(result, scalar, g1);
}

static void Hacl_Impl_Ed25519_Sign_Steps_point_mul_g_compress(uint8_t *out, uint8_t *s)
{
  uint64_t tmp[20] = { 0 };
  Hacl_Impl_Ed25519_Sign_Steps_point_mul_g(tmp, s);
  Hacl_Impl_Ed25519_PointCompress_point_compress(out, tmp);
}

static void
Hacl_Impl_Ed25519_Sign_Steps_copy_bytes(uint8_t *output, uint8_t *input, uint32_t len1)
{
  memcpy(output, input, len1 * sizeof input[0]);
}

static void
Hacl_Impl_Ed25519_Sign_Steps_sign_step_1(
  uint8_t *secret,
  uint8_t *tmp_bytes,
  uint64_t *tmp_ints
)
{
  uint8_t *a__ = tmp_bytes + (uint32_t )96;
  uint8_t *apre = tmp_bytes + (uint32_t )224;
  uint8_t *a = apre;
  (void )(apre + (uint32_t )32);
  Hacl_Impl_Ed25519_SecretExpand_secret_expand(apre, secret);
  Hacl_Impl_Ed25519_Sign_Steps_point_mul_g_compress(a__, a);
}

static void
Hacl_Impl_Ed25519_Sign_Steps_sign_step_2(
  uint8_t *msg,
  uint32_t len1,
  uint8_t *tmp_bytes,
  uint64_t *tmp_ints
)
{
  uint64_t *r = tmp_ints + (uint32_t )20;
  (void )(tmp_bytes + (uint32_t )96);
  uint8_t *apre = tmp_bytes + (uint32_t )224;
  uint8_t *prefix = apre + (uint32_t )32;
  Hacl_Impl_SHA512_ModQ_sha512_modq_pre(r, prefix, msg, len1);
}

static void
Hacl_Impl_Ed25519_Sign_Steps_sign_step_4(
  uint8_t *msg,
  uint32_t len1,
  uint8_t *tmp_bytes,
  uint64_t *tmp_ints
)
{
  (void )(tmp_ints + (uint32_t )20);
  uint64_t *h = tmp_ints + (uint32_t )60;
  uint8_t *a__ = tmp_bytes + (uint32_t )96;
  (void )(tmp_bytes + (uint32_t )128);
  uint8_t *rs_ = tmp_bytes + (uint32_t )160;
  uint8_t *apre = tmp_bytes + (uint32_t )224;
  (void )(apre + (uint32_t )32);
  Hacl_Impl_SHA512_ModQ_sha512_modq_pre_pre2(h, rs_, a__, msg, len1);
}

static void Hacl_Impl_Ed25519_Sign_Steps_sign_step_5(uint8_t *tmp_bytes, uint64_t *tmp_ints)
{
  uint64_t *r = tmp_ints + (uint32_t )20;
  uint64_t *aq = tmp_ints + (uint32_t )45;
  uint64_t *ha = tmp_ints + (uint32_t )50;
  uint64_t *s = tmp_ints + (uint32_t )55;
  uint64_t *h = tmp_ints + (uint32_t )60;
  uint8_t *s_ = tmp_bytes + (uint32_t )192;
  uint8_t *apre = tmp_bytes + (uint32_t )224;
  (void )(tmp_bytes + (uint32_t )160);
  uint8_t *a = apre;
  Hacl_Impl_Load56_load_32_bytes(aq, a);
  Hacl_Impl_BignumQ_Mul_mul_modq(ha, h, aq);
  Hacl_Impl_BignumQ_Mul_add_modq(s, r, ha);
  Hacl_Impl_Store56_store_56(s_, s);
}

static void Hacl_Impl_Ed25519_Sign_append_to_sig(uint8_t *signature, uint8_t *a, uint8_t *b)
{
  Hacl_Impl_Ed25519_Sign_Steps_copy_bytes(signature, a, (uint32_t )32);
  Hacl_Impl_Ed25519_Sign_Steps_copy_bytes(signature + (uint32_t )32, b, (uint32_t )32);
}

static void
Hacl_Impl_Ed25519_Sign_sign_(uint8_t *signature, uint8_t *secret, uint8_t *msg, uint32_t len1)
{
  uint8_t tmp_bytes[352] = { 0 };
  uint64_t tmp_ints[65] = { 0 };
  (void )(tmp_ints + (uint32_t )20);
  (void )(tmp_ints + (uint32_t )60);
  uint8_t *rs_ = tmp_bytes + (uint32_t )160;
  uint8_t *s_ = tmp_bytes + (uint32_t )192;
  Hacl_Impl_Ed25519_Sign_Steps_sign_step_1(secret, tmp_bytes, tmp_ints);
  Hacl_Impl_Ed25519_Sign_Steps_sign_step_2(msg, len1, tmp_bytes, tmp_ints);
  (void )(tmp_bytes + (uint32_t )96);
  (void )(tmp_bytes + (uint32_t )224);
  uint8_t rb[32] = { 0 };
  uint64_t *r = tmp_ints + (uint32_t )20;
  uint8_t *rs_0 = tmp_bytes + (uint32_t )160;
  Hacl_Impl_Store56_store_56(rb, r);
  Hacl_Impl_Ed25519_Sign_Steps_point_mul_g_compress(rs_0, rb);
  Hacl_Impl_Ed25519_Sign_Steps_sign_step_4(msg, len1, tmp_bytes, tmp_ints);
  Hacl_Impl_Ed25519_Sign_Steps_sign_step_5(tmp_bytes, tmp_ints);
  Hacl_Impl_Ed25519_Sign_append_to_sig(signature, rs_, s_);
}

static void
Hacl_Impl_Ed25519_Sign_sign(uint8_t *signature, uint8_t *secret, uint8_t *msg, uint32_t len1)
{
  Hacl_Impl_Ed25519_Sign_sign_(signature, secret, msg, len1);
}

void *Ed25519_op_String_Access(FStar_Monotonic_HyperStack_mem h, uint8_t *b)
{
  return (void *)(uint8_t )0;
}

void Ed25519_sign(uint8_t *signature, uint8_t *secret, uint8_t *msg, uint32_t len1)
{
  Hacl_Impl_Ed25519_Sign_sign(signature, secret, msg, len1);
}

bool Ed25519_verify(uint8_t *public, uint8_t *msg, uint32_t len1, uint8_t *signature)
{
  return Hacl_Impl_Ed25519_Verify_verify(public, msg, len1, signature);
}

void Ed25519_secret_to_public(uint8_t *out, uint8_t *secret)
{
  Hacl_Impl_Ed25519_SecretToPublic_secret_to_public(out, secret);
}

