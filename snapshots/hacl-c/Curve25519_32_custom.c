#include "Curve25519.h"

typedef struct {
  uint64_t high;
  uint64_t low;
} UInt115_t;


static inline UInt115_t FStar_Int_Cast_uint64_to_uint115(uint64_t x) {
  UInt115_t r;
  r.low = x & 0x7ffffffffffff;
  r.high = x >> 51;
  return r;
}

static inline uint64_t FStar_Int_Cast_uint115_to_uint64(UInt115_t r) {
  return r.low + (r.high << 51);
}

static inline UInt115_t UInt115_add_mod(UInt115_t x, UInt115_t y) {
  UInt115_t r;
  r.high = x.high + y.high;
  r.low = x.low + y.low;
  return r;
}

static inline UInt115_t UInt115_add(UInt115_t x, UInt115_t y) {
  return UInt115_add_mod(x,y);
}

static inline UInt115_t UInt115_mul_wide(uint64_t x, uint64_t y) {
  uint64_t x0 = x & 0x03ffffff;
  uint64_t x1 = x >> 26;
  uint64_t y0 = y & 0x03ffffff;
  uint64_t y1 = y >> 26;
  uint64_t l = x0*y0;
  uint64_t m = x0*y1 + y0*x1;
  uint64_t h = x1*y1;
  UInt115_t r;
  r.low = l + ((m & 0x1ffffff) << 26);
  r.high = (h << 1) + (m >> 25);
  return r;
}

static inline UInt115_t UInt115_square(uint64_t x) {
  uint64_t x0 = x & 0x03ffffff;
  uint64_t x1 = x >> 26;
  uint64_t l = x0*x0;
  uint64_t m = (x0*x1) << 1;
  uint64_t h = x1*x1;
  UInt115_t r;
  r.low = l + ((m & 0x1ffffff) << 26);
  r.high = (h << 1) + (m >> 25);
  return r;
}

static inline uint64_t UInt115_split51(UInt115_t s, uint64_t* low) {
  *low = s.low & 0x7ffffffffffff;
  uint64_t h = s.high + (s.low >> 51);
  return h;
}

inline static void Hacl_Bignum_Modulo_reduce(uint64_t *b)
{
  uint64_t b0 = b[0];
  b[0] = (uint64_t )19 * b0;
}

inline static void Hacl_Bignum_Modulo_carry_top_wide(UInt115_t *b)
{
  UInt115_t b4 = b[4];
  UInt115_t b0 = b[0];
  uint64_t l;
  uint64_t h = UInt115_split51(b4,&l);
  UInt115_t
  b0_ =
    UInt115_add(b0,
		UInt115_mul_wide((uint64_t )19, h));
  b[4] = FStar_Int_Cast_uint64_to_uint115(l);
  b[0] = b0_;
}

inline static void
Hacl_Bignum_Fproduct_copy_from_wide_(uint64_t *output, UInt115_t *input, uint32_t ctr)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    UInt115_t inputi = input[i];
    output[i] = FStar_Int_Cast_uint115_to_uint64(inputi);
    Hacl_Bignum_Fproduct_copy_from_wide_(output, input, i);
    return;
  }
}

inline static void Hacl_Bignum_Fproduct_shift_(uint64_t *output, uint32_t ctr)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint64_t z = output[ctr - (uint32_t )1];
    output[ctr] = z;
    Hacl_Bignum_Fproduct_shift_(output, ctr - (uint32_t )1);
    return;
  }
}

inline static void Hacl_Bignum_Fproduct_shift(uint64_t *output)
{
  uint64_t tmp = output[4];
  Hacl_Bignum_Fproduct_shift_(output, (uint32_t )4);
  output[0] = tmp;
}

inline static void
Hacl_Bignum_Fproduct_sum_scalar_multiplication_(
  UInt115_t *output,
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
    UInt115_t oi = output[i];
    uint64_t ii = input[i];
    output[i] = UInt115_add(oi, UInt115_mul_wide(ii, s));
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, s, i);
    return;
  }
}

inline static void Hacl_Bignum_Fproduct_carry_wide_(UInt115_t *tmp, uint32_t ctr)
{
  if (ctr == (uint32_t )4)
    return;
  else
  {
    UInt115_t tctr = tmp[ctr];
    UInt115_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint64_t l;
    uint64_t h = UInt115_split51(tctr,&l);
    tmp[ctr] = FStar_Int_Cast_uint64_to_uint115(l);
    tmp[ctr + (uint32_t )1] = UInt115_add(tctrp1, FStar_Int_Cast_uint64_to_uint115(h));
    Hacl_Bignum_Fproduct_carry_wide_(tmp, ctr + (uint32_t )1);
    return;
  }
}

inline static void Hacl_Bignum_Fproduct_carry_0_to_1(uint64_t *output)
{
  uint64_t i0 = output[0];
  uint64_t i1 = output[1];
  uint64_t i0_ = i0 & ((uint64_t )1 << (uint32_t )51) - (uint64_t )1;
  uint64_t i1_ = i1 + (i0 >> (uint32_t )51);
  output[0] = i0_;
  output[1] = i1_;
}

inline static void Hacl_Bignum_Fmul_shift_reduce(uint64_t *output)
{
  Hacl_Bignum_Fproduct_shift(output);
  Hacl_Bignum_Modulo_reduce(output);
  return;
}

inline static void
Hacl_Bignum_Fmul_mul_shift_reduce_(
  UInt115_t *output,
  void *init_input,
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
    uint32_t j = (uint32_t )4 - i;
    uint64_t input2i = input2[j];
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i, (uint32_t )5);
    if (ctr > (uint32_t )1)
      Hacl_Bignum_Fmul_shift_reduce(input);
    Hacl_Bignum_Fmul_mul_shift_reduce_(output, (void *)(uint8_t )0, input, input2, i);
    return;
  }
}

inline static void Hacl_Bignum_Fmul_fmul_(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  UInt115_t t[5];
  for (uintmax_t i = 0; i < (uint32_t )5; ++i)
    t[i] = FStar_Int_Cast_uint64_to_uint115((uint64_t )0);
  void
  *input_init =
    (void *)/* start inlining Hacl.Bignum.Fmul.get_seq */
      (void *)(uint8_t )0
    /* end inlining Hacl.Bignum.Fmul.get_seq */;
  Hacl_Bignum_Fmul_mul_shift_reduce_(t, (void *)(uint8_t )0, input, input2, (uint32_t )5);
  Hacl_Bignum_Fproduct_carry_wide_(t, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top_wide(t);
  Hacl_Bignum_Fproduct_copy_from_wide_(output, t, (uint32_t )5);
  Hacl_Bignum_Fproduct_carry_0_to_1(output);
}

inline static void Hacl_Bignum_Fmul_fmul(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  uint64_t tmp[5] = { 0 };
  memcpy(tmp, input, (uint32_t )5 * sizeof input[0]);
  Hacl_Bignum_Fmul_fmul_(output, tmp, input2);
}

inline static void
Hacl_Bignum_Fsquare_upd_5(
  UInt115_t *tmp,
  UInt115_t s0,
  UInt115_t s1,
  UInt115_t s2,
  UInt115_t s3,
  UInt115_t s4
)
{
  tmp[0] = s0;
  tmp[1] = s1;
  tmp[2] = s2;
  tmp[3] = s3;
  tmp[4] = s4;
}

inline static void Hacl_Bignum_Fsquare_fsquare__(UInt115_t *tmp, uint64_t *output)
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
  UInt115_t
  s0 =
    UInt115_add(UInt115_add(UInt115_square(r0),
        UInt115_mul_wide(d4, r1)),
      UInt115_mul_wide(d2, r3));
  UInt115_t
  s1 =
    UInt115_add(UInt115_add(UInt115_mul_wide(d0, r1),
        UInt115_mul_wide(d4, r2)),
      UInt115_mul_wide(r3 * (uint64_t )19, r3));
  UInt115_t
  s2 =
    UInt115_add(UInt115_add(UInt115_mul_wide(d0, r2),
        UInt115_square(r1)),
      UInt115_mul_wide(d4, r3));
  UInt115_t
  s3 =
    UInt115_add(UInt115_add(UInt115_mul_wide(d0, r3),
        UInt115_mul_wide(d1, r2)),
      UInt115_mul_wide(r4, d419));
  UInt115_t
  s4 =
    UInt115_add(UInt115_add(UInt115_mul_wide(d0, r4),
        UInt115_mul_wide(d1, r3)),
      UInt115_square(r2));
  Hacl_Bignum_Fsquare_upd_5(tmp, s0, s1, s2, s3, s4);
  return;
}

inline static void Hacl_Bignum_Fsquare_fsquare_(UInt115_t *tmp, uint64_t *output)
{
  Hacl_Bignum_Fsquare_fsquare__(tmp, output);
  Hacl_Bignum_Fproduct_carry_wide_(tmp, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top_wide(tmp);
  Hacl_Bignum_Fproduct_copy_from_wide_(output, tmp, (uint32_t )5);
  Hacl_Bignum_Fproduct_carry_0_to_1(output);
  return;
}

inline static void
Hacl_Bignum_Fsquare_fsquare_times_(uint64_t *output, UInt115_t *tmp, uint32_t count)
{
  if (count == (uint32_t )1)
  {
    Hacl_Bignum_Fsquare_fsquare_(tmp, output);
    return;
  }
  else
  {
    uint32_t i = count - (uint32_t )1;
    Hacl_Bignum_Fsquare_fsquare_(tmp, output);
    Hacl_Bignum_Fsquare_fsquare_times_(output, tmp, i);
    return;
  }
}

inline static void
Hacl_Bignum_Fsquare_fsquare_times(uint64_t *output, uint64_t *input, uint32_t count)
{
  UInt115_t t[5];
  for (uintmax_t i = 0; i < (uint32_t )5; ++i)
    t[i] = FStar_Int_Cast_uint64_to_uint115((uint64_t )0);
  memcpy(output, input, (uint32_t )5 * sizeof input[0]);
  Hacl_Bignum_Fsquare_fsquare_times_(output, t, count);
}

inline static void Hacl_Bignum_Fsquare_fsquare_times_inplace(uint64_t *output, uint32_t count)
{
  UInt115_t t[5];
  for (uintmax_t i = 0; i < (uint32_t )5; ++i)
    t[i] = FStar_Int_Cast_uint64_to_uint115((uint64_t )0);
  Hacl_Bignum_Fsquare_fsquare_times_(output, t, count);
}

inline static void Hacl_Bignum_Crecip_crecip(uint64_t *out, uint64_t *z)
{
  uint64_t buf[20] = { 0 };
  uint64_t *a = buf;
  uint64_t *t00 = buf + (uint32_t )5;
  uint64_t *b0 = buf + (uint32_t )10;
  uint64_t *c0 = buf + (uint32_t )15;
  /* start inlining Hacl.Bignum.Crecip.fsquare_times */
  Hacl_Bignum_Fsquare_fsquare_times(a, z, (uint32_t )1);
  /* end inlining Hacl.Bignum.Crecip.fsquare_times */
  /* start inlining Hacl.Bignum.Crecip.fsquare_times */
  Hacl_Bignum_Fsquare_fsquare_times(t00, a, (uint32_t )2);
  /* end inlining Hacl.Bignum.Crecip.fsquare_times */
  /* start inlining Hacl.Bignum.Crecip.fmul */
  Hacl_Bignum_Fmul_fmul(b0, t00, z);
  /* end inlining Hacl.Bignum.Crecip.fmul */
  /* start inlining Hacl.Bignum.Crecip.fmul */
  Hacl_Bignum_Fmul_fmul(a, b0, a);
  /* end inlining Hacl.Bignum.Crecip.fmul */
  /* start inlining Hacl.Bignum.Crecip.fsquare_times */
  Hacl_Bignum_Fsquare_fsquare_times(t00, a, (uint32_t )1);
  /* end inlining Hacl.Bignum.Crecip.fsquare_times */
  /* start inlining Hacl.Bignum.Crecip.fmul */
  Hacl_Bignum_Fmul_fmul(b0, t00, b0);
  /* end inlining Hacl.Bignum.Crecip.fmul */
  /* start inlining Hacl.Bignum.Crecip.crecip_1 */
  /* start inlining Hacl.Bignum.Crecip.fsquare_times */
  Hacl_Bignum_Fsquare_fsquare_times(t00, b0, (uint32_t )5);
  /* end inlining Hacl.Bignum.Crecip.fsquare_times */
  /* end inlining Hacl.Bignum.Crecip.crecip_1 */
  uint64_t *a0 = buf;
  uint64_t *t01 = buf + (uint32_t )5;
  uint64_t *b1 = buf + (uint32_t )10;
  uint64_t *c1 = buf + (uint32_t )15;
  /* start inlining Hacl.Bignum.Crecip.fmul */
  Hacl_Bignum_Fmul_fmul(b1, t01, b1);
  /* end inlining Hacl.Bignum.Crecip.fmul */
  /* start inlining Hacl.Bignum.Crecip.fsquare_times */
  Hacl_Bignum_Fsquare_fsquare_times(t01, b1, (uint32_t )10);
  /* end inlining Hacl.Bignum.Crecip.fsquare_times */
  /* start inlining Hacl.Bignum.Crecip.fmul */
  Hacl_Bignum_Fmul_fmul(c1, t01, b1);
  /* end inlining Hacl.Bignum.Crecip.fmul */
  /* start inlining Hacl.Bignum.Crecip.fsquare_times */
  Hacl_Bignum_Fsquare_fsquare_times(t01, c1, (uint32_t )20);
  /* end inlining Hacl.Bignum.Crecip.fsquare_times */
  /* start inlining Hacl.Bignum.Crecip.fmul */
  Hacl_Bignum_Fmul_fmul(t01, t01, c1);
  /* end inlining Hacl.Bignum.Crecip.fmul */
  /* start inlining Hacl.Bignum.Crecip.fsquare_times_inplace */
  Hacl_Bignum_Fsquare_fsquare_times_inplace(t01, (uint32_t )10);
  /* end inlining Hacl.Bignum.Crecip.fsquare_times_inplace */
  /* start inlining Hacl.Bignum.Crecip.fmul */
  Hacl_Bignum_Fmul_fmul(b1, t01, b1);
  /* end inlining Hacl.Bignum.Crecip.fmul */
  /* start inlining Hacl.Bignum.Crecip.crecip_2 */
  /* start inlining Hacl.Bignum.Crecip.fsquare_times */
  Hacl_Bignum_Fsquare_fsquare_times(t01, b1, (uint32_t )50);
  /* end inlining Hacl.Bignum.Crecip.fsquare_times */
  /* end inlining Hacl.Bignum.Crecip.crecip_2 */
  uint64_t *a1 = buf;
  uint64_t *t0 = buf + (uint32_t )5;
  uint64_t *b = buf + (uint32_t )10;
  uint64_t *c = buf + (uint32_t )15;
  /* start inlining Hacl.Bignum.Crecip.fmul */
  Hacl_Bignum_Fmul_fmul(c, t0, b);
  /* end inlining Hacl.Bignum.Crecip.fmul */
  /* start inlining Hacl.Bignum.Crecip.fsquare_times */
  Hacl_Bignum_Fsquare_fsquare_times(t0, c, (uint32_t )100);
  /* end inlining Hacl.Bignum.Crecip.fsquare_times */
  /* start inlining Hacl.Bignum.Crecip.fmul */
  Hacl_Bignum_Fmul_fmul(t0, t0, c);
  /* end inlining Hacl.Bignum.Crecip.fmul */
  /* start inlining Hacl.Bignum.Crecip.fsquare_times_inplace */
  Hacl_Bignum_Fsquare_fsquare_times_inplace(t0, (uint32_t )50);
  /* end inlining Hacl.Bignum.Crecip.fsquare_times_inplace */
  /* start inlining Hacl.Bignum.Crecip.fmul */
  Hacl_Bignum_Fmul_fmul(t0, t0, b);
  /* end inlining Hacl.Bignum.Crecip.fmul */
  /* start inlining Hacl.Bignum.Crecip.fsquare_times_inplace */
  Hacl_Bignum_Fsquare_fsquare_times_inplace(t0, (uint32_t )5);
  /* end inlining Hacl.Bignum.Crecip.fsquare_times_inplace */
  /* start inlining Hacl.Bignum.Crecip.crecip_3 */
  /* start inlining Hacl.Bignum.Crecip.fmul */
  Hacl_Bignum_Fmul_fmul(out, t0, a1);
  /* end inlining Hacl.Bignum.Crecip.fmul */
  /* end inlining Hacl.Bignum.Crecip.crecip_3 */
}

inline static void
Hacl_Bignum_Fscalar_fscalar_(UInt115_t *output, uint64_t *b, uint64_t s, uint32_t i)
{
  if (i == (uint32_t )0)
    return;
  else
  {
    uint32_t i0 = i - (uint32_t )1;
    uint64_t bi = b[i0];
    output[i0] = UInt115_mul_wide(bi, s);
    Hacl_Bignum_Fscalar_fscalar_(output, b, s, i0);
    return;
  }
}

inline static void
Hacl_Bignum_Fscalar_fscalar(UInt115_t *output, uint64_t *b, uint64_t s)
{
  Hacl_Bignum_Fscalar_fscalar_(output, b, s, (uint32_t )5);
  return;
}

inline static void Hacl_Bignum_fsum(uint64_t *a, uint64_t *b)
{
  /* start inlining Hacl.Bignum.Fsum.fsum_ */
  uint64_t a0 = a[0];
  uint64_t b0 = b[0];
  uint64_t a1 = a[1];
  uint64_t b1 = b[1];
  uint64_t a2 = a[2];
  uint64_t b2 = b[2];
  uint64_t a3 = a[3];
  uint64_t b3 = b[3];
  uint64_t a4 = a[4];
  uint64_t b4 = b[4];
  a[0] = a0 + b0;
  a[1] = a1 + b1;
  a[2] = a2 + b2;
  a[3] = a3 + b3;
  a[4] = a4 + b4;
  /* end inlining Hacl.Bignum.Fsum.fsum_ */
}

inline static void Hacl_Bignum_fdifference(uint64_t *a, uint64_t *b)
{
  uint64_t tmp[5] = { 0 };
  memcpy(tmp, b, (uint32_t )5 * sizeof b[0]);
  uint64_t b00 = tmp[0];
  uint64_t b10 = tmp[1];
  uint64_t b20 = tmp[2];
  uint64_t b30 = tmp[3];
  uint64_t b40 = tmp[4];
  tmp[0] = b00 + (uint64_t )0x3fffffffffff68;
  tmp[1] = b10 + (uint64_t )0x3ffffffffffff8;
  tmp[2] = b20 + (uint64_t )0x3ffffffffffff8;
  tmp[3] = b30 + (uint64_t )0x3ffffffffffff8;
  tmp[4] = b40 + (uint64_t )0x3ffffffffffff8;
  /* start inlining Hacl.Bignum.Modulo.add_zero */
  /* start inlining Hacl.Bignum.Modulo.add_zero_ */
  /* end inlining Hacl.Bignum.Modulo.add_zero_ */
  /* end inlining Hacl.Bignum.Modulo.add_zero */
  uint64_t a0 = a[0];
  uint64_t b0 = tmp[0];
  uint64_t a1 = a[1];
  uint64_t b1 = tmp[1];
  uint64_t a2 = a[2];
  uint64_t b2 = tmp[2];
  uint64_t a3 = a[3];
  uint64_t b3 = tmp[3];
  uint64_t a4 = a[4];
  uint64_t b4 = tmp[4];
  a[0] = b0 - a0;
  a[1] = b1 - a1;
  a[2] = b2 - a2;
  a[3] = b3 - a3;
  a[4] = b4 - a4;
  /* start inlining Hacl.Bignum.Fdifference.fdifference_ */
  /* end inlining Hacl.Bignum.Fdifference.fdifference_ */
}

inline static void Hacl_Bignum_fscalar(uint64_t *output, uint64_t *b, uint64_t s)
{
  UInt115_t tmp[5];
  for (uintmax_t i = 0; i < (uint32_t )5; ++i)
    tmp[i] = FStar_Int_Cast_uint64_to_uint115((uint64_t )0);
  Hacl_Bignum_Fscalar_fscalar(tmp, b, s);
  Hacl_Bignum_Fproduct_carry_wide_(tmp, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top_wide(tmp);
  Hacl_Bignum_Fproduct_copy_from_wide_(output, tmp, (uint32_t )5);
}

inline static void Hacl_Bignum_fmul(uint64_t *output, uint64_t *a, uint64_t *b)
{
  Hacl_Bignum_Fmul_fmul(output, a, b);
  return;
}

inline static void Hacl_Bignum_crecip(uint64_t *output, uint64_t *input)
{
  Hacl_Bignum_Crecip_crecip(output, input);
  return;
}

static void
Hacl_EC_Point_swap_conditional_step(uint64_t *a, uint64_t *b, uint64_t swap, uint32_t ctr)
{
  uint32_t i = ctr - (uint32_t )1;
  uint64_t ai0 = a[i];
  uint64_t bi0 = b[i];
  uint64_t x = swap & (ai0 ^ bi0);
  uint64_t ai = ai0 ^ x;
  uint64_t bi = bi0 ^ x;
  a[i] = ai;
  b[i] = bi;
}

static void
Hacl_EC_Point_swap_conditional_(uint64_t *a, uint64_t *b, uint64_t swap, uint32_t ctr)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    Hacl_EC_Point_swap_conditional_step(a, b, swap, ctr);
    uint32_t i = ctr - (uint32_t )1;
    Hacl_EC_Point_swap_conditional_(a, b, swap, i);
    return;
  }
}

static void Hacl_EC_Point_swap_conditional(uint64_t *a, uint64_t *b, uint64_t iswap)
{
  uint64_t swap = (uint64_t )0 - iswap;
  Hacl_EC_Point_swap_conditional_(a, b, swap, (uint32_t )5);
  Hacl_EC_Point_swap_conditional_(a + (uint32_t )5, b + (uint32_t )5, swap, (uint32_t )5);
  return;
}

static void Hacl_EC_Point_copy(uint64_t *output, uint64_t *input)
{
  memcpy(output, input, (uint32_t )5 * sizeof input[0]);
  memcpy(output + (uint32_t )5,
    input + (uint32_t )5,
    (uint32_t )5 * sizeof (input + (uint32_t )5)[0]);
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

static void Hacl_EC_Format_fexpand(uint64_t *output, uint8_t *input)
{
  uint64_t mask_51 = (uint64_t )0x7ffffffffffff;
  uint8_t *x00 = input;
  uint64_t
  i0 =
    /* start inlining Hacl.Endianness.hload64_le */
      /* start inlining Hacl.Endianness.load64_le */
        load64_le(x00)
      /* end inlining Hacl.Endianness.load64_le */
    /* end inlining Hacl.Endianness.hload64_le */;
  uint8_t *x01 = input + (uint32_t )6;
  uint64_t
  i1 =
    /* start inlining Hacl.Endianness.hload64_le */
      /* start inlining Hacl.Endianness.load64_le */
        load64_le(x01)
      /* end inlining Hacl.Endianness.load64_le */
    /* end inlining Hacl.Endianness.hload64_le */;
  uint8_t *x02 = input + (uint32_t )12;
  uint64_t
  i2 =
    /* start inlining Hacl.Endianness.hload64_le */
      /* start inlining Hacl.Endianness.load64_le */
        load64_le(x02)
      /* end inlining Hacl.Endianness.load64_le */
    /* end inlining Hacl.Endianness.hload64_le */;
  uint8_t *x03 = input + (uint32_t )19;
  uint64_t
  i3 =
    /* start inlining Hacl.Endianness.hload64_le */
      /* start inlining Hacl.Endianness.load64_le */
        load64_le(x03)
      /* end inlining Hacl.Endianness.load64_le */
    /* end inlining Hacl.Endianness.hload64_le */;
  uint8_t *x0 = input + (uint32_t )24;
  uint64_t
  i4 =
    /* start inlining Hacl.Endianness.hload64_le */
      /* start inlining Hacl.Endianness.load64_le */
        load64_le(x0)
      /* end inlining Hacl.Endianness.load64_le */
    /* end inlining Hacl.Endianness.hload64_le */;
  uint64_t output0 = i0 & mask_51;
  uint64_t output1 = i1 >> (uint32_t )3 & mask_51;
  uint64_t output2 = i2 >> (uint32_t )6 & mask_51;
  uint64_t output3 = i3 >> (uint32_t )1 & mask_51;
  uint64_t output4 = i4 >> (uint32_t )12 & mask_51;
  Hacl_EC_Format_upd_5(output, output0, output1, output2, output3, output4);
  return;
}

static void
Hacl_EC_Format_store_4(uint8_t *output, uint64_t v0, uint64_t v1, uint64_t v2, uint64_t v3)
{
  uint8_t *b0 = output;
  uint8_t *b1 = output + (uint32_t )8;
  uint8_t *b2 = output + (uint32_t )16;
  uint8_t *b3 = output + (uint32_t )24;
  /* start inlining Hacl.Endianness.hstore64_le */
  /* start inlining Hacl.Endianness.store64_le */
  store64_le(b0, v0);
  /* end inlining Hacl.Endianness.store64_le */
  /* end inlining Hacl.Endianness.hstore64_le */
  /* start inlining Hacl.Endianness.hstore64_le */
  /* start inlining Hacl.Endianness.store64_le */
  store64_le(b1, v1);
  /* end inlining Hacl.Endianness.store64_le */
  /* end inlining Hacl.Endianness.hstore64_le */
  /* start inlining Hacl.Endianness.hstore64_le */
  /* start inlining Hacl.Endianness.store64_le */
  store64_le(b2, v2);
  /* end inlining Hacl.Endianness.store64_le */
  /* end inlining Hacl.Endianness.hstore64_le */
  /* start inlining Hacl.Endianness.hstore64_le */
  /* start inlining Hacl.Endianness.store64_le */
  store64_le(b3, v3);
  return;
  /* end inlining Hacl.Endianness.store64_le */
  /* end inlining Hacl.Endianness.hstore64_le */
}

static void Hacl_EC_Format_fcontract(uint8_t *output, uint64_t *input)
{
  uint64_t mask_51 = (uint64_t )0x7ffffffffffff;
  uint64_t nineteen = (uint64_t )19;
  uint64_t t00 = input[0];
  uint64_t t10 = input[1];
  uint64_t t20 = input[2];
  uint64_t t30 = input[3];
  uint64_t t40 = input[4];
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
  uint64_t two51 = (uint64_t )0x8000000000000;
  uint64_t t08 = t07 + two51 - nineteen;
  uint64_t t17 = t16 + two51 - (uint64_t )1;
  uint64_t t27 = t26 + two51 - (uint64_t )1;
  uint64_t t37 = t36 + two51 - (uint64_t )1;
  uint64_t t47 = t46 + two51 - (uint64_t )1;
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
  Hacl_EC_Format_store_4(output, o0, o1, o2, o3);
  return;
}

static void Hacl_EC_Format_scalar_of_point(uint8_t *scalar, uint64_t *point)
{
  uint64_t *x = point;
  uint64_t *z = point + (uint32_t )5;
  uint64_t buf[10] = { 0 };
  uint64_t *zmone = buf;
  uint64_t *sc = buf + (uint32_t )5;
  Hacl_Bignum_crecip(zmone, z);
  Hacl_Bignum_fmul(sc, x, zmone);
  Hacl_EC_Format_fcontract(scalar, sc);
}

static void
Hacl_EC_AddAndDouble_fmonty(
  uint64_t *pp,
  uint64_t *ppq,
  uint64_t *p,
  uint64_t *pq,
  uint64_t *qmqp
)
{
  uint64_t *qx = qmqp;
  uint64_t *x2 = pp;
  uint64_t *z2 = pp + (uint32_t )5;
  uint64_t *x3 = ppq;
  uint64_t *z3 = ppq + (uint32_t )5;
  uint64_t *x = p;
  uint64_t *z = p + (uint32_t )5;
  uint64_t *xprime = pq;
  uint64_t *zprime = pq + (uint32_t )5;
  uint64_t buf[40] = { 0 };
  uint64_t *origx = buf;
  uint64_t *origxprime0 = buf + (uint32_t )5;
  uint64_t *zzz0 = buf + (uint32_t )10;
  uint64_t *xx0 = buf + (uint32_t )15;
  uint64_t *zz0 = buf + (uint32_t )20;
  uint64_t *xxprime0 = buf + (uint32_t )25;
  uint64_t *zzprime0 = buf + (uint32_t )30;
  uint64_t *zzzprime0 = buf + (uint32_t )35;
  uint64_t *origx0 = buf;
  uint64_t *origxprime = buf + (uint32_t )5;
  uint64_t *zzz1 = buf + (uint32_t )10;
  uint64_t *xx1 = buf + (uint32_t )15;
  uint64_t *zz1 = buf + (uint32_t )20;
  uint64_t *xxprime1 = buf + (uint32_t )25;
  uint64_t *zzprime1 = buf + (uint32_t )30;
  uint64_t *zzzprime1 = buf + (uint32_t )35;
  memcpy(origx0, x, (uint32_t )5 * sizeof x[0]);
  Hacl_Bignum_fsum(x, z);
  Hacl_Bignum_fdifference(z, origx0);
  memcpy(origxprime, xprime, (uint32_t )5 * sizeof xprime[0]);
  Hacl_Bignum_fsum(xprime, zprime);
  Hacl_Bignum_fdifference(zprime, origxprime);
  Hacl_Bignum_fmul(xxprime1, xprime, z);
  /* start inlining Hacl.EC.AddAndDouble.fmonty__1 */
  Hacl_Bignum_fmul(zzprime1, x, zprime);
  /* end inlining Hacl.EC.AddAndDouble.fmonty__1 */
  uint64_t *origx1 = buf;
  uint64_t *origxprime1 = buf + (uint32_t )5;
  uint64_t *zzz = buf + (uint32_t )10;
  uint64_t *xx2 = buf + (uint32_t )15;
  uint64_t *zz2 = buf + (uint32_t )20;
  uint64_t *xxprime2 = buf + (uint32_t )25;
  uint64_t *zzprime = buf + (uint32_t )30;
  uint64_t *zzzprime = buf + (uint32_t )35;
  memcpy(origxprime1, xxprime2, (uint32_t )5 * sizeof xxprime2[0]);
  Hacl_Bignum_fsum(xxprime2, zzprime);
  Hacl_Bignum_fdifference(zzprime, origxprime1);
  Hacl_Bignum_Fsquare_fsquare_times(x3, xxprime2, (uint32_t )1);
  Hacl_Bignum_Fsquare_fsquare_times(zzzprime, zzprime, (uint32_t )1);
  Hacl_Bignum_fmul(z3, zzzprime, qx);
  Hacl_Bignum_Fsquare_fsquare_times(xx2, x, (uint32_t )1);
  /* start inlining Hacl.EC.AddAndDouble.fmonty__2 */
  Hacl_Bignum_Fsquare_fsquare_times(zz2, z, (uint32_t )1);
  /* end inlining Hacl.EC.AddAndDouble.fmonty__2 */
  uint64_t *origx2 = buf;
  uint64_t *origxprime2 = buf + (uint32_t )5;
  uint64_t *zzz2 = buf + (uint32_t )10;
  uint64_t *xx = buf + (uint32_t )15;
  uint64_t *zz = buf + (uint32_t )20;
  uint64_t *xxprime = buf + (uint32_t )25;
  uint64_t *zzprime2 = buf + (uint32_t )30;
  uint64_t *zzzprime2 = buf + (uint32_t )35;
  Hacl_Bignum_fmul(x2, xx, zz);
  Hacl_Bignum_fdifference(zz, xx);
  uint64_t scalar = (uint64_t )121665;
  Hacl_Bignum_fscalar(zzz2, zz, scalar);
  Hacl_Bignum_fsum(zzz2, xx);
  /* start inlining Hacl.EC.AddAndDouble.fmonty__ */
  /* start inlining Hacl.EC.AddAndDouble.fmonty__3 */
  Hacl_Bignum_fmul(z2, zzz2, zz);
  /* end inlining Hacl.EC.AddAndDouble.fmonty__3 */
  /* end inlining Hacl.EC.AddAndDouble.fmonty__ */
}

static void
Hacl_EC_Ladder_SmallLoop_cmult_small_loop_step_1(
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
  uint64_t *q,
  uint8_t byt,
  uint32_t i
)
{
  uint64_t bit = (uint64_t )(byt >> (uint32_t )7);
  Hacl_EC_Point_swap_conditional(nq, nqpq, bit);
  return;
}

static void
Hacl_EC_Ladder_SmallLoop_cmult_small_loop_step_2(
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
  uint64_t *q,
  uint8_t byt,
  uint32_t i
)
{
  Hacl_EC_AddAndDouble_fmonty(nq2, nqpq2, nq, nqpq, q);
  return;
}

static void
Hacl_EC_Ladder_SmallLoop_cmult_small_loop_step(
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
  uint64_t *q,
  uint8_t byt,
  uint32_t i
)
{
  Hacl_EC_Ladder_SmallLoop_cmult_small_loop_step_1(nq, nqpq, nq2, nqpq2, q, byt, i);
  Hacl_EC_Ladder_SmallLoop_cmult_small_loop_step_2(nq, nqpq, nq2, nqpq2, q, byt, i);
  Hacl_EC_Ladder_SmallLoop_cmult_small_loop_step_1(nq2, nqpq2, nq, nqpq, q, byt, i);
  return;
}

static void
Hacl_EC_Ladder_SmallLoop_cmult_small_loop_double_step(
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
  uint64_t *q,
  uint8_t byt,
  uint32_t i
)
{
  Hacl_EC_Ladder_SmallLoop_cmult_small_loop_step(nq, nqpq, nq2, nqpq2, q, byt, i);
  uint8_t byt0 = byt << (uint32_t )1;
  Hacl_EC_Ladder_SmallLoop_cmult_small_loop_step(nq2,
    nqpq2,
    nq,
    nqpq,
    q,
    byt0,
    i - (uint32_t )1);
  return;
}

static void
Hacl_EC_Ladder_SmallLoop_cmult_small_loop(
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
  uint64_t *q,
  uint8_t byt,
  uint32_t i
)
{
  if (i == (uint32_t )0)
    return;
  else
  {
    uint32_t i_ = i - (uint32_t )2;
    Hacl_EC_Ladder_SmallLoop_cmult_small_loop_double_step(nq, nqpq, nq2, nqpq2, q, byt, i);
    uint8_t byt_ = byt << (uint32_t )2;
    Hacl_EC_Ladder_SmallLoop_cmult_small_loop(nq, nqpq, nq2, nqpq2, q, byt_, i_);
    return;
  }
}

static void
Hacl_EC_Ladder_BigLoop_cmult_big_loop(
  uint8_t *n,
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
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
    Hacl_EC_Ladder_SmallLoop_cmult_small_loop(nq, nqpq, nq2, nqpq2, q, byte, (uint32_t )8);
    Hacl_EC_Ladder_BigLoop_cmult_big_loop(n, nq, nqpq, nq2, nqpq2, q, i0);
    return;
  }
}

static void
Hacl_EC_Ladder_cmult_(uint64_t *result, uint64_t *point_buf, uint8_t *n, uint64_t *q)
{
  uint64_t *nq = point_buf;
  uint64_t *nqpq = point_buf + (uint32_t )10;
  uint64_t *nq2 = point_buf + (uint32_t )20;
  uint64_t *nqpq2 = point_buf + (uint32_t )30;
  Hacl_EC_Point_copy(nqpq, q);
  nq[0] = (uint64_t )1;
  Hacl_EC_Ladder_BigLoop_cmult_big_loop(n, nq, nqpq, nq2, nqpq2, q, (uint32_t )32);
  Hacl_EC_Point_copy(result, nq);
  return;
}

static void Hacl_EC_Ladder_cmult(uint64_t *result, uint8_t *n, uint64_t *q)
{
  uint64_t point_buf[40] = { 0 };
  Hacl_EC_Ladder_cmult_(result, point_buf, n, q);
}

static void
Hacl_EC_crypto_scalarmult__(
  uint8_t *mypublic,
  uint8_t *scalar,
  uint8_t *basepoint,
  uint64_t *q
)
{
  uint64_t buf[15] = { 0 };
  uint64_t *nq = buf;
  uint64_t *x = nq;
  uint64_t *z = nq + (uint32_t )5;
  uint64_t *zmone = buf + (uint32_t )5;
  x[0] = (uint64_t )1;
  Hacl_EC_Ladder_cmult(nq, scalar, q);
  Hacl_EC_Format_scalar_of_point(mypublic, nq);
}

static void
Hacl_EC_crypto_scalarmult_(uint8_t *mypublic, uint8_t *secret, uint8_t *basepoint, uint64_t *q)
{
  uint8_t e[32] = { 0 };
  memcpy(e, secret, (uint32_t )32 * sizeof secret[0]);
  uint8_t e00 = e[0];
  uint8_t e310 = e[31];
  uint8_t e0 = e00 & (uint8_t )248;
  uint8_t e31 = e310 & (uint8_t )127;
  uint8_t e311 = e31 | (uint8_t )64;
  e[0] = e0;
  e[31] = e311;
  uint8_t
  *scalar =
    /* start inlining Hacl.EC.Format.format_secret */
      e
    /* end inlining Hacl.EC.Format.format_secret */;
  Hacl_EC_crypto_scalarmult__(mypublic, scalar, basepoint, q);
}

void Hacl_EC_crypto_scalarmult(uint8_t *mypublic, uint8_t *secret, uint8_t *basepoint)
{
  uint64_t buf[10] = { 0 };
  uint64_t *x = buf;
  uint64_t *z = buf + (uint32_t )5;
  Hacl_EC_Format_fexpand(x, basepoint);
  z[0] = (uint64_t )1;
  uint64_t
  *q =
    /* start inlining Hacl.EC.Format.point_of_scalar */
      buf
    /* end inlining Hacl.EC.Format.point_of_scalar */;
  Hacl_EC_crypto_scalarmult_(mypublic, secret, basepoint, q);
}

void Curve25519_crypto_scalarmult(uint8_t *mypublic, uint8_t *secret, uint8_t *basepoint)
{
  Hacl_EC_crypto_scalarmult(mypublic, secret, basepoint);
  return;
}

