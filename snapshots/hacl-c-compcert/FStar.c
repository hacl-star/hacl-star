#include "FStar.h"

static uint64_t FStar_UInt128_constant_time_carry(uint64_t a, uint64_t b)
{
  return (a ^ (a ^ b | a - b ^ b)) >> (uint32_t )63;
}

static uint64_t FStar_UInt128_carry(uint64_t a, uint64_t b)
{
  return FStar_UInt128_constant_time_carry(a, b);
}

void
FStar_UInt128_add(
  FStar_UInt128_uint128 *a,
  FStar_UInt128_uint128 *b,
  FStar_UInt128_uint128 *ret
)
{
  ret[0] =
    (
      (FStar_UInt128_uint128 ){
        .low = a->low + b->low,
        .high = a->high + b->high + FStar_UInt128_carry(a->low + b->low, b->low)
      }
    );
}

void
FStar_UInt128_add_mod(
  FStar_UInt128_uint128 *a,
  FStar_UInt128_uint128 *b,
  FStar_UInt128_uint128 *ret
)
{
  ret[0] =
    (
      (FStar_UInt128_uint128 ){
        .low = a->low + b->low,
        .high = a->high + b->high + FStar_UInt128_carry(a->low + b->low, b->low)
      }
    );
}

void
FStar_UInt128_sub(
  FStar_UInt128_uint128 *a,
  FStar_UInt128_uint128 *b,
  FStar_UInt128_uint128 *ret
)
{
  ret[0] =
    (
      (FStar_UInt128_uint128 ){
        .low = a->low - b->low,
        .high = a->high - b->high - FStar_UInt128_carry(a->low, a->low - b->low)
      }
    );
}

static void
FStar_UInt128_sub_mod_impl(
  FStar_UInt128_uint128 *a,
  FStar_UInt128_uint128 *b,
  FStar_UInt128_uint128 *ret
)
{
  ret[0] =
    (
      (FStar_UInt128_uint128 ){
        .low = a->low - b->low,
        .high = a->high - b->high - FStar_UInt128_carry(a->low, a->low - b->low)
      }
    );
}

void
FStar_UInt128_sub_mod(
  FStar_UInt128_uint128 *a,
  FStar_UInt128_uint128 *b,
  FStar_UInt128_uint128 *ret
)
{
  FStar_UInt128_uint128 ret0;
  FStar_UInt128_sub_mod_impl(&a[0], &b[0], &ret0);
  ret[0] = ret0;
}

void
FStar_UInt128_logand(
  FStar_UInt128_uint128 *a,
  FStar_UInt128_uint128 *b,
  FStar_UInt128_uint128 *ret
)
{
  ret[0] = ((FStar_UInt128_uint128 ){ .low = a->low & b->low, .high = a->high & b->high });
}

void
FStar_UInt128_logxor(
  FStar_UInt128_uint128 *a,
  FStar_UInt128_uint128 *b,
  FStar_UInt128_uint128 *ret
)
{
  ret[0] = ((FStar_UInt128_uint128 ){ .low = a->low ^ b->low, .high = a->high ^ b->high });
}

void
FStar_UInt128_logor(
  FStar_UInt128_uint128 *a,
  FStar_UInt128_uint128 *b,
  FStar_UInt128_uint128 *ret
)
{
  ret[0] = ((FStar_UInt128_uint128 ){ .low = a->low | b->low, .high = a->high | b->high });
}

void FStar_UInt128_lognot(FStar_UInt128_uint128 *a, FStar_UInt128_uint128 *ret)
{
  ret[0] = ((FStar_UInt128_uint128 ){ .low = ~a->low, .high = ~a->high });
}

static uint32_t FStar_UInt128_u32_64 = (uint32_t )64;

static uint64_t FStar_UInt128_add_u64_shift_left(uint64_t hi, uint64_t lo, uint32_t s)
{
  return (hi << s) + (lo >> FStar_UInt128_u32_64 - s);
}

static uint64_t FStar_UInt128_add_u64_shift_left_respec(uint64_t hi, uint64_t lo, uint32_t s)
{
  return FStar_UInt128_add_u64_shift_left(hi, lo, s);
}

static void
FStar_UInt128_shift_left_small(
  FStar_UInt128_uint128 *a,
  uint32_t s,
  FStar_UInt128_uint128 *ret
)
{
  FStar_UInt128_uint128 ite;
  if (s == (uint32_t )0)
    ite = a[0];
  else
    ite =
      (
        (FStar_UInt128_uint128 ){
          .low = a->low << s,
          .high = FStar_UInt128_add_u64_shift_left_respec(a->high, a->low, s)
        }
      );
  ret[0] = ite;
}

static void
FStar_UInt128_shift_left_large(
  FStar_UInt128_uint128 *a,
  uint32_t s,
  FStar_UInt128_uint128 *ret
)
{
  ret[0] =
    ((FStar_UInt128_uint128 ){ .low = (uint64_t )0, .high = a->low << s - FStar_UInt128_u32_64 });
}

void FStar_UInt128_shift_left(FStar_UInt128_uint128 *a, uint32_t s, FStar_UInt128_uint128 *ret)
{
  FStar_UInt128_uint128 ite;
  if (s < FStar_UInt128_u32_64)
  {
    FStar_UInt128_uint128 ret;
    FStar_UInt128_shift_left_small(&a[0], s, &ret);
    ite = ret;
  }
  else
  {
    FStar_UInt128_uint128 ret;
    FStar_UInt128_shift_left_large(&a[0], s, &ret);
    ite = ret;
  }
  ret[0] = ite;
}

static uint64_t FStar_UInt128_add_u64_shift_right(uint64_t hi, uint64_t lo, uint32_t s)
{
  return (lo >> s) + (hi << FStar_UInt128_u32_64 - s);
}

static uint64_t FStar_UInt128_add_u64_shift_right_respec(uint64_t hi, uint64_t lo, uint32_t s)
{
  return FStar_UInt128_add_u64_shift_right(hi, lo, s);
}

static void
FStar_UInt128_shift_right_small(
  FStar_UInt128_uint128 *a,
  uint32_t s,
  FStar_UInt128_uint128 *ret
)
{
  FStar_UInt128_uint128 ite;
  if (s == (uint32_t )0)
    ite = a[0];
  else
    ite =
      (
        (FStar_UInt128_uint128 ){
          .low = FStar_UInt128_add_u64_shift_right_respec(a->high, a->low, s),
          .high = a->high >> s
        }
      );
  ret[0] = ite;
}

static void
FStar_UInt128_shift_right_large(
  FStar_UInt128_uint128 *a,
  uint32_t s,
  FStar_UInt128_uint128 *ret
)
{
  ret[0] =
    ((FStar_UInt128_uint128 ){ .low = a->high >> s - FStar_UInt128_u32_64, .high = (uint64_t )0 });
}

void
FStar_UInt128_shift_right(FStar_UInt128_uint128 *a, uint32_t s, FStar_UInt128_uint128 *ret)
{
  FStar_UInt128_uint128 ite;
  if (s < FStar_UInt128_u32_64)
  {
    FStar_UInt128_uint128 ret;
    FStar_UInt128_shift_right_small(&a[0], s, &ret);
    ite = ret;
  }
  else
  {
    FStar_UInt128_uint128 ret;
    FStar_UInt128_shift_right_large(&a[0], s, &ret);
    ite = ret;
  }
  ret[0] = ite;
}

void
FStar_UInt128_eq_mask(
  FStar_UInt128_uint128 *a,
  FStar_UInt128_uint128 *b,
  FStar_UInt128_uint128 *ret
)
{
  ret[0] =
    (
      (FStar_UInt128_uint128 ){
        .low = FStar_UInt64_eq_mask(a->low, b->low) & FStar_UInt64_eq_mask(a->high, b->high),
        .high = FStar_UInt64_eq_mask(a->low, b->low) & FStar_UInt64_eq_mask(a->high, b->high)
      }
    );
}

void
FStar_UInt128_gte_mask(
  FStar_UInt128_uint128 *a,
  FStar_UInt128_uint128 *b,
  FStar_UInt128_uint128 *ret
)
{
  ret[0] =
    (
      (FStar_UInt128_uint128 ){
        .low = FStar_UInt64_gte_mask(a->high,
          b->high)
        & ~FStar_UInt64_eq_mask(a->high, b->high)
        | FStar_UInt64_eq_mask(a->high, b->high) & FStar_UInt64_gte_mask(a->low, b->low),
        .high = FStar_UInt64_gte_mask(a->high,
          b->high)
        & ~FStar_UInt64_eq_mask(a->high, b->high)
        | FStar_UInt64_eq_mask(a->high, b->high) & FStar_UInt64_gte_mask(a->low, b->low)
      }
    );
}

static void FStar_UInt128_uint64_to_uint128(uint64_t a, FStar_UInt128_uint128 *ret)
{
  ret[0] = ((FStar_UInt128_uint128 ){ .low = a, .high = (uint64_t )0 });
}

static uint64_t FStar_UInt128_uint128_to_uint64(FStar_UInt128_uint128 *a)
{
  return a->low;
}

static uint64_t FStar_UInt128_u64_l32_mask = (uint64_t )0xffffffff;

static uint64_t FStar_UInt128_u64_mod_32(uint64_t a)
{
  return a & FStar_UInt128_u64_l32_mask;
}

static uint32_t FStar_UInt128_u32_32 = (uint32_t )32;

static void
FStar_UInt128_mul_wide_impl_t_(
  uint64_t x,
  uint64_t y,
  K___uint64_t_uint64_t_uint64_t_uint64_t *ret
)
{
  ret[0] =
    (
      (K___uint64_t_uint64_t_uint64_t_uint64_t ){
        .fst = FStar_UInt128_u64_mod_32(x),
        .snd = FStar_UInt128_u64_mod_32(FStar_UInt128_u64_mod_32(x) * FStar_UInt128_u64_mod_32(y)),
        .thd = x >> FStar_UInt128_u32_32,
        .f3 = (x >> FStar_UInt128_u32_32)
        * FStar_UInt128_u64_mod_32(y)
        + (FStar_UInt128_u64_mod_32(x) * FStar_UInt128_u64_mod_32(y) >> FStar_UInt128_u32_32)
      }
    );
}

static uint64_t FStar_UInt128_u32_combine_(uint64_t hi, uint64_t lo)
{
  return lo + (hi << FStar_UInt128_u32_32);
}

static void FStar_UInt128_mul_wide_impl(uint64_t x, uint64_t y, FStar_UInt128_uint128 *ret)
{
  K___uint64_t_uint64_t_uint64_t_uint64_t scrut;
  FStar_UInt128_mul_wide_impl_t_(x, y, &scrut);
  uint64_t u1 = scrut.fst;
  uint64_t w3 = scrut.snd;
  uint64_t x_ = scrut.thd;
  uint64_t t_ = scrut.f3;
  ret[0] =
    (
      (FStar_UInt128_uint128 ){
        .low = FStar_UInt128_u32_combine_(u1
          * (y >> FStar_UInt128_u32_32)
          + FStar_UInt128_u64_mod_32(t_),
          w3),
        .high = x_
        * (y >> FStar_UInt128_u32_32)
        + (t_ >> FStar_UInt128_u32_32)
        + (u1 * (y >> FStar_UInt128_u32_32) + FStar_UInt128_u64_mod_32(t_) >> FStar_UInt128_u32_32)
      }
    );
}

void FStar_UInt128_mul_wide(uint64_t x, uint64_t y, FStar_UInt128_uint128 *ret)
{
  FStar_UInt128_uint128 ret0;
  FStar_UInt128_mul_wide_impl(x, y, &ret0);
  ret[0] = ret0;
}

void FStar_Int_Cast_Full_uint64_to_uint128(uint64_t a, FStar_UInt128_uint128 *ret)
{
  FStar_UInt128_uint128 ret0;
  FStar_UInt128_uint64_to_uint128(a, &ret0);
  ret[0] = ret0;
}

uint64_t FStar_Int_Cast_Full_uint128_to_uint64(FStar_UInt128_uint128 *a)
{
  return FStar_UInt128_uint128_to_uint64(&a[0]);
}

