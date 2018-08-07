/* mpfr_mul -- multiply two floating-point numbers

Copyright 1999-2018 Free Software Foundation, Inc.
Contributed by the AriC and Caramba projects, INRIA.

This file is part of the GNU MPFR Library.

The GNU MPFR Library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation; either version 3 of the License, or (at your
option) any later version.

The GNU MPFR Library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public
License for more details.

You should have received a copy of the GNU Lesser General Public License
along with the GNU MPFR Library; see the file COPYING.LESSER.  If not, see
http://www.gnu.org/licenses/ or write to the Free Software Foundation, Inc.,
51 Franklin St, Fifth Floor, Boston, MA 02110-1301, USA. */

#define MPFR_NEED_LONGLONG_H
#include "mpfr-impl.h"


/********* BEGINNING CHECK *************/

/* Check if we have to check the result of mpfr_mul.
   TODO: Find a better (and faster?) check than using old implementation */
#if MPFR_WANT_ASSERT >= 2

int mpfr_mul2 (mpfr_ptr a, mpfr_srcptr b, mpfr_srcptr c, mpfr_rnd_t rnd_mode);
static int
mpfr_mul3 (mpfr_ptr a, mpfr_srcptr b, mpfr_srcptr c, mpfr_rnd_t rnd_mode)
{
  /* Old implementation */
  int sign_product, cc, inexact;
  mpfr_exp_t ax;
  mp_limb_t *tmp;
  mp_limb_t b1;
  mpfr_prec_t bq, cq;
  mp_size_t bn, cn, tn, k;
  MPFR_TMP_DECL(marker);

  /* deal with special cases */
  if (MPFR_ARE_SINGULAR(b,c))
    {
      if (MPFR_IS_NAN(b) || MPFR_IS_NAN(c))
        {
          MPFR_SET_NAN(a);
          MPFR_RET_NAN;
        }
      sign_product = MPFR_MULT_SIGN( MPFR_SIGN(b) , MPFR_SIGN(c) );
      if (MPFR_IS_INF(b))
        {
          if (MPFR_IS_INF(c) || MPFR_NOTZERO(c))
            {
              MPFR_SET_SIGN(a, sign_product);
              MPFR_SET_INF(a);
              MPFR_RET(0); /* exact */
            }
          else
            {
              MPFR_SET_NAN(a);
              MPFR_RET_NAN;
            }
        }
      else if (MPFR_IS_INF(c))
        {
          if (MPFR_NOTZERO(b))
            {
              MPFR_SET_SIGN(a, sign_product);
              MPFR_SET_INF(a);
              MPFR_RET(0); /* exact */
            }
          else
            {
              MPFR_SET_NAN(a);
              MPFR_RET_NAN;
            }
        }
      else
        {
          MPFR_ASSERTD(MPFR_IS_ZERO(b) || MPFR_IS_ZERO(c));
          MPFR_SET_SIGN(a, sign_product);
          MPFR_SET_ZERO(a);
          MPFR_RET(0); /* 0 * 0 is exact */
        }
    }
  sign_product = MPFR_MULT_SIGN( MPFR_SIGN(b) , MPFR_SIGN(c) );

  ax = MPFR_GET_EXP (b) + MPFR_GET_EXP (c);

  bq = MPFR_PREC (b);
  cq = MPFR_PREC (c);

  MPFR_ASSERTN ((mpfr_uprec_t) bq + cq <= MPFR_PREC_MAX);

  bn = MPFR_PREC2LIMBS (bq); /* number of limbs of b */
  cn = MPFR_PREC2LIMBS (cq); /* number of limbs of c */
  k = bn + cn; /* effective nb of limbs used by b*c (= tn or tn+1) below */
  tn = MPFR_PREC2LIMBS (bq + cq);
  /* <= k, thus no int overflow */
  MPFR_ASSERTD(tn <= k);

  /* Check for no size_t overflow*/
  MPFR_ASSERTD((size_t) k <= ((size_t) -1) / MPFR_BYTES_PER_MP_LIMB);
  MPFR_TMP_MARK(marker);
  tmp = MPFR_TMP_LIMBS_ALLOC (k);

  /* multiplies two mantissa in temporary allocated space */
  b1 = (MPFR_LIKELY(bn >= cn)) ?
    mpn_mul (tmp, MPFR_MANT(b), bn, MPFR_MANT(c), cn)
    : mpn_mul (tmp, MPFR_MANT(c), cn, MPFR_MANT(b), bn);

  /* now tmp[0]..tmp[k-1] contains the product of both mantissa,
     with tmp[k-1]>=2^(GMP_NUMB_BITS-2) */
  b1 >>= GMP_NUMB_BITS - 1; /* msb from the product */

  /* if the mantissas of b and c are uniformly distributed in ]1/2, 1],
     then their product is in ]1/4, 1/2] with probability 2*ln(2)-1 ~ 0.386
     and in [1/2, 1] with probability 2-2*ln(2) ~ 0.614 */
  tmp += k - tn;
  if (MPFR_UNLIKELY(b1 == 0))
    mpn_lshift (tmp, tmp, tn, 1); /* tn <= k, so no stack corruption */
  cc = mpfr_round_raw (MPFR_MANT (a), tmp, bq + cq,
                       MPFR_IS_NEG_SIGN(sign_product),
                       MPFR_PREC (a), rnd_mode, &inexact);

  /* cc = 1 ==> result is a power of two */
  if (MPFR_UNLIKELY(cc))
    MPFR_MANT(a)[MPFR_LIMB_SIZE(a)-1] = MPFR_LIMB_HIGHBIT;

  MPFR_TMP_FREE(marker);

  {
    mpfr_exp_t ax2 = ax + (mpfr_exp_t) (b1 - 1 + cc);
    if (MPFR_UNLIKELY( ax2 > __gmpfr_emax))
      return mpfr_overflow (a, rnd_mode, sign_product);
    if (MPFR_UNLIKELY( ax2 < __gmpfr_emin))
      {
        /* In the rounding to the nearest mode, if the exponent of the exact
           result (i.e. before rounding, i.e. without taking cc into account)
           is < __gmpfr_emin - 1 or the exact result is a power of 2 (i.e. if
           both arguments are powers of 2) in absolute value, then round to
           zero. */
        if (rnd_mode == MPFR_RNDN &&
            (ax + (mpfr_exp_t) b1 < __gmpfr_emin ||
             (mpfr_powerof2_raw (b) && mpfr_powerof2_raw (c))))
          rnd_mode = MPFR_RNDZ;
        return mpfr_underflow (a, rnd_mode, sign_product);
      }
    MPFR_SET_EXP (a, ax2);
    MPFR_SET_SIGN(a, sign_product);
  }
  MPFR_RET (inexact);
}

int
mpfr_mul (mpfr_ptr a, mpfr_srcptr b, mpfr_srcptr c, mpfr_rnd_t rnd_mode)
{
  mpfr_t ta, tb, tc;
  int inexact1, inexact2;

  if (rnd_mode == MPFR_RNDF)
    return mpfr_mul2 (a, b, c, rnd_mode);

  mpfr_init2 (ta, MPFR_PREC (a));
  mpfr_init2 (tb, MPFR_PREC (b));
  mpfr_init2 (tc, MPFR_PREC (c));
  MPFR_ASSERTN (mpfr_set (tb, b, MPFR_RNDN) == 0);
  MPFR_ASSERTN (mpfr_set (tc, c, MPFR_RNDN) == 0);

  inexact2 = mpfr_mul3 (ta, tb, tc, rnd_mode);
  inexact1 = mpfr_mul2 (a, b, c, rnd_mode);
  if (MPFR_IS_NAN (ta) && MPFR_IS_NAN (a))
    {
      /* Getting both NaN is OK. */
    }
  else if (! mpfr_equal_p (ta, a) || ! SAME_SIGN (inexact1, inexact2))
    {
      /* We do not have MPFR_PREC_FSPEC, so let's use mpfr_eexp_t and
         MPFR_EXP_FSPEC since mpfr_prec_t values are guaranteed to be
         representable in mpfr_exp_t, thus in mpfr_eexp_t. */
      fprintf (stderr, "mpfr_mul return different values for %s\n"
               "Prec_a = %" MPFR_EXP_FSPEC "d, "
               "Prec_b = %" MPFR_EXP_FSPEC "d, "
               "Prec_c = %" MPFR_EXP_FSPEC "d\nb = ",
               mpfr_print_rnd_mode (rnd_mode),
               (mpfr_eexp_t) MPFR_PREC (a),
               (mpfr_eexp_t) MPFR_PREC (b),
               (mpfr_eexp_t) MPFR_PREC (c));
      mpfr_fdump (stderr, b);
      fprintf (stderr, "c = ");
      mpfr_fdump (stderr, c);
      fprintf (stderr, "OldMul: ");
      mpfr_fdump (stderr, ta);
      fprintf (stderr, "NewMul: ");
      mpfr_fdump (stderr, a);
      fprintf (stderr, "NewInexact = %d | OldInexact = %d\n",
               inexact1, inexact2);
      MPFR_ASSERTN(0);
    }

  mpfr_clears (ta, tb, tc, (mpfr_ptr) 0);
  return inexact1;
}

# define mpfr_mul mpfr_mul2

#endif  /* MPFR_WANT_ASSERT >= 2 */

/****** END OF CHECK *******/

/* Multiply 2 mpfr_t */

#if !defined(MPFR_GENERIC_ABI)


#define uint32_t mpfr_prec_t
#define int32_t mpfr_exp_t
#define uint64_t mp_limb_t
#define bool int

typedef struct K___int32_t_uint64_t_uint64_t_s
{
  int32_t fst;
  uint64_t snd;
  uint64_t thd;
}
K___int32_t_uint64_t_uint64_t;

#define MPFR_Lib_mpfr_struct __mpfr_struct
#define MPFR_Exceptions_mpfr_overflow mpfr_overflow
#define MPFR_Exceptions_mpfr_underflow mpfr_underflow
#define mpfr_prec _mpfr_prec
#define mpfr_exp _mpfr_exp
#define mpfr_d _mpfr_d
#define mpfr_sign _mpfr_sign
#define MPFR_Lib_gmp_NUMB_BITS GMP_NUMB_BITS
#define MPFR_Lib_mpfr_EMAX __gmpfr_emax
#define MPFR_Lib_mpfr_EMIN __gmpfr_emin
#define MPFR_RoundingMode_MPFR_RNDZ MPFR_RNDZ

#define MPFR_RoundingMode_uu___is_MPFR_RNDN(rnd_mode) (rnd_mode == MPFR_RNDN)
#define MPFR_RoundingMode_mpfr_IS_LIKE_RNDZ MPFR_IS_LIKE_RNDZ
#define MPFR_RoundingMode_mpfr_IS_LIKE_RNDA MPFR_IS_LIKE_RNDA

/* Special code for prec(a) < GMP_NUMB_BITS and
   prec(b), prec(c) <= GMP_NUMB_BITS.
   Note: this code was copied in sqr.c, function mpfr_sqr_1 (this saves a few cycles
   with respect to have this function exported). As a consequence, any change here
   should be reported in mpfr_sqr_1. */
static int
mpfr_mul_1 (mpfr_ptr a, mpfr_srcptr b, mpfr_srcptr c, mpfr_rnd_t rnd_mode,
            mpfr_prec_t p)
{
  uint64_t *ap = a->mpfr_d;
  uint64_t *bp = b->mpfr_d;
  uint64_t *cp = c->mpfr_d;
  uint64_t b0 = bp[0U];
  uint64_t c0 = cp[0U];
  uint32_t sh = MPFR_Lib_gmp_NUMB_BITS - p;
  uint64_t mask = ((uint64_t)1U << sh) - (uint64_t)1U;
  int32_t ax = b->mpfr_exp + c->mpfr_exp;
  //K___uint64_t_uint64_t scrut0 = MPFR_Umul_ppmm_umul_ppmm(b0, c0);
  //uint64_t a0 = scrut0.fst;
  //uint64_t sb = scrut0.snd;
  uint64_t a0, sb;
  umul_ppmm (a0, sb, b0, c0);
  K___int32_t_uint64_t_uint64_t scrut;
  if (a0 < (uint64_t)0x8000000000000000U)
    scrut =
      (
        (K___int32_t_uint64_t_uint64_t){
          .fst = ax - (int32_t)1,
          .snd = a0 << (uint32_t)1U | sb >> MPFR_Lib_gmp_NUMB_BITS - (uint32_t)1U,
          .thd = sb << (uint32_t)1U
        }
      );
  else
    scrut = ((K___int32_t_uint64_t_uint64_t){ .fst = ax, .snd = a0, .thd = sb });
  int32_t ax1 = scrut.fst;
  uint64_t a01 = scrut.snd;
  uint64_t sb1 = scrut.thd;
  uint64_t rb = a01 & (uint64_t)1U << sh - (uint32_t)1U;
  uint64_t sb2 = sb1 | a01 & mask ^ rb;
  ap[0U] = a01 & ~mask;
  MPFR_Lib_mpfr_struct uu___55_2653 = a[0U];
  a[0U] =
    (
      (MPFR_Lib_mpfr_struct){
        .mpfr_prec = uu___55_2653.mpfr_prec,
        .mpfr_sign = b->mpfr_sign * c->mpfr_sign,
        .mpfr_exp = uu___55_2653.mpfr_exp,
        .mpfr_d = uu___55_2653.mpfr_d
      }
    );
  uint64_t *ap1 = a->mpfr_d;
  uint64_t a02 = ap1[0U];
  if (ax1 > MPFR_Lib_mpfr_EMAX)
    return MPFR_Exceptions_mpfr_overflow(a, rnd_mode, a->mpfr_sign);
  else if (ax1 < MPFR_Lib_mpfr_EMIN)
  {
    bool aneg = a->mpfr_sign < (int32_t)0;
    if
    (
      ax1
      == MPFR_Lib_mpfr_EMIN - (int32_t)1
      && a02 == ~mask
      &&
        (MPFR_RoundingMode_uu___is_MPFR_RNDN(rnd_mode)
        && rb > (uint64_t)0U
        || (rb | sb2) > (uint64_t)0U && MPFR_RoundingMode_mpfr_IS_LIKE_RNDA(rnd_mode, aneg))
    )
    {
      uint64_t *ap2 = a->mpfr_d;
      uint64_t a03 = ap2[0U];
      MPFR_Lib_mpfr_struct uu___54_2803 = a[0U];
      a[0U] =
        (
          (MPFR_Lib_mpfr_struct){
            .mpfr_prec = uu___54_2803.mpfr_prec,
            .mpfr_sign = uu___54_2803.mpfr_sign,
            .mpfr_exp = ax1,
            .mpfr_d = uu___54_2803.mpfr_d
          }
        );
      if (rb == (uint64_t)0U && sb2 == (uint64_t)0U)
        return (int32_t)0;
      else if (MPFR_RoundingMode_uu___is_MPFR_RNDN(rnd_mode))
        if (rb == (uint64_t)0U || sb2 == (uint64_t)0U && (a03 & (uint64_t)1U << sh) == (uint64_t)0U)
          if (a->mpfr_sign == (int32_t)1)
            return (int32_t)-1;
          else
            return (int32_t)1;
        else
        {
          uint64_t *ap3 = a->mpfr_d;
          ap3[0U] = ap3[0U] + ((uint64_t)1U << sh);
          if (ap3[0U] == (uint64_t)0U)
          {
            ap3[0U] = (uint64_t)0x8000000000000000U;
            if (ax1 + (int32_t)1 > MPFR_Lib_mpfr_EMAX)
              return MPFR_Exceptions_mpfr_overflow(a, rnd_mode, a->mpfr_sign);
            else
            {
              MPFR_Lib_mpfr_struct uu___54_2937 = a[0U];
              a[0U] =
                (
                  (MPFR_Lib_mpfr_struct){
                    .mpfr_prec = uu___54_2937.mpfr_prec,
                    .mpfr_sign = uu___54_2937.mpfr_sign,
                    .mpfr_exp = ax1 + (int32_t)1,
                    .mpfr_d = uu___54_2937.mpfr_d
                  }
                );
              return a->mpfr_sign;
            }
          }
          else
            return a->mpfr_sign;
        }
      else if (MPFR_RoundingMode_mpfr_IS_LIKE_RNDZ(rnd_mode, a->mpfr_sign < (int32_t)0))
        if (a->mpfr_sign == (int32_t)1)
          return (int32_t)-1;
        else
          return (int32_t)1;
      else
      {
        uint64_t *ap3 = a->mpfr_d;
        ap3[0U] = ap3[0U] + ((uint64_t)1U << sh);
        if (ap3[0U] == (uint64_t)0U)
        {
          ap3[0U] = (uint64_t)0x8000000000000000U;
          if (ax1 + (int32_t)1 > MPFR_Lib_mpfr_EMAX)
            return MPFR_Exceptions_mpfr_overflow(a, rnd_mode, a->mpfr_sign);
          else
          {
            MPFR_Lib_mpfr_struct uu___54_3120 = a[0U];
            a[0U] =
              (
                (MPFR_Lib_mpfr_struct){
                  .mpfr_prec = uu___54_3120.mpfr_prec,
                  .mpfr_sign = uu___54_3120.mpfr_sign,
                  .mpfr_exp = ax1 + (int32_t)1,
                  .mpfr_d = uu___54_3120.mpfr_d
                }
              );
            return a->mpfr_sign;
          }
        }
        else
          return a->mpfr_sign;
      }
    }
    else if
    (
      MPFR_RoundingMode_uu___is_MPFR_RNDN(rnd_mode)
      &&
        (ax1
        < MPFR_Lib_mpfr_EMIN - (int32_t)1
        || a02 == (uint64_t)0x8000000000000000U && (rb | sb2) == (uint64_t)0U)
    )
      return MPFR_Exceptions_mpfr_underflow(a, MPFR_RoundingMode_MPFR_RNDZ, a->mpfr_sign);
    else
      return MPFR_Exceptions_mpfr_underflow(a, rnd_mode, a->mpfr_sign);
  }
  else
  {
    uint64_t *ap2 = a->mpfr_d;
    uint64_t a03 = ap2[0U];
    MPFR_Lib_mpfr_struct uu___54_3303 = a[0U];
    a[0U] =
      (
        (MPFR_Lib_mpfr_struct){
          .mpfr_prec = uu___54_3303.mpfr_prec,
          .mpfr_sign = uu___54_3303.mpfr_sign,
          .mpfr_exp = ax1,
          .mpfr_d = uu___54_3303.mpfr_d
        }
      );
    if (rb == (uint64_t)0U && sb2 == (uint64_t)0U)
      return (int32_t)0;
    else if (MPFR_RoundingMode_uu___is_MPFR_RNDN(rnd_mode))
      if (rb == (uint64_t)0U || sb2 == (uint64_t)0U && (a03 & (uint64_t)1U << sh) == (uint64_t)0U)
        if (a->mpfr_sign == (int32_t)1)
          return (int32_t)-1;
        else
          return (int32_t)1;
      else
      {
        uint64_t *ap3 = a->mpfr_d;
        ap3[0U] = ap3[0U] + ((uint64_t)1U << sh);
        if (ap3[0U] == (uint64_t)0U)
        {
          ap3[0U] = (uint64_t)0x8000000000000000U;
          if (ax1 + (int32_t)1 > MPFR_Lib_mpfr_EMAX)
            return MPFR_Exceptions_mpfr_overflow(a, rnd_mode, a->mpfr_sign);
          else
          {
            MPFR_Lib_mpfr_struct uu___54_3437 = a[0U];
            a[0U] =
              (
                (MPFR_Lib_mpfr_struct){
                  .mpfr_prec = uu___54_3437.mpfr_prec,
                  .mpfr_sign = uu___54_3437.mpfr_sign,
                  .mpfr_exp = ax1 + (int32_t)1,
                  .mpfr_d = uu___54_3437.mpfr_d
                }
              );
            return a->mpfr_sign;
          }
        }
        else
          return a->mpfr_sign;
      }
    else if (MPFR_RoundingMode_mpfr_IS_LIKE_RNDZ(rnd_mode, a->mpfr_sign < (int32_t)0))
      if (a->mpfr_sign == (int32_t)1)
        return (int32_t)-1;
      else
        return (int32_t)1;
    else
    {
      uint64_t *ap3 = a->mpfr_d;
      ap3[0U] = ap3[0U] + ((uint64_t)1U << sh);
      if (ap3[0U] == (uint64_t)0U)
      {
        ap3[0U] = (uint64_t)0x8000000000000000U;
        if (ax1 + (int32_t)1 > MPFR_Lib_mpfr_EMAX)
          return MPFR_Exceptions_mpfr_overflow(a, rnd_mode, a->mpfr_sign);
        else
        {
          MPFR_Lib_mpfr_struct uu___54_3620 = a[0U];
          a[0U] =
            (
              (MPFR_Lib_mpfr_struct){
                .mpfr_prec = uu___54_3620.mpfr_prec,
                .mpfr_sign = uu___54_3620.mpfr_sign,
                .mpfr_exp = ax1 + (int32_t)1,
                .mpfr_d = uu___54_3620.mpfr_d
              }
            );
          return a->mpfr_sign;
        }
      }
      else
        return a->mpfr_sign;
    }
  }
}
  
/* Special code for prec(a) = GMP_NUMB_BITS and
   prec(b), prec(c) <= GMP_NUMB_BITS. */
static int
mpfr_mul_1n (mpfr_ptr a, mpfr_srcptr b, mpfr_srcptr c, mpfr_rnd_t rnd_mode)
{
  mp_limb_t a0;
  mpfr_limb_ptr ap = MPFR_MANT(a);
  mp_limb_t b0 = MPFR_MANT(b)[0];
  mp_limb_t c0 = MPFR_MANT(c)[0];
  mpfr_exp_t ax;
  mp_limb_t rb, sb;

  ax = MPFR_GET_EXP(b) + MPFR_GET_EXP(c);
  umul_ppmm (a0, sb, b0, c0);
  if (a0 < MPFR_LIMB_HIGHBIT)
    {
      ax --;
      /* TODO: This is actually an addition with carry (no shifts and no OR
         needed in asm). Make sure that GCC generates optimized code once
         it supports carry-in. */
      a0 = (a0 << 1) | (sb >> (GMP_NUMB_BITS - 1));
      sb <<= 1;
    }
  rb = sb & MPFR_LIMB_HIGHBIT;
  sb = sb & ~MPFR_LIMB_HIGHBIT;
  ap[0] = a0;

  MPFR_SIGN(a) = MPFR_MULT_SIGN (MPFR_SIGN (b), MPFR_SIGN (c));

  /* rounding */
  if (MPFR_UNLIKELY(ax > __gmpfr_emax))
    return mpfr_overflow (a, rnd_mode, MPFR_SIGN(a));

  /* Warning: underflow should be checked *after* rounding, thus when rounding
     away and when a > 0.111...111*2^(emin-1), or when rounding to nearest and
     a >= 0.111...111[1]*2^(emin-1), there is no underflow.
     Note: this case can only occur when the initial a0 (after the umul_ppmm
     call above) had its most significant bit 0, since the largest a0 is
     obtained for b0 = c0 = B-1 where B=2^GMP_NUMB_BITS, thus b0*c0 <= (B-1)^2
     thus a0 <= B-2. */
  if (MPFR_UNLIKELY(ax < __gmpfr_emin))
    {
      if (ax == __gmpfr_emin - 1 && ap[0] == ~MPFR_LIMB_ZERO &&
          ((rnd_mode == MPFR_RNDN && rb) ||
           (MPFR_IS_LIKE_RNDA(rnd_mode, MPFR_IS_NEG (a)) && (rb | sb))))
        goto rounding; /* no underflow */
      /* For RNDN, mpfr_underflow always rounds away, thus for |a| <= 2^(emin-2)
         we have to change to RNDZ. This corresponds to:
         (a) either ax < emin - 1
         (b) or ax = emin - 1 and ap[0] = 1000....000 and rb = sb = 0 */
      if (rnd_mode == MPFR_RNDN &&
          (ax < __gmpfr_emin - 1 ||
           (ap[0] == MPFR_LIMB_HIGHBIT && (rb | sb) == 0)))
        rnd_mode = MPFR_RNDZ;
      return mpfr_underflow (a, rnd_mode, MPFR_SIGN(a));
    }

 rounding:
  MPFR_EXP (a) = ax; /* Don't use MPFR_SET_EXP since ax might be < __gmpfr_emin
                        in the cases "goto rounding" above. */
  if ((rb == 0 && sb == 0) || rnd_mode == MPFR_RNDF)
    {
      MPFR_ASSERTD(ax >= __gmpfr_emin);
      MPFR_RET (0);
    }
  else if (rnd_mode == MPFR_RNDN)
    {
      if (rb == 0 || (sb == 0 && (ap[0] & MPFR_LIMB_ONE) == 0))
        goto truncate;
      else
        goto add_one_ulp;
    }
  else if (MPFR_IS_LIKE_RNDZ(rnd_mode, MPFR_IS_NEG(a)))
    {
    truncate:
      MPFR_ASSERTD(ax >= __gmpfr_emin);
      MPFR_RET(-MPFR_SIGN(a));
    }
  else /* round away from zero */
    {
    add_one_ulp:
      ap[0] += MPFR_LIMB_ONE;
      if (ap[0] == 0)
        {
          ap[0] = MPFR_LIMB_HIGHBIT;
          if (MPFR_UNLIKELY(ax + 1 > __gmpfr_emax))
            return mpfr_overflow (a, rnd_mode, MPFR_SIGN(a));
          MPFR_ASSERTD(ax + 1 <= __gmpfr_emax);
          MPFR_ASSERTD(ax + 1 >= __gmpfr_emin);
          MPFR_SET_EXP (a, ax + 1);
        }
      MPFR_RET(MPFR_SIGN(a));
    }
}

/* Special code for GMP_NUMB_BITS < prec(a) < 2*GMP_NUMB_BITS and
   GMP_NUMB_BITS < prec(b), prec(c) <= 2*GMP_NUMB_BITS.
   Note: this code was copied in sqr.c, function mpfr_sqr_2 (this saves a few cycles
   with respect to have this function exported). As a consequence, any change here
   should be reported in mpfr_sqr_2. */
static int
mpfr_mul_2 (mpfr_ptr a, mpfr_srcptr b, mpfr_srcptr c, mpfr_rnd_t rnd_mode,
            mpfr_prec_t p)
{
  mp_limb_t h, l, u, v, w;
  mpfr_limb_ptr ap = MPFR_MANT(a);
  mpfr_exp_t ax = MPFR_GET_EXP(b) + MPFR_GET_EXP(c);
  mpfr_prec_t sh = 2 * GMP_NUMB_BITS - p;
  mp_limb_t rb, sb, sb2, mask = MPFR_LIMB_MASK(sh);
  mp_limb_t *bp = MPFR_MANT(b), *cp = MPFR_MANT(c);

  /* we store the 4-limb product in h=ap[1], l=ap[0], sb=ap[-1], sb2=ap[-2] */
  umul_ppmm (h, l, bp[1], cp[1]);
  umul_ppmm (u, v, bp[1], cp[0]);
  l += u;
  h += (l < u);
  umul_ppmm (u, w, bp[0], cp[1]);
  l += u;
  h += (l < u);

  /* now the full product is {h, l, v + w + high(b0*c0), low(b0*c0)},
     where the lower part contributes to less than 3 ulps to {h, l} */

  /* If h has its most significant bit set and the low sh-1 bits of l are not
     000...000 nor 111...111 nor 111...110, then we can round correctly;
     if h has zero as most significant bit, we have to shift left h and l,
     thus if the low sh-2 bits are not 000...000 nor 111...111 nor 111...110,
     then we can round correctly. To avoid an extra test we consider the latter
     case (if we can round, we can also round in the former case).
     For sh <= 3, we have mask <= 7, thus (mask>>2) <= 1, and the approximation
     cannot be enough. */
  if (MPFR_LIKELY(((l + 2) & (mask >> 2)) > 2))
    sb = sb2 = 1; /* result cannot be exact in that case */
  else
    {
      umul_ppmm (sb, sb2, bp[0], cp[0]);
      /* the full product is {h, l, sb + v + w, sb2} */
      sb += v;
      l += (sb < v);
      h += (l == 0) && (sb < v);
      sb += w;
      l += (sb < w);
      h += (l == 0) && (sb < w);
    }
  if (h < MPFR_LIMB_HIGHBIT)
    {
      ax --;
      h = (h << 1) | (l >> (GMP_NUMB_BITS - 1));
      l = (l << 1) | (sb >> (GMP_NUMB_BITS - 1));
      sb <<= 1;
      /* no need to shift sb2 since we only want to know if it is zero or not */
    }
  ap[1] = h;
  rb = l & (MPFR_LIMB_ONE << (sh - 1));
  sb |= ((l & mask) ^ rb) | sb2;
  ap[0] = l & ~mask;

  MPFR_SIGN(a) = MPFR_MULT_SIGN (MPFR_SIGN (b), MPFR_SIGN (c));

  /* rounding */
  if (MPFR_UNLIKELY(ax > __gmpfr_emax))
    return mpfr_overflow (a, rnd_mode, MPFR_SIGN(a));

  /* Warning: underflow should be checked *after* rounding, thus when rounding
     away and when a > 0.111...111*2^(emin-1), or when rounding to nearest and
     a >= 0.111...111[1]*2^(emin-1), there is no underflow. */
  if (MPFR_UNLIKELY(ax < __gmpfr_emin))
    {
      if (ax == __gmpfr_emin - 1 &&
          ap[1] == MPFR_LIMB_MAX &&
          ap[0] == ~mask &&
          ((rnd_mode == MPFR_RNDN && rb) ||
           (MPFR_IS_LIKE_RNDA(rnd_mode, MPFR_IS_NEG (a)) && (rb | sb))))
        goto rounding; /* no underflow */
      /* for RNDN, mpfr_underflow always rounds away, thus for |a| <= 2^(emin-2)
         we have to change to RNDZ */
      if (rnd_mode == MPFR_RNDN &&
          (ax < __gmpfr_emin - 1 ||
           (ap[1] == MPFR_LIMB_HIGHBIT && ap[0] == 0 && (rb | sb) == 0)))
            rnd_mode = MPFR_RNDZ;
      return mpfr_underflow (a, rnd_mode, MPFR_SIGN(a));
    }

 rounding:
  MPFR_EXP (a) = ax; /* Don't use MPFR_SET_EXP since ax might be < __gmpfr_emin
                        in the cases "goto rounding" above. */
  if ((rb == 0 && sb == 0) || rnd_mode == MPFR_RNDF)
    {
      MPFR_ASSERTD(ax >= __gmpfr_emin);
      MPFR_RET (0);
    }
  else if (rnd_mode == MPFR_RNDN)
    {
      if (rb == 0 || (sb == 0 && (ap[0] & (MPFR_LIMB_ONE << sh)) == 0))
        goto truncate;
      else
        goto add_one_ulp;
    }
  else if (MPFR_IS_LIKE_RNDZ(rnd_mode, MPFR_IS_NEG(a)))
    {
    truncate:
      MPFR_ASSERTD(ax >= __gmpfr_emin);
      MPFR_RET(-MPFR_SIGN(a));
    }
  else /* round away from zero */
    {
    add_one_ulp:
      ap[0] += MPFR_LIMB_ONE << sh;
      ap[1] += (ap[0] == 0);
      if (ap[1] == 0)
        {
          ap[1] = MPFR_LIMB_HIGHBIT;
          if (MPFR_UNLIKELY(ax + 1 > __gmpfr_emax))
            return mpfr_overflow (a, rnd_mode, MPFR_SIGN(a));
          MPFR_ASSERTD(ax + 1 <= __gmpfr_emax);
          MPFR_ASSERTD(ax + 1 >= __gmpfr_emin);
          MPFR_SET_EXP (a, ax + 1);
        }
      MPFR_RET(MPFR_SIGN(a));
    }
}

/* Special code for 2*GMP_NUMB_BITS < prec(a) < 3*GMP_NUMB_BITS and
   2*GMP_NUMB_BITS < prec(b), prec(c) <= 3*GMP_NUMB_BITS. */
static int
mpfr_mul_3 (mpfr_ptr a, mpfr_srcptr b, mpfr_srcptr c, mpfr_rnd_t rnd_mode,
            mpfr_prec_t p)
{
  mp_limb_t a0, a1, a2, h, l, cy;
  mpfr_limb_ptr ap = MPFR_MANT(a);
  mpfr_exp_t ax = MPFR_GET_EXP(b) + MPFR_GET_EXP(c);
  mpfr_prec_t sh = 3 * GMP_NUMB_BITS - p;
  mp_limb_t rb, sb, sb2, mask = MPFR_LIMB_MASK(sh);
  mp_limb_t *bp = MPFR_MANT(b), *cp = MPFR_MANT(c);

  /* we store the upper 3-limb product in a2, a1, a0:
     b2*c2, b2*c1+b1*c2, b2*c0+b1*c1+b0*c2 */
  umul_ppmm (a2, a1, bp[2], cp[2]);
  umul_ppmm (h, a0, bp[2], cp[1]);
  a1 += h;
  a2 += (a1 < h);
  umul_ppmm (h, l, bp[1], cp[2]);
  a1 += h;
  a2 += (a1 < h);
  a0 += l;
  cy = a0 < l; /* carry in a1 */
  umul_ppmm (h, l, bp[2], cp[0]);
  a0 += h;
  cy += (a0 < h);
  umul_ppmm (h, l, bp[1], cp[1]);
  a0 += h;
  cy += (a0 < h);
  umul_ppmm (h, l, bp[0], cp[2]);
  a0 += h;
  cy += (a0 < h);
  /* now propagate cy */
  a1 += cy;
  a2 += (a1 < cy);

  /* Now the approximate product {a2, a1, a0} has an error of less than
     5 ulps (3 ulps for the ignored low limbs of b2*c0+b1*c1+b0*c2,
     plus 2 ulps for the ignored b1*c0+b0*c1 (plus b0*c0)).
     Since we might shift by 1 bit, we make sure the low sh-2 bits of a0
     are not 0, -1, -2, -3 or -4. */

  if (MPFR_LIKELY(((a0 + 4) & (mask >> 2)) > 4))
    sb = sb2 = 1; /* result cannot be exact in that case */
  else
    {
      mp_limb_t p[6];
      mpn_mul_n (p, bp, cp, 3);
      a2 = p[5];
      a1 = p[4];
      a0 = p[3];
      sb = p[2];
      sb2 = p[1] | p[0];
    }
  if (a2 < MPFR_LIMB_HIGHBIT)
    {
      ax --;
      a2 = (a2 << 1) | (a1 >> (GMP_NUMB_BITS - 1));
      a1 = (a1 << 1) | (a0 >> (GMP_NUMB_BITS - 1));
      a0 = (a0 << 1) | (sb >> (GMP_NUMB_BITS - 1));
      sb <<= 1;
      /* no need to shift sb2: we only need to know if it is zero or not */
    }
  ap[2] = a2;
  ap[1] = a1;
  rb = a0 & (MPFR_LIMB_ONE << (sh - 1));
  sb |= ((a0 & mask) ^ rb) | sb2;
  ap[0] = a0 & ~mask;

  MPFR_SIGN(a) = MPFR_MULT_SIGN (MPFR_SIGN (b), MPFR_SIGN (c));

  /* rounding */
  if (MPFR_UNLIKELY(ax > __gmpfr_emax))
    return mpfr_overflow (a, rnd_mode, MPFR_SIGN(a));

  /* Warning: underflow should be checked *after* rounding, thus when rounding
     away and when a > 0.111...111*2^(emin-1), or when rounding to nearest and
     a >= 0.111...111[1]*2^(emin-1), there is no underflow. */
  if (MPFR_UNLIKELY(ax < __gmpfr_emin))
    {
      if (ax == __gmpfr_emin - 1 &&
          ap[2] == MPFR_LIMB_MAX &&
          ap[1] == MPFR_LIMB_MAX &&
          ap[0] == ~mask &&
          ((rnd_mode == MPFR_RNDN && rb) ||
           (MPFR_IS_LIKE_RNDA(rnd_mode, MPFR_IS_NEG (a)) && (rb | sb))))
        goto rounding; /* no underflow */
      /* for RNDN, mpfr_underflow always rounds away, thus for |a| <= 2^(emin-2)
         we have to change to RNDZ */
      if (rnd_mode == MPFR_RNDN &&
          (ax < __gmpfr_emin - 1 ||
           (ap[2] == MPFR_LIMB_HIGHBIT && ap[1] == 0 && ap[0] == 0
            && (rb | sb) == 0)))
        rnd_mode = MPFR_RNDZ;
      return mpfr_underflow (a, rnd_mode, MPFR_SIGN(a));
    }

 rounding:
  MPFR_EXP (a) = ax; /* Don't use MPFR_SET_EXP since ax might be < __gmpfr_emin
                        in the cases "goto rounding" above. */
  if ((rb == 0 && sb == 0) || rnd_mode == MPFR_RNDF)
    {
      MPFR_ASSERTD(ax >= __gmpfr_emin);
      MPFR_RET (0);
    }
  else if (rnd_mode == MPFR_RNDN)
    {
      if (rb == 0 || (sb == 0 && (ap[0] & (MPFR_LIMB_ONE << sh)) == 0))
        goto truncate;
      else
        goto add_one_ulp;
    }
  else if (MPFR_IS_LIKE_RNDZ(rnd_mode, MPFR_IS_NEG(a)))
    {
    truncate:
      MPFR_ASSERTD(ax >= __gmpfr_emin);
      MPFR_RET(-MPFR_SIGN(a));
    }
  else /* round away from zero */
    {
    add_one_ulp:
      ap[0] += MPFR_LIMB_ONE << sh;
      ap[1] += (ap[0] == 0);
      ap[2] += (ap[1] == 0) && (ap[0] == 0);
      if (ap[2] == 0)
        {
          ap[2] = MPFR_LIMB_HIGHBIT;
          if (MPFR_UNLIKELY(ax + 1 > __gmpfr_emax))
            return mpfr_overflow (a, rnd_mode, MPFR_SIGN(a));
          MPFR_ASSERTD(ax + 1 <= __gmpfr_emax);
          MPFR_ASSERTD(ax + 1 >= __gmpfr_emin);
          MPFR_SET_EXP (a, ax + 1);
        }
      MPFR_RET(MPFR_SIGN(a));
    }
}

#endif /* !defined(MPFR_GENERIC_ABI) */

/* Note: mpfr_sqr will call mpfr_mul if bn > MPFR_SQR_THRESHOLD,
   in order to use Mulders' mulhigh, which is handled only here
   to avoid partial code duplication. There is some overhead due
   to the additional tests, but slowdown should not be noticeable
   as this code is not executed in very small precisions. */

MPFR_HOT_FUNCTION_ATTR int
mpfr_mul (mpfr_ptr a, mpfr_srcptr b, mpfr_srcptr c, mpfr_rnd_t rnd_mode)
{
  int sign, inexact;
  mpfr_exp_t ax, ax2;
  mp_limb_t *tmp;
  mp_limb_t b1;
  mpfr_prec_t aq, bq, cq;
  mp_size_t bn, cn, tn, k, threshold;
  MPFR_TMP_DECL (marker);

  MPFR_LOG_FUNC
    (("b[%Pu]=%.*Rg c[%Pu]=%.*Rg rnd=%d",
      mpfr_get_prec (b), mpfr_log_prec, b,
      mpfr_get_prec (c), mpfr_log_prec, c, rnd_mode),
     ("a[%Pu]=%.*Rg inexact=%d",
      mpfr_get_prec (a), mpfr_log_prec, a, inexact));

  /* deal with special cases */
  if (MPFR_ARE_SINGULAR (b, c))
    {
      if (MPFR_IS_NAN (b) || MPFR_IS_NAN (c))
        {
          MPFR_SET_NAN (a);
          MPFR_RET_NAN;
        }
      sign = MPFR_MULT_SIGN (MPFR_SIGN (b), MPFR_SIGN (c));
      if (MPFR_IS_INF (b))
        {
          if (!MPFR_IS_ZERO (c))
            {
              MPFR_SET_SIGN (a, sign);
              MPFR_SET_INF (a);
              MPFR_RET (0);
            }
          else
            {
              MPFR_SET_NAN (a);
              MPFR_RET_NAN;
            }
        }
      else if (MPFR_IS_INF (c))
        {
          if (!MPFR_IS_ZERO (b))
            {
              MPFR_SET_SIGN (a, sign);
              MPFR_SET_INF (a);
              MPFR_RET(0);
            }
          else
            {
              MPFR_SET_NAN (a);
              MPFR_RET_NAN;
            }
        }
      else
        {
          MPFR_ASSERTD (MPFR_IS_ZERO(b) || MPFR_IS_ZERO(c));
          MPFR_SET_SIGN (a, sign);
          MPFR_SET_ZERO (a);
          MPFR_RET (0);
        }
    }

  aq = MPFR_GET_PREC (a);
  bq = MPFR_GET_PREC (b);
  cq = MPFR_GET_PREC (c);

#if !defined(MPFR_GENERIC_ABI)
  if (aq == bq && aq == cq)
    {
      if (aq < GMP_NUMB_BITS)
        return mpfr_mul_1 (a, b, c, rnd_mode, aq);

      if (GMP_NUMB_BITS < aq && aq < 2 * GMP_NUMB_BITS)
        return mpfr_mul_2 (a, b, c, rnd_mode, aq);

      if (aq == GMP_NUMB_BITS)
        return mpfr_mul_1n (a, b, c, rnd_mode);

      if (2 * GMP_NUMB_BITS < aq && aq < 3 * GMP_NUMB_BITS)
        return mpfr_mul_3 (a, b, c, rnd_mode, aq);
    }
#endif

  sign = MPFR_MULT_SIGN (MPFR_SIGN (b), MPFR_SIGN (c));

  ax = MPFR_GET_EXP (b) + MPFR_GET_EXP (c);
  /* Note: the exponent of the exact result will be e = bx + cx + ec with
     ec in {-1,0,1} and the following assumes that e is representable. */

  /* FIXME: Useful since we do an exponent check after?
   * It is useful iff the precision is big, there is an overflow
   * and we are doing further mults...*/
#ifdef HUGE
  if (MPFR_UNLIKELY (ax > __gmpfr_emax + 1))
    return mpfr_overflow (a, rnd_mode, sign);
  if (MPFR_UNLIKELY (ax < __gmpfr_emin - 2))
    return mpfr_underflow (a, rnd_mode == MPFR_RNDN ? MPFR_RNDZ : rnd_mode,
                           sign);
#endif

  MPFR_ASSERTN ((mpfr_uprec_t) bq + cq <= MPFR_PREC_MAX);

  bn = MPFR_PREC2LIMBS (bq); /* number of limbs of b */
  cn = MPFR_PREC2LIMBS (cq); /* number of limbs of c */
  k = bn + cn; /* effective nb of limbs used by b*c (= tn or tn+1) below */
  tn = MPFR_PREC2LIMBS (bq + cq);
  MPFR_ASSERTD (tn <= k); /* tn <= k, thus no int overflow */

  /* Check for no size_t overflow. */
  MPFR_ASSERTD ((size_t) k <= ((size_t) -1) / MPFR_BYTES_PER_MP_LIMB);
  MPFR_TMP_MARK (marker);
  tmp = MPFR_TMP_LIMBS_ALLOC (k);

  /* multiplies two mantissa in temporary allocated space */
  if (MPFR_UNLIKELY (bn < cn))
    {
      mpfr_srcptr z = b;
      mp_size_t zn  = bn;
      b = c;
      bn = cn;
      c = z;
      cn = zn;
    }
  MPFR_ASSERTD (bn >= cn);
  if (bn <= 2)
    {
      /* The 3 cases perform the same first operation. */
      umul_ppmm (tmp[1], tmp[0], MPFR_MANT (b)[0], MPFR_MANT (c)[0]);
      if (bn == 1)
        {
          /* 1 limb * 1 limb */
          b1 = tmp[1];
        }
      else if (MPFR_UNLIKELY (cn == 1))
        {
          /* 2 limbs * 1 limb */
          mp_limb_t t;
          umul_ppmm (tmp[2], t, MPFR_MANT (b)[1], MPFR_MANT (c)[0]);
          add_ssaaaa (tmp[2], tmp[1], tmp[2], tmp[1], 0, t);
          b1 = tmp[2];
        }
      else
        {
          /* 2 limbs * 2 limbs */
          mp_limb_t t1, t2, t3;
          /* First 2 limbs * 1 limb */
          umul_ppmm (tmp[2], t1, MPFR_MANT (b)[1], MPFR_MANT (c)[0]);
          add_ssaaaa (tmp[2], tmp[1], tmp[2], tmp[1], 0, t1);
          /* Second, the other 2 limbs * 1 limb product */
          umul_ppmm (t1, t2, MPFR_MANT (b)[0], MPFR_MANT (c)[1]);
          umul_ppmm (tmp[3], t3, MPFR_MANT (b)[1], MPFR_MANT (c)[1]);
          add_ssaaaa (tmp[3], t1, tmp[3], t1, 0, t3);
          /* Sum those two partial products */
          add_ssaaaa (tmp[2], tmp[1], tmp[2], tmp[1], t1, t2);
          tmp[3] += (tmp[2] < t1);
          b1 = tmp[3];
        }
      b1 >>= (GMP_NUMB_BITS - 1);
      tmp += k - tn;
      if (MPFR_UNLIKELY (b1 == 0))
        mpn_lshift (tmp, tmp, tn, 1); /* tn <= k, so no stack corruption */
    }
  else /* bn >= cn and bn >= 3 */
    /* Mulders' mulhigh. This code can also be used via mpfr_sqr,
       hence the tests b != c. */
    if (MPFR_UNLIKELY (cn > (threshold = b != c ?
                             MPFR_MUL_THRESHOLD : MPFR_SQR_THRESHOLD)))
      {
        mp_limb_t *bp, *cp;
        mp_size_t n;
        mpfr_prec_t p;

        /* First check if we can reduce the precision of b or c:
           exact values are a nightmare for the short product trick */
        bp = MPFR_MANT (b);
        cp = MPFR_MANT (c);
        MPFR_STAT_STATIC_ASSERT (MPFR_MUL_THRESHOLD >= 1 &&
                                 MPFR_SQR_THRESHOLD >= 1);
        if (MPFR_UNLIKELY ((bp[0] == 0 && bp[1] == 0) ||
                           (cp[0] == 0 && cp[1] == 0)))
          {
            mpfr_t b_tmp, c_tmp;

            MPFR_TMP_FREE (marker);
            /* Check for b */
            while (*bp == 0)
              {
                bp++;
                bn--;
                MPFR_ASSERTD (bn > 0);
              } /* This must end since the most significant limb is != 0 */

            /* Check for c too: if b == c, this will do nothing */
            while (*cp == 0)
              {
                cp++;
                cn--;
                MPFR_ASSERTD (cn > 0);
              } /* This must end since the most significant limb is != 0 */

            /* It is not the fastest way, but it is safer. */
            MPFR_SET_SAME_SIGN (b_tmp, b);
            MPFR_SET_EXP (b_tmp, MPFR_GET_EXP (b));
            MPFR_PREC (b_tmp) = bn * GMP_NUMB_BITS;
            MPFR_MANT (b_tmp) = bp;

            if (b != c)
              {
                MPFR_SET_SAME_SIGN (c_tmp, c);
                MPFR_SET_EXP (c_tmp, MPFR_GET_EXP (c));
                MPFR_PREC (c_tmp) = cn * GMP_NUMB_BITS;
                MPFR_MANT (c_tmp) = cp;

                /* Call again mpfr_mul with the fixed arguments */
                return mpfr_mul (a, b_tmp, c_tmp, rnd_mode);
              }
            else
              /* Call mpfr_mul instead of mpfr_sqr as the precision
                 is probably still high enough. It is thus better to call
                 mpfr_mul again, but it should not give an infinite loop
                 if we call mpfr_sqr. */
              return mpfr_mul (a, b_tmp, b_tmp, rnd_mode);
          }

        /* Compute estimated precision of mulhigh.
           We could use `+ (n < cn) + (n < bn)' instead of `+ 2',
           but does it worth it? */
        n = MPFR_LIMB_SIZE (a) + 1;
        n = MIN (n, cn);
        MPFR_ASSERTD (n >= 1 && 2*n <= k && n <= cn && n <= bn);
        p = n * GMP_NUMB_BITS - MPFR_INT_CEIL_LOG2 (n + 2);
        bp += bn - n;
        cp += cn - n;

        /* Check if MulHigh can produce a roundable result.
           We may lose 1 bit due to RNDN, 1 due to final shift. */
        if (MPFR_UNLIKELY (aq > p - 5))
          {
            if (MPFR_UNLIKELY (aq > p - 5 + GMP_NUMB_BITS
                               || bn <= threshold + 1))
              {
                /* MulHigh can't produce a roundable result. */
                MPFR_LOG_MSG (("mpfr_mulhigh can't be used (%lu VS %lu)\n",
                               aq, p));
                goto full_multiply;
              }
            /* Add one extra limb to mantissa of b and c. */
            if (bn > n)
              bp --;
            else
              {
                bp = MPFR_TMP_LIMBS_ALLOC (n + 1);
                bp[0] = 0;
                MPN_COPY (bp + 1, MPFR_MANT (b) + bn - n, n);
              }
            if (b != c)
              {
#if GMP_NUMB_BITS <= 32
                if (cn > n)
                  cp --; /* This can only happen on a 32-bit computer,
                            and is very unlikely to happen.
                            Indeed, since n = MIN (an + 1, cn), with
                            an = MPFR_LIMB_SIZE(a), we can have cn > n
                            only when n = an + 1 < cn.
                            We are in the case aq > p - 5, with
                            aq = PREC(a) = an*W - sh, with W = GMP_NUMB_BITS
                            and 0 <= sh < W, and p = n*W - ceil(log2(n+2)),
                            thus an*W - sh > n*W - ceil(log2(n+2)) - 5.
                            Thus n < an + (ceil(log2(n+2)) + 5 - sh)/W.
                            To get n = an + 1, we need
                            ceil(log2(n+2)) + 5 - sh > W, thus since sh>=0
                            we need ceil(log2(n+2)) + 5 > W.
                            With W=32 this can only happen for n>=2^27-1,
                            thus for a precision of 2^32-64 for a,
                            and with W=64 for n>=2^59-1, which would give
                            a precision >= 2^64. */
                else
#endif
                  {
                    cp = MPFR_TMP_LIMBS_ALLOC (n + 1);
                    cp[0] = 0;
                    MPN_COPY (cp + 1, MPFR_MANT (c) + cn - n, n);
                  }
              }
            /* We will compute with one extra limb */
            n++;
            /* ceil(log2(n+2)) takes into account the lost bits due to
               Mulders' short product */
            p = n * GMP_NUMB_BITS - MPFR_INT_CEIL_LOG2 (n + 2);
            /* Due to some nasty reasons we can have only 4 bits */
            MPFR_ASSERTD (aq <= p - 4);

            if (MPFR_LIKELY (k < 2*n))
              {
                tmp = MPFR_TMP_LIMBS_ALLOC (2 * n);
                tmp += 2*n-k; /* `tmp' still points to an area of `k' limbs */
              }
          }
        MPFR_LOG_MSG (("Use mpfr_mulhigh (%lu VS %lu)\n", aq, p));
        /* Compute an approximation of the product of b and c */
        if (b != c)
          mpfr_mulhigh_n (tmp + k - 2 * n, bp, cp, n);
        else
          mpfr_sqrhigh_n (tmp + k - 2 * n, bp, n);
        /* now tmp[k-n]..tmp[k-1] contains an approximation of the n upper
           limbs of the product, with tmp[k-1] >= 2^(GMP_NUMB_BITS-2) */
        b1 = tmp[k-1] >> (GMP_NUMB_BITS - 1); /* msb from the product */

        /* If the mantissas of b and c are uniformly distributed in (1/2, 1],
           then their product is in (1/4, 1/2] with probability 2*ln(2)-1
           ~ 0.386 and in [1/2, 1] with probability 2-2*ln(2) ~ 0.614 */
        if (MPFR_UNLIKELY (b1 == 0))
          /* Warning: the mpfr_mulhigh_n call above only surely affects
             tmp[k-n-1..k-1], thus we shift only those limbs */
          mpn_lshift (tmp + k - n - 1, tmp + k - n - 1, n + 1, 1);
        tmp += k - tn;
        /* now the approximation is in tmp[tn-n]...tmp[tn-1] */
        MPFR_ASSERTD (MPFR_LIMB_MSB (tmp[tn-1]) != 0);

        /* for RNDF, we simply use RNDZ, since anyway here we multiply numbers
           with large precisions, thus the overhead of RNDZ is small */
        if (rnd_mode == MPFR_RNDF)
          rnd_mode = MPFR_RNDZ;

        /* if the most significant bit b1 is zero, we have only p-1 correct
           bits */
        if (MPFR_UNLIKELY (!mpfr_round_p (tmp, tn, p + b1 - 1,
                                          aq + (rnd_mode == MPFR_RNDN))))
          {
            tmp -= k - tn; /* tmp may have changed, FIX IT!!!!! */
            goto full_multiply;
          }
      }
    else
      {
      full_multiply:
        MPFR_LOG_MSG (("Use mpn_mul\n", 0));
        b1 = mpn_mul (tmp, MPFR_MANT (b), bn, MPFR_MANT (c), cn);

        /* now tmp[0]..tmp[k-1] contains the product of both mantissa,
           with tmp[k-1]>=2^(GMP_NUMB_BITS-2) */
        b1 >>= GMP_NUMB_BITS - 1; /* msb from the product */

        /* if the mantissas of b and c are uniformly distributed in (1/2, 1],
           then their product is in (1/4, 1/2] with probability 2*ln(2)-1
           ~ 0.386 and in [1/2, 1] with probability 2-2*ln(2) ~ 0.614 */
        tmp += k - tn;
        if (MPFR_UNLIKELY (b1 == 0))
          mpn_lshift (tmp, tmp, tn, 1); /* tn <= k, so no stack corruption */
      }

  ax2 = ax + (mpfr_exp_t) (b1 - 1);
  MPFR_RNDRAW (inexact, a, tmp, bq + cq, rnd_mode, sign, ax2++);
  MPFR_TMP_FREE (marker);
  MPFR_EXP (a) = ax2; /* Can't use MPFR_SET_EXP: Expo may be out of range */
  MPFR_SET_SIGN (a, sign);
  if (MPFR_UNLIKELY (ax2 > __gmpfr_emax))
    return mpfr_overflow (a, rnd_mode, sign);
  if (MPFR_UNLIKELY (ax2 < __gmpfr_emin))
    {
      /* In the rounding to the nearest mode, if the exponent of the exact
         result (i.e. before rounding, i.e. without taking cc into account)
         is < __gmpfr_emin - 1 or the exact result is a power of 2 (i.e. if
         both arguments are powers of 2), then round to zero. */
      if (rnd_mode == MPFR_RNDN
          && (ax + (mpfr_exp_t) b1 < __gmpfr_emin
              || (mpfr_powerof2_raw (b) && mpfr_powerof2_raw (c))))
        rnd_mode = MPFR_RNDZ;
      return mpfr_underflow (a, rnd_mode, sign);
    }
  MPFR_RET (inexact);
}
