/* mpfr_add1sp -- internal function to perform a "real" addition
   All the op must have the same precision

Copyright 2004-2018 Free Software Foundation, Inc.
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

#if MPFR_WANT_ASSERT >= 2
/* Check the result of mpfr_add1sp with mpfr_add1.

   Note: mpfr_add1sp itself has two algorithms: one always valid and one
   faster for small precisions (up to 3 limbs). The latter one is disabled
   if MPFR_GENERIC_ABI is defined. When MPFR_WANT_ASSERT >= 2, it could be
   interesting to compare the results of these different algorithms. For
   the time being, this is currently done by running the same code on the
   same data with and without MPFR_GENERIC_ABI defined, where we have the
   following comparisons in small precisions:
     mpfr_add1sp slow <-> mpfr_add1 when MPFR_GENERIC_ABI is defined;
     mpfr_add1sp fast <-> mpfr_add1 when MPFR_GENERIC_ABI is not defined.
   By transitivity, the absence of failures implies that the 3 results are
   the same.
*/

int mpfr_add1sp_ref (mpfr_ptr, mpfr_srcptr, mpfr_srcptr, mpfr_rnd_t);
int mpfr_add1sp (mpfr_ptr a, mpfr_srcptr b, mpfr_srcptr c, mpfr_rnd_t rnd_mode)
{
  mpfr_t tmpa, tmpb, tmpc, tmpd;
  mpfr_flags_t old_flags, flags, flags2;
  int inexb, inexc, inexact, inexact2;

  if (rnd_mode == MPFR_RNDF)
    return mpfr_add1sp_ref (a, b, c, rnd_mode);

  old_flags = __gmpfr_flags;

  mpfr_init2 (tmpa, MPFR_PREC (a));
  mpfr_init2 (tmpb, MPFR_PREC (b));
  mpfr_init2 (tmpc, MPFR_PREC (c));

  inexb = mpfr_set (tmpb, b, MPFR_RNDN);
  MPFR_ASSERTN (inexb == 0);

  inexc = mpfr_set (tmpc, c, MPFR_RNDN);
  MPFR_ASSERTN (inexc == 0);

  MPFR_ASSERTN (__gmpfr_flags == old_flags);

  if (MPFR_GET_EXP (tmpb) < MPFR_GET_EXP (tmpc))
    {
      /* The sign for the result will be taken from the second argument
         (= first input value, which is tmpb). */
      MPFR_ALIAS (tmpd, tmpc, MPFR_SIGN (tmpb), MPFR_EXP (tmpc));
      inexact2 = mpfr_add1 (tmpa, tmpd, tmpb, rnd_mode);
    }
  else
    {
      inexact2 = mpfr_add1 (tmpa, tmpb, tmpc, rnd_mode);
    }
  flags2 = __gmpfr_flags;

  __gmpfr_flags = old_flags;
  inexact = mpfr_add1sp_ref (a, b, c, rnd_mode);
  flags = __gmpfr_flags;

  if (! mpfr_equal_p (tmpa, a) || inexact != inexact2 /*|| flags != flags2*/)
    {
      fprintf (stderr, "add1 & add1sp return different values for %s\n"
               "Prec_a = %lu, Prec_b = %lu, Prec_c = %lu\nB = ",
               mpfr_print_rnd_mode (rnd_mode),
               (unsigned long) MPFR_PREC (a),
               (unsigned long) MPFR_PREC (b),
               (unsigned long) MPFR_PREC (c));
      mpfr_fdump (stderr, tmpb);
      fprintf (stderr, "C = ");
      mpfr_fdump (stderr, tmpc);
      fprintf (stderr, "\nadd1  : ");
      mpfr_fdump (stderr, tmpa);
      fprintf (stderr, "add1sp: ");
      mpfr_fdump (stderr, a);
      fprintf (stderr, "Inexact sp = %d | Inexact = %d\n"
               "Flags sp = %u | Flags = %u\n",
               inexact, inexact2, flags, flags2);
      MPFR_ASSERTN (0);
    }
  mpfr_clears (tmpa, tmpb, tmpc, (mpfr_ptr) 0);
  return inexact;
}
# define mpfr_add1sp mpfr_add1sp_ref
#endif  /* MPFR_WANT_ASSERT >= 2 */

#if !defined(MPFR_GENERIC_ABI)



#define uint32_t mpfr_prec_t
#define int32_t mpfr_exp_t
#define uint64_t mp_limb_t

typedef struct MPFR_Add1sp1_state_s
{
  uint32_t sh;
  int32_t bx;
  uint64_t rb;
  uint64_t sb;
}
MPFR_Add1sp1_state;

static MPFR_Add1sp1_state
MPFR_Add1sp1_mk_state(uint32_t sh, int32_t bx, uint64_t rb, uint64_t sb)
{
  return ((MPFR_Add1sp1_state){ .sh = sh, .bx = bx, .rb = rb, .sb = sb });
}

typedef struct K___uint64_t_int32_t_s
{
  uint64_t fst;
  int32_t snd;
}
K___uint64_t_int32_t;

typedef struct K___uint64_t_uint64_t_int32_t_s
{
  uint64_t fst;
  uint64_t snd;
  int32_t thd;
}
K___uint64_t_uint64_t_int32_t;

#define MPFR_Lib_mpfr_struct __mpfr_struct
#define MPFR_Exceptions_mpfr_overflow mpfr_overflow
#define mpfr_prec _mpfr_prec
#define mpfr_exp _mpfr_exp
#define mpfr_d _mpfr_d
#define mpfr_sign _mpfr_sign
#define MPFR_Lib_gmp_NUMB_BITS GMP_NUMB_BITS
#define MPFR_Lib_mpfr_EMAX __gmpfr_emax

#define MPFR_RoundingMode_uu___is_MPFR_RNDN(rnd_mode) (rnd_mode == MPFR_RNDN)
#define MPFR_RoundingMode_mpfr_IS_LIKE_RNDZ MPFR_IS_LIKE_RNDZ

/* same as mpfr_add1sp, but for p < GMP_NUMB_BITS */
static int
mpfr_add1sp1 (mpfr_ptr a, mpfr_srcptr b, mpfr_srcptr c, mpfr_rnd_t rnd_mode,
              mpfr_prec_t p)
{
  MPFR_Lib_mpfr_struct a0 = a[0U];
  MPFR_Lib_mpfr_struct b0 = b[0U];
  MPFR_Lib_mpfr_struct c0 = c[0U];
  int32_t bx = b0.mpfr_exp;
  int32_t cx = c0.mpfr_exp;
  uint32_t sh = MPFR_Lib_gmp_NUMB_BITS - p;
  MPFR_Add1sp1_state st;
  if (bx == cx)
  {
    uint64_t *ap = a0.mpfr_d;
    uint64_t *bp = b0.mpfr_d;
    uint64_t *cp = c0.mpfr_d;
    uint64_t a01 = (bp[0U] >> (uint32_t)1U) + (cp[0U] >> (uint32_t)1U);
    int32_t bx1 = b0.mpfr_exp + (int32_t)1;
    uint64_t rb = a01 & (uint64_t)1U << sh - (uint32_t)1U;
    ap[0U] = a01 ^ rb;
    uint64_t sb = (uint64_t)0U;
    st = MPFR_Add1sp1_mk_state(sh, bx1, rb, sb);
  }
  else
  {
    MPFR_Add1sp1_state ite0;
    if (bx > cx)
    {
      int32_t bx1 = b0.mpfr_exp;
      int32_t cx1 = c0.mpfr_exp;
      uint32_t d = (uint32_t)(bx1 - cx1);
      uint64_t mask = ((uint64_t)1U << sh) - (uint64_t)1U;
      MPFR_Add1sp1_state ite1;
      if (d < sh)
      {
        uint64_t *ap = a0.mpfr_d;
        uint64_t *bp = b0.mpfr_d;
        uint64_t *cp = c0.mpfr_d;
        int32_t bx2 = b0.mpfr_exp;
        uint64_t a01 = bp[0U] + (cp[0U] >> d);
        K___uint64_t_int32_t scrut;
        if (a01 < bp[0U])
          scrut =
            (
              (K___uint64_t_int32_t){
                .fst = (uint64_t)0x8000000000000000U | a01 >> (uint32_t)1U,
                .snd = bx2 + (int32_t)1
              }
            );
        else
          scrut = ((K___uint64_t_int32_t){ .fst = a01, .snd = bx2 });
        uint64_t a02 = scrut.fst;
        int32_t bx3 = scrut.snd;
        uint64_t rb = a02 & (uint64_t)1U << sh - (uint32_t)1U;
        uint64_t sb = a02 & mask ^ rb;
        ap[0U] = a02 & ~mask;
        ite1 = MPFR_Add1sp1_mk_state(sh, bx3, rb, sb);
      }
      else
      {
        MPFR_Add1sp1_state ite;
        if (d < MPFR_Lib_gmp_NUMB_BITS)
        {
          uint64_t *ap = a0.mpfr_d;
          uint64_t *bp = b0.mpfr_d;
          uint64_t *cp = c0.mpfr_d;
          int32_t bx2 = b0.mpfr_exp;
          uint64_t sb = cp[0U] << MPFR_Lib_gmp_NUMB_BITS - d;
          uint64_t a01 = bp[0U] + (cp[0U] >> d);
          K___uint64_t_uint64_t_int32_t scrut;
          if (a01 < bp[0U])
            scrut =
              (
                (K___uint64_t_uint64_t_int32_t){
                  .fst = sb | a01 & (uint64_t)1U,
                  .snd = (uint64_t)0x8000000000000000U | a01 >> (uint32_t)1U,
                  .thd = bx2 + (int32_t)1
                }
              );
          else
            scrut = ((K___uint64_t_uint64_t_int32_t){ .fst = sb, .snd = a01, .thd = bx2 });
          uint64_t sb1 = scrut.fst;
          uint64_t a02 = scrut.snd;
          int32_t bx3 = scrut.thd;
          uint64_t rb = a02 & (uint64_t)1U << sh - (uint32_t)1U;
          uint64_t sb2 = sb1 | a02 & mask ^ rb;
          ap[0U] = a02 & ~mask;
          ite = MPFR_Add1sp1_mk_state(sh, bx3, rb, sb2);
        }
        else
        {
          uint64_t *ap = a0.mpfr_d;
          uint64_t *bp = b0.mpfr_d;
          int32_t bx2 = b0.mpfr_exp;
          ap[0U] = bp[0U];
          uint64_t rb = (uint64_t)0U;
          uint64_t sb = (uint64_t)1U;
          ite = MPFR_Add1sp1_mk_state(sh, bx2, rb, sb);
        }
        ite1 = ite;
      }
      ite0 = ite1;
    }
    else
    {
      int32_t bx1 = c0.mpfr_exp;
      int32_t cx1 = b0.mpfr_exp;
      uint32_t d = (uint32_t)(bx1 - cx1);
      uint64_t mask = ((uint64_t)1U << sh) - (uint64_t)1U;
      MPFR_Add1sp1_state ite1;
      if (d < sh)
      {
        uint64_t *ap = a0.mpfr_d;
        uint64_t *bp = c0.mpfr_d;
        uint64_t *cp = b0.mpfr_d;
        int32_t bx2 = c0.mpfr_exp;
        uint64_t a01 = bp[0U] + (cp[0U] >> d);
        K___uint64_t_int32_t scrut;
        if (a01 < bp[0U])
          scrut =
            (
              (K___uint64_t_int32_t){
                .fst = (uint64_t)0x8000000000000000U | a01 >> (uint32_t)1U,
                .snd = bx2 + (int32_t)1
              }
            );
        else
          scrut = ((K___uint64_t_int32_t){ .fst = a01, .snd = bx2 });
        uint64_t a02 = scrut.fst;
        int32_t bx3 = scrut.snd;
        uint64_t rb = a02 & (uint64_t)1U << sh - (uint32_t)1U;
        uint64_t sb = a02 & mask ^ rb;
        ap[0U] = a02 & ~mask;
        ite1 = MPFR_Add1sp1_mk_state(sh, bx3, rb, sb);
      }
      else
      {
        MPFR_Add1sp1_state ite;
        if (d < MPFR_Lib_gmp_NUMB_BITS)
        {
          uint64_t *ap = a0.mpfr_d;
          uint64_t *bp = c0.mpfr_d;
          uint64_t *cp = b0.mpfr_d;
          int32_t bx2 = c0.mpfr_exp;
          uint64_t sb = cp[0U] << MPFR_Lib_gmp_NUMB_BITS - d;
          uint64_t a01 = bp[0U] + (cp[0U] >> d);
          K___uint64_t_uint64_t_int32_t scrut;
          if (a01 < bp[0U])
            scrut =
              (
                (K___uint64_t_uint64_t_int32_t){
                  .fst = sb | a01 & (uint64_t)1U,
                  .snd = (uint64_t)0x8000000000000000U | a01 >> (uint32_t)1U,
                  .thd = bx2 + (int32_t)1
                }
              );
          else
            scrut = ((K___uint64_t_uint64_t_int32_t){ .fst = sb, .snd = a01, .thd = bx2 });
          uint64_t sb1 = scrut.fst;
          uint64_t a02 = scrut.snd;
          int32_t bx3 = scrut.thd;
          uint64_t rb = a02 & (uint64_t)1U << sh - (uint32_t)1U;
          uint64_t sb2 = sb1 | a02 & mask ^ rb;
          ap[0U] = a02 & ~mask;
          ite = MPFR_Add1sp1_mk_state(sh, bx3, rb, sb2);
        }
        else
        {
          uint64_t *ap = a0.mpfr_d;
          uint64_t *bp = c0.mpfr_d;
          int32_t bx2 = c0.mpfr_exp;
          ap[0U] = bp[0U];
          uint64_t rb = (uint64_t)0U;
          uint64_t sb = (uint64_t)1U;
          ite = MPFR_Add1sp1_mk_state(sh, bx2, rb, sb);
        }
        ite1 = ite;
      }
      ite0 = ite1;
    }
    st = ite0;
  }
  if (st.bx > MPFR_Lib_mpfr_EMAX)
  {
    int32_t t = MPFR_Exceptions_mpfr_overflow(a, rnd_mode, a->mpfr_sign);
    return t;
  }
  else
  {
    uint64_t *ap = a->mpfr_d;
    uint64_t a01 = ap[0U];
    MPFR_Lib_mpfr_struct uu___54_3461 = a[0U];
    a[0U] =
      (
        (MPFR_Lib_mpfr_struct){
          .mpfr_prec = uu___54_3461.mpfr_prec,
          .mpfr_sign = uu___54_3461.mpfr_sign,
          .mpfr_exp = st.bx,
          .mpfr_d = uu___54_3461.mpfr_d
        }
      );
    if (st.rb == (uint64_t)0U && st.sb == (uint64_t)0U)
      return (int32_t)0;
    else if (MPFR_RoundingMode_uu___is_MPFR_RNDN(rnd_mode))
      if
      (
        st.rb
        == (uint64_t)0U
        || st.sb == (uint64_t)0U && (a01 & (uint64_t)1U << st.sh) == (uint64_t)0U
      )
        if (a->mpfr_sign == (int32_t)1)
          return (int32_t)-1;
        else
          return (int32_t)1;
      else
      {
        uint64_t *ap1 = a->mpfr_d;
        ap1[0U] = ap1[0U] + ((uint64_t)1U << st.sh);
        if (ap1[0U] == (uint64_t)0U)
        {
          ap1[0U] = (uint64_t)0x8000000000000000U;
          if (st.bx + (int32_t)1 <= MPFR_Lib_mpfr_EMAX)
          {
            MPFR_Lib_mpfr_struct uu___54_3556 = a[0U];
            a[0U] =
              (
                (MPFR_Lib_mpfr_struct){
                  .mpfr_prec = uu___54_3556.mpfr_prec,
                  .mpfr_sign = uu___54_3556.mpfr_sign,
                  .mpfr_exp = st.bx + (int32_t)1,
                  .mpfr_d = uu___54_3556.mpfr_d
                }
              );
            return a->mpfr_sign;
          }
          else
          {
            int32_t t = MPFR_Exceptions_mpfr_overflow(a, rnd_mode, a->mpfr_sign);
            return t;
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
      uint64_t *ap1 = a->mpfr_d;
      ap1[0U] = ap1[0U] + ((uint64_t)1U << st.sh);
      if (ap1[0U] == (uint64_t)0U)
      {
        ap1[0U] = (uint64_t)0x8000000000000000U;
        if (st.bx + (int32_t)1 <= MPFR_Lib_mpfr_EMAX)
        {
          MPFR_Lib_mpfr_struct uu___54_3760 = a[0U];
          a[0U] =
            (
              (MPFR_Lib_mpfr_struct){
                .mpfr_prec = uu___54_3760.mpfr_prec,
                .mpfr_sign = uu___54_3760.mpfr_sign,
                .mpfr_exp = st.bx + (int32_t)1,
                .mpfr_d = uu___54_3760.mpfr_d
              }
            );
          return a->mpfr_sign;
        }
        else
        {
          int32_t t = MPFR_Exceptions_mpfr_overflow(a, rnd_mode, a->mpfr_sign);
          return t;
        }
      }
      else
        return a->mpfr_sign;
    }
  }
}





/* same as mpfr_add1sp, but for p = GMP_NUMB_BITS */
static int
mpfr_add1sp1n (mpfr_ptr a, mpfr_srcptr b, mpfr_srcptr c, mpfr_rnd_t rnd_mode)
{
  mpfr_exp_t bx = MPFR_GET_EXP (b);
  mpfr_exp_t cx = MPFR_GET_EXP (c);
  mp_limb_t *ap = MPFR_MANT(a);
  mp_limb_t *bp = MPFR_MANT(b);
  mp_limb_t *cp = MPFR_MANT(c);
  mp_limb_t rb; /* round bit */
  mp_limb_t sb; /* sticky bit */
  mp_limb_t a0; /* to store the result */
  mpfr_uexp_t d;

  MPFR_ASSERTD(MPFR_PREC (a) == GMP_NUMB_BITS);
  MPFR_ASSERTD(MPFR_PREC (b) == GMP_NUMB_BITS);
  MPFR_ASSERTD(MPFR_PREC (c) == GMP_NUMB_BITS);

  if (bx == cx)
    {
      a0 = bp[0] + cp[0];
      rb = a0 & MPFR_LIMB_ONE;
      ap[0] = MPFR_LIMB_HIGHBIT | (a0 >> 1);
      bx ++;
      sb = 0; /* since b + c fits on p+1 bits, the sticky bit is zero */
    }
  else if (bx > cx)
    {
    BGreater1:
      d = (mpfr_uexp_t) bx - cx;
      if (d < GMP_NUMB_BITS) /* 1 <= d < GMP_NUMB_BITS */
        {
          a0 = bp[0] + (cp[0] >> d);
          sb = cp[0] << (GMP_NUMB_BITS - d); /* bits from cp[-1] after shift */
          if (a0 < bp[0]) /* carry */
            {
              ap[0] = MPFR_LIMB_HIGHBIT | (a0 >> 1);
              rb = a0 & 1;
              bx ++;
            }
          else /* no carry */
            {
              ap[0] = a0;
              rb = sb & MPFR_LIMB_HIGHBIT;
              sb &= ~MPFR_LIMB_HIGHBIT;
            }
        }
      else /* d >= GMP_NUMB_BITS */
        {
          sb = d != GMP_NUMB_BITS || cp[0] != MPFR_LIMB_HIGHBIT;
          ap[0] = bp[0];
          rb = d == GMP_NUMB_BITS;
        }
    }
  else /* bx < cx: swap b and c */
    {
      mpfr_exp_t tx;
      mp_limb_t *tp;
      tx = bx; bx = cx; cx = tx;
      tp = bp; bp = cp; cp = tp;
      goto BGreater1;
    }

  /* Note: we could keep the output significand in a0 for the rounding,
     and only store it in ap[0] at the very end, but this seems slower
     on average (but better for the worst case). */

  /* now perform rounding */
  if (MPFR_UNLIKELY(bx > __gmpfr_emax))
    return mpfr_overflow (a, rnd_mode, MPFR_SIGN(a));

  MPFR_SET_EXP (a, bx);
  if ((rb == 0 && sb == 0) || rnd_mode == MPFR_RNDF)
    MPFR_RET(0);
  else if (rnd_mode == MPFR_RNDN)
    {
      /* the condition below should be rb == 0 || (rb != 0 && ...), but this
         is equivalent to rb == 0 || (...) */
      if (rb == 0 || (sb == 0 && (ap[0] & MPFR_LIMB_ONE) == 0))
        goto truncate;
      else
        goto add_one_ulp;
    }
  else if (MPFR_IS_LIKE_RNDZ(rnd_mode, MPFR_IS_NEG(a)))
    {
    truncate:
      MPFR_RET(-MPFR_SIGN(a));
    }
  else /* round away from zero */
    {
    add_one_ulp:
      ap[0] += MPFR_LIMB_ONE;
      if (MPFR_UNLIKELY(ap[0] == 0))
        {
          ap[0] = MPFR_LIMB_HIGHBIT;
          /* no need to have MPFR_LIKELY here, since we are in a rare branch */
          if (bx + 1 <= __gmpfr_emax)
            MPFR_SET_EXP (a, bx + 1);
          else /* overflow */
            return mpfr_overflow (a, rnd_mode, MPFR_SIGN(a));
        }
      MPFR_RET(MPFR_SIGN(a));
    }
}

/* same as mpfr_add1sp, but for GMP_NUMB_BITS < p < 2*GMP_NUMB_BITS */
static int
mpfr_add1sp2 (mpfr_ptr a, mpfr_srcptr b, mpfr_srcptr c, mpfr_rnd_t rnd_mode,
              mpfr_prec_t p)
{
  mpfr_exp_t bx = MPFR_GET_EXP (b);
  mpfr_exp_t cx = MPFR_GET_EXP (c);
  mp_limb_t *ap = MPFR_MANT(a);
  mp_limb_t *bp = MPFR_MANT(b);
  mp_limb_t *cp = MPFR_MANT(c);
  mpfr_prec_t sh = 2*GMP_NUMB_BITS - p;
  mp_limb_t rb; /* round bit */
  mp_limb_t sb; /* sticky bit */
  mp_limb_t a1, a0;
  mp_limb_t mask;
  mpfr_uexp_t d;

  MPFR_ASSERTD(GMP_NUMB_BITS < p && p < 2 * GMP_NUMB_BITS);

  if (bx == cx)
    {
      /* since bp[1], cp[1] >= MPFR_LIMB_HIGHBIT, a carry always occurs */
      a0 = bp[0] + cp[0];
      a1 = bp[1] + cp[1] + (a0 < bp[0]);
      a0 = (a0 >> 1) | (a1 << (GMP_NUMB_BITS - 1));
      bx ++;
      rb = a0 & (MPFR_LIMB_ONE << (sh - 1));
      ap[1] = MPFR_LIMB_HIGHBIT | (a1 >> 1);
      ap[0] = a0 ^ rb;
      sb = 0; /* since b + c fits on p+1 bits, the sticky bit is zero */
    }
  else if (bx > cx)
    {
    BGreater2:
      d = (mpfr_uexp_t) bx - cx;
      mask = MPFR_LIMB_MASK(sh);
      if (d < GMP_NUMB_BITS) /* 0 < d < GMP_NUMB_BITS */
        {
          sb = cp[0] << (GMP_NUMB_BITS - d); /* bits from cp[-1] after shift */
          a0 = bp[0] + ((cp[1] << (GMP_NUMB_BITS - d)) | (cp[0] >> d));
          a1 = bp[1] + (cp[1] >> d) + (a0 < bp[0]);
          if (a1 < bp[1]) /* carry in high word */
            {
            exponent_shift:
              sb |= a0 & 1;
              /* shift a by 1 */
              a0 = (a1 << (GMP_NUMB_BITS - 1)) | (a0 >> 1);
              ap[1] = MPFR_LIMB_HIGHBIT | (a1 >> 1);
              bx ++;
            }
          else
            ap[1] = a1;
          rb = a0 & (MPFR_LIMB_ONE << (sh - 1));
          sb |= (a0 & mask) ^ rb;
          ap[0] = a0 & ~mask;
        }
      else if (d < 2*GMP_NUMB_BITS) /* GMP_NUMB_BITS <= d < 2*GMP_NUMB_BITS */
        {
          sb = (d == GMP_NUMB_BITS) ? cp[0]
            : cp[0] | (cp[1] << (2*GMP_NUMB_BITS-d));
          a0 = bp[0] + (cp[1] >> (d - GMP_NUMB_BITS));
          a1 = bp[1] + (a0 < bp[0]);
          if (a1 == 0)
            goto exponent_shift;
          rb = a0 & (MPFR_LIMB_ONE << (sh - 1));
          sb |= (a0 & mask) ^ rb;
          ap[0] = a0 & ~mask;
          ap[1] = a1;
        }
      else /* d >= 2*GMP_NUMB_BITS */
        {
          ap[0] = bp[0];
          ap[1] = bp[1];
          rb = 0; /* since p < 2*GMP_NUMB_BITS */
          sb = 1; /* since c <> 0 */
        }
    }
  else /* bx < cx: swap b and c */
    {
      mpfr_exp_t tx;
      mp_limb_t *tp;
      tx = bx; bx = cx; cx = tx;
      tp = bp; bp = cp; cp = tp;
      goto BGreater2;
    }

  /* now perform rounding */
  if (MPFR_UNLIKELY(bx > __gmpfr_emax))
    return mpfr_overflow (a, rnd_mode, MPFR_SIGN(a));

  MPFR_SET_EXP (a, bx);
  if ((rb == 0 && sb == 0) || rnd_mode == MPFR_RNDF)
    MPFR_RET(0);
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
      MPFR_RET(-MPFR_SIGN(a));
    }
  else /* round away from zero */
    {
    add_one_ulp:
      ap[0] += MPFR_LIMB_ONE << sh;
      ap[1] += (ap[0] == 0);
      if (MPFR_UNLIKELY(ap[1] == 0))
        {
          ap[1] = MPFR_LIMB_HIGHBIT;
          /* no need to have MPFR_LIKELY here, since we are in a rare branch */
          if (bx + 1 <= __gmpfr_emax)
            MPFR_SET_EXP (a, bx + 1);
          else /* overflow */
            return mpfr_overflow (a, rnd_mode, MPFR_SIGN(a));
        }
      MPFR_RET(MPFR_SIGN(a));
    }
}

/* same as mpfr_add1sp, but for 2*GMP_NUMB_BITS < p < 3*GMP_NUMB_BITS */
static int
mpfr_add1sp3 (mpfr_ptr a, mpfr_srcptr b, mpfr_srcptr c, mpfr_rnd_t rnd_mode,
              mpfr_prec_t p)
{
  mpfr_exp_t bx = MPFR_GET_EXP (b);
  mpfr_exp_t cx = MPFR_GET_EXP (c);
  mp_limb_t *ap = MPFR_MANT(a);
  mp_limb_t *bp = MPFR_MANT(b);
  mp_limb_t *cp = MPFR_MANT(c);
  mpfr_prec_t sh = 3*GMP_NUMB_BITS - p;
  mp_limb_t rb; /* round bit */
  mp_limb_t sb; /* sticky bit */
  mp_limb_t a2, a1, a0;
  mp_limb_t mask;
  mpfr_uexp_t d;

  MPFR_ASSERTD(2 * GMP_NUMB_BITS < p && p < 3 * GMP_NUMB_BITS);

  if (bx == cx)
    {
      /* since bp[2], cp[2] >= MPFR_LIMB_HIGHBIT, a carry always occurs */
      a0 = bp[0] + cp[0];
      a1 = bp[1] + cp[1] + (a0 < bp[0]);
      a2 = bp[2] + cp[2] + (a1 < bp[1] || (a1 == bp[1] && a0 < bp[0]));
      /* since p < 3 * GMP_NUMB_BITS, we lose no bit in a0 >> 1 */
      a0 = (a1 << (GMP_NUMB_BITS - 1)) | (a0 >> 1);
      bx ++;
      rb = a0 & (MPFR_LIMB_ONE << (sh - 1));
      ap[2] = MPFR_LIMB_HIGHBIT | (a2 >> 1);
      ap[1] = (a2 << (GMP_NUMB_BITS - 1)) | (a1 >> 1);
      ap[0] = a0 ^ rb;
      sb = 0; /* since b + c fits on p+1 bits, the sticky bit is zero */
    }
  else if (bx > cx)
    {
    BGreater2:
      d = (mpfr_uexp_t) bx - cx;
      mask = MPFR_LIMB_MASK(sh);
      if (d < GMP_NUMB_BITS) /* 0 < d < GMP_NUMB_BITS */
        {
          mp_limb_t cy;
          sb = cp[0] << (GMP_NUMB_BITS - d); /* bits from cp[-1] after shift */
          a0 = bp[0] + ((cp[1] << (GMP_NUMB_BITS - d)) | (cp[0] >> d));
          a1 = bp[1] + ((cp[2] << (GMP_NUMB_BITS - d)) | (cp[1] >> d))
            + (a0 < bp[0]);
          cy = a1 < bp[1] || (a1 == bp[1] && a0 < bp[0]); /* carry in a1 */
          a2 = bp[2] + (cp[2] >> d) + cy;
          if (a2 < bp[2] || (a2 == bp[2] && cy)) /* carry in high word */
            {
            exponent_shift:
              sb |= a0 & 1;
              /* shift a by 1 */
              a0 = (a1 << (GMP_NUMB_BITS - 1)) | (a0 >> 1);
              ap[1] = (a2 << (GMP_NUMB_BITS - 1)) | (a1 >> 1);
              ap[2] = MPFR_LIMB_HIGHBIT | (a2 >> 1);
              bx ++;
            }
          else
            {
              ap[1] = a1;
              ap[2] = a2;
            }
          rb = a0 & (MPFR_LIMB_ONE << (sh - 1));
          sb |= (a0 & mask) ^ rb;
          ap[0] = a0 & ~mask;
        }
      else if (d < 2*GMP_NUMB_BITS) /* GMP_NUMB_BITS <= d < 2*GMP_NUMB_BITS */
        {
          mp_limb_t c0shifted;
          sb = (d == GMP_NUMB_BITS) ? cp[0]
            : (cp[1] << (2*GMP_NUMB_BITS - d)) | cp[0];
          c0shifted = (d == GMP_NUMB_BITS) ? cp[1]
            : (cp[2] << (2*GMP_NUMB_BITS-d)) | (cp[1] >> (d - GMP_NUMB_BITS));
          a0 = bp[0] + c0shifted;
          a1 = bp[1] + (cp[2] >> (d - GMP_NUMB_BITS)) + (a0 < bp[0]);
          /* if a1 < bp[1], there was a carry in the above addition,
             or when a1 = bp[1] and one of the added terms is nonzero
             (the sum of cp[2] >> (d - GMP_NUMB_BITS) and a0 < bp[0]
             is at most 2^GMP_NUMB_BITS-d) */
          a2 = bp[2] + ((a1 < bp[1]) || (a1 == bp[1] && a0 < bp[0]));
          if (a2 == 0)
            goto exponent_shift;
          rb = a0 & (MPFR_LIMB_ONE << (sh - 1));
          sb |= (a0 & mask) ^ rb;
          ap[0] = a0 & ~mask;
          ap[1] = a1;
          ap[2] = a2;
        }
      else if (d < 3*GMP_NUMB_BITS) /* 2*GMP_NUMB_BITS<=d<3*GMP_NUMB_BITS */
        {
          MPFR_ASSERTD (2*GMP_NUMB_BITS <= d && d < 3*GMP_NUMB_BITS);
          sb = (d == 2*GMP_NUMB_BITS ? 0 : cp[2] << (3*GMP_NUMB_BITS - d))
            | cp[1] | cp[0];
          a0 = bp[0] + (cp[2] >> (d - 2*GMP_NUMB_BITS));
          a1 = bp[1] + (a0 < bp[0]);
          a2 = bp[2] + (a1 < bp[1]);
          if (a2 == 0)
            goto exponent_shift;
          rb = a0 & (MPFR_LIMB_ONE << (sh - 1));
          sb |= (a0 & mask) ^ rb;
          ap[0] = a0 & ~mask;
          ap[1] = a1;
          ap[2] = a2;
        }
      else /* d >= 2*GMP_NUMB_BITS */
        {
          ap[0] = bp[0];
          ap[1] = bp[1];
          ap[2] = bp[2];
          rb = 0; /* since p < 3*GMP_NUMB_BITS */
          sb = 1; /* since c <> 0 */
        }
    }
  else /* bx < cx: swap b and c */
    {
      mpfr_exp_t tx;
      mp_limb_t *tp;
      tx = bx; bx = cx; cx = tx;
      tp = bp; bp = cp; cp = tp;
      goto BGreater2;
    }

  /* now perform rounding */
  if (MPFR_UNLIKELY(bx > __gmpfr_emax))
    return mpfr_overflow (a, rnd_mode, MPFR_SIGN(a));

  MPFR_SET_EXP (a, bx);
  if ((rb == 0 && sb == 0) || rnd_mode == MPFR_RNDF)
    MPFR_RET(0);
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
      MPFR_RET(-MPFR_SIGN(a));
    }
  else /* round away from zero */
    {
    add_one_ulp:
      ap[0] += MPFR_LIMB_ONE << sh;
      ap[1] += (ap[0] == 0);
      ap[2] += (ap[1] == 0 && ap[0] == 0);
      if (MPFR_UNLIKELY(ap[2] == 0))
        {
          ap[2] = MPFR_LIMB_HIGHBIT;
          /* no need to have MPFR_LIKELY here, since we are in a rare branch */
          if (bx + 1 <= __gmpfr_emax)
            MPFR_SET_EXP (a, bx + 1);
          else /* overflow */
            return mpfr_overflow (a, rnd_mode, MPFR_SIGN(a));
        }
      MPFR_RET(MPFR_SIGN(a));
    }
}

#endif /* !defined(MPFR_GENERIC_ABI) */

/* {ap, n} <- {bp, n} + {cp + q, n - q} >> r where d = q * GMP_NUMB_BITS + r.
   Return the carry at ap[n+1] (0 or 1) and set *low so that:
   * the most significant bit of *low would be that of ap[-1] if we would
     compute one more limb of the (infinite) addition
   * the GMP_NUMB_BITS-1 least significant bits of *low are zero iff all bits
     of ap[-1], ap[-2], ... would be zero (except the most significant bit
     of ap[-1).
   Assume 0 < d < GMP_NUMB_BITS*n. */
static mp_limb_t
mpfr_addrsh (mp_limb_t *ap, mp_limb_t *bp, mp_limb_t *cp, mp_size_t n,
             mp_size_t d, mp_limb_t *low)
{
  mp_limb_t cy, cy2, c_shifted;
  mp_size_t i;

  if (d < GMP_NUMB_BITS)
    {
      /* {ap, n} <- {bp, n} + {cp, n} >> d */
      MPFR_ASSERTD (d > 0);
      /* thus 0 < GMP_NUMB_BITS - d < GMP_NUMB_BITS */
      *low = cp[0] << (GMP_NUMB_BITS - d);
      for (i = 0, cy = 0; i < n - 1; i++)
        {
          c_shifted = (cp[i+1] << (GMP_NUMB_BITS - d)) | (cp[i] >> d);
          ap[i] = bp[i] + c_shifted;
          cy2 = ap[i] < c_shifted;
          ap[i] += cy;
          cy = cy2 + (ap[i] < cy);
        }
      /* most significant limb is special */
      c_shifted = cp[i] >> d;
      ap[i] = bp[i] + c_shifted;
      cy2 = ap[i] < c_shifted;
      ap[i] += cy;
      cy = cy2 + (ap[i] < cy);
    }
  else /* d >= GMP_NUMB_BITS */
    {
      mp_size_t q = d / GMP_NUMB_BITS;
      mpfr_uexp_t r = d % GMP_NUMB_BITS;
      if (r == 0)
        {
          MPFR_ASSERTD(q > 0);
          *low = cp[q-1];
          for (i = 0; i < q-1; i++)
            *low |= !!cp[i];
          cy = mpn_add_n (ap, bp, cp + q, n - q);
          cy = mpn_add_1 (ap + n - q, bp + n - q, q, cy);
        }
      else /* 0 < r < GMP_NUMB_BITS */
        {
          *low = cp[q] << (GMP_NUMB_BITS - r);
          for (i = 0; i < q; i++)
            *low |= !!cp[i];
          for (i = 0, cy = 0; i < n - q - 1; i++)
            {
              c_shifted = (cp[q+i+1] << (GMP_NUMB_BITS - r)) | (cp[q+i] >> r);
              ap[i] = bp[i] + c_shifted;
              cy2 = ap[i] < c_shifted;
              ap[i] += cy;
              cy = cy2 + (ap[i] < cy);
            }
          /* most significant limb of c is special */
          MPFR_ASSERTD(i == n - q - 1);
          c_shifted = cp[n-1] >> r;
          ap[i] = bp[i] + c_shifted;
          cy2 = ap[i] < c_shifted;
          ap[i] += cy;
          cy = cy2 + (ap[i] < cy);
          /* upper limbs are copied */
          cy = mpn_add_1 (ap + n - q, bp + n - q, q, cy);
        }
    }
  return cy;
}

/* compute sign(b) * (|b| + |c|).
   Returns 0 iff result is exact,
   a negative value when the result is less than the exact value,
   a positive value otherwise. */
MPFR_HOT_FUNCTION_ATTR int
mpfr_add1sp (mpfr_ptr a, mpfr_srcptr b, mpfr_srcptr c, mpfr_rnd_t rnd_mode)
{
  mpfr_uexp_t d;
  mpfr_prec_t p;
  unsigned int sh;
  mp_size_t n;
  mp_limb_t *ap = MPFR_MANT(a);
  mpfr_exp_t bx;
  mp_limb_t limb, rb, sb;
  int inexact;
  int neg;

  MPFR_ASSERTD(MPFR_PREC(a) == MPFR_PREC(b) && MPFR_PREC(b) == MPFR_PREC(c));
  MPFR_ASSERTD(MPFR_IS_PURE_FP(b));
  MPFR_ASSERTD(MPFR_IS_PURE_FP(c));

  MPFR_SET_SAME_SIGN (a, b);

  /* Read prec and num of limbs */
  p = MPFR_GET_PREC (b);

#if !defined(MPFR_GENERIC_ABI)
  if (p < GMP_NUMB_BITS)
    return mpfr_add1sp1 (a, b, c, rnd_mode, p);

  if (GMP_NUMB_BITS < p && p < 2 * GMP_NUMB_BITS)
    return mpfr_add1sp2 (a, b, c, rnd_mode, p);

  /* we put this test after the mpfr_add1sp2() call, to avoid slowing down
     the more frequent case GMP_NUMB_BITS < p < 2 * GMP_NUMB_BITS */
  if (p == GMP_NUMB_BITS)
    return mpfr_add1sp1n (a, b, c, rnd_mode);

  if (2 * GMP_NUMB_BITS < p && p < 3 * GMP_NUMB_BITS)
    return mpfr_add1sp3 (a, b, c, rnd_mode, p);
#endif

  /* We need to get the sign before the possible exchange. */
  neg = MPFR_IS_NEG (b);

  bx = MPFR_GET_EXP(b);
  if (bx < MPFR_GET_EXP(c))
    {
      mpfr_srcptr t = b;
      bx = MPFR_GET_EXP(c);
      b = c;
      c = t;
    }
  MPFR_ASSERTD(bx >= MPFR_GET_EXP(c));

  n = MPFR_PREC2LIMBS (p);
  MPFR_UNSIGNED_MINUS_MODULO(sh, p);
  d = (mpfr_uexp_t) (bx - MPFR_GET_EXP(c));

  /* printf ("New add1sp with diff=%lu\n", (unsigned long) d); */

  if (d == 0)
    {
      /* d==0 */
      /* mpfr_print_mant_binary("C= ", MPFR_MANT(c), p); */
      /* mpfr_print_mant_binary("B= ", MPFR_MANT(b), p); */
      bx++;                                /* exp + 1 */
      limb = mpn_add_n (ap, MPFR_MANT(b), MPFR_MANT(c), n);
      /* mpfr_print_mant_binary("A= ", ap, p); */
      MPFR_ASSERTD(limb != 0);             /* There must be a carry */
      rb = ap[0] & (MPFR_LIMB_ONE << sh);  /* Get round bit (sb=0) */
      mpn_rshift (ap, ap, n, 1);           /* Shift mantissa A */
      ap[n-1] |= MPFR_LIMB_HIGHBIT;        /* Set MSB */
      ap[0]   &= ~MPFR_LIMB_MASK(sh);      /* Clear round bit */


      /* Fast track for faithful rounding: since b and c have the same
         precision and the same exponent, the neglected value is either
         0 or 1/2 ulp(a), thus returning a is fine. */
      if (rnd_mode == MPFR_RNDF)
        { inexact = 0; goto set_exponent; }

      if (rb == 0) /* Check exact case */
        { inexact = 0; goto set_exponent; }

      /* Zero: Truncate
         Nearest: Even Rule => truncate or add 1
         Away: Add 1 */
      if (MPFR_LIKELY (rnd_mode == MPFR_RNDN))
        {
          if ((ap[0] & (MPFR_LIMB_ONE << sh)) == 0)
            { inexact = -1; goto set_exponent; }
          else
            goto add_one_ulp;
        }
      MPFR_UPDATE_RND_MODE(rnd_mode, neg);
      if (rnd_mode == MPFR_RNDZ)
        { inexact = -1; goto set_exponent; }
      else
        goto add_one_ulp;
    }
  else if (MPFR_UNLIKELY (d >= p))
    {
      /* fast track for RNDF */
      if (MPFR_LIKELY(rnd_mode == MPFR_RNDF))
        goto copy_set_exponent;

      if (MPFR_LIKELY (d > p))
        {
          /* d > p : Copy B in A */
          /* Away:    Add 1
             Nearest: Trunc
             Zero:    Trunc */
          if (rnd_mode == MPFR_RNDN || MPFR_IS_LIKE_RNDZ (rnd_mode, neg))
            {
            copy_set_exponent:
              if (a != b)
                MPN_COPY (ap, MPFR_MANT(b), n);
              inexact = -1;
              goto set_exponent;
            }
          else
            {
            copy_add_one_ulp:
              if (a != b)
                MPN_COPY (ap, MPFR_MANT(b), n);
              goto add_one_ulp;
            }
        }
      else
        {
          /* d==p : Copy B in A */
          /* Away:     Add 1
             Nearest:  Even Rule if C is a power of 2, else Add 1
             Zero:     Trunc */
          if (rnd_mode == MPFR_RNDN)
            {
              /* Check if C was a power of 2 */
              if (mpfr_powerof2_raw (c) &&
                  ((MPFR_MANT (b))[0] & (MPFR_LIMB_ONE << sh)) == 0)
                goto copy_set_exponent;
              /* Not a Power of 2 */
              goto copy_add_one_ulp;
            }
          else if (MPFR_IS_LIKE_RNDZ (rnd_mode, neg))
            goto copy_set_exponent;
          else
            goto copy_add_one_ulp;
        }
    }
  else /* 0 < d < p */
    {
      mp_limb_t mask = ~MPFR_LIMB_MASK(sh);

      /* General case: 1 <= d < p */

      limb = mpfr_addrsh (ap, MPFR_MANT(b), MPFR_MANT(c), n, d, &sb);
      /* the most significant bit of sb contains what would be the most
         significant bit of ap[-1], and the remaining bits of sb are 0
         iff the remaining bits of ap[-1], ap[-2], ... are all zero */

      if (sh > 0)
        {
          /* The round bit and a part of the sticky bit are in ap[0]. */
          rb = (ap[0] & (MPFR_LIMB_ONE << (sh - 1)));
          sb |= ap[0] & MPFR_LIMB_MASK (sh - 1);
        }
      else
        {
          /* The round bit and possibly a part of the sticky bit are
             in sb. */
          rb = sb & MPFR_LIMB_HIGHBIT;
          sb &= ~MPFR_LIMB_HIGHBIT;
        }

      ap[0] &= mask;

      /* Check for carry out */
      if (MPFR_UNLIKELY (limb != 0))
        {
          limb = ap[0] & (MPFR_LIMB_ONE << sh); /* Get LSB (will be new rb) */
          mpn_rshift (ap, ap, n, 1);            /* Shift significand */
          bx++;                                 /* Increase exponent */
          ap[n-1] |= MPFR_LIMB_HIGHBIT;         /* Set MSB */
          ap[0]   &= mask;                      /* Clear LSB */
          sb      |= rb;                        /* Update sb */
          rb      = limb;                       /* New rb */
          /* printf ("(Overflow) rb=%lu sb=%lu\n",
             (unsigned long) rb, (unsigned long) sb);
             mpfr_print_mant_binary ("Add=  ", ap, p); */
        }

      /* Round:
          Zero: Truncate but could be exact.
          Away: Add 1 if rb or sb !=0
          Nearest: Truncate but could be exact if sb==0
                   Add 1 if rb !=0,
                   Even rule else */
      if (MPFR_LIKELY(rnd_mode == MPFR_RNDF))
        { inexact = 0; goto set_exponent; }
      else if (rnd_mode == MPFR_RNDN)
        {
          inexact = - (sb != 0);
          if (rb == 0)
            goto set_exponent;
          else if (MPFR_UNLIKELY (sb == 0) &&
                   (ap[0] & (MPFR_LIMB_ONE << sh)) == 0)
            { inexact = -1; goto set_exponent; }
          else
            goto add_one_ulp;
        }
      MPFR_UPDATE_RND_MODE(rnd_mode, neg);
      inexact = - (rb != 0 || sb != 0);
      if (rnd_mode == MPFR_RNDZ || inexact == 0)
        goto set_exponent;
      else
        goto add_one_ulp;
    }
  MPFR_RET_NEVER_GO_HERE();

 add_one_ulp:
  /* add one unit in last place to a */
  /* printf("AddOneUlp\n"); */
  if (MPFR_UNLIKELY (mpn_add_1 (ap, ap, n, MPFR_LIMB_ONE << sh)))
    {
      /* Case 100000x0 = 0x1111x1 + 1*/
      /* printf("Pow of 2\n"); */
      bx++;
      ap[n-1] = MPFR_LIMB_HIGHBIT;
    }
  inexact = 1;

 set_exponent:
  if (MPFR_UNLIKELY(bx > __gmpfr_emax)) /* Check for overflow */
    {
      /* printf("Overflow\n"); */
      return mpfr_overflow (a, rnd_mode, MPFR_SIGN(a));
    }
  MPFR_SET_EXP (a, bx);

  MPFR_RET (inexact * MPFR_INT_SIGN (a));
}
