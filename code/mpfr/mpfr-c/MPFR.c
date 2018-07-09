#include "MPFR.h"

static MPFR_Add1sp1_state
MPFR_Add1sp1_mk_state(int32_t s, int32_t ax, uint64_t am, uint64_t rb, uint64_t sb)
{
  return ((MPFR_Add1sp1_state ){ .sign = s, .ax = ax, .am = am, .rb = rb, .sb = sb });
}

static MPFR_Add1sp1_state MPFR_Add1sp1_mpfr_overflow(MPFR_Lib_mpfr_rnd_t rnd, int32_t sign)
{
  return MPFR_Add1sp1_mk_state(sign, (int32_t )0, (uint64_t )0, (uint64_t )0, (uint64_t )0);
}

static MPFR_Add1sp1_state
MPFR_Add1sp1_mpfr_add1sp1_gt(
  int32_t bx,
  uint64_t bm,
  int32_t cx,
  uint64_t cm,
  MPFR_Lib_mpfr_rnd_t rnd_mode,
  uint32_t p
)
{
  if ((uint32_t )(bx - cx) < MPFR_Lib_gmp_NUMB_BITS - p)
  {
    bool scrut0 = bm + (cm >> (uint32_t )(bx - cx)) < bm;
    K___uint64_t_int32_t scrut;
    if (scrut0 == true)
      scrut =
        (
          (K___uint64_t_int32_t ){
            .fst = MPFR_Lib_mpfr_LIMB_HIGHBIT | bm + (cm >> (uint32_t )(bx - cx)) >> (uint32_t )1,
            .snd = bx + (int32_t )1
          }
        );
    else
      scrut = ((K___uint64_t_int32_t ){ .fst = bm + (cm >> (uint32_t )(bx - cx)), .snd = bx });
    uint64_t am = scrut.fst;
    int32_t bx1 = scrut.snd;
    return
      MPFR_Add1sp1_mk_state((int32_t )0,
        bx1,
        am & ~MPFR_Lib_mpfr_LIMB_MASK(MPFR_Lib_gmp_NUMB_BITS - p),
        am & MPFR_Lib_mpfr_LIMB_ONE << MPFR_Lib_gmp_NUMB_BITS - p - (uint32_t )1,
        am
        & MPFR_Lib_mpfr_LIMB_MASK(MPFR_Lib_gmp_NUMB_BITS - p)
        ^ am & MPFR_Lib_mpfr_LIMB_ONE << MPFR_Lib_gmp_NUMB_BITS - p - (uint32_t )1);
  }
  else if ((uint32_t )(bx - cx) < MPFR_Lib_gmp_NUMB_BITS)
  {
    MPFR_Add1sp1_state ite0;
    if (bm + (cm >> (uint32_t )(bx - cx)) < bm)
      ite0 =
        MPFR_Add1sp1_mk_state((int32_t )0,
          bx + (int32_t )1,
          MPFR_Lib_mpfr_LIMB_HIGHBIT | bm + (cm >> (uint32_t )(bx - cx)) >> (uint32_t )1,
          (uint64_t )0,
          cm
          << MPFR_Lib_gmp_NUMB_BITS - (uint32_t )(bx - cx)
          | bm + (cm >> (uint32_t )(bx - cx)) & (uint64_t )1);
    else
      ite0 =
        MPFR_Add1sp1_mk_state((int32_t )0,
          bx,
          bm + (cm >> (uint32_t )(bx - cx)),
          (uint64_t )0,
          cm << MPFR_Lib_gmp_NUMB_BITS - (uint32_t )(bx - cx));
    MPFR_Add1sp1_state ite1;
    if (bm + (cm >> (uint32_t )(bx - cx)) < bm)
      ite1 =
        MPFR_Add1sp1_mk_state((int32_t )0,
          bx + (int32_t )1,
          MPFR_Lib_mpfr_LIMB_HIGHBIT | bm + (cm >> (uint32_t )(bx - cx)) >> (uint32_t )1,
          (uint64_t )0,
          cm
          << MPFR_Lib_gmp_NUMB_BITS - (uint32_t )(bx - cx)
          | bm + (cm >> (uint32_t )(bx - cx)) & (uint64_t )1);
    else
      ite1 =
        MPFR_Add1sp1_mk_state((int32_t )0,
          bx,
          bm + (cm >> (uint32_t )(bx - cx)),
          (uint64_t )0,
          cm << MPFR_Lib_gmp_NUMB_BITS - (uint32_t )(bx - cx));
    MPFR_Add1sp1_state ite2;
    if (bm + (cm >> (uint32_t )(bx - cx)) < bm)
      ite2 =
        MPFR_Add1sp1_mk_state((int32_t )0,
          bx + (int32_t )1,
          MPFR_Lib_mpfr_LIMB_HIGHBIT | bm + (cm >> (uint32_t )(bx - cx)) >> (uint32_t )1,
          (uint64_t )0,
          cm
          << MPFR_Lib_gmp_NUMB_BITS - (uint32_t )(bx - cx)
          | bm + (cm >> (uint32_t )(bx - cx)) & (uint64_t )1);
    else
      ite2 =
        MPFR_Add1sp1_mk_state((int32_t )0,
          bx,
          bm + (cm >> (uint32_t )(bx - cx)),
          (uint64_t )0,
          cm << MPFR_Lib_gmp_NUMB_BITS - (uint32_t )(bx - cx));
    MPFR_Add1sp1_state ite3;
    if (bm + (cm >> (uint32_t )(bx - cx)) < bm)
      ite3 =
        MPFR_Add1sp1_mk_state((int32_t )0,
          bx + (int32_t )1,
          MPFR_Lib_mpfr_LIMB_HIGHBIT | bm + (cm >> (uint32_t )(bx - cx)) >> (uint32_t )1,
          (uint64_t )0,
          cm
          << MPFR_Lib_gmp_NUMB_BITS - (uint32_t )(bx - cx)
          | bm + (cm >> (uint32_t )(bx - cx)) & (uint64_t )1);
    else
      ite3 =
        MPFR_Add1sp1_mk_state((int32_t )0,
          bx,
          bm + (cm >> (uint32_t )(bx - cx)),
          (uint64_t )0,
          cm << MPFR_Lib_gmp_NUMB_BITS - (uint32_t )(bx - cx));
    MPFR_Add1sp1_state ite4;
    if (bm + (cm >> (uint32_t )(bx - cx)) < bm)
      ite4 =
        MPFR_Add1sp1_mk_state((int32_t )0,
          bx + (int32_t )1,
          MPFR_Lib_mpfr_LIMB_HIGHBIT | bm + (cm >> (uint32_t )(bx - cx)) >> (uint32_t )1,
          (uint64_t )0,
          cm
          << MPFR_Lib_gmp_NUMB_BITS - (uint32_t )(bx - cx)
          | bm + (cm >> (uint32_t )(bx - cx)) & (uint64_t )1);
    else
      ite4 =
        MPFR_Add1sp1_mk_state((int32_t )0,
          bx,
          bm + (cm >> (uint32_t )(bx - cx)),
          (uint64_t )0,
          cm << MPFR_Lib_gmp_NUMB_BITS - (uint32_t )(bx - cx));
    MPFR_Add1sp1_state ite;
    if (bm + (cm >> (uint32_t )(bx - cx)) < bm)
      ite =
        MPFR_Add1sp1_mk_state((int32_t )0,
          bx + (int32_t )1,
          MPFR_Lib_mpfr_LIMB_HIGHBIT | bm + (cm >> (uint32_t )(bx - cx)) >> (uint32_t )1,
          (uint64_t )0,
          cm
          << MPFR_Lib_gmp_NUMB_BITS - (uint32_t )(bx - cx)
          | bm + (cm >> (uint32_t )(bx - cx)) & (uint64_t )1);
    else
      ite =
        MPFR_Add1sp1_mk_state((int32_t )0,
          bx,
          bm + (cm >> (uint32_t )(bx - cx)),
          (uint64_t )0,
          cm << MPFR_Lib_gmp_NUMB_BITS - (uint32_t )(bx - cx));
    return
      MPFR_Add1sp1_mk_state((int32_t )0,
        ite0.ax,
        ite1.am & ~MPFR_Lib_mpfr_LIMB_MASK(MPFR_Lib_gmp_NUMB_BITS - p),
        ite2.am & MPFR_Lib_mpfr_LIMB_ONE << MPFR_Lib_gmp_NUMB_BITS - p - (uint32_t )1,
        ite3.sb
        |
          ite4.am
          & MPFR_Lib_mpfr_LIMB_MASK(MPFR_Lib_gmp_NUMB_BITS - p)
          ^ ite.am & MPFR_Lib_mpfr_LIMB_ONE << MPFR_Lib_gmp_NUMB_BITS - p - (uint32_t )1);
  }
  else
    return MPFR_Add1sp1_mk_state((int32_t )0, bx, bm, (uint64_t )0, (uint64_t )1);
}

static MPFR_Add1sp1_state
MPFR_Add1sp1_mpfr_add1sp1_any(
  int32_t bx,
  uint64_t bm,
  int32_t cx,
  uint64_t cm,
  MPFR_Lib_mpfr_rnd_t rnd_mode,
  uint32_t p
)
{
  if (bx == cx)
    return
      MPFR_Add1sp1_mk_state((int32_t )0,
        bx + (int32_t )1,
        (bm >> (uint32_t )1)
        + (cm >> (uint32_t )1)
        ^
          (bm >> (uint32_t )1)
          + (cm >> (uint32_t )1)
          & MPFR_Lib_mpfr_LIMB_ONE << MPFR_Lib_gmp_NUMB_BITS - p - (uint32_t )1,
        (bm >> (uint32_t )1)
        + (cm >> (uint32_t )1)
        & MPFR_Lib_mpfr_LIMB_ONE << MPFR_Lib_gmp_NUMB_BITS - p - (uint32_t )1,
        (uint64_t )0);
  else if (bx > cx)
    return MPFR_Add1sp1_mpfr_add1sp1_gt(bx, bm, cx, cm, rnd_mode, p);
  else
    return MPFR_Add1sp1_mpfr_add1sp1_gt(cx, cm, bx, bm, rnd_mode, p);
}

static MPFR_Add1sp1_state
MPFR_Add1sp1_add_one_ulp(
  int32_t sign,
  int32_t ax,
  uint64_t am,
  MPFR_Lib_mpfr_rnd_t rnd_mode,
  uint32_t sh
)
{
  if (am + (MPFR_Lib_mpfr_LIMB_ONE << sh) == (uint64_t )0)
    if (ax + (int32_t )1 > MPFR_Lib_gmpfr_emax)
      return MPFR_Add1sp1_mpfr_overflow(rnd_mode, sign);
    else
      return
        MPFR_Add1sp1_mk_state(sign,
          ax + (int32_t )1,
          MPFR_Lib_mpfr_LIMB_HIGHBIT,
          (uint64_t )0,
          (uint64_t )0);
  else
    return
      MPFR_Add1sp1_mk_state(sign,
        ax,
        am + (MPFR_Lib_mpfr_LIMB_ONE << sh),
        (uint64_t )0,
        (uint64_t )0);
}

static MPFR_Add1sp1_state
MPFR_Add1sp1_mpfr_add1sp1_(
  int32_t bx,
  uint64_t bm,
  int32_t cx,
  uint64_t cm,
  MPFR_Lib_mpfr_rnd_t rnd_mode,
  uint32_t p,
  int32_t sign
)
{
  if (MPFR_Add1sp1_mpfr_add1sp1_any(bx, bm, cx, cm, rnd_mode, p).ax > MPFR_Lib_gmpfr_emax)
    return MPFR_Add1sp1_mpfr_overflow(rnd_mode, sign);
  else if
  (MPFR_Add1sp1_mpfr_add1sp1_any(bx,
    bm,
    cx,
    cm,
    rnd_mode,
    p).rb
  == (uint64_t )0
  && MPFR_Add1sp1_mpfr_add1sp1_any(bx, bm, cx, cm, rnd_mode, p).sb == (uint64_t )0
  || MPFR_Lib_uu___is_MPFR_RNDF(rnd_mode))
    return
      MPFR_Add1sp1_mk_state(sign,
        MPFR_Add1sp1_mpfr_add1sp1_any(bx, bm, cx, cm, rnd_mode, p).ax,
        MPFR_Add1sp1_mpfr_add1sp1_any(bx, bm, cx, cm, rnd_mode, p).am,
        (uint64_t )0,
        (uint64_t )0);
  else if (MPFR_Lib_uu___is_MPFR_RNDN(rnd_mode))
    if
    (MPFR_Add1sp1_mpfr_add1sp1_any(bx,
      bm,
      cx,
      cm,
      rnd_mode,
      p).rb
    == (uint64_t )0
    ||
      MPFR_Add1sp1_mpfr_add1sp1_any(bx,
        bm,
        cx,
        cm,
        rnd_mode,
        p).sb
      == (uint64_t )0
      &&
        (MPFR_Add1sp1_mpfr_add1sp1_any(bx,
          bm,
          cx,
          cm,
          rnd_mode,
          p).am
        & MPFR_Lib_mpfr_LIMB_ONE << MPFR_Lib_gmp_NUMB_BITS - p)
        == (uint64_t )0)
      return
        MPFR_Add1sp1_mk_state((int32_t )0 - sign,
          MPFR_Add1sp1_mpfr_add1sp1_any(bx, bm, cx, cm, rnd_mode, p).ax,
          MPFR_Add1sp1_mpfr_add1sp1_any(bx, bm, cx, cm, rnd_mode, p).am,
          (uint64_t )0,
          (uint64_t )0);
    else
      return
        MPFR_Add1sp1_add_one_ulp(sign,
          MPFR_Add1sp1_mpfr_add1sp1_any(bx, bm, cx, cm, rnd_mode, p).ax,
          MPFR_Add1sp1_mpfr_add1sp1_any(bx, bm, cx, cm, rnd_mode, p).am,
          rnd_mode,
          MPFR_Lib_gmp_NUMB_BITS - p);
  else if (MPFR_Lib_mpfr_IS_LIKE_RNDZ(rnd_mode, sign))
    return
      MPFR_Add1sp1_mk_state((int32_t )0 - sign,
        MPFR_Add1sp1_mpfr_add1sp1_any(bx, bm, cx, cm, rnd_mode, p).ax,
        MPFR_Add1sp1_mpfr_add1sp1_any(bx, bm, cx, cm, rnd_mode, p).am,
        (uint64_t )0,
        (uint64_t )0);
  else
    return
      MPFR_Add1sp1_add_one_ulp(sign,
        MPFR_Add1sp1_mpfr_add1sp1_any(bx, bm, cx, cm, rnd_mode, p).ax,
        MPFR_Add1sp1_mpfr_add1sp1_any(bx, bm, cx, cm, rnd_mode, p).am,
        rnd_mode,
        MPFR_Lib_gmp_NUMB_BITS - p);
}

static int32_t
MPFR_Add1sp1_mpfr_add1sp1(
  MPFR_Lib_mpfr_struct *a,
  MPFR_Lib_mpfr_struct *b,
  MPFR_Lib_mpfr_struct *c,
  MPFR_Lib_mpfr_rnd_t rnd_mode,
  uint32_t p
)
{
  int32_t sign = MPFR_Lib_mpfr_SIGN(a);
  int32_t bx = MPFR_Lib_mpfr_GET_EXP(b);
  uint64_t *bm = MPFR_Lib_mpfr_MANT(b);
  int32_t cx = MPFR_Lib_mpfr_GET_EXP(c);
  uint64_t *cm = MPFR_Lib_mpfr_MANT(c);
  uint64_t b0 = bm[0];
  uint64_t c0 = cm[0];
  MPFR_Add1sp1_state st = MPFR_Add1sp1_mpfr_add1sp1_(bx, b0, cx, c0, rnd_mode, p, sign);
  uint64_t a0 = st.am;
  int32_t as_583 = st.sign;
  int32_t ax = st.ax;
  uint64_t *am = MPFR_Lib_mpfr_MANT(a);
  am[0] = a0;
  MPFR_Lib_mpfr_struct ap = MPFR_Lib_mk_mpfr_struct(p, as_583, ax, am);
  a[0] = ap;
  return as_583;
}

int32_t
MPFR_mpfr_add1sp1(
  MPFR_Lib_mpfr_struct *x0,
  MPFR_Lib_mpfr_struct *x1,
  MPFR_Lib_mpfr_struct *x2,
  MPFR_Lib_mpfr_rnd_t x3,
  uint32_t x4
)
{
  return MPFR_Add1sp1_mpfr_add1sp1(x0, x1, x2, x3, x4);
}

