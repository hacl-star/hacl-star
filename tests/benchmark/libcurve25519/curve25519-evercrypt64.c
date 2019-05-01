#include "libcurve25519_inline.h"

#include "curve25519-vale-inline.h"
enum { CURVE25519_POINT_SIZE = 32 };

#define KRML_CHECK_SIZE(a,b) {}
static inline u64 load64_le(const u8* b){
  uint64_t x;
  memcpy(&x, b, 8);
  return x;
}
static inline void store64_le(u8* b,u64 o) {
  memcpy(b,&o,8);
}

inline static uint64_t FStar_UInt64_eq_mask(uint64_t a, uint64_t b)
{
  uint64_t x = a ^ b;
  uint64_t minus_x = ~x + (uint64_t)1U;
  uint64_t x_or_minus_x = x | minus_x;
  uint64_t xnx = x_or_minus_x >> (uint32_t)63U;
  return xnx - (uint64_t)1U;
}

inline static uint64_t FStar_UInt64_gte_mask(uint64_t a, uint64_t b)
{
  uint64_t x = a;
  uint64_t y = b;
  uint64_t x_xor_y = x ^ y;
  uint64_t x_sub_y = x - y;
  uint64_t x_sub_y_xor_y = x_sub_y ^ y;
  uint64_t q = x_xor_y | x_sub_y_xor_y;
  uint64_t x_xor_q = x ^ q;
  uint64_t x_xor_q_ = x_xor_q >> (uint32_t)63U;
  return x_xor_q_ - (uint64_t)1U;
}

inline static void
Hacl_Impl_Curve25519_AddAndDouble_point_add_and_double_64(
  uint64_t *q,
  uint64_t *p01_tmp1,
  uint64_t *tmp2
)
{
  uint64_t *nq = p01_tmp1;
  uint64_t *nq_p1 = p01_tmp1 + (uint32_t)8U;
  uint64_t *tmp1 = p01_tmp1 + (uint32_t)16U;
  uint64_t *x1 = q;
  uint64_t *x2 = nq;
  uint64_t *z2 = nq + (uint32_t)4U;
  uint64_t *z3 = nq_p1 + (uint32_t)4U;
  uint64_t *a = tmp1;
  uint64_t *b = tmp1 + (uint32_t)4U;
  uint64_t *ab = tmp1;
  uint64_t *dc = tmp1 + (uint32_t)8U;
  uint64_t *x3;
  uint64_t *z31;
  uint64_t *d0;
  uint64_t *c0;
  uint64_t *a1;
  uint64_t *b1;
  uint64_t *d;
  uint64_t *c;
  uint64_t *ab1;
  uint64_t *dc1;
  fadd(a, x2, z2);
  fsub(b, x2, z2);
  x3 = nq_p1;
  z31 = nq_p1 + (uint32_t)4U;
  d0 = dc;
  c0 = dc + (uint32_t)4U;
  fadd(c0, x3, z31);
  fsub(d0, x3, z31);
  fmul2(dc, dc, ab, tmp2);
  fadd(x3, d0, c0);
  fsub(z31, d0, c0);
  a1 = tmp1;
  b1 = tmp1 + (uint32_t)4U;
  d = tmp1 + (uint32_t)8U;
  c = tmp1 + (uint32_t)12U;
  ab1 = tmp1;
  dc1 = tmp1 + (uint32_t)8U;
  fsqr2(dc1, ab1, tmp2);
  fsqr2(nq_p1, nq_p1, tmp2);
  a1[0U] = c[0U];
  a1[1U] = c[1U];
  a1[2U] = c[2U];
  a1[3U] = c[3U];
  fsub(c, d, c);
  fmul1(b1, c, (uint64_t)121665U);
  fadd(b1, b1, d);
  fmul2(nq, dc1, ab1, tmp2);
  fmul(z3, z3, x1, tmp2);
}

inline static void
Hacl_Impl_Curve25519_AddAndDouble_point_double_64(uint64_t *nq, uint64_t *tmp1, uint64_t *tmp2)
{
  uint64_t *x2 = nq;
  uint64_t *z2 = nq + (uint32_t)4U;
  uint64_t *a = tmp1;
  uint64_t *b = tmp1 + (uint32_t)4U;
  uint64_t *d = tmp1 + (uint32_t)8U;
  uint64_t *c = tmp1 + (uint32_t)12U;
  uint64_t *ab = tmp1;
  uint64_t *dc = tmp1 + (uint32_t)8U;
  fadd(a, x2, z2);
  fsub(b, x2, z2);
  fsqr2(dc, ab, tmp2);
  a[0U] = c[0U];
  a[1U] = c[1U];
  a[2U] = c[2U];
  a[3U] = c[3U];
  fsub(c, d, c);
  fmul1(b, c, (uint64_t)121665U);
  fadd(b, b, d);
  fmul2(nq, dc, ab, tmp2);
}

inline static void
Hacl_Impl_Curve25519_Finv_fsquare_times_64(
  uint64_t *o,
  uint64_t *i,
  uint64_t *tmp,
  uint32_t n1
)
{
  uint32_t i0;
  fsqr(o, i, tmp);
  for (i0 = (uint32_t)0U; i0 < n1 - (uint32_t)1U; i0 = i0 + (uint32_t)1U)
  {
    fsqr(o, o, tmp);
  }
}

inline static void Hacl_Impl_Curve25519_Finv_finv_64(uint64_t *o, uint64_t *i, uint64_t *tmp)
{
  uint64_t t1[16U] = { 0U };
  uint64_t *a0 = t1;
  uint64_t *b = t1 + (uint32_t)4U;
  uint64_t *c = t1 + (uint32_t)8U;
  uint64_t *t00 = t1 + (uint32_t)12U;
  uint64_t *tmp1 = tmp;
  uint64_t *a;
  uint64_t *t0;
  Hacl_Impl_Curve25519_Finv_fsquare_times_64(a0, i, tmp1, (uint32_t)1U);
  Hacl_Impl_Curve25519_Finv_fsquare_times_64(t00, a0, tmp1, (uint32_t)2U);
  fmul(b, t00, i, tmp);
  fmul(a0, b, a0, tmp);
  Hacl_Impl_Curve25519_Finv_fsquare_times_64(t00, a0, tmp1, (uint32_t)1U);
  fmul(b, t00, b, tmp);
  Hacl_Impl_Curve25519_Finv_fsquare_times_64(t00, b, tmp1, (uint32_t)5U);
  fmul(b, t00, b, tmp);
  Hacl_Impl_Curve25519_Finv_fsquare_times_64(t00, b, tmp1, (uint32_t)10U);
  fmul(c, t00, b, tmp);
  Hacl_Impl_Curve25519_Finv_fsquare_times_64(t00, c, tmp1, (uint32_t)20U);
  fmul(t00, t00, c, tmp);
  Hacl_Impl_Curve25519_Finv_fsquare_times_64(t00, t00, tmp1, (uint32_t)10U);
  fmul(b, t00, b, tmp);
  Hacl_Impl_Curve25519_Finv_fsquare_times_64(t00, b, tmp1, (uint32_t)50U);
  fmul(c, t00, b, tmp);
  Hacl_Impl_Curve25519_Finv_fsquare_times_64(t00, c, tmp1, (uint32_t)100U);
  fmul(t00, t00, c, tmp);
  Hacl_Impl_Curve25519_Finv_fsquare_times_64(t00, t00, tmp1, (uint32_t)50U);
  fmul(t00, t00, b, tmp);
  Hacl_Impl_Curve25519_Finv_fsquare_times_64(t00, t00, tmp1, (uint32_t)5U);
  a = t1;
  t0 = t1 + (uint32_t)12U;
  fmul(o, t0, a, tmp);
}

inline static void
Hacl_Impl_Curve25519_Generic_montgomery_ladder_64(uint64_t *out, uint8_t *key, uint64_t *init1)
{
  uint64_t tmp2[16U] = { 0U };
  uint64_t p01_tmp1_swap[33U] = { 0U };
  uint64_t *p0 = p01_tmp1_swap;
  uint64_t *p01 = p01_tmp1_swap;
  uint64_t *p03 = p01;
  uint64_t *p11 = p01 + (uint32_t)8U;
  uint64_t *x0;
  uint64_t *z0;
  uint64_t *p01_tmp1;
  uint64_t *p01_tmp11;
  uint64_t *nq10;
  uint64_t *nq_p11;
  uint64_t *swap1;
  uint64_t sw0;
  uint64_t *nq1;
  uint64_t *tmp1;
  memcpy(p11, init1, (uint32_t)8U * sizeof init1[0U]);
  x0 = p03;
  z0 = p03 + (uint32_t)4U;
  x0[0U] = (uint64_t)1U;
  x0[1U] = (uint64_t)0U;
  x0[2U] = (uint64_t)0U;
  x0[3U] = (uint64_t)0U;
  z0[0U] = (uint64_t)0U;
  z0[1U] = (uint64_t)0U;
  z0[2U] = (uint64_t)0U;
  z0[3U] = (uint64_t)0U;
  p01_tmp1 = p01_tmp1_swap;
  p01_tmp11 = p01_tmp1_swap;
  nq10 = p01_tmp1_swap;
  nq_p11 = p01_tmp1_swap + (uint32_t)8U;
  swap1 = p01_tmp1_swap + (uint32_t)32U;
  cswap2((uint64_t)1U, nq10, nq_p11);
  Hacl_Impl_Curve25519_AddAndDouble_point_add_and_double_64(init1, p01_tmp11, tmp2);
  swap1[0U] = (uint64_t)1U;
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < (uint32_t)251U; i = i + (uint32_t)1U)
    {
      uint64_t *p01_tmp12 = p01_tmp1_swap;
      uint64_t *swap2 = p01_tmp1_swap + (uint32_t)32U;
      uint64_t *nq2 = p01_tmp12;
      uint64_t *nq_p12 = p01_tmp12 + (uint32_t)8U;
      uint64_t
      bit =
        (uint64_t)(key[((uint32_t)253U - i)
        / (uint32_t)8U]
        >> ((uint32_t)253U - i) % (uint32_t)8U
        & (uint8_t)1U);
      uint64_t sw = swap2[0U] ^ bit;
      cswap2(sw, nq2, nq_p12);
      Hacl_Impl_Curve25519_AddAndDouble_point_add_and_double_64(init1, p01_tmp12, tmp2);
      swap2[0U] = bit;
    }
  }
  sw0 = swap1[0U];
  cswap2(sw0, nq10, nq_p11);
  nq1 = p01_tmp1;
  tmp1 = p01_tmp1 + (uint32_t)16U;
  Hacl_Impl_Curve25519_AddAndDouble_point_double_64(nq1, tmp1, tmp2);
  Hacl_Impl_Curve25519_AddAndDouble_point_double_64(nq1, tmp1, tmp2);
  Hacl_Impl_Curve25519_AddAndDouble_point_double_64(nq1, tmp1, tmp2);
  memcpy(out, p0, (uint32_t)8U * sizeof p0[0U]);
}

static uint8_t
Hacl_Impl_Curve25519_Generic_g25519[32U] =
  {
    (uint8_t)9U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U
  };

static void Hacl_Curve25519_64_secret_to_public(uint8_t *pub, uint8_t *priv)
{
  uint8_t basepoint[32U] = { 0U };
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < (uint32_t)32U; i = i + (uint32_t)1U)
    {
      uint8_t *os = basepoint;
      uint8_t x = Hacl_Impl_Curve25519_Generic_g25519[i];
      os[i] = x;
    }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * (uint32_t)4U);
  {
    uint64_t init1[(uint32_t)2U * (uint32_t)4U];
    memset(init1, 0U, (uint32_t)2U * (uint32_t)4U * sizeof init1[0U]);
    {
      uint64_t tmp0[4U] = { 0U };
      uint64_t tmp3;
      uint64_t *x;
      uint64_t *z0;
      {
        uint64_t *os = tmp0;
        uint8_t *bj = basepoint + (uint32_t)0U * (uint32_t)8U;
        uint64_t u = load64_le(bj);
        uint64_t r = u;
        uint64_t x = r;
        os[0U] = x;
      }
      {
        uint64_t *os = tmp0;
        uint8_t *bj = basepoint + (uint32_t)1U * (uint32_t)8U;
        uint64_t u = load64_le(bj);
        uint64_t r = u;
        uint64_t x = r;
        os[1U] = x;
      }
      {
        uint64_t *os = tmp0;
        uint8_t *bj = basepoint + (uint32_t)2U * (uint32_t)8U;
        uint64_t u = load64_le(bj);
        uint64_t r = u;
        uint64_t x = r;
        os[2U] = x;
      }
      {
        uint64_t *os = tmp0;
        uint8_t *bj = basepoint + (uint32_t)3U * (uint32_t)8U;
        uint64_t u = load64_le(bj);
        uint64_t r = u;
        uint64_t x = r;
        os[3U] = x;
      }
      tmp3 = tmp0[3U];
      tmp0[3U] = tmp3 & (uint64_t)0x7fffffffffffffffU;
      x = init1;
      z0 = init1 + (uint32_t)4U;
      z0[0U] = (uint64_t)1U;
      z0[1U] = (uint64_t)0U;
      z0[2U] = (uint64_t)0U;
      z0[3U] = (uint64_t)0U;
      x[0U] = tmp0[0U];
      x[1U] = tmp0[1U];
      x[2U] = tmp0[2U];
      x[3U] = tmp0[3U];
      Hacl_Impl_Curve25519_Generic_montgomery_ladder_64(init1, priv, init1);
      {
        uint64_t *x0 = init1;
        uint64_t *z = init1 + (uint32_t)4U;
        uint64_t tmp[4U] = { 0U };
        uint64_t u64s[4U] = { 0U };
        KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * (uint32_t)8U);
        {
          uint64_t tmp_w[(uint32_t)2U * (uint32_t)8U];
          memset(tmp_w, 0U, (uint32_t)2U * (uint32_t)8U * sizeof tmp_w[0U]);
          {
            uint64_t f30;
            uint64_t top_bit0;
            uint64_t carry0;
            uint64_t f31;
            uint64_t top_bit;
            uint64_t carry;
            uint64_t f0;
            uint64_t f1;
            uint64_t f2;
            uint64_t f3;
            uint64_t m0;
            uint64_t m1;
            uint64_t m2;
            uint64_t m3;
            uint64_t mask;
            uint64_t f0_;
            uint64_t f1_;
            uint64_t f2_;
            uint64_t f3_;
            uint64_t o0;
            uint64_t o1;
            uint64_t o2;
            uint64_t o3;
            Hacl_Impl_Curve25519_Finv_finv_64(tmp, z, tmp_w);
            fmul(tmp, tmp, x0, tmp_w);
            f30 = tmp[3U];
            top_bit0 = f30 >> (uint32_t)63U;
            tmp[3U] = f30 & (uint64_t)0x7fffffffffffffffU;
            carry0 = add1(tmp, tmp, (uint64_t)19U * top_bit0);
            f31 = tmp[3U];
            top_bit = f31 >> (uint32_t)63U;
            tmp[3U] = f31 & (uint64_t)0x7fffffffffffffffU;
            carry = add1(tmp, tmp, (uint64_t)19U * top_bit);
            f0 = tmp[0U];
            f1 = tmp[1U];
            f2 = tmp[2U];
            f3 = tmp[3U];
            m0 = FStar_UInt64_gte_mask(f0, (uint64_t)0xffffffffffffffedU);
            m1 = FStar_UInt64_eq_mask(f1, (uint64_t)0xffffffffffffffffU);
            m2 = FStar_UInt64_eq_mask(f2, (uint64_t)0xffffffffffffffffU);
            m3 = FStar_UInt64_eq_mask(f3, (uint64_t)0x7fffffffffffffffU);
            mask = ((m0 & m1) & m2) & m3;
            f0_ = f0 - (mask & (uint64_t)0xffffffffffffffedU);
            f1_ = f1 - (mask & (uint64_t)0xffffffffffffffffU);
            f2_ = f2 - (mask & (uint64_t)0xffffffffffffffffU);
            f3_ = f3 - (mask & (uint64_t)0x7fffffffffffffffU);
            o0 = f0_;
            o1 = f1_;
            o2 = f2_;
            o3 = f3_;
            u64s[0U] = o0;
            u64s[1U] = o1;
            u64s[2U] = o2;
            u64s[3U] = o3;
            {
              store64_le(pub + (uint32_t)0U * (uint32_t)8U, u64s[0U]);
            }
            {
              store64_le(pub + (uint32_t)1U * (uint32_t)8U, u64s[1U]);
            }
            {
              store64_le(pub + (uint32_t)2U * (uint32_t)8U, u64s[2U]);
            }
            {
              store64_le(pub + (uint32_t)3U * (uint32_t)8U, u64s[3U]);
            }
          }
        }
      }
    }
  }
}

void curve25519_evercrypt64(uint8_t *shared, uint8_t *my_priv, uint8_t *their_pub)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * (uint32_t)4U);
  {
    uint64_t init1[(uint32_t)2U * (uint32_t)4U];
    memset(init1, 0U, (uint32_t)2U * (uint32_t)4U * sizeof init1[0U]);
    {
      uint64_t tmp0[4U] = { 0U };
      uint64_t tmp3;
      uint64_t *x;
      uint64_t *z0;
      {
        uint64_t *os = tmp0;
        uint8_t *bj = their_pub + (uint32_t)0U * (uint32_t)8U;
        uint64_t u = load64_le(bj);
        uint64_t r = u;
        uint64_t x = r;
        os[0U] = x;
      }
      {
        uint64_t *os = tmp0;
        uint8_t *bj = their_pub + (uint32_t)1U * (uint32_t)8U;
        uint64_t u = load64_le(bj);
        uint64_t r = u;
        uint64_t x = r;
        os[1U] = x;
      }
      {
        uint64_t *os = tmp0;
        uint8_t *bj = their_pub + (uint32_t)2U * (uint32_t)8U;
        uint64_t u = load64_le(bj);
        uint64_t r = u;
        uint64_t x = r;
        os[2U] = x;
      }
      {
        uint64_t *os = tmp0;
        uint8_t *bj = their_pub + (uint32_t)3U * (uint32_t)8U;
        uint64_t u = load64_le(bj);
        uint64_t r = u;
        uint64_t x = r;
        os[3U] = x;
      }
      tmp3 = tmp0[3U];
      tmp0[3U] = tmp3 & (uint64_t)0x7fffffffffffffffU;
      x = init1;
      z0 = init1 + (uint32_t)4U;
      z0[0U] = (uint64_t)1U;
      z0[1U] = (uint64_t)0U;
      z0[2U] = (uint64_t)0U;
      z0[3U] = (uint64_t)0U;
      x[0U] = tmp0[0U];
      x[1U] = tmp0[1U];
      x[2U] = tmp0[2U];
      x[3U] = tmp0[3U];
      Hacl_Impl_Curve25519_Generic_montgomery_ladder_64(init1, my_priv, init1);
      {
        uint64_t *x0 = init1;
        uint64_t *z = init1 + (uint32_t)4U;
        uint64_t tmp[4U] = { 0U };
        uint64_t u64s[4U] = { 0U };
        KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * (uint32_t)8U);
        {
          uint64_t tmp_w[(uint32_t)2U * (uint32_t)8U];
          memset(tmp_w, 0U, (uint32_t)2U * (uint32_t)8U * sizeof tmp_w[0U]);
          {
            uint64_t f30;
            uint64_t top_bit0;
            uint64_t carry0;
            uint64_t f31;
            uint64_t top_bit;
            uint64_t carry;
            uint64_t f0;
            uint64_t f1;
            uint64_t f2;
            uint64_t f3;
            uint64_t m0;
            uint64_t m1;
            uint64_t m2;
            uint64_t m3;
            uint64_t mask;
            uint64_t f0_;
            uint64_t f1_;
            uint64_t f2_;
            uint64_t f3_;
            uint64_t o0;
            uint64_t o1;
            uint64_t o2;
            uint64_t o3;
            Hacl_Impl_Curve25519_Finv_finv_64(tmp, z, tmp_w);
            fmul(tmp, tmp, x0, tmp_w);
            f30 = tmp[3U];
            top_bit0 = f30 >> (uint32_t)63U;
            tmp[3U] = f30 & (uint64_t)0x7fffffffffffffffU;
            carry0 = add1(tmp, tmp, (uint64_t)19U * top_bit0);
            f31 = tmp[3U];
            top_bit = f31 >> (uint32_t)63U;
            tmp[3U] = f31 & (uint64_t)0x7fffffffffffffffU;
            carry = add1(tmp, tmp, (uint64_t)19U * top_bit);
            f0 = tmp[0U];
            f1 = tmp[1U];
            f2 = tmp[2U];
            f3 = tmp[3U];
            m0 = FStar_UInt64_gte_mask(f0, (uint64_t)0xffffffffffffffedU);
            m1 = FStar_UInt64_eq_mask(f1, (uint64_t)0xffffffffffffffffU);
            m2 = FStar_UInt64_eq_mask(f2, (uint64_t)0xffffffffffffffffU);
            m3 = FStar_UInt64_eq_mask(f3, (uint64_t)0x7fffffffffffffffU);
            mask = ((m0 & m1) & m2) & m3;
            f0_ = f0 - (mask & (uint64_t)0xffffffffffffffedU);
            f1_ = f1 - (mask & (uint64_t)0xffffffffffffffffU);
            f2_ = f2 - (mask & (uint64_t)0xffffffffffffffffU);
            f3_ = f3 - (mask & (uint64_t)0x7fffffffffffffffU);
            o0 = f0_;
            o1 = f1_;
            o2 = f2_;
            o3 = f3_;
            u64s[0U] = o0;
            u64s[1U] = o1;
            u64s[2U] = o2;
            u64s[3U] = o3;
            {
              store64_le(shared + (uint32_t)0U * (uint32_t)8U, u64s[0U]);
            }
            {
              store64_le(shared + (uint32_t)1U * (uint32_t)8U, u64s[1U]);
            }
            {
              store64_le(shared + (uint32_t)2U * (uint32_t)8U, u64s[2U]);
            }
            {
              store64_le(shared + (uint32_t)3U * (uint32_t)8U, u64s[3U]);
            }
          }
        }
      }
    }
  }
}
