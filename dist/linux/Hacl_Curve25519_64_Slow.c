/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#include "Hacl_Curve25519_64_Slow.h"

typedef struct __u64_u64_s
{
  u64 fst;
  u64 snd;
}
__u64_u64;

static inline __u64_u64 addcarry(u64 x, u64 y, u64 cin)
{
  u64 res1 = x + cin;
  u64 c;
  if (res1 < cin)
    c = (u64)1U;
  else
    c = (u64)0U;
  {
    u64 res = res1 + y;
    u64 c1;
    if (res < res1)
      c1 = c + (u64)1U;
    else
      c1 = c;
    return ((__u64_u64){ .fst = res, .snd = c1 });
  }
}

static inline __u64_u64 subborrow(u64 x, u64 y, u64 cin)
{
  u64 res = x - y - cin;
  u64 c;
  if (cin == (u64)1U)
    if (x <= y)
      c = (u64)1U;
    else
      c = (u64)0U;
  else if (x < y)
    c = (u64)1U;
  else
    c = (u64)0U;
  return ((__u64_u64){ .fst = res, .snd = c });
}

static inline __u64_u64 mul64(u64 x, u64 y)
{
  uint128_t res = (uint128_t)x * y;
  return ((__u64_u64){ .fst = (uint64_t)res, .snd = (uint64_t)(res >> (u32)64U) });
}

static inline __u64_u64 add0carry(u64 x, u64 y)
{
  u64 res = x + y;
  u64 c;
  if (res < x)
    c = (u64)1U;
  else
    c = (u64)0U;
  return ((__u64_u64){ .fst = res, .snd = c });
}

typedef struct felem4_s
{
  u64 fst;
  u64 snd;
  u64 thd;
  u64 f3;
}
felem4;

typedef struct __u64_Hacl_Spec_Curve25519_Field64_Definition_felem4_s
{
  u64 fst;
  felem4 snd;
}
__u64_Hacl_Spec_Curve25519_Field64_Definition_felem4;

static __u64_Hacl_Spec_Curve25519_Field64_Definition_felem4 add1(felem4 f, u64 cin)
{
  u64 f0 = f.fst;
  u64 f1 = f.snd;
  u64 f2 = f.thd;
  u64 f3 = f.f3;
  __u64_u64 scrut = add0carry(f0, cin);
  u64 o0 = scrut.fst;
  u64 c0 = scrut.snd;
  __u64_u64 scrut0 = add0carry(f1, c0);
  u64 o1 = scrut0.fst;
  u64 c1 = scrut0.snd;
  __u64_u64 scrut1 = add0carry(f2, c1);
  u64 o2 = scrut1.fst;
  u64 c2 = scrut1.snd;
  __u64_u64 scrut2 = add0carry(f3, c2);
  u64 o3 = scrut2.fst;
  u64 c3 = scrut2.snd;
  felem4 out = { .fst = o0, .snd = o1, .thd = o2, .f3 = o3 };
  return ((__u64_Hacl_Spec_Curve25519_Field64_Definition_felem4){ .fst = c3, .snd = out });
}

static __u64_Hacl_Spec_Curve25519_Field64_Definition_felem4 sub1(felem4 f, u64 cin)
{
  u64 f0 = f.fst;
  u64 f1 = f.snd;
  u64 f2 = f.thd;
  u64 f3 = f.f3;
  __u64_u64 scrut = subborrow(f0, cin, (u64)0U);
  u64 o0 = scrut.fst;
  u64 c0 = scrut.snd;
  __u64_u64 scrut0 = subborrow(f1, (u64)0U, c0);
  u64 o1 = scrut0.fst;
  u64 c1 = scrut0.snd;
  __u64_u64 scrut1 = subborrow(f2, (u64)0U, c1);
  u64 o2 = scrut1.fst;
  u64 c2 = scrut1.snd;
  __u64_u64 scrut2 = subborrow(f3, (u64)0U, c2);
  u64 o3 = scrut2.fst;
  u64 c3 = scrut2.snd;
  felem4 out = { .fst = o0, .snd = o1, .thd = o2, .f3 = o3 };
  return ((__u64_Hacl_Spec_Curve25519_Field64_Definition_felem4){ .fst = c3, .snd = out });
}

static __u64_Hacl_Spec_Curve25519_Field64_Definition_felem4 mul1(felem4 f, u64 u)
{
  u64 f0 = f.fst;
  u64 f1 = f.snd;
  u64 f2 = f.thd;
  u64 f3 = f.f3;
  __u64_u64 scrut0 = mul64(f0, u);
  u64 l0 = scrut0.fst;
  u64 h0 = scrut0.snd;
  __u64_u64 scrut1 = mul64(f1, u);
  u64 l1 = scrut1.fst;
  u64 h1 = scrut1.snd;
  __u64_u64 scrut2 = mul64(f2, u);
  u64 l2 = scrut2.fst;
  u64 h2 = scrut2.snd;
  __u64_u64 scrut3 = mul64(f3, u);
  u64 l3 = scrut3.fst;
  u64 h3 = scrut3.snd;
  u64 o0 = l0;
  __u64_u64 scrut = addcarry(l1, h0, (u64)0U);
  u64 o1 = scrut.fst;
  u64 c0 = scrut.snd;
  __u64_u64 scrut4 = addcarry(l2, h1, c0);
  u64 o2 = scrut4.fst;
  u64 c1 = scrut4.snd;
  __u64_u64 scrut5 = addcarry(l3, h2, c1);
  u64 o3 = scrut5.fst;
  u64 c2 = scrut5.snd;
  felem4 out = { .fst = o0, .snd = o1, .thd = o2, .f3 = o3 };
  u64 c3 = h3 + c2;
  return ((__u64_Hacl_Spec_Curve25519_Field64_Definition_felem4){ .fst = c3, .snd = out });
}

static __u64_Hacl_Spec_Curve25519_Field64_Definition_felem4
mul1_add(felem4 f1, u64 u2, felem4 f3)
{
  __u64_Hacl_Spec_Curve25519_Field64_Definition_felem4 scrut0 = mul1(f1, u2);
  u64 c = scrut0.fst;
  felem4 out0 = scrut0.snd;
  u64 o0 = out0.fst;
  u64 o1 = out0.snd;
  u64 o2 = out0.thd;
  u64 o3 = out0.f3;
  u64 f30 = f3.fst;
  u64 f31 = f3.snd;
  u64 f32 = f3.thd;
  u64 f33 = f3.f3;
  __u64_u64 scrut = addcarry(f30, o0, (u64)0U);
  u64 o0_ = scrut.fst;
  u64 c0 = scrut.snd;
  __u64_u64 scrut1 = addcarry(f31, o1, c0);
  u64 o1_ = scrut1.fst;
  u64 c1 = scrut1.snd;
  __u64_u64 scrut2 = addcarry(f32, o2, c1);
  u64 o2_ = scrut2.fst;
  u64 c2 = scrut2.snd;
  __u64_u64 scrut3 = addcarry(f33, o3, c2);
  u64 o3_ = scrut3.fst;
  u64 c3 = scrut3.snd;
  felem4 out = { .fst = o0_, .snd = o1_, .thd = o2_, .f3 = o3_ };
  u64 c4 = c + c3;
  return ((__u64_Hacl_Spec_Curve25519_Field64_Definition_felem4){ .fst = c4, .snd = out });
}

static felem4 carry_pass(felem4 f, u64 cin)
{
  __u64_Hacl_Spec_Curve25519_Field64_Definition_felem4 scrut = add1(f, cin * (u64)38U);
  u64 carry = scrut.fst;
  felem4 out0 = scrut.snd;
  u64 o0 = out0.fst;
  u64 o1 = out0.snd;
  u64 o2 = out0.thd;
  u64 o3 = out0.f3;
  u64 o0_ = o0 + carry * (u64)38U;
  return ((felem4){ .fst = o0_, .snd = o1, .thd = o2, .f3 = o3 });
}

typedef struct felem_wide4_s
{
  u64 fst;
  u64 snd;
  u64 thd;
  u64 f3;
  u64 f4;
  u64 f5;
  u64 f6;
  u64 f7;
}
felem_wide4;

static felem4 carry_wide(felem_wide4 f)
{
  u64 f0 = f.fst;
  u64 f1 = f.snd;
  u64 f2 = f.thd;
  u64 f3 = f.f3;
  u64 f4 = f.f4;
  u64 f5 = f.f5;
  u64 f6 = f.f6;
  u64 f7 = f.f7;
  __u64_Hacl_Spec_Curve25519_Field64_Definition_felem4
  scrut =
    mul1_add(((felem4){ .fst = f4, .snd = f5, .thd = f6, .f3 = f7 }),
      (u64)38U,
      ((felem4){ .fst = f0, .snd = f1, .thd = f2, .f3 = f3 }));
  u64 c0 = scrut.fst;
  felem4 out0 = scrut.snd;
  felem4 out1 = carry_pass(out0, c0);
  return out1;
}

static __u64_Hacl_Spec_Curve25519_Field64_Definition_felem4 add4(felem4 f1, felem4 f2)
{
  u64 f10 = f1.fst;
  u64 f11 = f1.snd;
  u64 f12 = f1.thd;
  u64 f13 = f1.f3;
  u64 f20 = f2.fst;
  u64 f21 = f2.snd;
  u64 f22 = f2.thd;
  u64 f23 = f2.f3;
  __u64_u64 scrut = addcarry(f10, f20, (u64)0U);
  u64 o0 = scrut.fst;
  u64 c0 = scrut.snd;
  __u64_u64 scrut0 = addcarry(f11, f21, c0);
  u64 o1 = scrut0.fst;
  u64 c1 = scrut0.snd;
  __u64_u64 scrut1 = addcarry(f12, f22, c1);
  u64 o2 = scrut1.fst;
  u64 c2 = scrut1.snd;
  __u64_u64 scrut2 = addcarry(f13, f23, c2);
  u64 o3 = scrut2.fst;
  u64 c3 = scrut2.snd;
  felem4 out = { .fst = o0, .snd = o1, .thd = o2, .f3 = o3 };
  return ((__u64_Hacl_Spec_Curve25519_Field64_Definition_felem4){ .fst = c3, .snd = out });
}

static felem4 fadd4(felem4 f1, felem4 f2)
{
  __u64_Hacl_Spec_Curve25519_Field64_Definition_felem4 scrut = add4(f1, f2);
  u64 c0 = scrut.fst;
  felem4 out0 = scrut.snd;
  felem4 out = carry_pass(out0, c0);
  return out;
}

static __u64_Hacl_Spec_Curve25519_Field64_Definition_felem4 sub4(felem4 f1, felem4 f2)
{
  u64 f10 = f1.fst;
  u64 f11 = f1.snd;
  u64 f12 = f1.thd;
  u64 f13 = f1.f3;
  u64 f20 = f2.fst;
  u64 f21 = f2.snd;
  u64 f22 = f2.thd;
  u64 f23 = f2.f3;
  __u64_u64 scrut = subborrow(f10, f20, (u64)0U);
  u64 o0 = scrut.fst;
  u64 c0 = scrut.snd;
  __u64_u64 scrut0 = subborrow(f11, f21, c0);
  u64 o1 = scrut0.fst;
  u64 c1 = scrut0.snd;
  __u64_u64 scrut1 = subborrow(f12, f22, c1);
  u64 o2 = scrut1.fst;
  u64 c2 = scrut1.snd;
  __u64_u64 scrut2 = subborrow(f13, f23, c2);
  u64 o3 = scrut2.fst;
  u64 c3 = scrut2.snd;
  felem4 out = { .fst = o0, .snd = o1, .thd = o2, .f3 = o3 };
  return ((__u64_Hacl_Spec_Curve25519_Field64_Definition_felem4){ .fst = c3, .snd = out });
}

static felem4 fsub4(felem4 f1, felem4 f2)
{
  __u64_Hacl_Spec_Curve25519_Field64_Definition_felem4 scrut = sub4(f1, f2);
  u64 c0 = scrut.fst;
  felem4 out0 = scrut.snd;
  __u64_Hacl_Spec_Curve25519_Field64_Definition_felem4 scrut0 = sub1(out0, c0 * (u64)38U);
  u64 c1 = scrut0.fst;
  felem4 out1 = scrut0.snd;
  u64 o0 = out1.fst;
  u64 o1 = out1.snd;
  u64 o2 = out1.thd;
  u64 o3 = out1.f3;
  u64 o0_ = o0 - c1 * (u64)38U;
  return ((felem4){ .fst = o0_, .snd = o1, .thd = o2, .f3 = o3 });
}

static felem_wide4 mul4(felem4 f, felem4 r)
{
  u64 f0 = f.fst;
  u64 f1 = f.snd;
  u64 f2 = f.thd;
  u64 f3 = f.f3;
  __u64_Hacl_Spec_Curve25519_Field64_Definition_felem4 scrut = mul1(r, f0);
  u64 c0 = scrut.fst;
  felem4 out0 = scrut.snd;
  u64 o00 = out0.fst;
  u64 o01 = out0.snd;
  u64 o02 = out0.thd;
  u64 o03 = out0.f3;
  __u64_Hacl_Spec_Curve25519_Field64_Definition_felem4
  scrut0 = mul1_add(r, f1, ((felem4){ .fst = o01, .snd = o02, .thd = o03, .f3 = c0 }));
  u64 c1 = scrut0.fst;
  felem4 out1 = scrut0.snd;
  u64 o11 = out1.fst;
  u64 o12 = out1.snd;
  u64 o13 = out1.thd;
  u64 o14 = out1.f3;
  __u64_Hacl_Spec_Curve25519_Field64_Definition_felem4
  scrut1 = mul1_add(r, f2, ((felem4){ .fst = o12, .snd = o13, .thd = o14, .f3 = c1 }));
  u64 c2 = scrut1.fst;
  felem4 out2 = scrut1.snd;
  u64 o22 = out2.fst;
  u64 o23 = out2.snd;
  u64 o24 = out2.thd;
  u64 o25 = out2.f3;
  __u64_Hacl_Spec_Curve25519_Field64_Definition_felem4
  scrut2 = mul1_add(r, f3, ((felem4){ .fst = o23, .snd = o24, .thd = o25, .f3 = c2 }));
  u64 c3 = scrut2.fst;
  felem4 out3 = scrut2.snd;
  u64 o33 = out3.fst;
  u64 o34 = out3.snd;
  u64 o35 = out3.thd;
  u64 o36 = out3.f3;
  u64 o37 = c3;
  return
    (
      (felem_wide4){
        .fst = o00,
        .snd = o11,
        .thd = o22,
        .f3 = o33,
        .f4 = o34,
        .f5 = o35,
        .f6 = o36,
        .f7 = o37
      }
    );
}

static felem4 fmul4(felem4 f1, felem4 r)
{
  felem_wide4 tmp = mul4(f1, r);
  felem4 out = carry_wide(tmp);
  return out;
}

static felem4 fmul14(felem4 f1, u64 f2)
{
  __u64_Hacl_Spec_Curve25519_Field64_Definition_felem4 scrut = mul1(f1, f2);
  u64 c0 = scrut.fst;
  felem4 out0 = scrut.snd;
  felem4 out1 = carry_pass(out0, c0);
  return out1;
}

static inline u64 add1_(u64 *out, u64 *f1, u64 f2)
{
  u64 f10 = f1[0U];
  u64 f11 = f1[1U];
  u64 f12 = f1[2U];
  u64 f13 = f1[3U];
  __u64_Hacl_Spec_Curve25519_Field64_Definition_felem4
  scrut = add1(((felem4){ .fst = f10, .snd = f11, .thd = f12, .f3 = f13 }), f2);
  u64 o3 = scrut.snd.f3;
  u64 o2 = scrut.snd.thd;
  u64 o1 = scrut.snd.snd;
  u64 o0 = scrut.snd.fst;
  u64 carry = scrut.fst;
  out[0U] = o0;
  out[1U] = o1;
  out[2U] = o2;
  out[3U] = o3;
  return carry;
}

static inline void fadd_(u64 *out, u64 *f1, u64 *f2)
{
  u64 f10 = f1[0U];
  u64 f11 = f1[1U];
  u64 f12 = f1[2U];
  u64 f13 = f1[3U];
  u64 f20 = f2[0U];
  u64 f21 = f2[1U];
  u64 f22 = f2[2U];
  u64 f23 = f2[3U];
  felem4
  scrut =
    fadd4(((felem4){ .fst = f10, .snd = f11, .thd = f12, .f3 = f13 }),
      ((felem4){ .fst = f20, .snd = f21, .thd = f22, .f3 = f23 }));
  u64 o0 = scrut.fst;
  u64 o1 = scrut.snd;
  u64 o2 = scrut.thd;
  u64 o3 = scrut.f3;
  out[0U] = o0;
  out[1U] = o1;
  out[2U] = o2;
  out[3U] = o3;
}

static inline void fsub_(u64 *out, u64 *f1, u64 *f2)
{
  u64 f10 = f1[0U];
  u64 f11 = f1[1U];
  u64 f12 = f1[2U];
  u64 f13 = f1[3U];
  u64 f20 = f2[0U];
  u64 f21 = f2[1U];
  u64 f22 = f2[2U];
  u64 f23 = f2[3U];
  felem4
  scrut =
    fsub4(((felem4){ .fst = f10, .snd = f11, .thd = f12, .f3 = f13 }),
      ((felem4){ .fst = f20, .snd = f21, .thd = f22, .f3 = f23 }));
  u64 o0 = scrut.fst;
  u64 o1 = scrut.snd;
  u64 o2 = scrut.thd;
  u64 o3 = scrut.f3;
  out[0U] = o0;
  out[1U] = o1;
  out[2U] = o2;
  out[3U] = o3;
}

static inline void fmul_(u64 *out, u64 *f1, u64 *f2)
{
  u64 f10 = f1[0U];
  u64 f11 = f1[1U];
  u64 f12 = f1[2U];
  u64 f13 = f1[3U];
  u64 f20 = f2[0U];
  u64 f21 = f2[1U];
  u64 f22 = f2[2U];
  u64 f23 = f2[3U];
  felem4
  scrut =
    fmul4(((felem4){ .fst = f10, .snd = f11, .thd = f12, .f3 = f13 }),
      ((felem4){ .fst = f20, .snd = f21, .thd = f22, .f3 = f23 }));
  u64 o0 = scrut.fst;
  u64 o1 = scrut.snd;
  u64 o2 = scrut.thd;
  u64 o3 = scrut.f3;
  out[0U] = o0;
  out[1U] = o1;
  out[2U] = o2;
  out[3U] = o3;
}

static inline void fmul2_(u64 *out, u64 *f1, u64 *f2, u64 *tmp)
{
  u64 *out1 = out;
  u64 *out2 = out + (u32)4U;
  u64 *f11 = f1;
  u64 *f12 = f1 + (u32)4U;
  u64 *f21 = f2;
  u64 *f22 = f2 + (u32)4U;
  fmul_(out1, f11, f21);
  fmul_(out2, f12, f22);
}

static inline void fmul1_(u64 *out, u64 *f1, u64 f2)
{
  u64 f10 = f1[0U];
  u64 f11 = f1[1U];
  u64 f12 = f1[2U];
  u64 f13 = f1[3U];
  felem4 scrut = fmul14(((felem4){ .fst = f10, .snd = f11, .thd = f12, .f3 = f13 }), f2);
  u64 o0 = scrut.fst;
  u64 o1 = scrut.snd;
  u64 o2 = scrut.thd;
  u64 o3 = scrut.f3;
  out[0U] = o0;
  out[1U] = o1;
  out[2U] = o2;
  out[3U] = o3;
}

static inline void fsqr_(u64 *out, u64 *f1)
{
  u64 tmp1[16U] = { 0U };
  fmul_(out, f1, f1);
}

static inline void fsqr2_(u64 *out, u64 *f, u64 *tmp)
{
  fmul2_(out, f, f, tmp);
}

static inline void cswap2_(u64 bit, u64 *p1, u64 *p2)
{
  u64 mask = (u64)0U - bit;
  u32 i;
  for (i = (u32)0U; i < (u32)8U; i++)
  {
    u64 dummy = mask & (p1[i] ^ p2[i]);
    p1[i] = p1[i] ^ dummy;
    p2[i] = p2[i] ^ dummy;
  }
}

static const u8 g25519[32U] = { (u8)9U };

static void point_add_and_double(u64 *q, u64 *p01_tmp1, u64 *tmp2)
{
  u64 *nq = p01_tmp1;
  u64 *nq_p1 = p01_tmp1 + (u32)8U;
  u64 *tmp1 = p01_tmp1 + (u32)16U;
  u64 *x1 = q;
  u64 *x2 = nq;
  u64 *z2 = nq + (u32)4U;
  u64 *z3 = nq_p1 + (u32)4U;
  u64 *a = tmp1;
  u64 *b = tmp1 + (u32)4U;
  u64 *ab = tmp1;
  u64 *dc = tmp1 + (u32)8U;
  u64 *x3;
  u64 *z31;
  u64 *d0;
  u64 *c0;
  u64 *a1;
  u64 *b1;
  u64 *d;
  u64 *c;
  u64 *ab1;
  u64 *dc1;
  fadd_(a, x2, z2);
  fsub_(b, x2, z2);
  x3 = nq_p1;
  z31 = nq_p1 + (u32)4U;
  d0 = dc;
  c0 = dc + (u32)4U;
  fadd_(c0, x3, z31);
  fsub_(d0, x3, z31);
  fmul2_(dc, dc, ab, tmp2);
  fadd_(x3, d0, c0);
  fsub_(z31, d0, c0);
  a1 = tmp1;
  b1 = tmp1 + (u32)4U;
  d = tmp1 + (u32)8U;
  c = tmp1 + (u32)12U;
  ab1 = tmp1;
  dc1 = tmp1 + (u32)8U;
  fsqr2_(dc1, ab1, tmp2);
  fsqr2_(nq_p1, nq_p1, tmp2);
  a1[0U] = c[0U];
  a1[1U] = c[1U];
  a1[2U] = c[2U];
  a1[3U] = c[3U];
  fsub_(c, d, c);
  fmul1_(b1, c, (u64)121665U);
  fadd_(b1, b1, d);
  fmul2_(nq, dc1, ab1, tmp2);
  fmul_(z3, z3, x1);
}

static void point_double(u64 *nq, u64 *tmp1, u64 *tmp2)
{
  u64 *x2 = nq;
  u64 *z2 = nq + (u32)4U;
  u64 *a = tmp1;
  u64 *b = tmp1 + (u32)4U;
  u64 *d = tmp1 + (u32)8U;
  u64 *c = tmp1 + (u32)12U;
  u64 *ab = tmp1;
  u64 *dc = tmp1 + (u32)8U;
  fadd_(a, x2, z2);
  fsub_(b, x2, z2);
  fsqr2_(dc, ab, tmp2);
  a[0U] = c[0U];
  a[1U] = c[1U];
  a[2U] = c[2U];
  a[3U] = c[3U];
  fsub_(c, d, c);
  fmul1_(b, c, (u64)121665U);
  fadd_(b, b, d);
  fmul2_(nq, dc, ab, tmp2);
}

static void montgomery_ladder(u64 *out, u8 *key, u64 *init)
{
  u64 tmp2[16U] = { 0U };
  u64 p01_tmp1_swap[33U] = { 0U };
  u64 *p0 = p01_tmp1_swap;
  u64 *p01 = p01_tmp1_swap;
  u64 *p03 = p01;
  u64 *p11 = p01 + (u32)8U;
  u64 *x0;
  u64 *z0;
  u64 *p01_tmp1;
  u64 *p01_tmp11;
  u64 *nq10;
  u64 *nq_p11;
  u64 *swap;
  u64 sw0;
  u64 *nq1;
  u64 *tmp1;
  memcpy(p11, init, (u32)8U * sizeof (u64));
  x0 = p03;
  z0 = p03 + (u32)4U;
  x0[0U] = (u64)1U;
  x0[1U] = (u64)0U;
  x0[2U] = (u64)0U;
  x0[3U] = (u64)0U;
  z0[0U] = (u64)0U;
  z0[1U] = (u64)0U;
  z0[2U] = (u64)0U;
  z0[3U] = (u64)0U;
  p01_tmp1 = p01_tmp1_swap;
  p01_tmp11 = p01_tmp1_swap;
  nq10 = p01_tmp1_swap;
  nq_p11 = p01_tmp1_swap + (u32)8U;
  swap = p01_tmp1_swap + (u32)32U;
  cswap2_((u64)1U, nq10, nq_p11);
  point_add_and_double(init, p01_tmp11, tmp2);
  swap[0U] = (u64)1U;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)251U; i++)
    {
      u64 *p01_tmp12 = p01_tmp1_swap;
      u64 *swap1 = p01_tmp1_swap + (u32)32U;
      u64 *nq2 = p01_tmp12;
      u64 *nq_p12 = p01_tmp12 + (u32)8U;
      u64 bit = (u64)(key[((u32)253U - i) / (u32)8U] >> ((u32)253U - i) % (u32)8U & (u8)1U);
      u64 sw = swap1[0U] ^ bit;
      cswap2_(sw, nq2, nq_p12);
      point_add_and_double(init, p01_tmp12, tmp2);
      swap1[0U] = bit;
    }
  }
  sw0 = swap[0U];
  cswap2_(sw0, nq10, nq_p11);
  nq1 = p01_tmp1;
  tmp1 = p01_tmp1 + (u32)16U;
  point_double(nq1, tmp1, tmp2);
  point_double(nq1, tmp1, tmp2);
  point_double(nq1, tmp1, tmp2);
  memcpy(out, p0, (u32)8U * sizeof (u64));
}

static void fsquare_times(u64 *o, u64 *inp, u64 *tmp, u32 n)
{
  u32 i;
  fsqr_(o, inp);
  for (i = (u32)0U; i < n - (u32)1U; i++)
    fsqr_(o, o);
}

static void finv(u64 *o, u64 *i, u64 *tmp)
{
  u64 t1[16U] = { 0U };
  u64 *a1 = t1;
  u64 *b10 = t1 + (u32)4U;
  u64 *t010 = t1 + (u32)12U;
  u64 *tmp10 = tmp;
  u64 *b11;
  u64 *c10;
  u64 *t011;
  u64 *tmp11;
  u64 *b1;
  u64 *c1;
  u64 *t01;
  u64 *tmp1;
  u64 *a;
  u64 *t0;
  fsquare_times(a1, i, tmp10, (u32)1U);
  fsquare_times(t010, a1, tmp10, (u32)2U);
  fmul_(b10, t010, i);
  fmul_(a1, b10, a1);
  fsquare_times(t010, a1, tmp10, (u32)1U);
  fmul_(b10, t010, b10);
  fsquare_times(t010, b10, tmp10, (u32)5U);
  fmul_(b10, t010, b10);
  b11 = t1 + (u32)4U;
  c10 = t1 + (u32)8U;
  t011 = t1 + (u32)12U;
  tmp11 = tmp;
  fsquare_times(t011, b11, tmp11, (u32)10U);
  fmul_(c10, t011, b11);
  fsquare_times(t011, c10, tmp11, (u32)20U);
  fmul_(t011, t011, c10);
  fsquare_times(t011, t011, tmp11, (u32)10U);
  fmul_(b11, t011, b11);
  fsquare_times(t011, b11, tmp11, (u32)50U);
  fmul_(c10, t011, b11);
  b1 = t1 + (u32)4U;
  c1 = t1 + (u32)8U;
  t01 = t1 + (u32)12U;
  tmp1 = tmp;
  fsquare_times(t01, c1, tmp1, (u32)100U);
  fmul_(t01, t01, c1);
  fsquare_times(t01, t01, tmp1, (u32)50U);
  fmul_(t01, t01, b1);
  fsquare_times(t01, t01, tmp1, (u32)5U);
  a = t1;
  t0 = t1 + (u32)12U;
  fmul_(o, t0, a);
}

static void store_felem(u64 *b, u64 *f)
{
  u64 f30 = f[3U];
  u64 top_bit0 = f30 >> (u32)63U;
  u64 carry0;
  u64 f31;
  u64 top_bit;
  u64 carry;
  u64 f0;
  u64 f1;
  u64 f2;
  u64 f3;
  u64 m0;
  u64 m1;
  u64 m2;
  u64 m3;
  u64 mask;
  u64 f0_;
  u64 f1_;
  u64 f2_;
  u64 f3_;
  u64 o0;
  u64 o1;
  u64 o2;
  u64 o3;
  f[3U] = f30 & (u64)0x7fffffffffffffffU;
  carry0 = add1_(f, f, (u64)19U * top_bit0);
  f31 = f[3U];
  top_bit = f31 >> (u32)63U;
  f[3U] = f31 & (u64)0x7fffffffffffffffU;
  carry = add1_(f, f, (u64)19U * top_bit);
  f0 = f[0U];
  f1 = f[1U];
  f2 = f[2U];
  f3 = f[3U];
  m0 = FStar_UInt64_gte_mask(f0, (u64)0xffffffffffffffedU);
  m1 = FStar_UInt64_eq_mask(f1, (u64)0xffffffffffffffffU);
  m2 = FStar_UInt64_eq_mask(f2, (u64)0xffffffffffffffffU);
  m3 = FStar_UInt64_eq_mask(f3, (u64)0x7fffffffffffffffU);
  mask = ((m0 & m1) & m2) & m3;
  f0_ = f0 - (mask & (u64)0xffffffffffffffedU);
  f1_ = f1 - (mask & (u64)0xffffffffffffffffU);
  f2_ = f2 - (mask & (u64)0xffffffffffffffffU);
  f3_ = f3 - (mask & (u64)0x7fffffffffffffffU);
  o0 = f0_;
  o1 = f1_;
  o2 = f2_;
  o3 = f3_;
  b[0U] = o0;
  b[1U] = o1;
  b[2U] = o2;
  b[3U] = o3;
}

static void encode_point(u8 *o, u64 *i)
{
  u64 *x = i;
  u64 *z = i + (u32)4U;
  u64 tmp[4U] = { 0U };
  u64 u64s[4U] = { 0U };
  u64 tmp_w[16U] = { 0U };
  finv(tmp, z, tmp_w);
  fmul_(tmp, tmp, x);
  store_felem(u64s, tmp);
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < (u32)4U; i0++)
      store64_le(o + i0 * (u32)8U, u64s[i0]);
  }
}

void Hacl_Curve25519_64_Slow_scalarmult(u8 *out, u8 *priv, u8 *pub)
{
  u64 init[8U] = { 0U };
  u64 tmp[4U] = { 0U };
  u64 tmp3;
  u64 *x;
  u64 *z;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)4U; i++)
    {
      u64 *os = tmp;
      u8 *bj = pub + i * (u32)8U;
      u64 u = load64_le(bj);
      u64 r = u;
      u64 x0 = r;
      os[i] = x0;
    }
  }
  tmp3 = tmp[3U];
  tmp[3U] = tmp3 & (u64)0x7fffffffffffffffU;
  x = init;
  z = init + (u32)4U;
  z[0U] = (u64)1U;
  z[1U] = (u64)0U;
  z[2U] = (u64)0U;
  z[3U] = (u64)0U;
  x[0U] = tmp[0U];
  x[1U] = tmp[1U];
  x[2U] = tmp[2U];
  x[3U] = tmp[3U];
  montgomery_ladder(init, priv, init);
  encode_point(out, init);
}

void Hacl_Curve25519_64_Slow_secret_to_public(u8 *pub, u8 *priv)
{
  u8 basepoint[32U] = { 0U };
  {
    u32 i;
    for (i = (u32)0U; i < (u32)32U; i++)
    {
      u8 *os = basepoint;
      u8 x = g25519[i];
      os[i] = x;
    }
  }
  Hacl_Curve25519_64_Slow_scalarmult(pub, priv, basepoint);
}

bool Hacl_Curve25519_64_Slow_ecdh(u8 *out, u8 *priv, u8 *pub)
{
  u8 zeros[32U] = { 0U };
  Hacl_Curve25519_64_Slow_scalarmult(out, priv, pub);
  {
    u8 res = (u8)255U;
    u8 z;
    bool r;
    {
      u32 i;
      for (i = (u32)0U; i < (u32)32U; i++)
      {
        u8 uu____0 = FStar_UInt8_eq_mask(out[i], zeros[i]);
        res = uu____0 & res;
      }
    }
    z = res;
    r = z == (u8)255U;
    return !r;
  }
}

