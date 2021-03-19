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


#include "Hacl_Bignum32.h"

/*******************************************************************************

A verified bignum library.

This is a 32-bit optimized version, where bignums are represented as an array
of `len` unsigned 32-bit integers, i.e. uint32_t[len].

*******************************************************************************/

/************************/
/* Arithmetic functions */
/************************/


/*
Write `a + b mod 2 ^ (32 * len)` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be `len` limbs in size, i.e. uint32_t[len]
*/
uint32_t Hacl_Bignum32_add(uint32_t len, uint32_t *a, uint32_t *b, uint32_t *res)
{
  return Hacl_Bignum_Addition_bn_add_eq_len_u32(len, a, b, res);
}

/*
Write `a - b mod 2 ^ (32 * len)` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be `len` limbs in size, i.e. uint32_t[len]
*/
uint32_t Hacl_Bignum32_sub(uint32_t len, uint32_t *a, uint32_t *b, uint32_t *res)
{
  return Hacl_Bignum_Addition_bn_sub_eq_len_u32(len, a, b, res);
}

/*
Write `a * b` in `res`.

  The arguments a and b are meant to be `len` limbs in size, i.e. uint32_t[len].
  The outparam res is meant to be `2*len` limbs in size, i.e. uint32_t[2*len].
*/
void Hacl_Bignum32_mul(uint32_t len, uint32_t *a, uint32_t *b, uint32_t *res)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * len);
  {
    uint32_t tmp[(uint32_t)4U * len];
    memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint32_t));
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len, a, b, tmp, res);
  }
}

/*
Write `a * a` in `res`.

  The argument a is meant to be `len` limbs in size, i.e. uint32_t[len].
  The outparam res is meant to be `2*len` limbs in size, i.e. uint32_t[2*len].
*/
void Hacl_Bignum32_sqr(uint32_t len, uint32_t *a, uint32_t *res)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * len);
  {
    uint32_t tmp[(uint32_t)4U * len];
    memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint32_t));
    Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(len, a, tmp, res);
  }
}

/*
Write `a mod n` in `res` if a < n * n.

  The argument a is meant to be `2*len` limbs in size, i.e. uint32_t[2*len].
  The argument n, r2 and the outparam res are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument r2 is a precomputed constant 2 ^ (64 * len) mod n obtained through Hacl_Bignum32_new_precompr2.

  This function is *UNSAFE* and requires C clients to observe the precondition
  of bn_mod_slow_precompr2_lemma in Hacl.Spec.Bignum.ModReduction.fst, which
  amounts to:
  • 1 < n
  • n % 2 = 1
  • a < n * n

  Owing to the absence of run-time checks, and factoring out the precomputation
  r2, this function is notably faster than mod below.
*/
void
Hacl_Bignum32_mod_precompr2(
  uint32_t len,
  uint32_t *n,
  uint32_t *a,
  uint32_t *r2,
  uint32_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  {
    uint32_t a_mod[len];
    memset(a_mod, 0U, len * sizeof (uint32_t));
    KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
    {
      uint32_t a1[len + len];
      memset(a1, 0U, (len + len) * sizeof (uint32_t));
      {
        uint32_t mu;
        memcpy(a1, a, (len + len) * sizeof (uint32_t));
        mu = Hacl_Bignum_ModInvLimb_mod_inv_uint32(n[0U]);
        {
          uint32_t c0 = (uint32_t)0U;
          uint32_t c01;
          {
            uint32_t i0;
            for (i0 = (uint32_t)0U; i0 < len; i0++)
            {
              uint32_t qj = mu * a1[i0];
              uint32_t *res_j0 = a1 + i0;
              uint32_t c = (uint32_t)0U;
              {
                uint32_t i;
                for (i = (uint32_t)0U; i < len / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
                {
                  uint32_t a_i = n[(uint32_t)4U * i];
                  uint32_t *res_i0 = res_j0 + (uint32_t)4U * i;
                  c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c, res_i0);
                  {
                    uint32_t a_i0 = n[(uint32_t)4U * i + (uint32_t)1U];
                    uint32_t *res_i1 = res_j0 + (uint32_t)4U * i + (uint32_t)1U;
                    c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c, res_i1);
                    {
                      uint32_t a_i1 = n[(uint32_t)4U * i + (uint32_t)2U];
                      uint32_t *res_i2 = res_j0 + (uint32_t)4U * i + (uint32_t)2U;
                      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c, res_i2);
                      {
                        uint32_t a_i2 = n[(uint32_t)4U * i + (uint32_t)3U];
                        uint32_t *res_i = res_j0 + (uint32_t)4U * i + (uint32_t)3U;
                        c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c, res_i);
                      }
                    }
                  }
                }
              }
              {
                uint32_t i;
                for (i = len / (uint32_t)4U * (uint32_t)4U; i < len; i++)
                {
                  uint32_t a_i = n[i];
                  uint32_t *res_i = res_j0 + i;
                  c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c, res_i);
                }
              }
              {
                uint32_t r = c;
                uint32_t c1 = r;
                uint32_t *resb = a1 + len + i0;
                uint32_t res_j = a1[len + i0];
                c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c1, res_j, resb);
              }
            }
          }
          memcpy(a_mod, a1 + len, (len + len - len) * sizeof (uint32_t));
          c01 = c0;
          KRML_CHECK_SIZE(sizeof (uint32_t), len);
          {
            uint32_t tmp0[len];
            memset(tmp0, 0U, len * sizeof (uint32_t));
            {
              uint32_t c2 = (uint32_t)0U;
              uint32_t c1;
              uint32_t c;
              {
                uint32_t i;
                for (i = (uint32_t)0U; i < len / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
                {
                  uint32_t t1 = a_mod[(uint32_t)4U * i];
                  uint32_t t20 = n[(uint32_t)4U * i];
                  uint32_t *res_i0 = tmp0 + (uint32_t)4U * i;
                  c2 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c2, t1, t20, res_i0);
                  {
                    uint32_t t10 = a_mod[(uint32_t)4U * i + (uint32_t)1U];
                    uint32_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
                    uint32_t *res_i1 = tmp0 + (uint32_t)4U * i + (uint32_t)1U;
                    c2 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c2, t10, t21, res_i1);
                    {
                      uint32_t t11 = a_mod[(uint32_t)4U * i + (uint32_t)2U];
                      uint32_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
                      uint32_t *res_i2 = tmp0 + (uint32_t)4U * i + (uint32_t)2U;
                      c2 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c2, t11, t22, res_i2);
                      {
                        uint32_t t12 = a_mod[(uint32_t)4U * i + (uint32_t)3U];
                        uint32_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
                        uint32_t *res_i = tmp0 + (uint32_t)4U * i + (uint32_t)3U;
                        c2 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c2, t12, t2, res_i);
                      }
                    }
                  }
                }
              }
              {
                uint32_t i;
                for (i = len / (uint32_t)4U * (uint32_t)4U; i < len; i++)
                {
                  uint32_t t1 = a_mod[i];
                  uint32_t t2 = n[i];
                  uint32_t *res_i = tmp0 + i;
                  c2 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c2, t1, t2, res_i);
                }
              }
              c1 = c2;
              c = c01 - c1;
              {
                uint32_t i;
                for (i = (uint32_t)0U; i < len; i++)
                {
                  uint32_t *os = a_mod;
                  uint32_t x = (c & a_mod[i]) | (~c & tmp0[i]);
                  os[i] = x;
                }
              }
              KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
              {
                uint32_t c3[len + len];
                memset(c3, 0U, (len + len) * sizeof (uint32_t));
                KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * len);
                {
                  uint32_t tmp[(uint32_t)4U * len];
                  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint32_t));
                  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len, a_mod, r2, tmp, c3);
                  Hacl_Bignum_Montgomery_bn_mont_reduction_u32(len, n, mu, c3, res);
                }
              }
            }
          }
        }
      }
    }
  }
}

/*
Write `a mod n` in `res` if a < n * n.

  The argument a is meant to be `2*len` limbs in size, i.e. uint32_t[2*len].
  The argument n and the outparam res are meant to be `len` limbs in size, i.e. uint32_t[len].

  The function returns false if any of the preconditions of mod_precompr2 above
  are violated, true otherwise.
*/
bool Hacl_Bignum32_mod(uint32_t len, uint32_t *n, uint32_t *a, uint32_t *res)
{
  uint32_t m0 = Hacl_Bignum_Montgomery_bn_check_modulus_u32(len, n);
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  {
    uint32_t n2[len + len];
    memset(n2, 0U, (len + len) * sizeof (uint32_t));
    KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * len);
    {
      uint32_t tmp[(uint32_t)4U * len];
      memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint32_t));
      Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len, n, n, tmp, n2);
      {
        uint32_t acc = (uint32_t)0U;
        uint32_t m1;
        uint32_t is_valid_m;
        uint32_t nBits;
        {
          uint32_t i;
          for (i = (uint32_t)0U; i < len + len; i++)
          {
            uint32_t beq = FStar_UInt32_eq_mask(a[i], n2[i]);
            uint32_t blt = ~FStar_UInt32_gte_mask(a[i], n2[i]);
            acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
          }
        }
        m1 = acc;
        is_valid_m = m0 & m1;
        nBits = (uint32_t)32U * Hacl_Bignum_Lib_bn_get_top_index_u32(len, n);
        KRML_CHECK_SIZE(sizeof (uint32_t), len);
        {
          uint32_t r2[len];
          memset(r2, 0U, len * sizeof (uint32_t));
          {
            uint32_t i;
            uint32_t j;
            memset(r2, 0U, len * sizeof (uint32_t));
            i = nBits / (uint32_t)32U;
            j = nBits % (uint32_t)32U;
            r2[i] = r2[i] | (uint32_t)1U << j;
            {
              uint32_t i0;
              for (i0 = (uint32_t)0U; i0 < (uint32_t)64U * len - nBits; i0++)
              {
                Hacl_Bignum_bn_add_mod_n_u32(len, n, r2, r2, r2);
              }
            }
            Hacl_Bignum32_mod_precompr2(len, n, a, r2, res);
            {
              uint32_t i0;
              for (i0 = (uint32_t)0U; i0 < len; i0++)
              {
                uint32_t *os = res;
                uint32_t x = res[i0];
                uint32_t x0 = is_valid_m & x;
                os[i0] = x0;
              }
            }
            return is_valid_m == (uint32_t)0xFFFFFFFFU;
          }
        }
      }
    }
  }
}

/*
Write `a ^ b mod n` in `res`.

  The arguments a, n, r2 and the outparam res are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument r2 is a precomputed constant 2 ^ (64 * len) mod n obtained through Hacl_Bignum32_new_precompr2.
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_consttime_* functions for constant-time variants.

  This function is *UNSAFE* and requires C clients to observe bn_mod_exp_pre
  from Hacl.Spec.Bignum.Exponentiation.fsti, which amounts to:
  • n % 2 = 1
  • 1 < n
  • 0 < b
  • b < pow2 bBits
  • a < n

  Owing to the absence of run-time checks, and factoring out the precomputation
  r2, this function is notably faster than mod_exp_vartime below.
*/
void
Hacl_Bignum32_mod_exp_vartime_precompr2(
  uint32_t len,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *r2,
  uint32_t *res
)
{
  if (bBits < (uint32_t)200U)
  {
    Hacl_Bignum_Exponentiation_bn_mod_exp_bm_vartime_precompr2_u32(len, n, a, bBits, b, r2, res);
    return;
  }
  Hacl_Bignum_Exponentiation_bn_mod_exp_fw_vartime_precompr2_u32(len,
    (uint32_t)4U,
    n,
    a,
    bBits,
    b,
    r2,
    res);
}

/*
Write `a ^ b mod n` in `res`.

  The arguments a, n, r2 and the outparam res are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument r2 is a precomputed constant 2 ^ (64 * len) mod n obtained through Hacl_Bignum32_new_precompr2.
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_vartime_precompr2.

  This function is *UNSAFE* and requires C clients to observe bn_mod_exp_pre
  from Hacl.Spec.Bignum.Exponentiation.fsti, which amounts to:
  • n % 2 = 1
  • 1 < n
  • 0 < b
  • b < pow2 bBits
  • a < n

  Owing to the absence of run-time checks, and factoring out the precomputation
  r2, this function is notably faster than mod_exp_consttime below.
*/
void
Hacl_Bignum32_mod_exp_consttime_precompr2(
  uint32_t len,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *r2,
  uint32_t *res
)
{
  if (bBits < (uint32_t)200U)
  {
    Hacl_Bignum_Exponentiation_bn_mod_exp_bm_consttime_precompr2_u32(len, n, a, bBits, b, r2, res);
    return;
  }
  Hacl_Bignum_Exponentiation_bn_mod_exp_fw_consttime_precompr2_u32(len,
    (uint32_t)4U,
    n,
    a,
    bBits,
    b,
    r2,
    res);
}

/*
Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_consttime_* functions for constant-time variants.

  The function returns false if any of the preconditions of mod_exp_precompr2 are
  violated, true otherwise.
*/
bool
Hacl_Bignum32_mod_exp_vartime(
  uint32_t len,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  uint32_t is_valid_m = Hacl_Bignum_Exponentiation_bn_check_mod_exp_u32(len, n, a, bBits, b);
  uint32_t nBits = (uint32_t)32U * Hacl_Bignum_Lib_bn_get_top_index_u32(len, n);
  if (is_valid_m == (uint32_t)0xFFFFFFFFU)
  {
    KRML_CHECK_SIZE(sizeof (uint32_t), len);
    {
      uint32_t r2[len];
      memset(r2, 0U, len * sizeof (uint32_t));
      memset(r2, 0U, len * sizeof (uint32_t));
      {
        uint32_t i = nBits / (uint32_t)32U;
        uint32_t j = nBits % (uint32_t)32U;
        r2[i] = r2[i] | (uint32_t)1U << j;
        {
          uint32_t i0;
          for (i0 = (uint32_t)0U; i0 < (uint32_t)64U * len - nBits; i0++)
          {
            Hacl_Bignum_bn_add_mod_n_u32(len, n, r2, r2, r2);
          }
        }
        Hacl_Bignum32_mod_exp_vartime_precompr2(len, n, a, bBits, b, r2, res);
      }
    }
  }
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < len; i++)
    {
      uint32_t *os = res;
      uint32_t x = res[i];
      uint32_t x0 = is_valid_m & x;
      os[i] = x0;
    }
  }
  return is_valid_m == (uint32_t)0xFFFFFFFFU;
}

/*
Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_vartime.

  The function returns false if any of the preconditions of
  mod_exp_consttime_precompr2 are violated, true otherwise.
*/
bool
Hacl_Bignum32_mod_exp_consttime(
  uint32_t len,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  uint32_t is_valid_m = Hacl_Bignum_Exponentiation_bn_check_mod_exp_u32(len, n, a, bBits, b);
  uint32_t nBits = (uint32_t)32U * Hacl_Bignum_Lib_bn_get_top_index_u32(len, n);
  if (is_valid_m == (uint32_t)0xFFFFFFFFU)
  {
    KRML_CHECK_SIZE(sizeof (uint32_t), len);
    {
      uint32_t r2[len];
      memset(r2, 0U, len * sizeof (uint32_t));
      memset(r2, 0U, len * sizeof (uint32_t));
      {
        uint32_t i = nBits / (uint32_t)32U;
        uint32_t j = nBits % (uint32_t)32U;
        r2[i] = r2[i] | (uint32_t)1U << j;
        {
          uint32_t i0;
          for (i0 = (uint32_t)0U; i0 < (uint32_t)64U * len - nBits; i0++)
          {
            Hacl_Bignum_bn_add_mod_n_u32(len, n, r2, r2, r2);
          }
        }
        Hacl_Bignum32_mod_exp_consttime_precompr2(len, n, a, bBits, b, r2, res);
      }
    }
  }
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < len; i++)
    {
      uint32_t *os = res;
      uint32_t x = res[i];
      uint32_t x0 = is_valid_m & x;
      os[i] = x0;
    }
  }
  return is_valid_m == (uint32_t)0xFFFFFFFFU;
}

/*
Compute `2 ^ (64 * len) mod n`.

  The argument n points to `len` limbs of valid memory.
  The function returns a heap-allocated bignum of size `len`, or NULL if:
  • the allocation failed, or
  • n % 2 = 1 && 1 < n does not hold

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
uint32_t *Hacl_Bignum32_new_precompr2(uint32_t len, uint32_t *n)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  {
    uint32_t one[len];
    memset(one, 0U, len * sizeof (uint32_t));
    {
      uint32_t bit0;
      uint32_t m0;
      memset(one, 0U, len * sizeof (uint32_t));
      one[0U] = (uint32_t)1U;
      bit0 = n[0U] & (uint32_t)1U;
      m0 = (uint32_t)0U - bit0;
      {
        uint32_t acc = (uint32_t)0U;
        uint32_t m1;
        uint32_t is_valid_m;
        uint32_t *ite;
        {
          uint32_t i;
          for (i = (uint32_t)0U; i < len; i++)
          {
            uint32_t beq = FStar_UInt32_eq_mask(one[i], n[i]);
            uint32_t blt = ~FStar_UInt32_gte_mask(one[i], n[i]);
            acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
          }
        }
        m1 = acc;
        is_valid_m = m0 & m1;
        if (!(is_valid_m == (uint32_t)0xFFFFFFFFU))
        {
          ite = NULL;
        }
        else
        {
          KRML_CHECK_SIZE(sizeof (uint32_t), len);
          {
            uint32_t *res = KRML_HOST_CALLOC(len, sizeof (uint32_t));
            if (res == NULL)
            {
              ite = res;
            }
            else
            {
              uint32_t *res1 = res;
              uint32_t *res2 = res1;
              uint32_t nBits = (uint32_t)32U * Hacl_Bignum_Lib_bn_get_top_index_u32(len, n);
              memset(res2, 0U, len * sizeof (uint32_t));
              {
                uint32_t i = nBits / (uint32_t)32U;
                uint32_t j = nBits % (uint32_t)32U;
                res2[i] = res2[i] | (uint32_t)1U << j;
                {
                  uint32_t i0;
                  for (i0 = (uint32_t)0U; i0 < (uint32_t)64U * len - nBits; i0++)
                  {
                    Hacl_Bignum_bn_add_mod_n_u32(len, n, res2, res2, res2);
                  }
                }
                ite = res2;
              }
            }
          }
        }
        return ite;
      }
    }
  }
}

/*
Write `a ^ (-1) mod n` in `res`.

  The arguments a, n and the outparam res are meant to be `len` limbs in size, i.e. uint32_t[len].

  This function is *UNSAFE* and requires C clients to observe bn_mod_inv_prime_pre
  from Hacl.Spec.Bignum.ModInv.fst, which amounts to:
  • n is a prime

  The function returns false if any of the following preconditions are violated, true otherwise.
  • n % 2 = 1
  • 1 < n
  • 0 < a
  • a < n 
*/
bool Hacl_Bignum32_mod_inv_prime_vartime(uint32_t len, uint32_t *n, uint32_t *a, uint32_t *res)
{
  uint32_t m0 = Hacl_Bignum_Montgomery_bn_check_modulus_u32(len, n);
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  {
    uint32_t bn_zero[len];
    memset(bn_zero, 0U, len * sizeof (uint32_t));
    {
      uint32_t mask = (uint32_t)0xFFFFFFFFU;
      uint32_t mask1;
      uint32_t res10;
      uint32_t m1;
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < len; i++)
        {
          uint32_t uu____0 = FStar_UInt32_eq_mask(a[i], bn_zero[i]);
          mask = uu____0 & mask;
        }
      }
      mask1 = mask;
      res10 = mask1;
      m1 = res10;
      {
        uint32_t acc = (uint32_t)0U;
        uint32_t m2;
        uint32_t is_valid_m;
        uint32_t nBits;
        {
          uint32_t i;
          for (i = (uint32_t)0U; i < len; i++)
          {
            uint32_t beq = FStar_UInt32_eq_mask(a[i], n[i]);
            uint32_t blt = ~FStar_UInt32_gte_mask(a[i], n[i]);
            acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
          }
        }
        m2 = acc;
        is_valid_m = (m0 & ~m1) & m2;
        nBits = (uint32_t)32U * Hacl_Bignum_Lib_bn_get_top_index_u32(len, n);
        if (is_valid_m == (uint32_t)0xFFFFFFFFU)
        {
          KRML_CHECK_SIZE(sizeof (uint32_t), len);
          {
            uint32_t n2[len];
            memset(n2, 0U, len * sizeof (uint32_t));
            {
              uint32_t
              c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32((uint32_t)0U, n[0U], (uint32_t)2U, n2);
              uint32_t c1;
              if ((uint32_t)1U < len)
              {
                uint32_t rLen = len - (uint32_t)1U;
                uint32_t *a1 = n + (uint32_t)1U;
                uint32_t *res1 = n2 + (uint32_t)1U;
                uint32_t c = c0;
                {
                  uint32_t i;
                  for (i = (uint32_t)0U; i < rLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
                  {
                    uint32_t t1 = a1[(uint32_t)4U * i];
                    uint32_t *res_i0 = res1 + (uint32_t)4U * i;
                    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, (uint32_t)0U, res_i0);
                    {
                      uint32_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
                      uint32_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
                      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, (uint32_t)0U, res_i1);
                      {
                        uint32_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
                        uint32_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
                        c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, (uint32_t)0U, res_i2);
                        {
                          uint32_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
                          uint32_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
                          c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t12, (uint32_t)0U, res_i);
                        }
                      }
                    }
                  }
                }
                {
                  uint32_t i;
                  for (i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
                  {
                    uint32_t t1 = a1[i];
                    uint32_t *res_i = res1 + i;
                    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, (uint32_t)0U, res_i);
                  }
                }
                {
                  uint32_t c10 = c;
                  c1 = c10;
                }
              }
              else
              {
                c1 = c0;
              }
              KRML_CHECK_SIZE(sizeof (uint32_t), len);
              {
                uint32_t r2[len];
                memset(r2, 0U, len * sizeof (uint32_t));
                memset(r2, 0U, len * sizeof (uint32_t));
                {
                  uint32_t i = nBits / (uint32_t)32U;
                  uint32_t j = nBits % (uint32_t)32U;
                  r2[i] = r2[i] | (uint32_t)1U << j;
                  {
                    uint32_t i0;
                    for (i0 = (uint32_t)0U; i0 < (uint32_t)64U * len - nBits; i0++)
                    {
                      Hacl_Bignum_bn_add_mod_n_u32(len, n, r2, r2, r2);
                    }
                  }
                  Hacl_Bignum32_mod_exp_vartime_precompr2(len,
                    n,
                    a,
                    (uint32_t)32U * len,
                    n2,
                    r2,
                    res);
                }
              }
            }
          }
        }
        {
          uint32_t i;
          for (i = (uint32_t)0U; i < len; i++)
          {
            uint32_t *os = res;
            uint32_t x = res[i];
            uint32_t x0 = is_valid_m & x;
            os[i] = x0;
          }
        }
        return is_valid_m == (uint32_t)0xFFFFFFFFU;
      }
    }
  }
}


/********************/
/* Loads and stores */
/********************/


/*
Load a bid-endian bignum from memory.

  The argument b points to `len` bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
uint32_t *Hacl_Bignum32_new_bn_from_bytes_be(uint32_t len, uint8_t *b)
{
  if
  (
    len
    == (uint32_t)0U
    || !((len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U <= (uint32_t)1073741823U)
  )
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), (len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U);
  {
    uint32_t
    *res = KRML_HOST_CALLOC((len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U, sizeof (uint32_t));
    if (res == NULL)
    {
      return res;
    }
    {
      uint32_t *res1 = res;
      uint32_t *res2 = res1;
      uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U;
      uint32_t tmpLen = (uint32_t)4U * bnLen;
      KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
      {
        uint8_t tmp[tmpLen];
        memset(tmp, 0U, tmpLen * sizeof (uint8_t));
        memcpy(tmp + tmpLen - len, b, len * sizeof (uint8_t));
        {
          uint32_t i;
          for (i = (uint32_t)0U; i < bnLen; i++)
          {
            uint32_t *os = res2;
            uint32_t u = load32_be(tmp + (bnLen - i - (uint32_t)1U) * (uint32_t)4U);
            uint32_t x = u;
            os[i] = x;
          }
        }
        return res2;
      }
    }
  }
}

/*
Load a little-endian bignum from memory.

  The argument b points to `len` bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
uint32_t *Hacl_Bignum32_new_bn_from_bytes_le(uint32_t len, uint8_t *b)
{
  if
  (
    len
    == (uint32_t)0U
    || !((len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U <= (uint32_t)1073741823U)
  )
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), (len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U);
  {
    uint32_t
    *res = KRML_HOST_CALLOC((len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U, sizeof (uint32_t));
    if (res == NULL)
    {
      return res;
    }
    {
      uint32_t *res1 = res;
      uint32_t *res2 = res1;
      uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U;
      uint32_t tmpLen = (uint32_t)4U * bnLen;
      KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
      {
        uint8_t tmp[tmpLen];
        memset(tmp, 0U, tmpLen * sizeof (uint8_t));
        memcpy(tmp, b, len * sizeof (uint8_t));
        {
          uint32_t i;
          for (i = (uint32_t)0U; i < (len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U; i++)
          {
            uint32_t *os = res2;
            uint8_t *bj = tmp + i * (uint32_t)4U;
            uint32_t u = load32_le(bj);
            uint32_t r1 = u;
            uint32_t x = r1;
            os[i] = x;
          }
        }
        return res2;
      }
    }
  }
}

/*
Serialize a bignum into big-endian memory.

  The argument b points to a bignum of `32 * len` size.
  The outparam res points to `len` bytes of valid memory.
*/
void Hacl_Bignum32_bn_to_bytes_be(uint32_t len, uint32_t *b, uint8_t *res)
{
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)4U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  {
    uint8_t tmp[tmpLen];
    memset(tmp, 0U, tmpLen * sizeof (uint8_t));
    {
      uint32_t numb = (uint32_t)4U;
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < bnLen; i++)
        {
          store32_be(tmp + i * numb, b[bnLen - i - (uint32_t)1U]);
        }
      }
      memcpy(res, tmp + tmpLen - len, len * sizeof (uint8_t));
    }
  }
}

/*
Serialize a bignum into little-endian memory.

  The argument b points to a bignum of `32 * len` size.
  The outparam res points to `len` bytes of valid memory.
*/
void Hacl_Bignum32_bn_to_bytes_le(uint32_t len, uint32_t *b, uint8_t *res)
{
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)4U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  {
    uint8_t tmp[tmpLen];
    memset(tmp, 0U, tmpLen * sizeof (uint8_t));
    {
      uint32_t i;
      for (i = (uint32_t)0U; i < bnLen; i++)
      {
        store32_le(tmp + i * (uint32_t)4U, b[i]);
      }
    }
    memcpy(res, tmp, len * sizeof (uint8_t));
  }
}


/***************/
/* Comparisons */
/***************/


/*
Returns 2 ^ 32 - 1 if and only if argument a is strictly less than the argument b, otherwise returns 0.
*/
uint32_t Hacl_Bignum32_lt_mask(uint32_t len, uint32_t *a, uint32_t *b)
{
  uint32_t acc = (uint32_t)0U;
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < len; i++)
    {
      uint32_t beq = FStar_UInt32_eq_mask(a[i], b[i]);
      uint32_t blt = ~FStar_UInt32_gte_mask(a[i], b[i]);
      acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
    }
  }
  return acc;
}

