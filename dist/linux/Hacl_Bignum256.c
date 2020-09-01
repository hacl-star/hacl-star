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


#include "Hacl_Bignum256.h"

/************************/
/* Arithmetic functions */
/************************/


/*
Write `a + b mod 2^256` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 256-bit bignums, i.e. uint64_t[4]
*/
u64 Hacl_Bignum256_add(u64 *a, u64 *b, u64 *res)
{
  u64 c = (u64)0U;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)4U; i++)
    {
      u64 t1 = a[i];
      u64 t2 = b[i];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t2, res + i);
    }
  }
  return c;
}

/*
Write `a - b mod 2^256` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 256-bit bignums, i.e. uint64_t[4]
*/
u64 Hacl_Bignum256_sub(u64 *a, u64 *b, u64 *res)
{
  u64 c = (u64)0U;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)4U; i++)
    {
      u64 t1 = a[i];
      u64 t2 = b[i];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res + i);
    }
  }
  return c;
}

/*
Write `a * b` in `res`.

  The arguments a and b are meant to be 256-bit bignums, i.e. uint64_t[4].
  The outparam res is meant to be a 512-bit bignum, i.e. uint64_t[8].
*/
void Hacl_Bignum256_mul(u64 *a, u64 *b, u64 *res)
{
  u32 resLen = (u32)8U;
  u32 i;
  memset(res, 0U, resLen * sizeof (u64));
  for (i = (u32)0U; i < (u32)4U; i++)
  {
    u64 uu____0 = b[i];
    u64 *res_ = res + i;
    u64 c = (u64)0U;
    u64 r;
    {
      u32 i0;
      for (i0 = (u32)0U; i0 < (u32)4U; i0++)
        c = Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c, a[i0], uu____0, res_ + i0);
    }
    r = c;
    res[(u32)4U + i] = r;
  }
}

static void bit_set(u64 *input, u32 ind)
{
  u32 i = ind / (u32)64U;
  u32 j = ind % (u32)64U;
  input[i] = input[i] | (u64)1U << j;
}

static void add_mod_n(u64 *n, u64 *a, u64 *b, u64 *res)
{
  u64 tmp[4U] = { 0U };
  u64 c2 = (u64)0U;
  u64 c0;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)4U; i++)
    {
      u64 t1 = a[i];
      u64 t2 = b[i];
      c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t1, t2, res + i);
    }
  }
  c0 = c2;
  {
    u64 c3 = (u64)0U;
    u64 c1;
    u64 c;
    {
      u32 i;
      for (i = (u32)0U; i < (u32)4U; i++)
      {
        u64 t1 = res[i];
        u64 t2 = n[i];
        c3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c3, t1, t2, tmp + i);
      }
    }
    c1 = c3;
    c = c0 - c1;
    {
      u32 i;
      for (i = (u32)0U; i < (u32)4U; i++)
      {
        u64 *os = res;
        u64 x = (c & res[i]) | (~c & tmp[i]);
        os[i] = x;
      }
    }
  }
}

static void sub_mask(u64 *n, u64 *a)
{
  u64 mask = (u64)0xFFFFFFFFFFFFFFFFU;
  u64 mod_mask[4U] = { 0U };
  u64 mask1;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)4U; i++)
    {
      u64 uu____0 = FStar_UInt64_eq_mask(n[i], a[i]);
      mask = uu____0 & mask;
    }
  }
  mask1 = mask;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)4U; i++)
    {
      u64 *os = mod_mask;
      u64 x = n[i];
      u64 x0 = mask1 & x;
      os[i] = x0;
    }
  }
  {
    u64 c = (u64)0U;
    u64 uu____1;
    {
      u32 i;
      for (i = (u32)0U; i < (u32)4U; i++)
      {
        u64 t1 = a[i];
        u64 t2 = mod_mask[i];
        c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, a + i);
      }
    }
    uu____1 = c;
  }
}

static void mul_(u64 *a, u64 *b, u64 *res)
{
  u32 resLen = (u32)10U;
  u32 i;
  memset(res, 0U, resLen * sizeof (u64));
  for (i = (u32)0U; i < (u32)5U; i++)
  {
    u64 uu____0 = b[i];
    u64 *res_ = res + i;
    u64 c = (u64)0U;
    u64 r;
    {
      u32 i0;
      for (i0 = (u32)0U; i0 < (u32)5U; i0++)
        c = Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c, a[i0], uu____0, res_ + i0);
    }
    r = c;
    res[(u32)5U + i] = r;
  }
}

static void precomp(u32 modBits, u64 *n, u64 *res)
{
  u32 i;
  memset(res, 0U, (u32)4U * sizeof (u64));
  bit_set(res, modBits - (u32)1U);
  for (i = (u32)0U; i < (u32)641U - modBits; i++)
    add_mod_n(n, res, res, res);
}

static void reduction(u64 *n, u64 nInv_u64, u64 *c, u64 *res)
{
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < (u32)4U + (u32)1U; i0++)
    {
      u64 qj = nInv_u64 * c[i0];
      u64 *res_ = c + i0;
      u64 c1 = (u64)0U;
      {
        u32 i;
        for (i = (u32)0U; i < (u32)4U; i++)
          c1 = Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c1, n[i], qj, res_ + i);
      }
      {
        u64 r0 = c1;
        u64 c10 = r0;
        u64 c2 = c10;
        u64 *res2 = c + i0 + (u32)4U;
        u64 *a0 = res2;
        u64 *res0 = res2;
        u64 c30 = (u64)0U;
        {
          u32 i;
          for (i = (u32)0U; i < (u32)1U; i++)
          {
            u64 t1 = a0[i];
            u64 t2 = (&c2)[i];
            c30 = Lib_IntTypes_Intrinsics_add_carry_u64(c30, t1, t2, res0 + i);
          }
        }
        {
          u64 c0 = c30;
          u64 r;
          if ((u32)1U < (u32)4U + (u32)1U + (u32)4U + (u32)1U - i0 - (u32)4U)
          {
            u32 rLen = (u32)4U + (u32)1U + (u32)4U + (u32)1U - i0 - (u32)4U - (u32)1U;
            u64 *a1 = res2 + (u32)1U;
            u64 *res1 = res2 + (u32)1U;
            u64 c3 = c0;
            {
              u32 i;
              for (i = (u32)0U; i < rLen; i++)
              {
                u64 t1 = a1[i];
                c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c3, t1, (u64)0U, res1 + i);
              }
            }
            {
              u64 c11 = c3;
              r = c11;
            }
          }
          else
            r = c0;
          {
            u64 uu____0 = r;
          }
        }
      }
    }
  }
  memcpy(res,
    c + (u32)4U + (u32)1U,
    ((u32)4U + (u32)1U + (u32)4U + (u32)1U - ((u32)4U + (u32)1U)) * sizeof (u64));
}

static void to(u64 *n, u64 nInv_u64, u64 *r2, u64 *a, u64 *aM)
{
  KRML_CHECK_SIZE(sizeof (u64), (u32)4U + (u32)1U + (u32)4U + (u32)1U);
  {
    u64 tmp[(u32)4U + (u32)1U + (u32)4U + (u32)1U];
    memset(tmp, 0U, ((u32)4U + (u32)1U + (u32)4U + (u32)1U) * sizeof (u64));
    {
      u64 *c = tmp;
      Hacl_Bignum256_mul(a, r2, c);
      reduction(n, nInv_u64, tmp, aM);
    }
  }
}

static void from(u64 *n, u64 nInv_u64, u64 *aM, u64 *a)
{
  KRML_CHECK_SIZE(sizeof (u64), (u32)4U + (u32)1U + (u32)4U + (u32)1U);
  {
    u64 tmp[(u32)4U + (u32)1U + (u32)4U + (u32)1U];
    memset(tmp, 0U, ((u32)4U + (u32)1U + (u32)4U + (u32)1U) * sizeof (u64));
    memcpy(tmp, aM, ((u32)4U + (u32)1U) * sizeof (u64));
    KRML_CHECK_SIZE(sizeof (u64), (u32)4U + (u32)1U);
    {
      u64 a_[(u32)4U + (u32)1U];
      memset(a_, 0U, ((u32)4U + (u32)1U) * sizeof (u64));
      reduction(n, nInv_u64, tmp, a_);
      memcpy(a, a_, (u32)4U * sizeof (u64));
    }
  }
}

static void mont_mul(u64 *n, u64 nInv_u64, u64 *aM, u64 *bM, u64 *resM)
{
  KRML_CHECK_SIZE(sizeof (u64), (u32)4U + (u32)1U + (u32)4U + (u32)1U);
  {
    u64 c[(u32)4U + (u32)1U + (u32)4U + (u32)1U];
    memset(c, 0U, ((u32)4U + (u32)1U + (u32)4U + (u32)1U) * sizeof (u64));
    mul_(aM, bM, c);
    reduction(n, nInv_u64, c, resM);
  }
}

static void mod_exp_loop(u64 *n, u64 nInv_u64, u32 bBits, u32 bLen, u64 *b, u64 *aM, u64 *accM)
{
  u32 i;
  for (i = (u32)0U; i < bBits; i++)
  {
    if (Hacl_Bignum_bn_is_bit_set(bLen, b, i))
      mont_mul(n, nInv_u64, aM, accM, accM);
    mont_mul(n, nInv_u64, aM, aM, aM);
  }
}

/*
Write `a ^ b mod n1` in `res`.

  The arguments a, n1 and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. For instance, if b is a 256-bit bignum,
  bBits should be 256.
*/
void Hacl_Bignum256_mod_exp(u64 *n, u64 *a, u32 bBits, u64 *b, u64 *res)
{
  u64 acc[4U] = { 0U };
  memset(acc, 0U, (u32)4U * sizeof (u64));
  acc[0U] = (u64)1U;
  {
    u32 rLen = (u32)5U;
    u32 bLen = (bBits - (u32)1U) / (u32)64U + (u32)1U;
    u64 nInv_u64 = Hacl_Bignum_ModInv64_mod_inv_u64(n[0U]);
    u64 r2[4U] = { 0U };
    precomp((u32)256U, n, r2);
    KRML_CHECK_SIZE(sizeof (u64), rLen);
    {
      u64 aM[rLen];
      memset(aM, 0U, rLen * sizeof (u64));
      KRML_CHECK_SIZE(sizeof (u64), rLen);
      {
        u64 accM[rLen];
        memset(accM, 0U, rLen * sizeof (u64));
        to(n, nInv_u64, r2, a, aM);
        to(n, nInv_u64, r2, acc, accM);
        mod_exp_loop(n, nInv_u64, bBits, bLen, b, aM, accM);
        from(n, nInv_u64, accM, res);
        sub_mask(n, res);
      }
    }
  }
}


/********************/
/* Loads and stores */
/********************/


/*
Load a bid-endian bignum from memory.

  The argument b points to len bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
    result of loading b, or NULL if the amount of required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
u64 *Hacl_Bignum256_new_bn_from_bytes_be(u32 len, u8 *b)
{
  if (len == (u32)0U || !((len - (u32)1U) / (u32)8U + (u32)1U <= (u32)536870911U))
    return NULL;
  KRML_CHECK_SIZE(sizeof (u64), (len - (u32)1U) / (u32)8U + (u32)1U);
  {
    u64 *res = KRML_HOST_CALLOC((len - (u32)1U) / (u32)8U + (u32)1U, sizeof (u64));
    u64 *res1 = res;
    u64 *res2 = res1;
    u32 bnLen = (len - (u32)1U) / (u32)8U + (u32)1U;
    u32 tmpLen = (u32)8U * bnLen;
    KRML_CHECK_SIZE(sizeof (u8), tmpLen);
    {
      u8 tmp[tmpLen];
      memset(tmp, 0U, tmpLen * sizeof (u8));
      memcpy(tmp + tmpLen - len, b, len * sizeof (u8));
      {
        u32 i;
        for (i = (u32)0U; i < bnLen; i++)
        {
          u64 *os = res2;
          u64 u = load64_be(tmp + (bnLen - i - (u32)1U) * (u32)8U);
          u64 x = u;
          os[i] = x;
        }
      }
      return res2;
    }
  }
}

/*
Serialize a bignum into big-endian memory.

  The argument b points to a 256-bit bignum.
  The outparam res points to 32 bytes of valid memory.
*/
void Hacl_Bignum256_bn_to_bytes_be(u64 *b, u8 *res)
{
  u32 bnLen = ((u32)32U - (u32)1U) / (u32)8U + (u32)1U;
  u32 tmpLen = (u32)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (u8), tmpLen);
  {
    u8 tmp[tmpLen];
    memset(tmp, 0U, tmpLen * sizeof (u8));
    {
      u32 i;
      for (i = (u32)0U; i < bnLen; i++)
        store64_be(tmp + i * (u32)8U, b[bnLen - i - (u32)1U]);
    }
    memcpy(res, tmp + tmpLen - (u32)32U, (u32)32U * sizeof (u8));
  }
}


/***************/
/* Comparisons */
/***************/


/*
Returns true if and only if argument a is strictly less than the argument b.
*/
bool Hacl_Bignum256_lt(u64 *a, u64 *b)
{
  u64 acc = (u64)0U;
  u64 mask;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)4U; i++)
    {
      u64 beq = FStar_UInt64_eq_mask(a[i], b[i]);
      u64 blt = ~FStar_UInt64_gte_mask(a[i], b[i]);
      acc = (beq & acc) | (~beq & ((blt & (u64)0xFFFFFFFFFFFFFFFFU) | (~blt & (u64)0U)));
    }
  }
  mask = acc;
  return mask == (u64)0xFFFFFFFFFFFFFFFFU;
}

