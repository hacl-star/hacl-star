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


#include "Hacl_Frodo_KEM.h"

static inline void matrix_add(u32 n1, u32 n2, u16 *a, u16 *b)
{
  u32 i;
  for (i = (u32)0U; i < n1; i++)
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < n2; i0++)
      a[i * n2 + i0] = a[i * n2 + i0] + b[i * n2 + i0];
  }
}

static inline void matrix_sub(u32 n1, u32 n2, u16 *a, u16 *b)
{
  u32 i;
  for (i = (u32)0U; i < n1; i++)
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < n2; i0++)
      b[i * n2 + i0] = a[i * n2 + i0] - b[i * n2 + i0];
  }
}

static inline void matrix_mul(u32 n1, u32 n2, u32 n3, u16 *a, u16 *b, u16 *c)
{
  u32 i0;
  for (i0 = (u32)0U; i0 < n1; i0++)
  {
    u32 i1;
    for (i1 = (u32)0U; i1 < n3; i1++)
    {
      u16 res = (u16)0U;
      {
        u32 i;
        for (i = (u32)0U; i < n2; i++)
        {
          u16 aij = a[i0 * n2 + i];
          u16 bjk = b[i * n3 + i1];
          u16 res0 = res;
          res = res0 + aij * bjk;
        }
      }
      c[i0 * n3 + i1] = res;
    }
  }
}

static inline void matrix_mul_s(u32 n1, u32 n2, u32 n3, u16 *a, u16 *b, u16 *c)
{
  u32 i0;
  for (i0 = (u32)0U; i0 < n1; i0++)
  {
    u32 i1;
    for (i1 = (u32)0U; i1 < n3; i1++)
    {
      u16 res = (u16)0U;
      {
        u32 i;
        for (i = (u32)0U; i < n2; i++)
        {
          u16 aij = a[i0 * n2 + i];
          u16 bjk = b[i1 * n2 + i];
          u16 res0 = res;
          res = res0 + aij * bjk;
        }
      }
      c[i0 * n3 + i1] = res;
    }
  }
}

static inline bool matrix_eq(u32 n1, u32 n2, u32 m, u16 *a, u16 *b)
{
  bool res = true;
  u32 n = n1 * n2;
  {
    u32 i;
    for (i = (u32)0U; i < n; i++)
    {
      u16 ai = a[i];
      u16 bi = b[i];
      bool a1 = res;
      res = a1 && ((u32)ai & (((u32)1U << m) - (u32)1U)) == ((u32)bi & (((u32)1U << m) - (u32)1U));
    }
  }
  return res;
}

static inline void matrix_to_lbytes(u32 n1, u32 n2, u16 *m, u8 *res)
{
  u32 n = n1 * n2;
  u32 i;
  for (i = (u32)0U; i < n; i++)
  {
    u8 *tmp = res + (u32)2U * i;
    store16_le(tmp, m[i]);
  }
}

static inline void matrix_from_lbytes(u32 n1, u32 n2, u8 *b, u16 *res)
{
  u32 n = n1 * n2;
  u32 i;
  for (i = (u32)0U; i < n; i++)
  {
    u16 u = load16_le(b + (u32)2U * i);
    res[i] = u;
  }
}

static inline void frodo_gen_matrix_cshake(u32 n, u32 seed_len, u8 *seed, u16 *res)
{
  KRML_CHECK_SIZE(sizeof (u8), (u32)2U * n);
  {
    u8 r[(u32)2U * n];
    memset(r, 0U, (u32)2U * n * sizeof (u8));
    memset(res, 0U, n * n * sizeof (u16));
    {
      u32 i;
      for (i = (u32)0U; i < n; i++)
      {
        u32 ctr = (u32)256U + i;
        u64 s[25U] = { 0U };
        s[0U] = (u64)0x10010001a801U | (u64)(u16)ctr << (u32)48U;
        Hacl_Impl_SHA3_state_permute(s);
        Hacl_Impl_SHA3_absorb(s, (u32)168U, seed_len, seed, (u8)0x04U);
        Hacl_Impl_SHA3_squeeze(s, (u32)168U, (u32)2U * n, r);
        {
          u32 i0;
          for (i0 = (u32)0U; i0 < n; i0++)
          {
            u8 *resij = r + (u32)2U * i0;
            u16 u = load16_le(resij);
            res[i * n + i0] = u;
          }
        }
      }
    }
  }
}

static const
u16
cdf_table[12U] =
  {
    (u16)4727U, (u16)13584U, (u16)20864U, (u16)26113U, (u16)29434U, (u16)31278U, (u16)32176U,
    (u16)32560U, (u16)32704U, (u16)32751U, (u16)32764U, (u16)32767U
  };

static inline u16 frodo_sample(u16 r)
{
  u16 prnd = r >> (u32)1U;
  u16 sign = r & (u16)1U;
  u16 sample = (u16)0U;
  u32 bound = (u32)11U;
  u16 sample00;
  {
    u32 i;
    for (i = (u32)0U; i < bound; i++)
    {
      u16 sample0 = sample;
      u16 ti = cdf_table[i];
      u16 samplei = (u16)(u32)(ti - prnd) >> (u32)15U;
      sample = samplei + sample0;
    }
  }
  sample00 = sample;
  return ((~sign + (u16)1U) ^ sample00) + sign;
}

static inline void
frodo_sample_matrix(u32 n1, u32 n2, u32 seed_len, u8 *seed, u16 ctr, u16 *res)
{
  KRML_CHECK_SIZE(sizeof (u8), (u32)2U * n1 * n2);
  {
    u8 r[(u32)2U * n1 * n2];
    memset(r, 0U, (u32)2U * n1 * n2 * sizeof (u8));
    {
      u64 s[25U] = { 0U };
      s[0U] = (u64)0x10010001a801U | (u64)ctr << (u32)48U;
      Hacl_Impl_SHA3_state_permute(s);
      Hacl_Impl_SHA3_absorb(s, (u32)168U, seed_len, seed, (u8)0x04U);
      Hacl_Impl_SHA3_squeeze(s, (u32)168U, (u32)2U * n1 * n2, r);
      memset(res, 0U, n1 * n2 * sizeof (u16));
      {
        u32 i0;
        for (i0 = (u32)0U; i0 < n1; i0++)
        {
          u32 i;
          for (i = (u32)0U; i < n2; i++)
          {
            u8 *resij = r + (u32)2U * (n2 * i0 + i);
            u16 u = load16_le(resij);
            res[i0 * n2 + i] = frodo_sample(u);
          }
        }
      }
    }
  }
}

static inline void frodo_pack(u32 n1, u32 n2, u32 d, u16 *a, u8 *res)
{
  u32 n = n1 * n2 / (u32)8U;
  u32 i;
  for (i = (u32)0U; i < n; i++)
  {
    u16 *a1 = a + (u32)8U * i;
    u8 *r = res + d * i;
    u16 maskd = (u16)((u32)1U << d) - (u16)1U;
    u8 v16[16U] = { 0U };
    u16 a0 = a1[0U] & maskd;
    u16 a11 = a1[1U] & maskd;
    u16 a2 = a1[2U] & maskd;
    u16 a3 = a1[3U] & maskd;
    u16 a4 = a1[4U] & maskd;
    u16 a5 = a1[5U] & maskd;
    u16 a6 = a1[6U] & maskd;
    u16 a7 = a1[7U] & maskd;
    uint128_t
    templong =
      (((((((uint128_t)(u64)a0 << (u32)7U * d | (uint128_t)(u64)a11 << (u32)6U * d)
      | (uint128_t)(u64)a2 << (u32)5U * d)
      | (uint128_t)(u64)a3 << (u32)4U * d)
      | (uint128_t)(u64)a4 << (u32)3U * d)
      | (uint128_t)(u64)a5 << (u32)2U * d)
      | (uint128_t)(u64)a6 << (u32)1U * d)
      | (uint128_t)(u64)a7 << (u32)0U * d;
    u8 *src;
    store128_be(v16, templong);
    src = v16 + (u32)16U - d;
    memcpy(r, src, d * sizeof (u8));
  }
}

static inline void frodo_unpack(u32 n1, u32 n2, u32 d, u8 *b, u16 *res)
{
  u32 n = n1 * n2 / (u32)8U;
  u32 i;
  for (i = (u32)0U; i < n; i++)
  {
    u8 *b1 = b + d * i;
    u16 *r = res + (u32)8U * i;
    u16 maskd = (u16)((u32)1U << d) - (u16)1U;
    u8 src[16U] = { 0U };
    uint128_t u;
    uint128_t templong;
    memcpy(src + (u32)16U - d, b1, d * sizeof (u8));
    u = load128_be(src);
    templong = u;
    r[0U] = (u16)(uint64_t)(templong >> (u32)7U * d) & maskd;
    r[1U] = (u16)(uint64_t)(templong >> (u32)6U * d) & maskd;
    r[2U] = (u16)(uint64_t)(templong >> (u32)5U * d) & maskd;
    r[3U] = (u16)(uint64_t)(templong >> (u32)4U * d) & maskd;
    r[4U] = (u16)(uint64_t)(templong >> (u32)3U * d) & maskd;
    r[5U] = (u16)(uint64_t)(templong >> (u32)2U * d) & maskd;
    r[6U] = (u16)(uint64_t)(templong >> (u32)1U * d) & maskd;
    r[7U] = (u16)(uint64_t)(templong >> (u32)0U * d) & maskd;
  }
}

static void randombytes_(u32 len, u8 *res)
{
  bool b = Lib_RandomBuffer_System_randombytes(res, len);
}

static u32 bytes_mu = (u32)16U;

static u32 crypto_publickeybytes = (u32)976U;

static u32 crypto_ciphertextbytes = (u32)1096U;

static inline void frodo_mul_add_as_plus_e_pack(u8 *seed_a, u8 *seed_e, u8 *b, u8 *s)
{
  u16 s_matrix[512U] = { 0U };
  frodo_sample_matrix((u32)64U, (u32)8U, (u32)16U, seed_e, (u16)1U, s_matrix);
  matrix_to_lbytes((u32)64U, (u32)8U, s_matrix, s);
  {
    u16 b_matrix[512U] = { 0U };
    u16 a_matrix[4096U] = { 0U };
    u16 e_matrix[512U] = { 0U };
    frodo_gen_matrix_cshake((u32)64U, (u32)16U, seed_a, a_matrix);
    frodo_sample_matrix((u32)64U, (u32)8U, (u32)16U, seed_e, (u16)2U, e_matrix);
    matrix_mul_s((u32)64U, (u32)64U, (u32)8U, a_matrix, s_matrix, b_matrix);
    matrix_add((u32)64U, (u32)8U, b_matrix, e_matrix);
    Lib_Memzero_clear_words_u16((u32)512U, e_matrix);
    frodo_pack((u32)64U, (u32)8U, (u32)15U, b_matrix, b);
    Lib_Memzero_clear_words_u16((u32)512U, s_matrix);
  }
}

static inline void frodo_key_encode(u32 b, u8 *a, u16 *res)
{
  u32 i0;
  for (i0 = (u32)0U; i0 < (u32)8U; i0++)
  {
    u8 v8[8U] = { 0U };
    u8 *chunk = a + i0 * b;
    u64 u;
    u64 x0;
    u64 x;
    u32 i;
    memcpy(v8, chunk, b * sizeof (u8));
    u = load64_le(v8);
    x0 = u;
    x = x0;
    for (i = (u32)0U; i < (u32)8U; i++)
    {
      u64 rk = x >> b * i & (((u64)1U << b) - (u64)1U);
      res[i0 * (u32)8U + i] = (u16)rk << ((u32)15U - b);
    }
  }
}

static inline void frodo_key_decode(u32 b, u16 *a, u8 *res)
{
  u32 i;
  for (i = (u32)0U; i < (u32)8U; i++)
  {
    u64 templong0 = (u64)0U;
    u64 templong;
    {
      u32 i0;
      for (i0 = (u32)0U; i0 < (u32)8U; i0++)
      {
        u16 aik = a[i * (u32)8U + i0];
        u16 res1 = (aik + ((u16)1U << ((u32)15U - b - (u32)1U))) >> ((u32)15U - b);
        templong0 = templong0 | (u64)(res1 & (((u16)1U << b) - (u16)1U)) << b * i0;
      }
    }
    templong = templong0;
    {
      u8 v8[8U] = { 0U };
      u8 *tmp;
      store64_le(v8, templong);
      tmp = v8;
      memcpy(res + i * b, tmp, b * sizeof (u8));
    }
  }
}

static inline void
frodo_mul_add_sb_plus_e_plus_mu(u8 *b, u8 *seed_e, u8 *coins, u16 *sp_matrix, u16 *v_matrix)
{
  u16 b_matrix[512U] = { 0U };
  u16 epp_matrix[64U] = { 0U };
  frodo_unpack((u32)64U, (u32)8U, (u32)15U, b, b_matrix);
  frodo_sample_matrix((u32)8U, (u32)8U, (u32)16U, seed_e, (u16)6U, epp_matrix);
  matrix_mul((u32)8U, (u32)64U, (u32)8U, sp_matrix, b_matrix, v_matrix);
  matrix_add((u32)8U, (u32)8U, v_matrix, epp_matrix);
  Lib_Memzero_clear_words_u16((u32)64U, epp_matrix);
  {
    u16 mu_encode[64U] = { 0U };
    frodo_key_encode((u32)2U, coins, mu_encode);
    matrix_add((u32)8U, (u32)8U, v_matrix, mu_encode);
  }
}

static inline void crypto_kem_enc_ct(u8 *pk, u8 *g, u8 *coins, u8 *ct)
{
  u8 *seed_a = pk;
  u8 *b = pk + (u32)16U;
  u8 *seed_e = g;
  u8 *d = g + (u32)32U;
  u16 sp_matrix[512U] = { 0U };
  u32 c1Len;
  u32 c2Len;
  u32 c12Len;
  u8 *c1;
  frodo_sample_matrix((u32)8U, (u32)64U, (u32)16U, seed_e, (u16)4U, sp_matrix);
  c1Len = (u32)960U;
  c2Len = (u32)120U;
  c12Len = c1Len + c2Len;
  c1 = ct;
  {
    u16 bp_matrix[512U] = { 0U };
    u16 a_matrix[4096U] = { 0U };
    u16 ep_matrix[512U] = { 0U };
    u8 *c2;
    frodo_gen_matrix_cshake((u32)64U, (u32)16U, seed_a, a_matrix);
    frodo_sample_matrix((u32)8U, (u32)64U, (u32)16U, seed_e, (u16)5U, ep_matrix);
    matrix_mul((u32)8U, (u32)64U, (u32)64U, sp_matrix, a_matrix, bp_matrix);
    matrix_add((u32)8U, (u32)64U, bp_matrix, ep_matrix);
    Lib_Memzero_clear_words_u16((u32)512U, ep_matrix);
    frodo_pack((u32)8U, (u32)64U, (u32)15U, bp_matrix, c1);
    c2 = ct + c1Len;
    {
      u16 v_matrix[64U] = { 0U };
      frodo_mul_add_sb_plus_e_plus_mu(b, seed_e, coins, sp_matrix, v_matrix);
      frodo_pack((u32)8U, (u32)8U, (u32)15U, v_matrix, c2);
      Lib_Memzero_clear_words_u16((u32)64U, v_matrix);
      memcpy(ct + c12Len, d, (u32)16U * sizeof (u8));
      Lib_Memzero_clear_words_u16((u32)512U, sp_matrix);
    }
  }
}

static inline void crypto_kem_enc_ss(u8 *g, u8 *ct, u8 *ss)
{
  u32 ss_init_len = crypto_ciphertextbytes + (u32)16U;
  KRML_CHECK_SIZE(sizeof (u8), ss_init_len);
  {
    u8 ss_init[ss_init_len];
    memset(ss_init, 0U, ss_init_len * sizeof (u8));
    {
      u8 *c12 = ct;
      u8 *kd = g + (u32)16U;
      memcpy(ss_init, c12, (crypto_ciphertextbytes - (u32)16U) * sizeof (u8));
      memcpy(ss_init + crypto_ciphertextbytes - (u32)16U, kd, (u32)32U * sizeof (u8));
      {
        u64 s[25U] = { 0U };
        s[0U] = (u64)0x10010001a801U | (u64)(u16)7U << (u32)48U;
        Hacl_Impl_SHA3_state_permute(s);
        Hacl_Impl_SHA3_absorb(s, (u32)168U, ss_init_len, ss_init, (u8)0x04U);
        Hacl_Impl_SHA3_squeeze(s, (u32)168U, (u32)16U, ss);
      }
    }
  }
}

u32 Hacl_Frodo_KEM_crypto_kem_keypair(u8 *pk, u8 *sk)
{
  u8 coins[48U] = { 0U };
  u8 *s;
  u8 *seed_e;
  u8 *z;
  u8 *seed_a;
  randombytes_((u32)48U, coins);
  s = coins;
  seed_e = coins + (u32)16U;
  z = coins + (u32)32U;
  seed_a = pk;
  {
    u64 s1[25U] = { 0U };
    u8 *b;
    u8 *s_bytes;
    s1[0U] = (u64)0x10010001a801U | (u64)(u16)0U << (u32)48U;
    Hacl_Impl_SHA3_state_permute(s1);
    Hacl_Impl_SHA3_absorb(s1, (u32)168U, (u32)16U, z, (u8)0x04U);
    Hacl_Impl_SHA3_squeeze(s1, (u32)168U, (u32)16U, seed_a);
    b = pk + (u32)16U;
    s_bytes = sk + (u32)16U + crypto_publickeybytes;
    frodo_mul_add_as_plus_e_pack(seed_a, seed_e, b, s_bytes);
    memcpy(sk, s, (u32)16U * sizeof (u8));
    memcpy(sk + (u32)16U, pk, crypto_publickeybytes * sizeof (u8));
    return (u32)0U;
  }
}

u32 Hacl_Frodo_KEM_crypto_kem_enc(u8 *ct, u8 *ss, u8 *pk)
{
  u8 coins[16U] = { 0U };
  randombytes_(bytes_mu, coins);
  {
    u8 g[48U] = { 0U };
    u8 pk_coins[992U] = { 0U };
    memcpy(pk_coins, pk, crypto_publickeybytes * sizeof (u8));
    memcpy(pk_coins + crypto_publickeybytes, coins, bytes_mu * sizeof (u8));
    {
      u64 s[25U] = { 0U };
      s[0U] = (u64)0x10010001a801U | (u64)(u16)3U << (u32)48U;
      Hacl_Impl_SHA3_state_permute(s);
      Hacl_Impl_SHA3_absorb(s, (u32)168U, crypto_publickeybytes + bytes_mu, pk_coins, (u8)0x04U);
      Hacl_Impl_SHA3_squeeze(s, (u32)168U, (u32)48U, g);
      crypto_kem_enc_ct(pk, g, coins, ct);
      crypto_kem_enc_ss(g, ct, ss);
      Lib_Memzero_clear_words_u8((u32)32U, g);
      return (u32)0U;
    }
  }
}

u32 Hacl_Frodo_KEM_crypto_kem_dec(u8 *ss, u8 *ct, u8 *sk)
{
  u16 bp_matrix[512U] = { 0U };
  u16 c_matrix[64U] = { 0U };
  u8 mu_decode[16U] = { 0U };
  u32 c1Len = (u32)960U;
  u8 *c1 = ct;
  u8 *c2 = ct + c1Len;
  u8 *s_bytes;
  frodo_unpack((u32)8U, (u32)64U, (u32)15U, c1, bp_matrix);
  frodo_unpack((u32)8U, (u32)8U, (u32)15U, c2, c_matrix);
  s_bytes = sk + (u32)16U + crypto_publickeybytes;
  {
    u8 mu_decode1[16U] = { 0U };
    u16 s_matrix[512U] = { 0U };
    u16 m_matrix[64U] = { 0U };
    matrix_from_lbytes((u32)64U, (u32)8U, s_bytes, s_matrix);
    matrix_mul_s((u32)8U, (u32)64U, (u32)8U, bp_matrix, s_matrix, m_matrix);
    matrix_sub((u32)8U, (u32)8U, c_matrix, m_matrix);
    frodo_key_decode((u32)2U, m_matrix, mu_decode1);
    {
      u8 g[48U] = { 0U };
      u32 pk_mu_decode_len = crypto_publickeybytes + bytes_mu;
      KRML_CHECK_SIZE(sizeof (u8), pk_mu_decode_len);
      {
        u8 pk_mu_decode[pk_mu_decode_len];
        memset(pk_mu_decode, 0U, pk_mu_decode_len * sizeof (u8));
        {
          u8 *pk0 = sk + (u32)16U;
          memcpy(pk_mu_decode, pk0, crypto_publickeybytes * sizeof (u8));
          memcpy(pk_mu_decode + crypto_publickeybytes, mu_decode1, bytes_mu * sizeof (u8));
          {
            u64 s0[25U] = { 0U };
            s0[0U] = (u64)0x10010001a801U | (u64)(u16)3U << (u32)48U;
            Hacl_Impl_SHA3_state_permute(s0);
            Hacl_Impl_SHA3_absorb(s0, (u32)168U, pk_mu_decode_len, pk_mu_decode, (u8)0x04U);
            Hacl_Impl_SHA3_squeeze(s0, (u32)168U, (u32)48U, g);
            {
              u8 *dp = g + (u32)32U;
              u8 *d0 = ct + crypto_ciphertextbytes - (u32)16U;
              u16 bpp_matrix[512U] = { 0U };
              u16 cp_matrix[64U] = { 0U };
              u8 *pk = sk + (u32)16U;
              u8 *seed_a = pk;
              u8 *b0 = pk + (u32)16U;
              u8 *seed_ep = g;
              u16 sp_matrix[512U] = { 0U };
              frodo_sample_matrix((u32)8U, (u32)64U, (u32)16U, seed_ep, (u16)4U, sp_matrix);
              {
                u16 a_matrix[4096U] = { 0U };
                u16 ep_matrix[512U] = { 0U };
                frodo_gen_matrix_cshake((u32)64U, (u32)16U, seed_a, a_matrix);
                frodo_sample_matrix((u32)8U, (u32)64U, (u32)16U, seed_ep, (u16)5U, ep_matrix);
                matrix_mul((u32)8U, (u32)64U, (u32)64U, sp_matrix, a_matrix, bpp_matrix);
                matrix_add((u32)8U, (u32)64U, bpp_matrix, ep_matrix);
                Lib_Memzero_clear_words_u16((u32)512U, ep_matrix);
                frodo_mul_add_sb_plus_e_plus_mu(b0, seed_ep, mu_decode1, sp_matrix, cp_matrix);
                Lib_Memzero_clear_words_u16((u32)512U, sp_matrix);
                {
                  u8 res = (u8)255U;
                  u8 z;
                  bool b1;
                  bool b2;
                  bool b3;
                  bool b4;
                  bool b;
                  u8 *kp;
                  u8 *s;
                  u8 *kp_s;
                  {
                    u32 i;
                    for (i = (u32)0U; i < (u32)16U; i++)
                    {
                      u8 uu____0 = FStar_UInt8_eq_mask(d0[i], dp[i]);
                      res = uu____0 & res;
                    }
                  }
                  z = res;
                  b1 = z == (u8)255U;
                  b2 = matrix_eq((u32)8U, (u32)64U, (u32)15U, bp_matrix, bpp_matrix);
                  b3 = matrix_eq((u32)8U, (u32)8U, (u32)15U, c_matrix, cp_matrix);
                  b4 = b1 && b2 && b3;
                  b = b4;
                  kp = g + (u32)16U;
                  s = sk;
                  if (b)
                    kp_s = kp;
                  else
                    kp_s = s;
                  {
                    u8 *c12 = ct;
                    u8 *d = ct + crypto_ciphertextbytes - (u32)16U;
                    u32 ss_init_len = crypto_ciphertextbytes + (u32)16U;
                    KRML_CHECK_SIZE(sizeof (u8), ss_init_len);
                    {
                      u8 ss_init[ss_init_len];
                      memset(ss_init, 0U, ss_init_len * sizeof (u8));
                      memcpy(ss_init, c12, (crypto_ciphertextbytes - (u32)16U) * sizeof (u8));
                      memcpy(ss_init + crypto_ciphertextbytes - (u32)16U,
                        kp_s,
                        (u32)16U * sizeof (u8));
                      memcpy(ss_init + crypto_ciphertextbytes - (u32)16U + (u32)16U,
                        d,
                        (u32)16U * sizeof (u8));
                      {
                        u64 s1[25U] = { 0U };
                        s1[0U] = (u64)0x10010001a801U | (u64)(u16)7U << (u32)48U;
                        Hacl_Impl_SHA3_state_permute(s1);
                        Hacl_Impl_SHA3_absorb(s1, (u32)168U, ss_init_len, ss_init, (u8)0x04U);
                        Hacl_Impl_SHA3_squeeze(s1, (u32)168U, (u32)16U, ss);
                        Lib_Memzero_clear_words_u8((u32)32U, g);
                        return (u32)0U;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

