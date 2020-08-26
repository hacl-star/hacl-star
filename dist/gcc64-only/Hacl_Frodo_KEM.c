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

static inline void matrix_add(uint32_t n1, uint32_t n2, uint16_t *a, uint16_t *b)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < n1; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < n2; i++)
    {
      a[i0 * n2 + i] = a[i0 * n2 + i] + b[i0 * n2 + i];
    }
  }
}

static inline void matrix_sub(uint32_t n1, uint32_t n2, uint16_t *a, uint16_t *b)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < n1; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < n2; i++)
    {
      b[i0 * n2 + i] = a[i0 * n2 + i] - b[i0 * n2 + i];
    }
  }
}

static inline void
matrix_mul(uint32_t n1, uint32_t n2, uint32_t n3, uint16_t *a, uint16_t *b, uint16_t *c)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < n1; i0++)
  {
    for (uint32_t i1 = (uint32_t)0U; i1 < n3; i1++)
    {
      uint16_t res = (uint16_t)0U;
      for (uint32_t i = (uint32_t)0U; i < n2; i++)
      {
        uint16_t aij = a[i0 * n2 + i];
        uint16_t bjk = b[i * n3 + i1];
        uint16_t res0 = res;
        res = res0 + aij * bjk;
      }
      c[i0 * n3 + i1] = res;
    }
  }
}

static inline void
matrix_mul_s(uint32_t n1, uint32_t n2, uint32_t n3, uint16_t *a, uint16_t *b, uint16_t *c)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < n1; i0++)
  {
    for (uint32_t i1 = (uint32_t)0U; i1 < n3; i1++)
    {
      uint16_t res = (uint16_t)0U;
      for (uint32_t i = (uint32_t)0U; i < n2; i++)
      {
        uint16_t aij = a[i0 * n2 + i];
        uint16_t bjk = b[i1 * n2 + i];
        uint16_t res0 = res;
        res = res0 + aij * bjk;
      }
      c[i0 * n3 + i1] = res;
    }
  }
}

static inline bool matrix_eq(uint32_t n1, uint32_t n2, uint32_t m, uint16_t *a, uint16_t *b)
{
  bool res = true;
  uint32_t n = n1 * n2;
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    uint16_t ai = a[i];
    uint16_t bi = b[i];
    bool a1 = res;
    res =
      a1
      &&
        ((uint32_t)ai & (((uint32_t)1U << m) - (uint32_t)1U))
        == ((uint32_t)bi & (((uint32_t)1U << m) - (uint32_t)1U));
  }
  return res;
}

static inline void matrix_to_lbytes(uint32_t n1, uint32_t n2, uint16_t *m, uint8_t *res)
{
  uint32_t n = n1 * n2;
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    uint8_t *tmp = res + (uint32_t)2U * i;
    store16_le(tmp, m[i]);
  }
}

static inline void matrix_from_lbytes(uint32_t n1, uint32_t n2, uint8_t *b, uint16_t *res)
{
  uint32_t n = n1 * n2;
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    uint16_t u = load16_le(b + (uint32_t)2U * i);
    res[i] = u;
  }
}

static inline void
frodo_gen_matrix_cshake(uint32_t n, uint32_t seed_len, uint8_t *seed, uint16_t *res)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)2U * n);
  uint8_t r[(uint32_t)2U * n];
  memset(r, 0U, (uint32_t)2U * n * sizeof (uint8_t));
  memset(res, 0U, n * n * sizeof (uint16_t));
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    uint32_t ctr = (uint32_t)256U + i;
    uint64_t s[25U] = { 0U };
    s[0U] = (uint64_t)0x10010001a801U | (uint64_t)(uint16_t)ctr << (uint32_t)48U;
    Hacl_Impl_SHA3_state_permute(s);
    Hacl_Impl_SHA3_absorb(s, (uint32_t)168U, seed_len, seed, (uint8_t)0x04U);
    Hacl_Impl_SHA3_squeeze(s, (uint32_t)168U, (uint32_t)2U * n, r);
    for (uint32_t i0 = (uint32_t)0U; i0 < n; i0++)
    {
      uint8_t *resij = r + (uint32_t)2U * i0;
      uint16_t u = load16_le(resij);
      res[i * n + i0] = u;
    }
  }
}

static const
uint16_t
cdf_table[12U] =
  {
    (uint16_t)4727U, (uint16_t)13584U, (uint16_t)20864U, (uint16_t)26113U, (uint16_t)29434U,
    (uint16_t)31278U, (uint16_t)32176U, (uint16_t)32560U, (uint16_t)32704U, (uint16_t)32751U,
    (uint16_t)32764U, (uint16_t)32767U
  };

static inline uint16_t frodo_sample(uint16_t r)
{
  uint16_t prnd = r >> (uint32_t)1U;
  uint16_t sign = r & (uint16_t)1U;
  uint16_t sample = (uint16_t)0U;
  uint32_t bound = (uint32_t)11U;
  for (uint32_t i = (uint32_t)0U; i < bound; i++)
  {
    uint16_t sample0 = sample;
    uint16_t ti = cdf_table[i];
    uint16_t samplei = (uint16_t)(uint32_t)(ti - prnd) >> (uint32_t)15U;
    sample = samplei + sample0;
  }
  uint16_t sample0 = sample;
  return ((~sign + (uint16_t)1U) ^ sample0) + sign;
}

static inline void
frodo_sample_matrix(
  uint32_t n1,
  uint32_t n2,
  uint32_t seed_len,
  uint8_t *seed,
  uint16_t ctr,
  uint16_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)2U * n1 * n2);
  uint8_t r[(uint32_t)2U * n1 * n2];
  memset(r, 0U, (uint32_t)2U * n1 * n2 * sizeof (uint8_t));
  uint64_t s[25U] = { 0U };
  s[0U] = (uint64_t)0x10010001a801U | (uint64_t)ctr << (uint32_t)48U;
  Hacl_Impl_SHA3_state_permute(s);
  Hacl_Impl_SHA3_absorb(s, (uint32_t)168U, seed_len, seed, (uint8_t)0x04U);
  Hacl_Impl_SHA3_squeeze(s, (uint32_t)168U, (uint32_t)2U * n1 * n2, r);
  memset(res, 0U, n1 * n2 * sizeof (uint16_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < n1; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < n2; i++)
    {
      uint8_t *resij = r + (uint32_t)2U * (n2 * i0 + i);
      uint16_t u = load16_le(resij);
      res[i0 * n2 + i] = frodo_sample(u);
    }
  }
}

static inline void frodo_pack(uint32_t n1, uint32_t n2, uint32_t d, uint16_t *a, uint8_t *res)
{
  uint32_t n = n1 * n2 / (uint32_t)8U;
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    uint16_t *a1 = a + (uint32_t)8U * i;
    uint8_t *r = res + d * i;
    uint16_t maskd = (uint16_t)((uint32_t)1U << d) - (uint16_t)1U;
    uint8_t v16[16U] = { 0U };
    uint16_t a0 = a1[0U] & maskd;
    uint16_t a11 = a1[1U] & maskd;
    uint16_t a2 = a1[2U] & maskd;
    uint16_t a3 = a1[3U] & maskd;
    uint16_t a4 = a1[4U] & maskd;
    uint16_t a5 = a1[5U] & maskd;
    uint16_t a6 = a1[6U] & maskd;
    uint16_t a7 = a1[7U] & maskd;
    uint128_t
    templong =
      (((((((uint128_t)(uint64_t)a0
      << (uint32_t)7U * d
      | (uint128_t)(uint64_t)a11 << (uint32_t)6U * d)
      | (uint128_t)(uint64_t)a2 << (uint32_t)5U * d)
      | (uint128_t)(uint64_t)a3 << (uint32_t)4U * d)
      | (uint128_t)(uint64_t)a4 << (uint32_t)3U * d)
      | (uint128_t)(uint64_t)a5 << (uint32_t)2U * d)
      | (uint128_t)(uint64_t)a6 << (uint32_t)1U * d)
      | (uint128_t)(uint64_t)a7 << (uint32_t)0U * d;
    store128_be(v16, templong);
    uint8_t *src = v16 + (uint32_t)16U - d;
    memcpy(r, src, d * sizeof (uint8_t));
  }
}

static inline void
frodo_unpack(uint32_t n1, uint32_t n2, uint32_t d, uint8_t *b, uint16_t *res)
{
  uint32_t n = n1 * n2 / (uint32_t)8U;
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    uint8_t *b1 = b + d * i;
    uint16_t *r = res + (uint32_t)8U * i;
    uint16_t maskd = (uint16_t)((uint32_t)1U << d) - (uint16_t)1U;
    uint8_t src[16U] = { 0U };
    memcpy(src + (uint32_t)16U - d, b1, d * sizeof (uint8_t));
    uint128_t u = load128_be(src);
    uint128_t templong = u;
    r[0U] = (uint16_t)(uint64_t)(templong >> (uint32_t)7U * d) & maskd;
    r[1U] = (uint16_t)(uint64_t)(templong >> (uint32_t)6U * d) & maskd;
    r[2U] = (uint16_t)(uint64_t)(templong >> (uint32_t)5U * d) & maskd;
    r[3U] = (uint16_t)(uint64_t)(templong >> (uint32_t)4U * d) & maskd;
    r[4U] = (uint16_t)(uint64_t)(templong >> (uint32_t)3U * d) & maskd;
    r[5U] = (uint16_t)(uint64_t)(templong >> (uint32_t)2U * d) & maskd;
    r[6U] = (uint16_t)(uint64_t)(templong >> (uint32_t)1U * d) & maskd;
    r[7U] = (uint16_t)(uint64_t)(templong >> (uint32_t)0U * d) & maskd;
  }
}

static void randombytes_(uint32_t len, uint8_t *res)
{
  bool b = Lib_RandomBuffer_System_randombytes(res, len);
}

static uint32_t bytes_mu = (uint32_t)16U;

static uint32_t crypto_publickeybytes = (uint32_t)976U;

static uint32_t crypto_ciphertextbytes = (uint32_t)1096U;

static inline void
frodo_mul_add_as_plus_e_pack(uint8_t *seed_a, uint8_t *seed_e, uint8_t *b, uint8_t *s)
{
  uint16_t s_matrix[512U] = { 0U };
  frodo_sample_matrix((uint32_t)64U,
    (uint32_t)8U,
    (uint32_t)16U,
    seed_e,
    (uint16_t)1U,
    s_matrix);
  matrix_to_lbytes((uint32_t)64U, (uint32_t)8U, s_matrix, s);
  uint16_t b_matrix[512U] = { 0U };
  uint16_t a_matrix[4096U] = { 0U };
  uint16_t e_matrix[512U] = { 0U };
  frodo_gen_matrix_cshake((uint32_t)64U, (uint32_t)16U, seed_a, a_matrix);
  frodo_sample_matrix((uint32_t)64U,
    (uint32_t)8U,
    (uint32_t)16U,
    seed_e,
    (uint16_t)2U,
    e_matrix);
  matrix_mul_s((uint32_t)64U, (uint32_t)64U, (uint32_t)8U, a_matrix, s_matrix, b_matrix);
  matrix_add((uint32_t)64U, (uint32_t)8U, b_matrix, e_matrix);
  Lib_Memzero_clear_words_u16((uint32_t)512U, e_matrix);
  frodo_pack((uint32_t)64U, (uint32_t)8U, (uint32_t)15U, b_matrix, b);
  Lib_Memzero_clear_words_u16((uint32_t)512U, s_matrix);
}

static inline void frodo_key_encode(uint32_t b, uint8_t *a, uint16_t *res)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)8U; i0++)
  {
    uint8_t v8[8U] = { 0U };
    uint8_t *chunk = a + i0 * b;
    memcpy(v8, chunk, b * sizeof (uint8_t));
    uint64_t u = load64_le(v8);
    uint64_t x = u;
    uint64_t x0 = x;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
    {
      uint64_t rk = x0 >> b * i & (((uint64_t)1U << b) - (uint64_t)1U);
      res[i0 * (uint32_t)8U + i] = (uint16_t)rk << ((uint32_t)15U - b);
    }
  }
}

static inline void frodo_key_decode(uint32_t b, uint16_t *a, uint8_t *res)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)8U; i0++)
  {
    uint64_t templong = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
    {
      uint16_t aik = a[i0 * (uint32_t)8U + i];
      uint16_t
      res1 = (aik + ((uint16_t)1U << ((uint32_t)15U - b - (uint32_t)1U))) >> ((uint32_t)15U - b);
      templong = templong | (uint64_t)(res1 & (((uint16_t)1U << b) - (uint16_t)1U)) << b * i;
    }
    uint64_t templong0 = templong;
    uint8_t v8[8U] = { 0U };
    store64_le(v8, templong0);
    uint8_t *tmp = v8;
    memcpy(res + i0 * b, tmp, b * sizeof (uint8_t));
  }
}

static inline void
frodo_mul_add_sb_plus_e_plus_mu(
  uint8_t *b,
  uint8_t *seed_e,
  uint8_t *coins,
  uint16_t *sp_matrix,
  uint16_t *v_matrix
)
{
  uint16_t b_matrix[512U] = { 0U };
  uint16_t epp_matrix[64U] = { 0U };
  frodo_unpack((uint32_t)64U, (uint32_t)8U, (uint32_t)15U, b, b_matrix);
  frodo_sample_matrix((uint32_t)8U,
    (uint32_t)8U,
    (uint32_t)16U,
    seed_e,
    (uint16_t)6U,
    epp_matrix);
  matrix_mul((uint32_t)8U, (uint32_t)64U, (uint32_t)8U, sp_matrix, b_matrix, v_matrix);
  matrix_add((uint32_t)8U, (uint32_t)8U, v_matrix, epp_matrix);
  Lib_Memzero_clear_words_u16((uint32_t)64U, epp_matrix);
  uint16_t mu_encode[64U] = { 0U };
  frodo_key_encode((uint32_t)2U, coins, mu_encode);
  matrix_add((uint32_t)8U, (uint32_t)8U, v_matrix, mu_encode);
}

static inline void crypto_kem_enc_ct(uint8_t *pk, uint8_t *g, uint8_t *coins, uint8_t *ct)
{
  uint8_t *seed_a = pk;
  uint8_t *b = pk + (uint32_t)16U;
  uint8_t *seed_e = g;
  uint8_t *d = g + (uint32_t)32U;
  uint16_t sp_matrix[512U] = { 0U };
  frodo_sample_matrix((uint32_t)8U,
    (uint32_t)64U,
    (uint32_t)16U,
    seed_e,
    (uint16_t)4U,
    sp_matrix);
  uint32_t c1Len = (uint32_t)960U;
  uint32_t c2Len = (uint32_t)120U;
  uint32_t c12Len = c1Len + c2Len;
  uint8_t *c1 = ct;
  uint16_t bp_matrix[512U] = { 0U };
  uint16_t a_matrix[4096U] = { 0U };
  uint16_t ep_matrix[512U] = { 0U };
  frodo_gen_matrix_cshake((uint32_t)64U, (uint32_t)16U, seed_a, a_matrix);
  frodo_sample_matrix((uint32_t)8U,
    (uint32_t)64U,
    (uint32_t)16U,
    seed_e,
    (uint16_t)5U,
    ep_matrix);
  matrix_mul((uint32_t)8U, (uint32_t)64U, (uint32_t)64U, sp_matrix, a_matrix, bp_matrix);
  matrix_add((uint32_t)8U, (uint32_t)64U, bp_matrix, ep_matrix);
  Lib_Memzero_clear_words_u16((uint32_t)512U, ep_matrix);
  frodo_pack((uint32_t)8U, (uint32_t)64U, (uint32_t)15U, bp_matrix, c1);
  uint8_t *c2 = ct + c1Len;
  uint16_t v_matrix[64U] = { 0U };
  frodo_mul_add_sb_plus_e_plus_mu(b, seed_e, coins, sp_matrix, v_matrix);
  frodo_pack((uint32_t)8U, (uint32_t)8U, (uint32_t)15U, v_matrix, c2);
  Lib_Memzero_clear_words_u16((uint32_t)64U, v_matrix);
  memcpy(ct + c12Len, d, (uint32_t)16U * sizeof (uint8_t));
  Lib_Memzero_clear_words_u16((uint32_t)512U, sp_matrix);
}

static inline void crypto_kem_enc_ss(uint8_t *g, uint8_t *ct, uint8_t *ss)
{
  uint32_t ss_init_len = crypto_ciphertextbytes + (uint32_t)16U;
  KRML_CHECK_SIZE(sizeof (uint8_t), ss_init_len);
  uint8_t ss_init[ss_init_len];
  memset(ss_init, 0U, ss_init_len * sizeof (uint8_t));
  uint8_t *c12 = ct;
  uint8_t *kd = g + (uint32_t)16U;
  memcpy(ss_init, c12, (crypto_ciphertextbytes - (uint32_t)16U) * sizeof (uint8_t));
  memcpy(ss_init + crypto_ciphertextbytes - (uint32_t)16U, kd, (uint32_t)32U * sizeof (uint8_t));
  uint64_t s[25U] = { 0U };
  s[0U] = (uint64_t)0x10010001a801U | (uint64_t)(uint16_t)7U << (uint32_t)48U;
  Hacl_Impl_SHA3_state_permute(s);
  Hacl_Impl_SHA3_absorb(s, (uint32_t)168U, ss_init_len, ss_init, (uint8_t)0x04U);
  Hacl_Impl_SHA3_squeeze(s, (uint32_t)168U, (uint32_t)16U, ss);
}

uint32_t Hacl_Frodo_KEM_crypto_kem_keypair(uint8_t *pk, uint8_t *sk)
{
  uint8_t coins[48U] = { 0U };
  randombytes_((uint32_t)48U, coins);
  uint8_t *s = coins;
  uint8_t *seed_e = coins + (uint32_t)16U;
  uint8_t *z = coins + (uint32_t)32U;
  uint8_t *seed_a = pk;
  uint64_t s1[25U] = { 0U };
  s1[0U] = (uint64_t)0x10010001a801U | (uint64_t)(uint16_t)0U << (uint32_t)48U;
  Hacl_Impl_SHA3_state_permute(s1);
  Hacl_Impl_SHA3_absorb(s1, (uint32_t)168U, (uint32_t)16U, z, (uint8_t)0x04U);
  Hacl_Impl_SHA3_squeeze(s1, (uint32_t)168U, (uint32_t)16U, seed_a);
  uint8_t *b = pk + (uint32_t)16U;
  uint8_t *s_bytes = sk + (uint32_t)16U + crypto_publickeybytes;
  frodo_mul_add_as_plus_e_pack(seed_a, seed_e, b, s_bytes);
  memcpy(sk, s, (uint32_t)16U * sizeof (uint8_t));
  memcpy(sk + (uint32_t)16U, pk, crypto_publickeybytes * sizeof (uint8_t));
  return (uint32_t)0U;
}

uint32_t Hacl_Frodo_KEM_crypto_kem_enc(uint8_t *ct, uint8_t *ss, uint8_t *pk)
{
  uint8_t coins[16U] = { 0U };
  randombytes_(bytes_mu, coins);
  uint8_t g[48U] = { 0U };
  uint8_t pk_coins[992U] = { 0U };
  memcpy(pk_coins, pk, crypto_publickeybytes * sizeof (uint8_t));
  memcpy(pk_coins + crypto_publickeybytes, coins, bytes_mu * sizeof (uint8_t));
  uint64_t s[25U] = { 0U };
  s[0U] = (uint64_t)0x10010001a801U | (uint64_t)(uint16_t)3U << (uint32_t)48U;
  Hacl_Impl_SHA3_state_permute(s);
  Hacl_Impl_SHA3_absorb(s,
    (uint32_t)168U,
    crypto_publickeybytes + bytes_mu,
    pk_coins,
    (uint8_t)0x04U);
  Hacl_Impl_SHA3_squeeze(s, (uint32_t)168U, (uint32_t)48U, g);
  crypto_kem_enc_ct(pk, g, coins, ct);
  crypto_kem_enc_ss(g, ct, ss);
  Lib_Memzero_clear_words_u8((uint32_t)32U, g);
  return (uint32_t)0U;
}

uint32_t Hacl_Frodo_KEM_crypto_kem_dec(uint8_t *ss, uint8_t *ct, uint8_t *sk)
{
  uint16_t bp_matrix[512U] = { 0U };
  uint16_t c_matrix[64U] = { 0U };
  uint8_t mu_decode[16U] = { 0U };
  uint32_t c1Len = (uint32_t)960U;
  uint8_t *c1 = ct;
  uint8_t *c2 = ct + c1Len;
  frodo_unpack((uint32_t)8U, (uint32_t)64U, (uint32_t)15U, c1, bp_matrix);
  frodo_unpack((uint32_t)8U, (uint32_t)8U, (uint32_t)15U, c2, c_matrix);
  uint8_t *s_bytes = sk + (uint32_t)16U + crypto_publickeybytes;
  uint8_t mu_decode1[16U] = { 0U };
  uint16_t s_matrix[512U] = { 0U };
  uint16_t m_matrix[64U] = { 0U };
  matrix_from_lbytes((uint32_t)64U, (uint32_t)8U, s_bytes, s_matrix);
  matrix_mul_s((uint32_t)8U, (uint32_t)64U, (uint32_t)8U, bp_matrix, s_matrix, m_matrix);
  matrix_sub((uint32_t)8U, (uint32_t)8U, c_matrix, m_matrix);
  frodo_key_decode((uint32_t)2U, m_matrix, mu_decode1);
  uint8_t g[48U] = { 0U };
  uint32_t pk_mu_decode_len = crypto_publickeybytes + bytes_mu;
  KRML_CHECK_SIZE(sizeof (uint8_t), pk_mu_decode_len);
  uint8_t pk_mu_decode[pk_mu_decode_len];
  memset(pk_mu_decode, 0U, pk_mu_decode_len * sizeof (uint8_t));
  uint8_t *pk0 = sk + (uint32_t)16U;
  memcpy(pk_mu_decode, pk0, crypto_publickeybytes * sizeof (uint8_t));
  memcpy(pk_mu_decode + crypto_publickeybytes, mu_decode1, bytes_mu * sizeof (uint8_t));
  uint64_t s0[25U] = { 0U };
  s0[0U] = (uint64_t)0x10010001a801U | (uint64_t)(uint16_t)3U << (uint32_t)48U;
  Hacl_Impl_SHA3_state_permute(s0);
  Hacl_Impl_SHA3_absorb(s0, (uint32_t)168U, pk_mu_decode_len, pk_mu_decode, (uint8_t)0x04U);
  Hacl_Impl_SHA3_squeeze(s0, (uint32_t)168U, (uint32_t)48U, g);
  uint8_t *dp = g + (uint32_t)32U;
  uint8_t *d0 = ct + crypto_ciphertextbytes - (uint32_t)16U;
  uint16_t bpp_matrix[512U] = { 0U };
  uint16_t cp_matrix[64U] = { 0U };
  uint8_t *pk = sk + (uint32_t)16U;
  uint8_t *seed_a = pk;
  uint8_t *b = pk + (uint32_t)16U;
  uint8_t *seed_ep = g;
  uint16_t sp_matrix[512U] = { 0U };
  frodo_sample_matrix((uint32_t)8U,
    (uint32_t)64U,
    (uint32_t)16U,
    seed_ep,
    (uint16_t)4U,
    sp_matrix);
  uint16_t a_matrix[4096U] = { 0U };
  uint16_t ep_matrix[512U] = { 0U };
  frodo_gen_matrix_cshake((uint32_t)64U, (uint32_t)16U, seed_a, a_matrix);
  frodo_sample_matrix((uint32_t)8U,
    (uint32_t)64U,
    (uint32_t)16U,
    seed_ep,
    (uint16_t)5U,
    ep_matrix);
  matrix_mul((uint32_t)8U, (uint32_t)64U, (uint32_t)64U, sp_matrix, a_matrix, bpp_matrix);
  matrix_add((uint32_t)8U, (uint32_t)64U, bpp_matrix, ep_matrix);
  Lib_Memzero_clear_words_u16((uint32_t)512U, ep_matrix);
  frodo_mul_add_sb_plus_e_plus_mu(b, seed_ep, mu_decode1, sp_matrix, cp_matrix);
  Lib_Memzero_clear_words_u16((uint32_t)512U, sp_matrix);
  uint8_t res = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint8_t uu____0 = FStar_UInt8_eq_mask(d0[i], dp[i]);
    res = uu____0 & res;
  }
  uint8_t z = res;
  bool b1 = z == (uint8_t)255U;
  bool b2 = matrix_eq((uint32_t)8U, (uint32_t)64U, (uint32_t)15U, bp_matrix, bpp_matrix);
  bool b3 = matrix_eq((uint32_t)8U, (uint32_t)8U, (uint32_t)15U, c_matrix, cp_matrix);
  bool b0 = b1 && b2 && b3;
  bool b4 = b0;
  uint8_t *kp = g + (uint32_t)16U;
  uint8_t *s = sk;
  uint8_t *kp_s;
  if (b4)
  {
    kp_s = kp;
  }
  else
  {
    kp_s = s;
  }
  uint8_t *c12 = ct;
  uint8_t *d = ct + crypto_ciphertextbytes - (uint32_t)16U;
  uint32_t ss_init_len = crypto_ciphertextbytes + (uint32_t)16U;
  KRML_CHECK_SIZE(sizeof (uint8_t), ss_init_len);
  uint8_t ss_init[ss_init_len];
  memset(ss_init, 0U, ss_init_len * sizeof (uint8_t));
  memcpy(ss_init, c12, (crypto_ciphertextbytes - (uint32_t)16U) * sizeof (uint8_t));
  memcpy(ss_init + crypto_ciphertextbytes - (uint32_t)16U,
    kp_s,
    (uint32_t)16U * sizeof (uint8_t));
  memcpy(ss_init + crypto_ciphertextbytes - (uint32_t)16U + (uint32_t)16U,
    d,
    (uint32_t)16U * sizeof (uint8_t));
  uint64_t s1[25U] = { 0U };
  s1[0U] = (uint64_t)0x10010001a801U | (uint64_t)(uint16_t)7U << (uint32_t)48U;
  Hacl_Impl_SHA3_state_permute(s1);
  Hacl_Impl_SHA3_absorb(s1, (uint32_t)168U, ss_init_len, ss_init, (uint8_t)0x04U);
  Hacl_Impl_SHA3_squeeze(s1, (uint32_t)168U, (uint32_t)16U, ss);
  Lib_Memzero_clear_words_u8((uint32_t)32U, g);
  return (uint32_t)0U;
}

