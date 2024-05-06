/* MIT License
 *
 * Copyright (c) 2016-2022 INRIA, CMU and Microsoft Corporation
 * Copyright (c) 2022-2023 HACL* Contributors
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


#include "Hacl_Frodo976.h"

#include "internal/Hacl_Spec.h"
#include "internal/Hacl_Frodo_KEM.h"
#include "lib_memzero0.h"

uint32_t Hacl_Frodo976_crypto_bytes = 24U;

uint32_t Hacl_Frodo976_crypto_publickeybytes = 15632U;

uint32_t Hacl_Frodo976_crypto_secretkeybytes = 31296U;

uint32_t Hacl_Frodo976_crypto_ciphertextbytes = 15744U;

uint32_t Hacl_Frodo976_crypto_kem_keypair(uint8_t *pk, uint8_t *sk)
{
  uint8_t coins[64U] = { 0U };
  randombytes_(64U, coins);
  uint8_t *s = coins;
  uint8_t *seed_se = coins + 24U;
  uint8_t *z = coins + 48U;
  uint8_t *seed_a = pk;
  Hacl_Hash_SHA3_shake256(seed_a, 16U, z, 16U);
  uint8_t *b_bytes = pk + 16U;
  uint8_t *s_bytes = sk + 15656U;
  uint16_t s_matrix[7808U] = { 0U };
  uint16_t e_matrix[7808U] = { 0U };
  uint8_t r[31232U] = { 0U };
  uint8_t shake_input_seed_se[25U] = { 0U };
  shake_input_seed_se[0U] = 0x5fU;
  memcpy(shake_input_seed_se + 1U, seed_se, 24U * sizeof (uint8_t));
  Hacl_Hash_SHA3_shake256(r, 31232U, shake_input_seed_se, 25U);
  Lib_Memzero0_memzero(shake_input_seed_se, 25U, uint8_t, void *);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix976(976U, 8U, r, s_matrix);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix976(976U, 8U, r + 15616U, e_matrix);
  uint16_t b_matrix[7808U] = { 0U };
  KRML_CHECK_SIZE(sizeof (uint16_t), 952576U);
  uint16_t a_matrix[952576U] = { 0U };
  Hacl_Impl_Frodo_Params_frodo_gen_matrix(Spec_Frodo_Params_SHAKE128, 976U, seed_a, a_matrix);
  Hacl_Impl_Matrix_matrix_mul_s(976U, 976U, 8U, a_matrix, s_matrix, b_matrix);
  Hacl_Impl_Matrix_matrix_add(976U, 8U, b_matrix, e_matrix);
  Hacl_Impl_Frodo_Pack_frodo_pack(976U, 8U, 16U, b_matrix, b_bytes);
  Hacl_Impl_Matrix_matrix_to_lbytes(976U, 8U, s_matrix, s_bytes);
  Lib_Memzero0_memzero(s_matrix, 7808U, uint16_t, void *);
  Lib_Memzero0_memzero(e_matrix, 7808U, uint16_t, void *);
  uint32_t slen1 = 31272U;
  uint8_t *sk_p = sk;
  memcpy(sk_p, s, 24U * sizeof (uint8_t));
  memcpy(sk_p + 24U, pk, 15632U * sizeof (uint8_t));
  Hacl_Hash_SHA3_shake256(sk + slen1, 24U, pk, 15632U);
  Lib_Memzero0_memzero(coins, 64U, uint8_t, void *);
  return 0U;
}

uint32_t Hacl_Frodo976_crypto_kem_enc(uint8_t *ct, uint8_t *ss, uint8_t *pk)
{
  uint8_t coins[24U] = { 0U };
  randombytes_(24U, coins);
  uint8_t seed_se_k[48U] = { 0U };
  uint8_t pkh_mu[48U] = { 0U };
  Hacl_Hash_SHA3_shake256(pkh_mu, 24U, pk, 15632U);
  memcpy(pkh_mu + 24U, coins, 24U * sizeof (uint8_t));
  Hacl_Hash_SHA3_shake256(seed_se_k, 48U, pkh_mu, 48U);
  uint8_t *seed_se = seed_se_k;
  uint8_t *k = seed_se_k + 24U;
  uint8_t *seed_a = pk;
  uint8_t *b = pk + 16U;
  uint16_t sp_matrix[7808U] = { 0U };
  uint16_t ep_matrix[7808U] = { 0U };
  uint16_t epp_matrix[64U] = { 0U };
  uint8_t r[31360U] = { 0U };
  uint8_t shake_input_seed_se[25U] = { 0U };
  shake_input_seed_se[0U] = 0x96U;
  memcpy(shake_input_seed_se + 1U, seed_se, 24U * sizeof (uint8_t));
  Hacl_Hash_SHA3_shake256(r, 31360U, shake_input_seed_se, 25U);
  Lib_Memzero0_memzero(shake_input_seed_se, 25U, uint8_t, void *);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix976(8U, 976U, r, sp_matrix);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix976(8U, 976U, r + 15616U, ep_matrix);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix976(8U, 8U, r + 31232U, epp_matrix);
  uint8_t *c1 = ct;
  uint8_t *c2 = ct + 15616U;
  uint16_t bp_matrix[7808U] = { 0U };
  KRML_CHECK_SIZE(sizeof (uint16_t), 952576U);
  uint16_t a_matrix[952576U] = { 0U };
  Hacl_Impl_Frodo_Params_frodo_gen_matrix(Spec_Frodo_Params_SHAKE128, 976U, seed_a, a_matrix);
  Hacl_Impl_Matrix_matrix_mul(8U, 976U, 976U, sp_matrix, a_matrix, bp_matrix);
  Hacl_Impl_Matrix_matrix_add(8U, 976U, bp_matrix, ep_matrix);
  Hacl_Impl_Frodo_Pack_frodo_pack(8U, 976U, 16U, bp_matrix, c1);
  uint16_t v_matrix[64U] = { 0U };
  uint16_t b_matrix[7808U] = { 0U };
  Hacl_Impl_Frodo_Pack_frodo_unpack(976U, 8U, 16U, b, b_matrix);
  Hacl_Impl_Matrix_matrix_mul(8U, 976U, 8U, sp_matrix, b_matrix, v_matrix);
  Hacl_Impl_Matrix_matrix_add(8U, 8U, v_matrix, epp_matrix);
  uint16_t mu_encode[64U] = { 0U };
  Hacl_Impl_Frodo_Encode_frodo_key_encode(16U, 3U, 8U, coins, mu_encode);
  Hacl_Impl_Matrix_matrix_add(8U, 8U, v_matrix, mu_encode);
  Lib_Memzero0_memzero(mu_encode, 64U, uint16_t, void *);
  Hacl_Impl_Frodo_Pack_frodo_pack(8U, 8U, 16U, v_matrix, c2);
  Lib_Memzero0_memzero(v_matrix, 64U, uint16_t, void *);
  Lib_Memzero0_memzero(sp_matrix, 7808U, uint16_t, void *);
  Lib_Memzero0_memzero(ep_matrix, 7808U, uint16_t, void *);
  Lib_Memzero0_memzero(epp_matrix, 64U, uint16_t, void *);
  uint32_t ss_init_len = 15768U;
  KRML_CHECK_SIZE(sizeof (uint8_t), ss_init_len);
  uint8_t *shake_input_ss = (uint8_t *)alloca(ss_init_len * sizeof (uint8_t));
  memset(shake_input_ss, 0U, ss_init_len * sizeof (uint8_t));
  memcpy(shake_input_ss, ct, 15744U * sizeof (uint8_t));
  memcpy(shake_input_ss + 15744U, k, 24U * sizeof (uint8_t));
  Hacl_Hash_SHA3_shake256(ss, 24U, shake_input_ss, ss_init_len);
  Lib_Memzero0_memzero(shake_input_ss, ss_init_len, uint8_t, void *);
  Lib_Memzero0_memzero(seed_se_k, 48U, uint8_t, void *);
  Lib_Memzero0_memzero(coins, 24U, uint8_t, void *);
  return 0U;
}

uint32_t Hacl_Frodo976_crypto_kem_dec(uint8_t *ss, uint8_t *ct, uint8_t *sk)
{
  uint16_t bp_matrix[7808U] = { 0U };
  uint16_t c_matrix[64U] = { 0U };
  uint8_t *c1 = ct;
  uint8_t *c2 = ct + 15616U;
  Hacl_Impl_Frodo_Pack_frodo_unpack(8U, 976U, 16U, c1, bp_matrix);
  Hacl_Impl_Frodo_Pack_frodo_unpack(8U, 8U, 16U, c2, c_matrix);
  uint8_t mu_decode[24U] = { 0U };
  uint8_t *s_bytes = sk + 15656U;
  uint16_t s_matrix[7808U] = { 0U };
  uint16_t m_matrix[64U] = { 0U };
  Hacl_Impl_Matrix_matrix_from_lbytes(976U, 8U, s_bytes, s_matrix);
  Hacl_Impl_Matrix_matrix_mul_s(8U, 976U, 8U, bp_matrix, s_matrix, m_matrix);
  Hacl_Impl_Matrix_matrix_sub(8U, 8U, c_matrix, m_matrix);
  Hacl_Impl_Frodo_Encode_frodo_key_decode(16U, 3U, 8U, m_matrix, mu_decode);
  Lib_Memzero0_memzero(s_matrix, 7808U, uint16_t, void *);
  Lib_Memzero0_memzero(m_matrix, 64U, uint16_t, void *);
  uint8_t seed_se_k[48U] = { 0U };
  uint32_t pkh_mu_decode_len = 48U;
  KRML_CHECK_SIZE(sizeof (uint8_t), pkh_mu_decode_len);
  uint8_t *pkh_mu_decode = (uint8_t *)alloca(pkh_mu_decode_len * sizeof (uint8_t));
  memset(pkh_mu_decode, 0U, pkh_mu_decode_len * sizeof (uint8_t));
  uint8_t *pkh = sk + 31272U;
  memcpy(pkh_mu_decode, pkh, 24U * sizeof (uint8_t));
  memcpy(pkh_mu_decode + 24U, mu_decode, 24U * sizeof (uint8_t));
  Hacl_Hash_SHA3_shake256(seed_se_k, 48U, pkh_mu_decode, pkh_mu_decode_len);
  uint8_t *seed_se = seed_se_k;
  uint8_t *kp = seed_se_k + 24U;
  uint8_t *s = sk;
  uint16_t bpp_matrix[7808U] = { 0U };
  uint16_t cp_matrix[64U] = { 0U };
  uint16_t sp_matrix[7808U] = { 0U };
  uint16_t ep_matrix[7808U] = { 0U };
  uint16_t epp_matrix[64U] = { 0U };
  uint8_t r[31360U] = { 0U };
  uint8_t shake_input_seed_se[25U] = { 0U };
  shake_input_seed_se[0U] = 0x96U;
  memcpy(shake_input_seed_se + 1U, seed_se, 24U * sizeof (uint8_t));
  Hacl_Hash_SHA3_shake256(r, 31360U, shake_input_seed_se, 25U);
  Lib_Memzero0_memzero(shake_input_seed_se, 25U, uint8_t, void *);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix976(8U, 976U, r, sp_matrix);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix976(8U, 976U, r + 15616U, ep_matrix);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix976(8U, 8U, r + 31232U, epp_matrix);
  uint8_t *pk = sk + 24U;
  uint8_t *seed_a = pk;
  uint8_t *b = pk + 16U;
  KRML_CHECK_SIZE(sizeof (uint16_t), 952576U);
  uint16_t a_matrix[952576U] = { 0U };
  Hacl_Impl_Frodo_Params_frodo_gen_matrix(Spec_Frodo_Params_SHAKE128, 976U, seed_a, a_matrix);
  Hacl_Impl_Matrix_matrix_mul(8U, 976U, 976U, sp_matrix, a_matrix, bpp_matrix);
  Hacl_Impl_Matrix_matrix_add(8U, 976U, bpp_matrix, ep_matrix);
  uint16_t b_matrix[7808U] = { 0U };
  Hacl_Impl_Frodo_Pack_frodo_unpack(976U, 8U, 16U, b, b_matrix);
  Hacl_Impl_Matrix_matrix_mul(8U, 976U, 8U, sp_matrix, b_matrix, cp_matrix);
  Hacl_Impl_Matrix_matrix_add(8U, 8U, cp_matrix, epp_matrix);
  uint16_t mu_encode[64U] = { 0U };
  Hacl_Impl_Frodo_Encode_frodo_key_encode(16U, 3U, 8U, mu_decode, mu_encode);
  Hacl_Impl_Matrix_matrix_add(8U, 8U, cp_matrix, mu_encode);
  Lib_Memzero0_memzero(mu_encode, 64U, uint16_t, void *);
  Hacl_Impl_Matrix_mod_pow2(8U, 976U, 16U, bpp_matrix);
  Hacl_Impl_Matrix_mod_pow2(8U, 8U, 16U, cp_matrix);
  Lib_Memzero0_memzero(sp_matrix, 7808U, uint16_t, void *);
  Lib_Memzero0_memzero(ep_matrix, 7808U, uint16_t, void *);
  Lib_Memzero0_memzero(epp_matrix, 64U, uint16_t, void *);
  uint16_t b1 = Hacl_Impl_Matrix_matrix_eq(8U, 976U, bp_matrix, bpp_matrix);
  uint16_t b2 = Hacl_Impl_Matrix_matrix_eq(8U, 8U, c_matrix, cp_matrix);
  uint16_t mask = (uint32_t)b1 & (uint32_t)b2;
  uint16_t mask0 = mask;
  uint8_t kp_s[24U] = { 0U };
  for (uint32_t i = 0U; i < 24U; i++)
  {
    uint8_t *os = kp_s;
    uint8_t uu____0 = s[i];
    uint8_t
    x = (uint32_t)uu____0 ^ ((uint32_t)(uint8_t)mask0 & ((uint32_t)kp[i] ^ (uint32_t)uu____0));
    os[i] = x;
  }
  uint32_t ss_init_len = 15768U;
  KRML_CHECK_SIZE(sizeof (uint8_t), ss_init_len);
  uint8_t *ss_init = (uint8_t *)alloca(ss_init_len * sizeof (uint8_t));
  memset(ss_init, 0U, ss_init_len * sizeof (uint8_t));
  memcpy(ss_init, ct, 15744U * sizeof (uint8_t));
  memcpy(ss_init + 15744U, kp_s, 24U * sizeof (uint8_t));
  Hacl_Hash_SHA3_shake256(ss, 24U, ss_init, ss_init_len);
  Lib_Memzero0_memzero(ss_init, ss_init_len, uint8_t, void *);
  Lib_Memzero0_memzero(kp_s, 24U, uint8_t, void *);
  Lib_Memzero0_memzero(seed_se_k, 48U, uint8_t, void *);
  Lib_Memzero0_memzero(mu_decode, 24U, uint8_t, void *);
  return 0U;
}

