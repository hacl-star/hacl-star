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


#include "Hacl_Frodo1344.h"

#include "internal/Hacl_Spec.h"
#include "internal/Hacl_Frodo_KEM.h"
#include "lib_memzero0.h"

uint32_t Hacl_Frodo1344_crypto_bytes = 32U;

uint32_t Hacl_Frodo1344_crypto_publickeybytes = 21520U;

uint32_t Hacl_Frodo1344_crypto_secretkeybytes = 43088U;

uint32_t Hacl_Frodo1344_crypto_ciphertextbytes = 21632U;

uint32_t Hacl_Frodo1344_crypto_kem_keypair(uint8_t *pk, uint8_t *sk)
{
  uint8_t coins[80U] = { 0U };
  randombytes_(80U, coins);
  uint8_t *s = coins;
  uint8_t *seed_se = coins + 32U;
  uint8_t *z = coins + 64U;
  uint8_t *seed_a = pk;
  Hacl_Hash_SHA3_shake256(seed_a, 16U, z, 16U);
  uint8_t *b_bytes = pk + 16U;
  uint8_t *s_bytes = sk + 21552U;
  uint16_t s_matrix[10752U] = { 0U };
  uint16_t e_matrix[10752U] = { 0U };
  uint8_t r[43008U] = { 0U };
  uint8_t shake_input_seed_se[33U] = { 0U };
  shake_input_seed_se[0U] = 0x5fU;
  memcpy(shake_input_seed_se + 1U, seed_se, 32U * sizeof (uint8_t));
  Hacl_Hash_SHA3_shake256(r, 43008U, shake_input_seed_se, 33U);
  Lib_Memzero0_memzero(shake_input_seed_se, 33U, uint8_t, void *);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix1344(1344U, 8U, r, s_matrix);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix1344(1344U, 8U, r + 21504U, e_matrix);
  uint16_t b_matrix[10752U] = { 0U };
  KRML_CHECK_SIZE(sizeof (uint16_t), 1806336U);
  uint16_t a_matrix[1806336U] = { 0U };
  Hacl_Impl_Frodo_Params_frodo_gen_matrix(Spec_Frodo_Params_SHAKE128, 1344U, seed_a, a_matrix);
  Hacl_Impl_Matrix_matrix_mul_s(1344U, 1344U, 8U, a_matrix, s_matrix, b_matrix);
  Hacl_Impl_Matrix_matrix_add(1344U, 8U, b_matrix, e_matrix);
  Hacl_Impl_Frodo_Pack_frodo_pack(1344U, 8U, 16U, b_matrix, b_bytes);
  Hacl_Impl_Matrix_matrix_to_lbytes(1344U, 8U, s_matrix, s_bytes);
  Lib_Memzero0_memzero(s_matrix, 10752U, uint16_t, void *);
  Lib_Memzero0_memzero(e_matrix, 10752U, uint16_t, void *);
  uint32_t slen1 = 43056U;
  uint8_t *sk_p = sk;
  memcpy(sk_p, s, 32U * sizeof (uint8_t));
  memcpy(sk_p + 32U, pk, 21520U * sizeof (uint8_t));
  Hacl_Hash_SHA3_shake256(sk + slen1, 32U, pk, 21520U);
  Lib_Memzero0_memzero(coins, 80U, uint8_t, void *);
  return 0U;
}

uint32_t Hacl_Frodo1344_crypto_kem_enc(uint8_t *ct, uint8_t *ss, uint8_t *pk)
{
  uint8_t coins[32U] = { 0U };
  randombytes_(32U, coins);
  uint8_t seed_se_k[64U] = { 0U };
  uint8_t pkh_mu[64U] = { 0U };
  Hacl_Hash_SHA3_shake256(pkh_mu, 32U, pk, 21520U);
  memcpy(pkh_mu + 32U, coins, 32U * sizeof (uint8_t));
  Hacl_Hash_SHA3_shake256(seed_se_k, 64U, pkh_mu, 64U);
  uint8_t *seed_se = seed_se_k;
  uint8_t *k = seed_se_k + 32U;
  uint8_t *seed_a = pk;
  uint8_t *b = pk + 16U;
  uint16_t sp_matrix[10752U] = { 0U };
  uint16_t ep_matrix[10752U] = { 0U };
  uint16_t epp_matrix[64U] = { 0U };
  uint8_t r[43136U] = { 0U };
  uint8_t shake_input_seed_se[33U] = { 0U };
  shake_input_seed_se[0U] = 0x96U;
  memcpy(shake_input_seed_se + 1U, seed_se, 32U * sizeof (uint8_t));
  Hacl_Hash_SHA3_shake256(r, 43136U, shake_input_seed_se, 33U);
  Lib_Memzero0_memzero(shake_input_seed_se, 33U, uint8_t, void *);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix1344(8U, 1344U, r, sp_matrix);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix1344(8U, 1344U, r + 21504U, ep_matrix);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix1344(8U, 8U, r + 43008U, epp_matrix);
  uint8_t *c1 = ct;
  uint8_t *c2 = ct + 21504U;
  uint16_t bp_matrix[10752U] = { 0U };
  KRML_CHECK_SIZE(sizeof (uint16_t), 1806336U);
  uint16_t a_matrix[1806336U] = { 0U };
  Hacl_Impl_Frodo_Params_frodo_gen_matrix(Spec_Frodo_Params_SHAKE128, 1344U, seed_a, a_matrix);
  Hacl_Impl_Matrix_matrix_mul(8U, 1344U, 1344U, sp_matrix, a_matrix, bp_matrix);
  Hacl_Impl_Matrix_matrix_add(8U, 1344U, bp_matrix, ep_matrix);
  Hacl_Impl_Frodo_Pack_frodo_pack(8U, 1344U, 16U, bp_matrix, c1);
  uint16_t v_matrix[64U] = { 0U };
  uint16_t b_matrix[10752U] = { 0U };
  Hacl_Impl_Frodo_Pack_frodo_unpack(1344U, 8U, 16U, b, b_matrix);
  Hacl_Impl_Matrix_matrix_mul(8U, 1344U, 8U, sp_matrix, b_matrix, v_matrix);
  Hacl_Impl_Matrix_matrix_add(8U, 8U, v_matrix, epp_matrix);
  uint16_t mu_encode[64U] = { 0U };
  Hacl_Impl_Frodo_Encode_frodo_key_encode(16U, 4U, 8U, coins, mu_encode);
  Hacl_Impl_Matrix_matrix_add(8U, 8U, v_matrix, mu_encode);
  Lib_Memzero0_memzero(mu_encode, 64U, uint16_t, void *);
  Hacl_Impl_Frodo_Pack_frodo_pack(8U, 8U, 16U, v_matrix, c2);
  Lib_Memzero0_memzero(v_matrix, 64U, uint16_t, void *);
  Lib_Memzero0_memzero(sp_matrix, 10752U, uint16_t, void *);
  Lib_Memzero0_memzero(ep_matrix, 10752U, uint16_t, void *);
  Lib_Memzero0_memzero(epp_matrix, 64U, uint16_t, void *);
  uint32_t ss_init_len = 21664U;
  KRML_CHECK_SIZE(sizeof (uint8_t), ss_init_len);
  uint8_t shake_input_ss[ss_init_len];
  memset(shake_input_ss, 0U, ss_init_len * sizeof (uint8_t));
  memcpy(shake_input_ss, ct, 21632U * sizeof (uint8_t));
  memcpy(shake_input_ss + 21632U, k, 32U * sizeof (uint8_t));
  Hacl_Hash_SHA3_shake256(ss, 32U, shake_input_ss, ss_init_len);
  Lib_Memzero0_memzero(shake_input_ss, ss_init_len, uint8_t, void *);
  Lib_Memzero0_memzero(seed_se_k, 64U, uint8_t, void *);
  Lib_Memzero0_memzero(coins, 32U, uint8_t, void *);
  return 0U;
}

uint32_t Hacl_Frodo1344_crypto_kem_dec(uint8_t *ss, uint8_t *ct, uint8_t *sk)
{
  uint16_t bp_matrix[10752U] = { 0U };
  uint16_t c_matrix[64U] = { 0U };
  uint8_t *c1 = ct;
  uint8_t *c2 = ct + 21504U;
  Hacl_Impl_Frodo_Pack_frodo_unpack(8U, 1344U, 16U, c1, bp_matrix);
  Hacl_Impl_Frodo_Pack_frodo_unpack(8U, 8U, 16U, c2, c_matrix);
  uint8_t mu_decode[32U] = { 0U };
  uint8_t *s_bytes = sk + 21552U;
  uint16_t s_matrix[10752U] = { 0U };
  uint16_t m_matrix[64U] = { 0U };
  Hacl_Impl_Matrix_matrix_from_lbytes(1344U, 8U, s_bytes, s_matrix);
  Hacl_Impl_Matrix_matrix_mul_s(8U, 1344U, 8U, bp_matrix, s_matrix, m_matrix);
  Hacl_Impl_Matrix_matrix_sub(8U, 8U, c_matrix, m_matrix);
  Hacl_Impl_Frodo_Encode_frodo_key_decode(16U, 4U, 8U, m_matrix, mu_decode);
  Lib_Memzero0_memzero(s_matrix, 10752U, uint16_t, void *);
  Lib_Memzero0_memzero(m_matrix, 64U, uint16_t, void *);
  uint8_t seed_se_k[64U] = { 0U };
  uint32_t pkh_mu_decode_len = 64U;
  KRML_CHECK_SIZE(sizeof (uint8_t), pkh_mu_decode_len);
  uint8_t pkh_mu_decode[pkh_mu_decode_len];
  memset(pkh_mu_decode, 0U, pkh_mu_decode_len * sizeof (uint8_t));
  uint8_t *pkh = sk + 43056U;
  memcpy(pkh_mu_decode, pkh, 32U * sizeof (uint8_t));
  memcpy(pkh_mu_decode + 32U, mu_decode, 32U * sizeof (uint8_t));
  Hacl_Hash_SHA3_shake256(seed_se_k, 64U, pkh_mu_decode, pkh_mu_decode_len);
  uint8_t *seed_se = seed_se_k;
  uint8_t *kp = seed_se_k + 32U;
  uint8_t *s = sk;
  uint16_t bpp_matrix[10752U] = { 0U };
  uint16_t cp_matrix[64U] = { 0U };
  uint16_t sp_matrix[10752U] = { 0U };
  uint16_t ep_matrix[10752U] = { 0U };
  uint16_t epp_matrix[64U] = { 0U };
  uint8_t r[43136U] = { 0U };
  uint8_t shake_input_seed_se[33U] = { 0U };
  shake_input_seed_se[0U] = 0x96U;
  memcpy(shake_input_seed_se + 1U, seed_se, 32U * sizeof (uint8_t));
  Hacl_Hash_SHA3_shake256(r, 43136U, shake_input_seed_se, 33U);
  Lib_Memzero0_memzero(shake_input_seed_se, 33U, uint8_t, void *);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix1344(8U, 1344U, r, sp_matrix);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix1344(8U, 1344U, r + 21504U, ep_matrix);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix1344(8U, 8U, r + 43008U, epp_matrix);
  uint8_t *pk = sk + 32U;
  uint8_t *seed_a = pk;
  uint8_t *b = pk + 16U;
  KRML_CHECK_SIZE(sizeof (uint16_t), 1806336U);
  uint16_t a_matrix[1806336U] = { 0U };
  Hacl_Impl_Frodo_Params_frodo_gen_matrix(Spec_Frodo_Params_SHAKE128, 1344U, seed_a, a_matrix);
  Hacl_Impl_Matrix_matrix_mul(8U, 1344U, 1344U, sp_matrix, a_matrix, bpp_matrix);
  Hacl_Impl_Matrix_matrix_add(8U, 1344U, bpp_matrix, ep_matrix);
  uint16_t b_matrix[10752U] = { 0U };
  Hacl_Impl_Frodo_Pack_frodo_unpack(1344U, 8U, 16U, b, b_matrix);
  Hacl_Impl_Matrix_matrix_mul(8U, 1344U, 8U, sp_matrix, b_matrix, cp_matrix);
  Hacl_Impl_Matrix_matrix_add(8U, 8U, cp_matrix, epp_matrix);
  uint16_t mu_encode[64U] = { 0U };
  Hacl_Impl_Frodo_Encode_frodo_key_encode(16U, 4U, 8U, mu_decode, mu_encode);
  Hacl_Impl_Matrix_matrix_add(8U, 8U, cp_matrix, mu_encode);
  Lib_Memzero0_memzero(mu_encode, 64U, uint16_t, void *);
  Hacl_Impl_Matrix_mod_pow2(8U, 1344U, 16U, bpp_matrix);
  Hacl_Impl_Matrix_mod_pow2(8U, 8U, 16U, cp_matrix);
  Lib_Memzero0_memzero(sp_matrix, 10752U, uint16_t, void *);
  Lib_Memzero0_memzero(ep_matrix, 10752U, uint16_t, void *);
  Lib_Memzero0_memzero(epp_matrix, 64U, uint16_t, void *);
  uint16_t b1 = Hacl_Impl_Matrix_matrix_eq(8U, 1344U, bp_matrix, bpp_matrix);
  uint16_t b2 = Hacl_Impl_Matrix_matrix_eq(8U, 8U, c_matrix, cp_matrix);
  uint16_t mask = (uint32_t)b1 & (uint32_t)b2;
  uint16_t mask0 = mask;
  uint8_t kp_s[32U] = { 0U };
  for (uint32_t i = 0U; i < 32U; i++)
  {
    uint8_t *os = kp_s;
    uint8_t uu____0 = s[i];
    uint8_t
    x = (uint32_t)uu____0 ^ ((uint32_t)(uint8_t)mask0 & ((uint32_t)kp[i] ^ (uint32_t)uu____0));
    os[i] = x;
  }
  uint32_t ss_init_len = 21664U;
  KRML_CHECK_SIZE(sizeof (uint8_t), ss_init_len);
  uint8_t ss_init[ss_init_len];
  memset(ss_init, 0U, ss_init_len * sizeof (uint8_t));
  memcpy(ss_init, ct, 21632U * sizeof (uint8_t));
  memcpy(ss_init + 21632U, kp_s, 32U * sizeof (uint8_t));
  Hacl_Hash_SHA3_shake256(ss, 32U, ss_init, ss_init_len);
  Lib_Memzero0_memzero(ss_init, ss_init_len, uint8_t, void *);
  Lib_Memzero0_memzero(kp_s, 32U, uint8_t, void *);
  Lib_Memzero0_memzero(seed_se_k, 64U, uint8_t, void *);
  Lib_Memzero0_memzero(mu_decode, 32U, uint8_t, void *);
  return 0U;
}

