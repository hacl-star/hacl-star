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


#include "Hacl_Frodo64.h"

#include "internal/Hacl_Spec.h"
#include "internal/Hacl_Frodo_KEM.h"

/*
 this variant is used only for testing purposes!
 */


uint32_t Hacl_Frodo64_crypto_bytes = (uint32_t)16U;

uint32_t Hacl_Frodo64_crypto_publickeybytes = (uint32_t)976U;

uint32_t Hacl_Frodo64_crypto_secretkeybytes = (uint32_t)2032U;

uint32_t Hacl_Frodo64_crypto_ciphertextbytes = (uint32_t)1080U;

uint32_t Hacl_Frodo64_crypto_kem_keypair(uint8_t *pk, uint8_t *sk)
{
  uint8_t coins[48U] = { 0U };
  randombytes_((uint32_t)48U, coins);
  uint8_t *s = coins;
  uint8_t *seed_se = coins + (uint32_t)16U;
  uint8_t *z = coins + (uint32_t)32U;
  uint8_t *seed_a = pk;
  Hacl_SHA3_shake128_hacl((uint32_t)16U, z, (uint32_t)16U, seed_a);
  uint8_t *b_bytes = pk + (uint32_t)16U;
  uint8_t *s_bytes = sk + (uint32_t)992U;
  uint16_t s_matrix[512U] = { 0U };
  uint16_t e_matrix[512U] = { 0U };
  uint8_t r[2048U] = { 0U };
  uint8_t shake_input_seed_se[17U] = { 0U };
  shake_input_seed_se[0U] = (uint8_t)0x5fU;
  memcpy(shake_input_seed_se + (uint32_t)1U, seed_se, (uint32_t)16U * sizeof (uint8_t));
  Hacl_SHA3_shake128_hacl((uint32_t)17U, shake_input_seed_se, (uint32_t)2048U, r);
  Lib_Memzero0_memzero(shake_input_seed_se, (uint32_t)17U * sizeof (shake_input_seed_se[0U]));
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix64((uint32_t)64U, (uint32_t)8U, r, s_matrix);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix64((uint32_t)64U,
    (uint32_t)8U,
    r + (uint32_t)1024U,
    e_matrix);
  uint16_t b_matrix[512U] = { 0U };
  uint16_t a_matrix[4096U] = { 0U };
  Hacl_Impl_Frodo_Params_frodo_gen_matrix(Spec_Frodo_Params_SHAKE128,
    (uint32_t)64U,
    seed_a,
    a_matrix);
  Hacl_Impl_Matrix_matrix_mul_s((uint32_t)64U,
    (uint32_t)64U,
    (uint32_t)8U,
    a_matrix,
    s_matrix,
    b_matrix);
  Hacl_Impl_Matrix_matrix_add((uint32_t)64U, (uint32_t)8U, b_matrix, e_matrix);
  Hacl_Impl_Frodo_Pack_frodo_pack((uint32_t)64U, (uint32_t)8U, (uint32_t)15U, b_matrix, b_bytes);
  Hacl_Impl_Matrix_matrix_to_lbytes((uint32_t)64U, (uint32_t)8U, s_matrix, s_bytes);
  Lib_Memzero0_memzero(s_matrix, (uint32_t)512U * sizeof (s_matrix[0U]));
  Lib_Memzero0_memzero(e_matrix, (uint32_t)512U * sizeof (e_matrix[0U]));
  uint32_t slen1 = (uint32_t)2016U;
  uint8_t *sk_p = sk;
  memcpy(sk_p, s, (uint32_t)16U * sizeof (uint8_t));
  memcpy(sk_p + (uint32_t)16U, pk, (uint32_t)976U * sizeof (uint8_t));
  Hacl_SHA3_shake128_hacl((uint32_t)976U, pk, (uint32_t)16U, sk + slen1);
  Lib_Memzero0_memzero(coins, (uint32_t)48U * sizeof (coins[0U]));
  return (uint32_t)0U;
}

uint32_t Hacl_Frodo64_crypto_kem_enc(uint8_t *ct, uint8_t *ss, uint8_t *pk)
{
  uint8_t coins[16U] = { 0U };
  randombytes_((uint32_t)16U, coins);
  uint8_t seed_se_k[32U] = { 0U };
  uint8_t pkh_mu[32U] = { 0U };
  Hacl_SHA3_shake128_hacl((uint32_t)976U, pk, (uint32_t)16U, pkh_mu);
  memcpy(pkh_mu + (uint32_t)16U, coins, (uint32_t)16U * sizeof (uint8_t));
  Hacl_SHA3_shake128_hacl((uint32_t)32U, pkh_mu, (uint32_t)32U, seed_se_k);
  uint8_t *seed_se = seed_se_k;
  uint8_t *k = seed_se_k + (uint32_t)16U;
  uint8_t *seed_a = pk;
  uint8_t *b = pk + (uint32_t)16U;
  uint16_t sp_matrix[512U] = { 0U };
  uint16_t ep_matrix[512U] = { 0U };
  uint16_t epp_matrix[64U] = { 0U };
  uint8_t r[2176U] = { 0U };
  uint8_t shake_input_seed_se[17U] = { 0U };
  shake_input_seed_se[0U] = (uint8_t)0x96U;
  memcpy(shake_input_seed_se + (uint32_t)1U, seed_se, (uint32_t)16U * sizeof (uint8_t));
  Hacl_SHA3_shake128_hacl((uint32_t)17U, shake_input_seed_se, (uint32_t)2176U, r);
  Lib_Memzero0_memzero(shake_input_seed_se, (uint32_t)17U * sizeof (shake_input_seed_se[0U]));
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix64((uint32_t)8U, (uint32_t)64U, r, sp_matrix);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix64((uint32_t)8U,
    (uint32_t)64U,
    r + (uint32_t)1024U,
    ep_matrix);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix64((uint32_t)8U,
    (uint32_t)8U,
    r + (uint32_t)2048U,
    epp_matrix);
  uint8_t *c1 = ct;
  uint8_t *c2 = ct + (uint32_t)960U;
  uint16_t bp_matrix[512U] = { 0U };
  uint16_t a_matrix[4096U] = { 0U };
  Hacl_Impl_Frodo_Params_frodo_gen_matrix(Spec_Frodo_Params_SHAKE128,
    (uint32_t)64U,
    seed_a,
    a_matrix);
  Hacl_Impl_Matrix_matrix_mul((uint32_t)8U,
    (uint32_t)64U,
    (uint32_t)64U,
    sp_matrix,
    a_matrix,
    bp_matrix);
  Hacl_Impl_Matrix_matrix_add((uint32_t)8U, (uint32_t)64U, bp_matrix, ep_matrix);
  Hacl_Impl_Frodo_Pack_frodo_pack((uint32_t)8U, (uint32_t)64U, (uint32_t)15U, bp_matrix, c1);
  uint16_t v_matrix[64U] = { 0U };
  uint16_t b_matrix[512U] = { 0U };
  Hacl_Impl_Frodo_Pack_frodo_unpack((uint32_t)64U, (uint32_t)8U, (uint32_t)15U, b, b_matrix);
  Hacl_Impl_Matrix_matrix_mul((uint32_t)8U,
    (uint32_t)64U,
    (uint32_t)8U,
    sp_matrix,
    b_matrix,
    v_matrix);
  Hacl_Impl_Matrix_matrix_add((uint32_t)8U, (uint32_t)8U, v_matrix, epp_matrix);
  uint16_t mu_encode[64U] = { 0U };
  Hacl_Impl_Frodo_Encode_frodo_key_encode((uint32_t)15U,
    (uint32_t)2U,
    (uint32_t)8U,
    coins,
    mu_encode);
  Hacl_Impl_Matrix_matrix_add((uint32_t)8U, (uint32_t)8U, v_matrix, mu_encode);
  Lib_Memzero0_memzero(mu_encode, (uint32_t)64U * sizeof (mu_encode[0U]));
  Hacl_Impl_Frodo_Pack_frodo_pack((uint32_t)8U, (uint32_t)8U, (uint32_t)15U, v_matrix, c2);
  Lib_Memzero0_memzero(v_matrix, (uint32_t)64U * sizeof (v_matrix[0U]));
  Lib_Memzero0_memzero(sp_matrix, (uint32_t)512U * sizeof (sp_matrix[0U]));
  Lib_Memzero0_memzero(ep_matrix, (uint32_t)512U * sizeof (ep_matrix[0U]));
  Lib_Memzero0_memzero(epp_matrix, (uint32_t)64U * sizeof (epp_matrix[0U]));
  uint32_t ss_init_len = (uint32_t)1096U;
  KRML_CHECK_SIZE(sizeof (uint8_t), ss_init_len);
  uint8_t shake_input_ss[ss_init_len];
  memset(shake_input_ss, 0U, ss_init_len * sizeof (uint8_t));
  memcpy(shake_input_ss, ct, (uint32_t)1080U * sizeof (uint8_t));
  memcpy(shake_input_ss + (uint32_t)1080U, k, (uint32_t)16U * sizeof (uint8_t));
  Hacl_SHA3_shake128_hacl(ss_init_len, shake_input_ss, (uint32_t)16U, ss);
  Lib_Memzero0_memzero(shake_input_ss, ss_init_len * sizeof (shake_input_ss[0U]));
  Lib_Memzero0_memzero(seed_se_k, (uint32_t)32U * sizeof (seed_se_k[0U]));
  Lib_Memzero0_memzero(coins, (uint32_t)16U * sizeof (coins[0U]));
  return (uint32_t)0U;
}

uint32_t Hacl_Frodo64_crypto_kem_dec(uint8_t *ss, uint8_t *ct, uint8_t *sk)
{
  uint16_t bp_matrix[512U] = { 0U };
  uint16_t c_matrix[64U] = { 0U };
  uint8_t *c1 = ct;
  uint8_t *c2 = ct + (uint32_t)960U;
  Hacl_Impl_Frodo_Pack_frodo_unpack((uint32_t)8U, (uint32_t)64U, (uint32_t)15U, c1, bp_matrix);
  Hacl_Impl_Frodo_Pack_frodo_unpack((uint32_t)8U, (uint32_t)8U, (uint32_t)15U, c2, c_matrix);
  uint8_t mu_decode[16U] = { 0U };
  uint8_t *s_bytes = sk + (uint32_t)992U;
  uint16_t s_matrix[512U] = { 0U };
  uint16_t m_matrix[64U] = { 0U };
  Hacl_Impl_Matrix_matrix_from_lbytes((uint32_t)64U, (uint32_t)8U, s_bytes, s_matrix);
  Hacl_Impl_Matrix_matrix_mul_s((uint32_t)8U,
    (uint32_t)64U,
    (uint32_t)8U,
    bp_matrix,
    s_matrix,
    m_matrix);
  Hacl_Impl_Matrix_matrix_sub((uint32_t)8U, (uint32_t)8U, c_matrix, m_matrix);
  Hacl_Impl_Frodo_Encode_frodo_key_decode((uint32_t)15U,
    (uint32_t)2U,
    (uint32_t)8U,
    m_matrix,
    mu_decode);
  Lib_Memzero0_memzero(s_matrix, (uint32_t)512U * sizeof (s_matrix[0U]));
  Lib_Memzero0_memzero(m_matrix, (uint32_t)64U * sizeof (m_matrix[0U]));
  uint8_t seed_se_k[32U] = { 0U };
  uint32_t pkh_mu_decode_len = (uint32_t)32U;
  KRML_CHECK_SIZE(sizeof (uint8_t), pkh_mu_decode_len);
  uint8_t pkh_mu_decode[pkh_mu_decode_len];
  memset(pkh_mu_decode, 0U, pkh_mu_decode_len * sizeof (uint8_t));
  uint8_t *pkh = sk + (uint32_t)2016U;
  memcpy(pkh_mu_decode, pkh, (uint32_t)16U * sizeof (uint8_t));
  memcpy(pkh_mu_decode + (uint32_t)16U, mu_decode, (uint32_t)16U * sizeof (uint8_t));
  Hacl_SHA3_shake128_hacl(pkh_mu_decode_len, pkh_mu_decode, (uint32_t)32U, seed_se_k);
  uint8_t *seed_se = seed_se_k;
  uint8_t *kp = seed_se_k + (uint32_t)16U;
  uint8_t *s = sk;
  uint16_t bpp_matrix[512U] = { 0U };
  uint16_t cp_matrix[64U] = { 0U };
  uint16_t sp_matrix[512U] = { 0U };
  uint16_t ep_matrix[512U] = { 0U };
  uint16_t epp_matrix[64U] = { 0U };
  uint8_t r[2176U] = { 0U };
  uint8_t shake_input_seed_se[17U] = { 0U };
  shake_input_seed_se[0U] = (uint8_t)0x96U;
  memcpy(shake_input_seed_se + (uint32_t)1U, seed_se, (uint32_t)16U * sizeof (uint8_t));
  Hacl_SHA3_shake128_hacl((uint32_t)17U, shake_input_seed_se, (uint32_t)2176U, r);
  Lib_Memzero0_memzero(shake_input_seed_se, (uint32_t)17U * sizeof (shake_input_seed_se[0U]));
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix64((uint32_t)8U, (uint32_t)64U, r, sp_matrix);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix64((uint32_t)8U,
    (uint32_t)64U,
    r + (uint32_t)1024U,
    ep_matrix);
  Hacl_Impl_Frodo_Sample_frodo_sample_matrix64((uint32_t)8U,
    (uint32_t)8U,
    r + (uint32_t)2048U,
    epp_matrix);
  uint8_t *pk = sk + (uint32_t)16U;
  uint8_t *seed_a = pk;
  uint8_t *b = pk + (uint32_t)16U;
  uint16_t a_matrix[4096U] = { 0U };
  Hacl_Impl_Frodo_Params_frodo_gen_matrix(Spec_Frodo_Params_SHAKE128,
    (uint32_t)64U,
    seed_a,
    a_matrix);
  Hacl_Impl_Matrix_matrix_mul((uint32_t)8U,
    (uint32_t)64U,
    (uint32_t)64U,
    sp_matrix,
    a_matrix,
    bpp_matrix);
  Hacl_Impl_Matrix_matrix_add((uint32_t)8U, (uint32_t)64U, bpp_matrix, ep_matrix);
  uint16_t b_matrix[512U] = { 0U };
  Hacl_Impl_Frodo_Pack_frodo_unpack((uint32_t)64U, (uint32_t)8U, (uint32_t)15U, b, b_matrix);
  Hacl_Impl_Matrix_matrix_mul((uint32_t)8U,
    (uint32_t)64U,
    (uint32_t)8U,
    sp_matrix,
    b_matrix,
    cp_matrix);
  Hacl_Impl_Matrix_matrix_add((uint32_t)8U, (uint32_t)8U, cp_matrix, epp_matrix);
  uint16_t mu_encode[64U] = { 0U };
  Hacl_Impl_Frodo_Encode_frodo_key_encode((uint32_t)15U,
    (uint32_t)2U,
    (uint32_t)8U,
    mu_decode,
    mu_encode);
  Hacl_Impl_Matrix_matrix_add((uint32_t)8U, (uint32_t)8U, cp_matrix, mu_encode);
  Lib_Memzero0_memzero(mu_encode, (uint32_t)64U * sizeof (mu_encode[0U]));
  Hacl_Impl_Matrix_mod_pow2((uint32_t)8U, (uint32_t)64U, (uint32_t)15U, bpp_matrix);
  Hacl_Impl_Matrix_mod_pow2((uint32_t)8U, (uint32_t)8U, (uint32_t)15U, cp_matrix);
  Lib_Memzero0_memzero(sp_matrix, (uint32_t)512U * sizeof (sp_matrix[0U]));
  Lib_Memzero0_memzero(ep_matrix, (uint32_t)512U * sizeof (ep_matrix[0U]));
  Lib_Memzero0_memzero(epp_matrix, (uint32_t)64U * sizeof (epp_matrix[0U]));
  uint16_t b1 = Hacl_Impl_Matrix_matrix_eq((uint32_t)8U, (uint32_t)64U, bp_matrix, bpp_matrix);
  uint16_t b2 = Hacl_Impl_Matrix_matrix_eq((uint32_t)8U, (uint32_t)8U, c_matrix, cp_matrix);
  uint16_t mask = b1 & b2;
  uint16_t mask0 = mask;
  uint8_t kp_s[16U] = { 0U };
  KRML_MAYBE_FOR16(i,
    (uint32_t)0U,
    (uint32_t)16U,
    (uint32_t)1U,
    uint8_t *os = kp_s;
    uint8_t uu____0 = s[i];
    uint8_t x = uu____0 ^ ((uint8_t)mask0 & (kp[i] ^ uu____0));
    os[i] = x;);
  uint32_t ss_init_len = (uint32_t)1096U;
  KRML_CHECK_SIZE(sizeof (uint8_t), ss_init_len);
  uint8_t ss_init[ss_init_len];
  memset(ss_init, 0U, ss_init_len * sizeof (uint8_t));
  memcpy(ss_init, ct, (uint32_t)1080U * sizeof (uint8_t));
  memcpy(ss_init + (uint32_t)1080U, kp_s, (uint32_t)16U * sizeof (uint8_t));
  Hacl_SHA3_shake128_hacl(ss_init_len, ss_init, (uint32_t)16U, ss);
  Lib_Memzero0_memzero(ss_init, ss_init_len * sizeof (ss_init[0U]));
  Lib_Memzero0_memzero(kp_s, (uint32_t)16U * sizeof (kp_s[0U]));
  Lib_Memzero0_memzero(seed_se_k, (uint32_t)32U * sizeof (seed_se_k[0U]));
  Lib_Memzero0_memzero(mu_decode, (uint32_t)16U * sizeof (mu_decode[0U]));
  return (uint32_t)0U;
}

