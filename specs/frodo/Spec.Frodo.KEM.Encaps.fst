module Spec.Frodo.KEM.Encaps

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Matrix
open Spec.Frodo.Lemmas
open Spec.Frodo.Params
open Spec.Frodo.Encode
open Spec.Frodo.Pack
open Spec.Frodo.Sample

module LSeq = Lib.Sequence
module Matrix = Spec.Matrix
module KG = Spec.Frodo.KEM.KeyGen

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val frodo_mul_add_sa_plus_e:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> seed_a:lbytes bytes_seed_a
  -> sp_matrix:matrix params_nbar (params_n a)
  -> ep_matrix:matrix params_nbar (params_n a)
  -> matrix params_nbar (params_n a)

let frodo_mul_add_sa_plus_e a gen_a seed_a sp_matrix ep_matrix =
  let a_matrix  = frodo_gen_matrix gen_a (params_n a) seed_a in
  let b_matrix  = Matrix.add (Matrix.mul sp_matrix a_matrix) ep_matrix in
  b_matrix


val crypto_kem_enc_ct_pack_c1:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> seed_a:lbytes bytes_seed_a
  -> sp_matrix:matrix params_nbar (params_n a)
  -> ep_matrix:matrix params_nbar (params_n a)
  -> lbytes (ct1bytes_len a)

let crypto_kem_enc_ct_pack_c1 a gen_a seed_a sp_matrix ep_matrix =
  let bp_matrix = frodo_mul_add_sa_plus_e a gen_a seed_a sp_matrix ep_matrix in
  let ct1 = frodo_pack (params_logq a) bp_matrix in
  ct1


val frodo_mul_add_sb_plus_e:
    a:frodo_alg
  -> b:lbytes (publicmatrixbytes_len a)
  -> sp_matrix:matrix params_nbar (params_n a)
  -> epp_matrix:matrix params_nbar params_nbar
  -> matrix params_nbar params_nbar

let frodo_mul_add_sb_plus_e a b sp_matrix epp_matrix =
  let b_matrix = frodo_unpack #(params_n a) #params_nbar (params_logq a) b in
  let v_matrix = Matrix.add (Matrix.mul sp_matrix b_matrix) epp_matrix in
  v_matrix


val frodo_mul_add_sb_plus_e_plus_mu:
    a:frodo_alg
  -> mu:lbytes (bytes_mu a)
  -> b:lbytes (publicmatrixbytes_len a)
  -> sp_matrix:matrix params_nbar (params_n a)
  -> epp_matrix:matrix params_nbar params_nbar
  -> matrix params_nbar params_nbar

let frodo_mul_add_sb_plus_e_plus_mu a mu b sp_matrix epp_matrix =
  let v_matrix  = frodo_mul_add_sb_plus_e a b sp_matrix epp_matrix in
  let mu_encode = frodo_key_encode (params_logq a) (params_extracted_bits a) params_nbar mu in
  let v_matrix  = Matrix.add v_matrix mu_encode in
  v_matrix


val crypto_kem_enc_ct_pack_c2:
    a:frodo_alg
  -> mu:lbytes (bytes_mu a)
  -> b:lbytes (publicmatrixbytes_len a)
  -> sp_matrix:matrix params_nbar (params_n a)
  -> epp_matrix:matrix params_nbar params_nbar
  -> lbytes (ct2bytes_len a)

let crypto_kem_enc_ct_pack_c2 a mu b sp_matrix epp_matrix =
  let v_matrix = frodo_mul_add_sb_plus_e_plus_mu a mu b sp_matrix epp_matrix in
  let ct2 = frodo_pack (params_logq a) v_matrix in
  ct2


val get_sp_ep_epp_matrices:
    a:frodo_alg
  -> seed_se:lbytes (crypto_bytes a)
  -> matrix params_nbar (params_n a) & matrix params_nbar (params_n a) & matrix params_nbar params_nbar

let get_sp_ep_epp_matrices a seed_se =
  let s_bytes_len = secretmatrixbytes_len a in
  let r = KG.frodo_shake_r a (u8 0x96) seed_se (2 * s_bytes_len + 2 * params_nbar * params_nbar) in
  let sp_matrix = frodo_sample_matrix a params_nbar (params_n a) (LSeq.sub r 0 s_bytes_len) in
  let ep_matrix = frodo_sample_matrix a params_nbar (params_n a) (LSeq.sub r s_bytes_len s_bytes_len) in
  let epp_matrix = frodo_sample_matrix a params_nbar params_nbar (LSeq.sub r (2 * s_bytes_len) (2 * params_nbar * params_nbar)) in
  sp_matrix, ep_matrix, epp_matrix


val crypto_kem_enc_ct:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> mu:lbytes (bytes_mu a)
  -> pk:lbytes (crypto_publickeybytes a)
  -> seed_se:lbytes (crypto_bytes a)
  -> lbytes (crypto_ciphertextbytes a)

let crypto_kem_enc_ct a gen_a mu pk seed_se =
  expand_crypto_publickeybytes a;
  let seed_a = LSeq.sub pk 0 bytes_seed_a in
  let b = LSeq.sub pk bytes_seed_a (publicmatrixbytes_len a) in

  let sp_matrix, ep_matrix, epp_matrix = get_sp_ep_epp_matrices a seed_se in
  let c1 = crypto_kem_enc_ct_pack_c1 a gen_a seed_a sp_matrix ep_matrix in
  let c2 = crypto_kem_enc_ct_pack_c2 a mu b sp_matrix epp_matrix in
  expand_crypto_ciphertextbytes a;
  let ct = concat c1 c2 in
  ct


val crypto_kem_enc_ss:
    a:frodo_alg
  -> k:lbytes (crypto_bytes a)
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> lbytes (crypto_bytes a)

let crypto_kem_enc_ss a k ct =
  let shake_input_ss = concat ct k in
  let ss = frodo_shake a (crypto_ciphertextbytes a + crypto_bytes a) shake_input_ss (crypto_bytes a) in
  ss


val crypto_kem_enc_seed_se_k:
    a:frodo_alg
  -> mu:lbytes (bytes_mu a)
  -> pk:lbytes (crypto_publickeybytes a)
  -> lbytes (2 * crypto_bytes a)

let crypto_kem_enc_seed_se_k a mu pk =
  let pkh = frodo_shake a (crypto_publickeybytes a) pk (bytes_pkhash a) in
  let pkh_mu = concat pkh mu in
  let seed_se_k = frodo_shake a (bytes_pkhash a + bytes_mu a) pkh_mu (2 * crypto_bytes a) in
  seed_se_k


val crypto_kem_enc_:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> mu:lbytes (bytes_mu a)
  -> pk:lbytes (crypto_publickeybytes a)
  -> lbytes (crypto_ciphertextbytes a) & lbytes (crypto_bytes a)

let crypto_kem_enc_ a gen_a mu pk =
  let seed_se_k = crypto_kem_enc_seed_se_k a mu pk in
  let seed_se = LSeq.sub seed_se_k 0 (crypto_bytes a) in
  let k = LSeq.sub seed_se_k (crypto_bytes a) (crypto_bytes a) in

  let ct = crypto_kem_enc_ct a gen_a mu pk seed_se in
  let ss = crypto_kem_enc_ss a k ct in
  ct, ss


val crypto_kem_enc:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> state:Spec.Frodo.Random.state_t
  -> pk:lbytes (crypto_publickeybytes a)
  -> lbytes (crypto_ciphertextbytes a) & lbytes (crypto_bytes a)

let crypto_kem_enc a gen_a state pk =
  let mu, _ = Spec.Frodo.Random.randombytes_ state (bytes_mu a) in
  crypto_kem_enc_ a gen_a mu pk
