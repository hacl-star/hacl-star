module Spec.Frodo.KEM.Encaps

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul

open Spec.Matrix
open Spec.Frodo.Lemmas
open Spec.Frodo.Params
open Spec.Frodo.Encode
open Spec.Frodo.Pack
open Spec.Frodo.Sample

module Seq = Lib.Sequence
module Matrix = Spec.Matrix

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.* +FStar.Pervasives'"

val frodo_mul_add_sa_plus_e:
    seed_a:lbytes bytes_seed_a
  -> seed_e:lbytes crypto_bytes
  -> sp_matrix:matrix params_nbar params_n
  -> matrix params_nbar params_n
let frodo_mul_add_sa_plus_e seed_a seed_e sp_matrix =
  let a_matrix  = frodo_gen_matrix params_n bytes_seed_a seed_a in
  let ep_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_e (u16 5) in
  let b_matrix  = Matrix.add (Matrix.mul sp_matrix a_matrix) ep_matrix in
  b_matrix

val frodo_mul_add_sb_plus_e:
    b:lbytes (params_logq * params_n * params_nbar / 8)
  -> seed_e:lbytes crypto_bytes
  -> sp_matrix:matrix params_nbar params_n
  -> matrix params_nbar params_nbar
let frodo_mul_add_sb_plus_e b seed_e sp_matrix =
  let b_matrix = frodo_unpack #params_n #params_nbar params_logq b in
  let epp_matrix = frodo_sample_matrix params_nbar params_nbar crypto_bytes seed_e (u16 6) in
  let v_matrix = Matrix.add (Matrix.mul sp_matrix b_matrix) epp_matrix in
  v_matrix

val frodo_mul_add_sb_plus_e_plus_mu:
    b:lbytes (params_logq * params_n * params_nbar / 8)
  -> seed_e:lbytes crypto_bytes
  -> coins:lbytes bytes_mu
  -> sp_matrix:matrix params_nbar params_n
  -> matrix params_nbar params_nbar
let frodo_mul_add_sb_plus_e_plus_mu b seed_e coins sp_matrix =
  let v_matrix  = frodo_mul_add_sb_plus_e b seed_e sp_matrix in
  let mu_encode = frodo_key_encode params_extracted_bits coins in
  let v_matrix  = Matrix.add v_matrix mu_encode in
  v_matrix

val crypto_kem_enc_ct_pack_c1:
    seed_a:lbytes bytes_seed_a
  -> seed_e:lbytes crypto_bytes
  -> sp_matrix:matrix params_nbar params_n
  -> lbytes (params_logq * params_nbar * params_n / 8)
let crypto_kem_enc_ct_pack_c1 seed_a seed_e sp_matrix =
  let bp_matrix = frodo_mul_add_sa_plus_e seed_a seed_e sp_matrix in
  frodo_pack params_logq bp_matrix

val crypto_kem_enc_ct_pack_c2:
    seed_e:lbytes crypto_bytes
  -> coins:lbytes bytes_mu
  -> b:lbytes (params_logq * params_n * params_nbar / 8)
  -> sp_matrix:matrix params_nbar params_n
  -> lbytes (params_logq * params_nbar * params_nbar / 8)
let crypto_kem_enc_ct_pack_c2 seed_e coins b sp_matrix =
  let v_matrix = frodo_mul_add_sb_plus_e_plus_mu b seed_e coins sp_matrix in
  frodo_pack params_logq v_matrix

val crypto_kem_enc_ct:
    pk:lbytes crypto_publickeybytes
  -> g:lbytes (3 * crypto_bytes)
  -> coins:lbytes bytes_mu
  -> lbytes crypto_ciphertextbytes
let crypto_kem_enc_ct pk g coins =
  let seed_a = Seq.sub pk 0 bytes_seed_a in
  let b = Seq.sub pk bytes_seed_a (crypto_publickeybytes - bytes_seed_a) in
  let seed_e = Seq.sub g 0 crypto_bytes in
  let d = Seq.sub g (2 * crypto_bytes) crypto_bytes in
  let sp_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_e (u16 4) in
  let c2 = crypto_kem_enc_ct_pack_c2 seed_e coins b sp_matrix in
  let c1 = crypto_kem_enc_ct_pack_c1 seed_a seed_e sp_matrix in
  expand_crypto_ciphertextbytes ();
  let ct = concat (concat c1 c2) d in
  ct

val crypto_kem_enc_ss:
    g:lbytes (3 * crypto_bytes)
  -> ct:lbytes crypto_ciphertextbytes
  -> lbytes crypto_bytes
let crypto_kem_enc_ss g ct =
  expand_crypto_ciphertextbytes ();
  let c12 = Seq.sub ct 0 (crypto_ciphertextbytes - crypto_bytes) in
  let kd = Seq.sub g crypto_bytes (crypto_bytes + crypto_bytes) in
  let ss_init = concat c12 kd in
  frodo_prf_spec (crypto_ciphertextbytes + crypto_bytes) ss_init (u16 7) crypto_bytes

val crypto_kem_enc_:
    coins:lbytes bytes_mu
  -> pk:lbytes crypto_publickeybytes
  -> lbytes crypto_ciphertextbytes & lbytes crypto_bytes
let crypto_kem_enc_ coins pk =
  let pk_coins = concat pk coins in
  let g = frodo_prf_spec (crypto_publickeybytes + bytes_mu) pk_coins (u16 3) (3 * crypto_bytes) in
  let ct = crypto_kem_enc_ct pk g coins in
  let ss = crypto_kem_enc_ss g ct in
  ct, ss

val crypto_kem_enc:
    state: Spec.Frodo.Random.state_t
  -> pk:lbytes crypto_publickeybytes
  -> lbytes crypto_ciphertextbytes & lbytes crypto_bytes
let crypto_kem_enc state pk =
  let coins, _ = Spec.Frodo.Random.randombytes_ state bytes_mu in
  crypto_kem_enc_ coins pk
