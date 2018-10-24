module Spec.Frodo.KEM.Encaps

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Matrix
open Spec.Frodo.Lemmas
open Spec.Frodo.Params
open Spec.Frodo.KEM
open Spec.Frodo.Encode
open Spec.Frodo.Pack
open Spec.Frodo.Sample

module Seq = Lib.Sequence
module Matrix = Spec.Matrix

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.* +FStar.Pervasives'"

val update_ct:
    c1:lbytes (params_logq * params_nbar * params_n / 8)
  -> c2:lbytes (params_logq * params_nbar * params_nbar / 8)
  -> d:lbytes crypto_bytes
  -> lbytes crypto_ciphertextbytes
let update_ct c1 c2 d = c1 @| c2 @| d

val update_ss_init:
    c12:lbytes (crypto_ciphertextbytes - crypto_bytes)
  -> kd:lbytes (crypto_bytes + crypto_bytes)
  -> lbytes (crypto_ciphertextbytes + crypto_bytes)
let update_ss_init c12 kd = c12 @| kd

val update_ss:
    c12:lbytes (crypto_ciphertextbytes - crypto_bytes)
  -> kd:lbytes (crypto_bytes + crypto_bytes)
  -> lbytes crypto_bytes
let update_ss c12 kd =
  let ss_init = update_ss_init c12 kd in
  frodo_prf_spec (crypto_ciphertextbytes + crypto_bytes) ss_init (u16 7) crypto_bytes

val frodo_mul_add_sa_plus_e:
    seed_a:lbytes bytes_seed_a
  -> seed_e:lbytes crypto_bytes
  -> sp_matrix:matrix params_nbar params_n
  -> matrix params_nbar params_n
let frodo_mul_add_sa_plus_e seed_a seed_e sp_matrix =
  let a_matrix  = frodo_gen_matrix params_n bytes_seed_a seed_a in
  let ep_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_e (u16 5) in
  let b_matrix  = Matrix.add (Matrix.mul sp_matrix a_matrix) ep_matrix in
  //assert (params_nbar * params_n % 2 = 0);
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
  -> coins:lbytes (params_nbar * params_nbar * params_extracted_bits / 8)
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
  assert (params_logq * (params_nbar * params_n / 8) =
          params_logq * params_nbar * params_n / 8);
  assert (params_nbar * params_n <= max_size_t /\ params_n % 8 = 0);
  assert (forall (j:nat{j < params_nbar * params_n / 8}).
      params_logq * j + params_logq <= params_logq * (params_nbar * params_n / 8) /\
      0 <= params_logq * j);
  let bp_matrix = frodo_mul_add_sa_plus_e seed_a seed_e sp_matrix in
  frodo_pack params_logq bp_matrix

val crypto_kem_enc_ct_pack_c2:
    seed_e:lbytes crypto_bytes
  -> coins:lbytes (params_nbar * params_nbar * params_extracted_bits / 8)
  -> b:lbytes (params_logq * params_n * params_nbar / 8)
  -> sp_matrix:matrix params_nbar params_n
  -> lbytes (params_logq * params_nbar * params_nbar / 8)
let crypto_kem_enc_ct_pack_c2 seed_e coins b sp_matrix =
  assert (params_logq * (params_nbar * params_nbar/ 8) =
          params_logq * params_nbar * params_nbar/ 8);
  assert (params_nbar * params_nbar<= max_size_t /\ params_nbar% 8 = 0);
  assert (forall (j:nat{j < params_nbar * params_nbar/ 8}).
      params_logq * j + params_logq <= params_logq * (params_nbar * params_nbar/ 8) /\
      0 <= params_logq * j);
  let v_matrix = frodo_mul_add_sb_plus_e_plus_mu b seed_e coins sp_matrix in
  frodo_pack params_logq v_matrix

val crypto_kem_enc_ct_inner:
    seed_a:lbytes bytes_seed_a
  -> seed_e:lbytes crypto_bytes
  -> b:lbytes (params_logq * params_n * params_nbar / 8)
  -> coins:lbytes (params_nbar * params_nbar * params_extracted_bits / 8)
  -> sp_matrix:matrix params_nbar params_n
  -> d:lbytes crypto_bytes
  -> lbytes crypto_ciphertextbytes
let crypto_kem_enc_ct_inner seed_a seed_e b coins sp_matrix d =
  let c1 = crypto_kem_enc_ct_pack_c1 seed_a seed_e sp_matrix in
  let c2 = crypto_kem_enc_ct_pack_c2 seed_e coins b sp_matrix in
  update_ct c1 c2 d

val crypto_kem_enc_ct:
    pk:lbytes crypto_publickeybytes
  -> g:lbytes (3 * crypto_bytes)
  -> coins:lbytes (params_nbar * params_nbar * params_extracted_bits / 8)
  -> lbytes crypto_ciphertextbytes
let crypto_kem_enc_ct pk g coins =
  let seed_a = Seq.sub pk 0 bytes_seed_a in
  let b = Seq.sub pk bytes_seed_a (crypto_publickeybytes - bytes_seed_a) in
  let seed_e = Seq.sub g 0 crypto_bytes in
  let d = Seq.sub g (2 * crypto_bytes) crypto_bytes in
  let sp_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_e (u16 4) in
  crypto_kem_enc_ct_inner seed_a seed_e b coins sp_matrix d

val crypto_kem_enc_0:
    coins:lbytes bytes_mu
  -> pk:lbytes crypto_publickeybytes
  -> lbytes (3 * crypto_bytes)
let crypto_kem_enc_0 coins pk =
  let pk_coins = Seq.create (crypto_publickeybytes + bytes_mu) (u8 0) in
  let pk_coins = update_sub pk_coins 0 crypto_publickeybytes pk in
  let pk_coins = update_sub pk_coins crypto_publickeybytes bytes_mu coins in
  frodo_prf_spec (crypto_publickeybytes + bytes_mu) pk_coins (u16 3) (3 * crypto_bytes)

val crypto_kem_enc_1:
    g:lbytes (3 * crypto_bytes)
  -> coins:lbytes bytes_mu
  -> pk:lbytes crypto_publickeybytes
  -> lbytes crypto_ciphertextbytes & lbytes crypto_bytes
let crypto_kem_enc_1 g coins pk =
  assert (crypto_bytes <= crypto_ciphertextbytes);
  let ct = crypto_kem_enc_ct pk g coins in
  let c12 = Seq.sub ct 0 (crypto_ciphertextbytes - crypto_bytes) in
  let kd = Seq.sub g crypto_bytes (crypto_bytes + crypto_bytes) in
  let ss = update_ss c12 kd in
  ct, ss

val crypto_kem_enc_:
    coins:lbytes bytes_mu
  -> pk:lbytes crypto_publickeybytes
  -> lbytes crypto_ciphertextbytes & lbytes crypto_bytes
let crypto_kem_enc_ coins pk =
  let g = crypto_kem_enc_0 coins pk in
  crypto_kem_enc_1 g coins pk

val crypto_kem_enc:
    state: Spec.Frodo.Random.state_t
  -> pk:lbytes crypto_publickeybytes
  -> lbytes crypto_ciphertextbytes & lbytes crypto_bytes
let crypto_kem_enc state pk =
  let bytes_mu = params_nbar * params_nbar * params_extracted_bits / 8 in
  let coins, _ = Spec.Frodo.Random.randombytes_ state bytes_mu in
  crypto_kem_enc_ coins pk
