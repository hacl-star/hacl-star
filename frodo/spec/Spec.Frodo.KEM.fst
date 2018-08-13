module Spec.Frodo.KEM

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Matrix
open Spec.Frodo.Keccak
open Spec.Frodo.Lemmas
open Spec.Frodo.Params
open Spec.Frodo.Encode
open Spec.Frodo.Pack
open Spec.Frodo.Sample
open Spec.Frodo.Gen

module Seq = Lib.Sequence
module Matrix = Spec.Matrix

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.* +FStar.Pervasives'"

let cshake_frodo = cshake128_frodo
let frodo_gen_matrix = frodo_gen_matrix_cshake

let bytes_mu: size_nat =
  (params_extracted_bits * params_nbar * params_nbar) / 8

let crypto_publickeybytes: size_nat =
  bytes_seed_a + (params_logq * params_n * params_nbar) / 8

let crypto_secretkeybytes: size_nat =
  crypto_bytes + crypto_publickeybytes + 2 * params_n * params_nbar

let crypto_ciphertextbytes: size_nat =
  ((params_nbar * params_n + params_nbar * params_nbar) * params_logq) / 8 + crypto_bytes

val expand_crypto_ciphertextbytes: unit -> Lemma
   (crypto_ciphertextbytes ==
    params_logq * params_nbar * params_n / 8
    + (params_logq * params_nbar * params_nbar / 8 + crypto_bytes))
let expand_crypto_ciphertextbytes _ = ()

val crypto_kem_keypair:
    coins: lbytes (2 * crypto_bytes + bytes_seed_a)
  -> tuple2 (lbytes crypto_publickeybytes) (lbytes crypto_secretkeybytes)
let crypto_kem_keypair coins =
  let s = Seq.sub coins 0 crypto_bytes in
  let seed_e = Seq.sub coins crypto_bytes crypto_bytes in
  let z = Seq.sub coins (2 * crypto_bytes) bytes_seed_a in
  let seed_a = cshake_frodo bytes_seed_a z (u16 0) bytes_seed_a in

  let a_matrix = frodo_gen_matrix params_n bytes_seed_a seed_a in
  let s_matrix = frodo_sample_matrix params_n params_nbar crypto_bytes seed_e (u16 1) in
  let e_matrix = frodo_sample_matrix params_n params_nbar crypto_bytes seed_e (u16 2) in
  let b_matrix = Matrix.add (Matrix.mul_s a_matrix s_matrix) e_matrix in
  let b = frodo_pack params_n params_nbar b_matrix params_logq in

  let pk = concat seed_a b in
  let sk = concat s (concat pk (matrix_to_lbytes s_matrix)) in
  (pk, sk)

val crypto_kem_enc:
    coins: lbytes bytes_mu
  -> pk: lbytes crypto_publickeybytes
  -> tuple2 (lbytes crypto_ciphertextbytes) (lbytes crypto_bytes)
let crypto_kem_enc coins pk =
  let seed_a = Seq.sub pk 0 bytes_seed_a in
  let b = Seq.sub pk bytes_seed_a (crypto_publickeybytes - bytes_seed_a) in

  let g = cshake_frodo (crypto_publickeybytes + bytes_mu) (concat pk coins) (u16 3) (3 * crypto_bytes) in
  let seed_e = Seq.sub g 0 crypto_bytes in
  let k = Seq.sub g crypto_bytes crypto_bytes in
  let d = Seq.sub g (2*crypto_bytes) crypto_bytes in

  let sp_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_e (u16 4) in
  let ep_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_e (u16 5) in
  let a_matrix = frodo_gen_matrix params_n bytes_seed_a seed_a in
  let bp_matrix = Matrix.add (Matrix.mul sp_matrix a_matrix) ep_matrix in
  let c1 = frodo_pack params_nbar params_n bp_matrix params_logq in
  let epp_matrix = frodo_sample_matrix params_nbar params_nbar crypto_bytes seed_e (u16 6) in
  let b_matrix = frodo_unpack params_n params_nbar params_logq b in
  let v_matrix = Matrix.add (Matrix.mul sp_matrix b_matrix) epp_matrix in
  let mu_encode = frodo_key_encode params_extracted_bits coins in
  let c_matrix = Matrix.add v_matrix mu_encode in
  let c2 = frodo_pack params_nbar params_nbar c_matrix params_logq in

  let ss_init = concat c1 (concat c2 (concat k d)) in
  let ss_init_len = (params_logq * params_nbar * params_n) / 8 + (params_logq * params_nbar * params_nbar) / 8 + 2 * crypto_bytes in
  let ss = cshake_frodo ss_init_len ss_init (u16 7) crypto_bytes in
  expand_crypto_ciphertextbytes ();
  let ct = concat c1 (concat c2 d) in
  (ct, ss)

//TODO: fix
#set-options "--admit_smt_queries true"

val crypto_kem_dec:
    ct:lbytes crypto_ciphertextbytes
  -> sk:lbytes crypto_secretkeybytes
  -> lbytes crypto_bytes
let crypto_kem_dec ct sk =
  let c1Len = (params_logq * params_nbar * params_n) / 8 in
  let c2Len = (params_logq * params_nbar * params_nbar) / 8 in
  let c1 = Seq.sub ct 0 c1Len in
  let c2 = Seq.sub ct c1Len c2Len in
  let d = Seq.sub ct (c1Len+c2Len) crypto_bytes in

  let s = Seq.sub sk 0 crypto_bytes in
  let pk = Seq.sub sk crypto_bytes crypto_publickeybytes in
  let s_matrix = matrix_from_lbytes params_n params_nbar
    (Seq.sub sk (crypto_bytes + crypto_publickeybytes) (2*params_n*params_nbar)) in
  let seed_a = Seq.sub pk 0 bytes_seed_a in
  let b = Seq.sub pk bytes_seed_a (crypto_publickeybytes - bytes_seed_a) in

  let bp_matrix = frodo_unpack params_nbar params_n params_logq c1 in
  let c_matrix = frodo_unpack params_nbar params_nbar params_logq c2 in
  let m_matrix = Matrix.sub c_matrix (Matrix.mul_s bp_matrix s_matrix) in
  let mu_decode = frodo_key_decode params_extracted_bits m_matrix in

  let g = cshake_frodo (crypto_publickeybytes + (params_nbar * params_nbar * params_extracted_bits) / 8) (concat pk mu_decode)  (u16 3) (3 * crypto_bytes) in
  let seed_ep = Seq.sub g 0 crypto_bytes in
  let kp = Seq.sub g crypto_bytes crypto_bytes in
  let dp = Seq.sub g (2*crypto_bytes) crypto_bytes in

  let sp_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_ep (u16 4) in
  let ep_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_ep (u16 5) in
  let a_matrix = frodo_gen_matrix params_n bytes_seed_a seed_a in
  let bpp_matrix = Matrix.add (Matrix.mul sp_matrix a_matrix) ep_matrix in

  let epp_matrix = frodo_sample_matrix params_nbar params_nbar crypto_bytes seed_ep (u16 6) in
  let b_matrix = frodo_unpack params_n params_nbar params_logq b in
  let v_matrix = Matrix.add (Matrix.mul sp_matrix b_matrix) epp_matrix in

  let mu_encode = frodo_key_encode params_extracted_bits mu_decode in
  let cp_matrix = Matrix.add v_matrix mu_encode in

  let ss_init = concat c1 c2 in
  let ss_init_len = (params_logq * params_nbar * params_n) / 8
                    + (params_logq * params_nbar * params_nbar) / 8 + 2 * crypto_bytes in
  let ss_init1:lbytes ss_init_len = concat ss_init (concat kp d) in
  let ss_init2:lbytes ss_init_len = concat ss_init (concat s d) in

  let bcond = lbytes_eq d dp
              && matrix_eq params_logq bp_matrix bpp_matrix
              && matrix_eq params_logq c_matrix cp_matrix in
  let ss_init = if bcond then ss_init1 else ss_init2 in
  let ss = cshake_frodo ss_init_len ss_init (u16 7) crypto_bytes in
  ss
