module Spec.Frodo.KEM.Decaps

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

//TODO: fix
#set-options "--admit_smt_queries true"

val crypto_kem_dec:
    ct:lbytes crypto_ciphertextbytes
  -> sk:lbytes crypto_secretkeybytes
  -> ss:lbytes crypto_bytes
  -> lbytes crypto_bytes
let crypto_kem_dec ct sk ss =
  let c1Len = params_logq * params_nbar * params_n / 8 in
  let c2Len = params_logq * params_nbar * params_nbar / 8 in
  let c1 = Seq.sub ct 0 c1Len in
  let c2 = Seq.sub ct c1Len c2Len in
  let d = Seq.sub ct (c1Len + c2Len) crypto_bytes in

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

  let bytes_mu = params_nbar * params_nbar * params_extracted_bits / 8 in
  let pk_mu_decode = Seq.create (crypto_publickeybytes + bytes_mu) (u8 0) in
  let pk_mu_decode = update_sub pk_mu_decode 0 crypto_publickeybytes pk in
  let pk_mu_decode = update_sub pk_mu_decode crypto_publickeybytes bytes_mu mu_decode in
  let g = cshake_frodo (crypto_publickeybytes + bytes_mu) pk_mu_decode (u16 3) (3 * crypto_bytes) in
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

  let ss_init_len = c1Len + c2Len + 2 * crypto_bytes in
  let ss_init = Seq.create ss_init_len (u8 0) in
  let ss_init = update_sub ss_init 0 c1Len c1 in
  let ss_init = update_sub ss_init c1Len c2Len c2 in
  let ss_init = update_sub ss_init (ss_init_len - crypto_bytes) crypto_bytes d in
  let ss_init1:lbytes ss_init_len = update_sub ss_init (c1Len + c2Len) crypto_bytes kp in
  let ss_init2:lbytes ss_init_len = update_sub ss_init (c1Len + c2Len) crypto_bytes s in

  let bcond = lbytes_eq d dp
              && matrix_eq params_logq bp_matrix bpp_matrix
              && matrix_eq params_logq c_matrix cp_matrix in
  let ss_init = if bcond then ss_init1 else ss_init2 in
  let ss = cshake_frodo ss_init_len ss_init (u16 7) crypto_bytes in
  ss
