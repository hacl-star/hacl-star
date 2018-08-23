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
open Spec.Frodo.KEM.Encaps
open Spec.Frodo.Encode
open Spec.Frodo.Pack
open Spec.Frodo.Sample

module Seq = Lib.Sequence
module Matrix = Spec.Matrix

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.* +FStar.Pervasives'"

val frodo_sub_mul_c_minus_bs_inner:
    sk:lbytes crypto_secretkeybytes
  -> bp_matrix:matrix params_nbar params_n
  -> c_matrix:matrix params_nbar params_nbar
  -> matrix params_nbar params_nbar
let frodo_sub_mul_c_minus_bs_inner sk bp_matrix c_matrix =
  expand_crypto_secretkeybytes ();
  let s_bytes = Seq.sub sk (crypto_bytes + crypto_publickeybytes) (2 * params_n * params_nbar) in
  let s_matrix = matrix_from_lbytes params_n params_nbar s_bytes in
  let m_matrix = Matrix.sub c_matrix (Matrix.mul_s bp_matrix s_matrix) in
  m_matrix

val frodo_sub_mul_c_minus_bs:
    sk:lbytes crypto_secretkeybytes
  -> bp_matrix:matrix params_nbar params_n
  -> c_matrix:matrix params_nbar params_nbar
  -> lbytes (params_nbar * params_nbar * params_extracted_bits / 8)
let frodo_sub_mul_c_minus_bs sk bp_matrix c_matrix = admit(); //FIX
  let m_matrix = frodo_sub_mul_c_minus_bs_inner sk bp_matrix c_matrix in
  let mu_decode = frodo_key_decode params_extracted_bits m_matrix in
  mu_decode

val get_dec_ss:
    ct:lbytes crypto_ciphertextbytes
  -> kp_s:lbytes crypto_bytes
  -> ss:lbytes crypto_bytes
let get_dec_ss ct kp_s =
  let c12 = Seq.sub ct 0 (crypto_ciphertextbytes - crypto_bytes) in
  let d = Seq.sub ct (crypto_ciphertextbytes - crypto_bytes) crypto_bytes in

  let ss_init_len = crypto_ciphertextbytes + crypto_bytes in
  let ss_init = Seq.create ss_init_len (u8 0) in

  let ss_init = update_sub ss_init 0 (crypto_ciphertextbytes - crypto_bytes) c12 in
  let ss_init = update_sub ss_init (crypto_ciphertextbytes - crypto_bytes) crypto_bytes kp_s in
  let ss_init = update_sub ss_init crypto_ciphertextbytes crypto_bytes d in
  let ss = frodo_prf_spec ss_init_len ss_init (u16 7) crypto_bytes in
  ss

val get_bpp_cp_matrices:
    g:lbytes (3 * crypto_bytes)
  -> mu_decode:lbytes (params_nbar * params_nbar * params_extracted_bits / 8)
  -> sk:lbytes crypto_secretkeybytes
  -> tuple2 (matrix params_nbar params_n) (matrix params_nbar params_nbar)
let get_bpp_cp_matrices g mu_decode sk =
  let pk = Seq.sub sk crypto_bytes crypto_publickeybytes in
  let seed_a = Seq.sub pk 0 bytes_seed_a in
  let b = Seq.sub pk bytes_seed_a (crypto_publickeybytes - bytes_seed_a) in
  let seed_ep = Seq.sub g 0 crypto_bytes in

  let sp_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_ep (u16 4) in
  let bpp_matrix = frodo_mul_add_sa_plus_e seed_a seed_ep sp_matrix in
  let cp_matrix = frodo_mul_add_sb_plus_e_plus_mu b seed_ep mu_decode sp_matrix in
  bpp_matrix, cp_matrix

inline_for_extraction noextract
val crypto_kem_dec_ss_inner:
    mu_decode:lbytes (params_nbar * params_nbar * params_extracted_bits / 8)
  -> g:lbytes (3 * crypto_bytes)
  -> bp_matrix:matrix params_nbar params_n
  -> c_matrix:matrix params_nbar params_nbar
  -> sk:lbytes crypto_secretkeybytes
  -> ct:lbytes crypto_ciphertextbytes
  -> lbytes crypto_bytes
let crypto_kem_dec_ss_inner mu_decode g bp_matrix c_matrix sk ct =
  expand_crypto_ciphertextbytes ();
  expand_crypto_secretkeybytes ();
  let dp = Seq.sub #_ #(3 * crypto_bytes) g (crypto_bytes + crypto_bytes) crypto_bytes in
  let d  = Seq.sub #_ #crypto_ciphertextbytes ct (crypto_ciphertextbytes - crypto_bytes) crypto_bytes in
  let kp = Seq.sub #_ #(3 * crypto_bytes) g crypto_bytes crypto_bytes in
  let s  = Seq.sub #_ #crypto_secretkeybytes sk 0 crypto_bytes in

  let bpp_matrix, cp_matrix = get_bpp_cp_matrices g mu_decode sk in
  let b1 = lbytes_eq d dp in
  let b2 = matrix_eq params_logq bp_matrix bpp_matrix in
  let b3 = matrix_eq params_logq c_matrix cp_matrix in
  let kp_s = if (b1 && b2 && b3) then kp else s in
  let ss = get_dec_ss ct kp_s in
  ss

val crypto_kem_dec_ss:
    mu_decode:lbytes (params_nbar * params_nbar * params_extracted_bits / 8)
  -> bp_matrix:matrix params_nbar params_n
  -> c_matrix:matrix params_nbar params_nbar
  -> sk:lbytes crypto_secretkeybytes
  -> ct:lbytes crypto_ciphertextbytes
  -> ss:lbytes crypto_bytes
let crypto_kem_dec_ss mu_decode bp_matrix c_matrix sk ct =
  let pk = Seq.sub sk crypto_bytes crypto_publickeybytes in
  let mu_decode_len = params_nbar * params_nbar * params_extracted_bits / 8 in
  let pk_mu_decode_len = crypto_publickeybytes + mu_decode_len in
  let pk_mu_decode = Seq.create pk_mu_decode_len (u8 0) in
  let pk_mu_decode = update_sub pk_mu_decode 0 crypto_publickeybytes pk in
  let pk_mu_decode = update_sub pk_mu_decode crypto_publickeybytes mu_decode_len mu_decode in

  let g = frodo_prf_spec pk_mu_decode_len pk_mu_decode (u16 3) (3 * crypto_bytes) in
  let ss = crypto_kem_dec_ss_inner mu_decode g bp_matrix c_matrix sk ct in
  ss

val crypto_kem_dec:
    ct:lbytes crypto_ciphertextbytes
  -> sk:lbytes crypto_secretkeybytes
  -> ss:lbytes crypto_bytes
let crypto_kem_dec ct sk =
  let c1Len = params_logq * params_nbar * params_n / 8 in
  let c2Len = params_logq * params_nbar * params_nbar / 8 in
  let c1 = Seq.sub ct 0 c1Len in
  let c2 = Seq.sub ct c1Len c2Len in

  let bp_matrix = frodo_unpack params_nbar params_n params_logq c1 in
  let c_matrix  = frodo_unpack params_nbar params_nbar params_logq c2 in
  let mu_decode = frodo_sub_mul_c_minus_bs sk bp_matrix c_matrix in
  let ss = crypto_kem_dec_ss mu_decode bp_matrix c_matrix sk ct in
  ss
