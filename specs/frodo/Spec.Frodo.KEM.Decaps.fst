module Spec.Frodo.KEM.Decaps

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul

open Spec.Matrix
open Spec.Frodo.Params
open Spec.Frodo.KEM.Encaps
open Spec.Frodo.Encode
open Spec.Frodo.Pack
open Spec.Frodo.Sample

module Seq = Lib.Sequence
module Matrix = Spec.Matrix

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.* +FStar.Pervasives'"

val get_bp_c_matrices:
    ct:lbytes crypto_ciphertextbytes
  -> matrix params_nbar params_n & matrix params_nbar params_nbar
let get_bp_c_matrices ct =
  let c1Len = params_logq * params_nbar * params_n / 8 in
  let c2Len = params_logq * params_nbar * params_nbar / 8 in
  let c1 = Seq.sub ct 0 c1Len in
  let c2 = Seq.sub ct c1Len c2Len in
  let bp_matrix = frodo_unpack #params_nbar #params_n params_logq c1 in
  let c_matrix  = frodo_unpack #params_nbar #params_nbar params_logq c2 in
  bp_matrix, c_matrix

val get_bpp_cp_matrices:
    g:lbytes (3 * crypto_bytes)
  -> mu_decode:lbytes bytes_mu
  -> sk:lbytes crypto_secretkeybytes
  -> matrix params_nbar params_n & matrix params_nbar params_nbar
let get_bpp_cp_matrices g mu_decode sk =
  assert_norm (params_nbar * params_nbar <= max_size_t);
  let pk = Seq.sub sk crypto_bytes crypto_publickeybytes in
  let seed_a = Seq.sub pk 0 bytes_seed_a in
  let b = Seq.sub pk bytes_seed_a (crypto_publickeybytes - bytes_seed_a) in
  let seed_ep = Seq.sub g 0 crypto_bytes in
  let sp_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_ep (u16 4) in
  let bpp_matrix = frodo_mul_add_sa_plus_e seed_a seed_ep sp_matrix in
  let cp_matrix = frodo_mul_add_sb_plus_e_plus_mu b seed_ep mu_decode sp_matrix in
  bpp_matrix, cp_matrix

val frodo_mu_decode:
    s_bytes:lbytes (2 * params_n * params_nbar)
  -> bp_matrix:matrix params_nbar params_n
  -> c_matrix:matrix params_nbar params_nbar
  -> lbytes bytes_mu
let frodo_mu_decode s_bytes bp_matrix c_matrix =
  let s_matrix = matrix_from_lbytes params_n params_nbar s_bytes in
  let m_matrix = Matrix.sub c_matrix (Matrix.mul_s bp_matrix s_matrix) in
  let mu_decode = frodo_key_decode params_extracted_bits m_matrix in
  mu_decode

val crypto_kem_dec_kp_s_cond:
    d:lbytes crypto_bytes
  -> dp:lbytes crypto_bytes
  -> bp_matrix:matrix params_nbar params_n
  -> bpp_matrix:matrix params_nbar params_n
  -> c_matrix:matrix params_nbar params_nbar
  -> cp_matrix:matrix params_nbar params_nbar
  -> bool
let crypto_kem_dec_kp_s_cond d dp bp_matrix bpp_matrix c_matrix cp_matrix =
  let b1 = lbytes_eq d dp in
  let b2 = matrix_eq params_logq bp_matrix bpp_matrix in
  let b3 = matrix_eq params_logq c_matrix cp_matrix in
  b1 && b2 && b3

val crypto_kem_dec_kp_s:
    mu_decode:lbytes bytes_mu
  -> g:lbytes (3 * crypto_bytes)
  -> bp_matrix:matrix params_nbar params_n
  -> c_matrix:matrix params_nbar params_nbar
  -> sk:lbytes crypto_secretkeybytes
  -> ct:lbytes crypto_ciphertextbytes
  -> bool
let crypto_kem_dec_kp_s mu_decode g bp_matrix c_matrix sk ct =
  expand_crypto_ciphertextbytes ();
  let dp = Seq.sub g (crypto_bytes + crypto_bytes) crypto_bytes in
  let d  = Seq.sub ct (crypto_ciphertextbytes - crypto_bytes) crypto_bytes in
  let bpp_matrix, cp_matrix = get_bpp_cp_matrices g mu_decode sk in
  crypto_kem_dec_kp_s_cond d dp bp_matrix bpp_matrix c_matrix cp_matrix

val crypto_kem_dec_ss0:
    ct:lbytes crypto_ciphertextbytes
  -> kp_s:lbytes crypto_bytes
  -> lbytes crypto_bytes
let crypto_kem_dec_ss0 ct kp_s =
  let c12 = Seq.sub ct 0 (crypto_ciphertextbytes - crypto_bytes) in
  let d = Seq.sub ct (crypto_ciphertextbytes - crypto_bytes) crypto_bytes in
  let ss_init = concat (concat c12 kp_s) d in
  frodo_prf_spec (crypto_ciphertextbytes + crypto_bytes) ss_init (u16 7) crypto_bytes

val crypto_kem_dec_ss:
    ct:lbytes crypto_ciphertextbytes
  -> sk:lbytes crypto_secretkeybytes
  -> g:lbytes (3 * crypto_bytes)
  -> mu_decode:lbytes bytes_mu
  -> bp_matrix:matrix params_nbar params_n
  -> c_matrix:matrix params_nbar params_nbar
  -> lbytes crypto_bytes
let crypto_kem_dec_ss ct sk g mu_decode bp_matrix c_matrix =
  let b = crypto_kem_dec_kp_s mu_decode g bp_matrix c_matrix sk ct in
  let kp = Seq.sub g crypto_bytes crypto_bytes in
  let s  = Seq.sub sk 0 crypto_bytes in
  let kp_s = if b then kp else s in
  crypto_kem_dec_ss0 ct kp_s

val crypto_kem_dec:
    ct:lbytes crypto_ciphertextbytes
  -> sk:lbytes crypto_secretkeybytes
  -> ss:lbytes crypto_bytes
let crypto_kem_dec ct sk =
  expand_crypto_secretkeybytes ();
  let bp_matrix, c_matrix = get_bp_c_matrices ct in
  let s_bytes = Seq.sub sk (crypto_bytes + crypto_publickeybytes) (2 * params_n * params_nbar) in
  let pk = Seq.sub sk crypto_bytes crypto_publickeybytes in
  let mu_decode = frodo_mu_decode s_bytes bp_matrix c_matrix in
  let pk_mu_decode = concat pk mu_decode in
  let g = frodo_prf_spec (crypto_publickeybytes + bytes_mu) pk_mu_decode (u16 3) (3 * crypto_bytes) in
  crypto_kem_dec_ss ct sk g mu_decode bp_matrix c_matrix
