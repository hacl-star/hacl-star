module Spec.Frodo.KEM.Decaps

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Matrix
open Spec.Frodo.Params
open Spec.Frodo.KEM.Encaps
open Spec.Frodo.Encode
open Spec.Frodo.Pack
open Spec.Frodo.Sample

module LSeq = Lib.Sequence
module Matrix = Spec.Matrix
module KG = Spec.Frodo.KEM.KeyGen
module FL = Spec.Frodo.Lemmas

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val get_bp_c_matrices:
    a:frodo_alg
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> matrix params_nbar (params_n a) & matrix params_nbar params_nbar

let get_bp_c_matrices a ct =
  expand_crypto_ciphertextbytes a;
  let c1 = LSeq.sub ct 0 (ct1bytes_len a) in
  let c2 = LSeq.sub ct (ct1bytes_len a) (ct2bytes_len a) in
  let bp_matrix = frodo_unpack #params_nbar #(params_n a) (params_logq a) c1 in
  let c_matrix  = frodo_unpack #params_nbar #params_nbar (params_logq a) c2 in
  bp_matrix, c_matrix


val frodo_mu_decode:
    a:frodo_alg
  -> s_bytes:lbytes (secretmatrixbytes_len a)
  -> bp_matrix:matrix params_nbar (params_n a)
  -> c_matrix:matrix params_nbar params_nbar
  -> lbytes (bytes_mu a)

let frodo_mu_decode a s_bytes bp_matrix c_matrix =
  let s_matrix = matrix_from_lbytes (params_n a) params_nbar s_bytes in
  let m_matrix = Matrix.sub c_matrix (Matrix.mul_s bp_matrix s_matrix) in
  let mu_decode = frodo_key_decode (params_logq a) (params_extracted_bits a) params_nbar m_matrix in
  mu_decode


val get_bpp_cp_matrices_:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> mu_decode:lbytes (bytes_mu a) //mup
  -> sk:lbytes (crypto_secretkeybytes a)
  -> sp_matrix:matrix params_nbar (params_n a)
  -> ep_matrix:matrix params_nbar (params_n a)
  -> epp_matrix:matrix params_nbar params_nbar
  -> matrix params_nbar (params_n a) & matrix params_nbar params_nbar

let get_bpp_cp_matrices_ a gen_a mu_decode sk sp_matrix ep_matrix epp_matrix =
  let pk = LSeq.sub sk (crypto_bytes a) (crypto_publickeybytes a) in
  let seed_a = LSeq.sub pk 0 bytes_seed_a in
  let b = LSeq.sub pk bytes_seed_a (crypto_publickeybytes a - bytes_seed_a) in

  let bpp_matrix = frodo_mul_add_sa_plus_e a gen_a seed_a sp_matrix ep_matrix in
  let cp_matrix = frodo_mul_add_sb_plus_e_plus_mu a mu_decode b sp_matrix epp_matrix in

  let bpp_matrix = mod_pow2 (params_logq a) bpp_matrix in
  let cp_matrix = mod_pow2 (params_logq a) cp_matrix in
  bpp_matrix, cp_matrix


val get_bpp_cp_matrices:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> mu_decode:lbytes (bytes_mu a) //mup
  -> seed_se:lbytes (crypto_bytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> matrix params_nbar (params_n a) & matrix params_nbar params_nbar

let get_bpp_cp_matrices a gen_a mu_decode seed_se sk =
  let sp_matrix, ep_matrix, epp_matrix = get_sp_ep_epp_matrices a seed_se in
  let bpp_matrix, cp_matrix = get_bpp_cp_matrices_ a gen_a mu_decode sk sp_matrix ep_matrix epp_matrix in
  bpp_matrix, cp_matrix


val crypto_kem_dec_kp_s_cond:
    a:frodo_alg
  -> bp_matrix:matrix params_nbar (params_n a)
  -> bpp_matrix:matrix params_nbar (params_n a)
  -> c_matrix:matrix params_nbar params_nbar
  -> cp_matrix:matrix params_nbar params_nbar
  -> Pure uint16
    (requires True)
    (ensures  fun r ->
      ((bp_matrix == bpp_matrix /\ c_matrix == cp_matrix) ==> v r == v (ones U16 SEC)) /\
      ((bp_matrix =!= bpp_matrix \/ c_matrix =!= cp_matrix) ==> v r == 0))

let crypto_kem_dec_kp_s_cond a bp_matrix bpp_matrix c_matrix cp_matrix =
  let b1 = matrix_eq bp_matrix bpp_matrix in
  let b2 = matrix_eq c_matrix cp_matrix in
  logand_lemma b1 b2;
  b1 &. b2


val crypto_kem_dec_kp_s:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> mu_decode:lbytes (bytes_mu a)
  -> seed_se:lbytes (crypto_bytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> bp_matrix:matrix params_nbar (params_n a)
  -> c_matrix:matrix params_nbar params_nbar
  -> mask:uint16{v mask == 0 \/ v mask == v (ones U16 SEC)}

let crypto_kem_dec_kp_s a gen_a mu_decode seed_se sk bp_matrix c_matrix =
  let bpp_matrix, cp_matrix = get_bpp_cp_matrices a gen_a mu_decode seed_se sk in
  let mask = crypto_kem_dec_kp_s_cond a bp_matrix bpp_matrix c_matrix cp_matrix in
  mask


val crypto_kem_dec_ss0:
    a:frodo_alg
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> mask:uint16{v mask == 0 \/ v mask == v (ones U16 SEC)}
  -> kp:lbytes (crypto_bytes a)
  -> s:lbytes (crypto_bytes a)
  -> lbytes (crypto_bytes a)

let crypto_kem_dec_ss0 a ct mask kp s =
  FL.lemma_mask_cast mask;
  let kp_s = seq_mask_select kp s (to_u8 mask) in
  //if v mask = v (ones U16 SEC) then kp else s in

  let shake_input_ss = concat ct kp_s in
  let ss = frodo_shake a (crypto_ciphertextbytes a + crypto_bytes a) shake_input_ss (crypto_bytes a) in
  ss


val crypto_kem_dec_seed_se_k:
    a:frodo_alg
  -> mu_decode:lbytes (bytes_mu a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> lbytes (2 * crypto_bytes a)

let crypto_kem_dec_seed_se_k a mu_decode sk =
  expand_crypto_secretkeybytes a;
  let pkh = LSeq.sub sk (crypto_secretkeybytes a - bytes_pkhash a) (bytes_pkhash a) in
  let pkh_mu_decode = concat pkh mu_decode in
  let seed_se_k = frodo_shake a (bytes_pkhash a + bytes_mu a) pkh_mu_decode (2 * crypto_bytes a) in
  seed_se_k


val crypto_kem_dec_ss1:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> mu_decode:lbytes (bytes_mu a)
  -> seed_se_k:lbytes (2 * crypto_bytes a)
  -> bp_matrix:matrix params_nbar (params_n a)
  -> c_matrix:matrix params_nbar params_nbar
  -> lbytes (crypto_bytes a)

let crypto_kem_dec_ss1 a gen_a ct sk mu_decode seed_se_k bp_matrix c_matrix =
  let seed_se = LSeq.sub seed_se_k 0 (crypto_bytes a) in
  let kp = LSeq.sub seed_se_k (crypto_bytes a) (crypto_bytes a) in
  let s  = LSeq.sub sk 0 (crypto_bytes a) in

  let mask = crypto_kem_dec_kp_s a gen_a mu_decode seed_se sk bp_matrix c_matrix in
  let ss = crypto_kem_dec_ss0 a ct mask kp s in
  ss


val crypto_kem_dec_ss2:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> mu_decode:lbytes (bytes_mu a)
  -> bp_matrix:matrix params_nbar (params_n a)
  -> c_matrix:matrix params_nbar params_nbar
  -> lbytes (crypto_bytes a)

let crypto_kem_dec_ss2 a gen_a ct sk mu_decode bp_matrix c_matrix =
  let seed_se_k = crypto_kem_dec_seed_se_k a mu_decode sk in
  let ss = crypto_kem_dec_ss1 a gen_a ct sk mu_decode seed_se_k bp_matrix c_matrix in
  ss


val crypto_kem_dec_mu:
    a:frodo_alg
  -> sk:lbytes (crypto_secretkeybytes a)
  -> bp_matrix:matrix params_nbar (params_n a)
  -> c_matrix:matrix params_nbar params_nbar
  -> lbytes (bytes_mu a)

let crypto_kem_dec_mu a sk bp_matrix c_matrix =
  expand_crypto_secretkeybytes a;
  let s_bytes = LSeq.sub sk (crypto_bytes a + crypto_publickeybytes a) (secretmatrixbytes_len a) in
  let mu_decode = frodo_mu_decode a s_bytes bp_matrix c_matrix in
  mu_decode


val crypto_kem_dec_:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> bp_matrix:matrix params_nbar (params_n a)
  -> c_matrix:matrix params_nbar params_nbar
  -> lbytes (crypto_bytes a)

let crypto_kem_dec_ a gen_a ct sk bp_matrix c_matrix =
  let mu_decode = crypto_kem_dec_mu a sk bp_matrix c_matrix in
  let ss = crypto_kem_dec_ss2 a gen_a ct sk mu_decode bp_matrix c_matrix in
  ss


val crypto_kem_dec:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> lbytes (crypto_bytes a)

let crypto_kem_dec a gen_a ct sk =
  let bp_matrix, c_matrix = get_bp_c_matrices a ct in
  let ss = crypto_kem_dec_ a gen_a ct sk bp_matrix c_matrix in
  ss
