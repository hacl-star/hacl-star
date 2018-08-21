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
open Spec.Frodo.Clear

module Seq = Lib.Sequence
module Matrix = Spec.Matrix

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.* +FStar.Pervasives'"

val update_ct:
    c1:lbytes (params_logq * params_nbar * params_n / 8)
  -> c2:lbytes (params_logq * params_nbar * params_nbar / 8)
  -> d:lbytes crypto_bytes
  -> ct:lbytes crypto_ciphertextbytes
  -> res:lbytes crypto_ciphertextbytes
    {let c1Len = params_logq * params_nbar * params_n / 8 in
     let c2Len = params_logq * params_nbar * params_nbar / 8 in
     expand_crypto_ciphertextbytes ();
     Seq.sub res 0 c1Len == c1 /\
     Seq.sub res c1Len c2Len == c2 /\
     Seq.sub res (c1Len + c2Len) crypto_bytes == d}
let update_ct c1 c2 d ct =
  expand_crypto_ciphertextbytes ();
  let c1Len = params_logq * params_nbar * params_n / 8 in
  let c2Len = params_logq * params_nbar * params_nbar / 8 in

  let ct = update_sub ct 0 c1Len c1 in
  let ct = update_sub ct c1Len c2Len c2 in
  eq_intro (Seq.sub ct 0 c1Len) c1;
  let ct = update_sub ct (c1Len + c2Len) crypto_bytes d in
  eq_intro (Seq.sub ct 0 c1Len) c1;
  eq_intro (Seq.sub ct c1Len c2Len) c2;
  ct

val lemma_update_ct:
    c1:lbytes (params_logq * params_nbar * params_n / 8)
  -> c2:lbytes (params_logq * params_nbar * params_nbar / 8)
  -> d:lbytes crypto_bytes
  -> ct0:lbytes crypto_ciphertextbytes
  -> ct:lbytes crypto_ciphertextbytes
  -> Lemma
    (requires (
      let c1Len = params_logq * params_nbar * params_n / 8 in
      let c2Len = params_logq * params_nbar * params_nbar / 8 in
      expand_crypto_ciphertextbytes ();
      Seq.sub ct 0 c1Len == c1 /\
      Seq.sub ct c1Len c2Len == c2 /\
      Seq.sub ct (c1Len + c2Len) crypto_bytes == d))
    (ensures ct == update_ct c1 c2 d ct0)
let lemma_update_ct c1 c2 d ct0 ct =
  let ct1 = update_ct c1 c2 d ct0 in
  let c1Len = params_logq * params_nbar * params_n / 8 in
  let c2Len = params_logq * params_nbar * params_nbar / 8 in
  expand_crypto_ciphertextbytes ();

  FStar.Seq.Properties.lemma_split (Seq.sub ct 0 (c1Len + c2Len)) c1Len;
  FStar.Seq.Properties.lemma_split (Seq.sub ct1 0 (c1Len + c2Len)) c1Len;
  FStar.Seq.Properties.lemma_split ct (c1Len + c2Len);
  FStar.Seq.Properties.lemma_split ct1 (c1Len + c2Len)

val update_ss_init:
    c12:lbytes (params_logq * params_nbar * params_n / 8 + params_logq * params_nbar * params_nbar / 8)
  -> kd:lbytes (crypto_bytes + crypto_bytes)
  -> ss_init:lbytes (crypto_ciphertextbytes + crypto_bytes)
  -> res:lbytes (crypto_ciphertextbytes + crypto_bytes)
    {let c1Len = params_logq * params_nbar * params_n / 8 in
     let c2Len = params_logq * params_nbar * params_nbar / 8 in
     expand_crypto_ciphertextbytes ();
     Seq.sub res 0 (c1Len + c2Len) == c12 /\
     Seq.sub res (c1Len + c2Len) (crypto_bytes + crypto_bytes) == kd}
let update_ss_init c12 kd ss_init =
  expand_crypto_ciphertextbytes ();
  let c1Len = params_logq * params_nbar * params_n / 8 in
  let c2Len = params_logq * params_nbar * params_nbar / 8 in
  let ss_init = update_sub ss_init 0 (c1Len + c2Len) c12 in
  let ss_init = update_sub ss_init (c1Len + c2Len) (crypto_bytes + crypto_bytes) kd in
  eq_intro (Seq.sub ss_init 0 (c1Len + c2Len)) c12;
  ss_init

val lemma_updade_ss_init:
    c12:lbytes (params_logq * params_nbar * params_n / 8 + params_logq * params_nbar * params_nbar / 8)
  -> kd:lbytes (crypto_bytes + crypto_bytes)
  -> ss_init0:lbytes (crypto_ciphertextbytes + crypto_bytes)
  -> ss_init:lbytes (crypto_ciphertextbytes + crypto_bytes)
  -> Lemma
    (requires (
      let c1Len = params_logq * params_nbar * params_n / 8 in
      let c2Len = params_logq * params_nbar * params_nbar / 8 in
      expand_crypto_ciphertextbytes ();
      Seq.sub ss_init 0 (c1Len + c2Len) == c12 /\
      Seq.sub ss_init (c1Len + c2Len) (crypto_bytes + crypto_bytes) == kd))
    (ensures ss_init == update_ss_init c12 kd ss_init0)
let lemma_updade_ss_init c12 kd ss_init0 ss_init =
  let ss_init1 = update_ss_init c12 kd ss_init0 in
  let c1Len = params_logq * params_nbar * params_n / 8 in
  let c2Len = params_logq * params_nbar * params_nbar / 8 in
  expand_crypto_ciphertextbytes ();
  FStar.Seq.Properties.lemma_split ss_init (c1Len + c2Len);
  FStar.Seq.Properties.lemma_split ss_init1 (c1Len + c2Len)

val update_ss:
    c12:lbytes (params_logq * params_nbar * params_n / 8 + params_logq * params_nbar * params_nbar / 8)
  -> kd:lbytes (crypto_bytes + crypto_bytes)
  -> ss:lbytes crypto_bytes
  -> res:lbytes crypto_bytes
let update_ss c12 kd ss =
  let ss_init_len = crypto_ciphertextbytes + crypto_bytes in
  let ss_init = Seq.create ss_init_len (u8 0) in
  let ss_init = update_ss_init c12 kd ss_init in
  let ss = cshake_frodo ss_init_len ss_init (u16 7) crypto_bytes in
  ss

#set-options "--max_ifuel 1"

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
  let ep_matrix = clear_matrix ep_matrix in
  b_matrix

val frodo_mul_add_sb_plus_e:
     b:lbytes (params_logq * params_n * params_nbar / 8)
  -> seed_e:lbytes crypto_bytes
  -> sp_matrix:matrix params_nbar params_n
  -> matrix params_nbar params_nbar
let frodo_mul_add_sb_plus_e b seed_e sp_matrix =
  let b_matrix = frodo_unpack params_n params_nbar params_logq b in
  let epp_matrix = frodo_sample_matrix params_nbar params_nbar crypto_bytes seed_e (u16 6) in
  let v_matrix = Matrix.add (Matrix.mul sp_matrix b_matrix) epp_matrix in
  let epp_matrix = clear_matrix epp_matrix in
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

#set-options "--max_ifuel 0"

val crypto_kem_enc_ct_pack_c1:
    seed_a:lbytes bytes_seed_a
  -> seed_e:lbytes crypto_bytes
  -> sp_matrix:matrix params_nbar params_n
  -> lbytes (params_logq * params_nbar * params_n / 8)
let crypto_kem_enc_ct_pack_c1 seed_a seed_e sp_matrix =
  let bp_matrix = frodo_mul_add_sa_plus_e seed_a seed_e sp_matrix in
  assume (params_n % 8 = 0);
  let c1 = frodo_pack bp_matrix params_logq in
  c1

val crypto_kem_enc_ct_pack_c2:
    seed_e:lbytes crypto_bytes
  -> coins:lbytes (params_nbar * params_nbar * params_extracted_bits / 8)
  -> b:lbytes (params_logq * params_n * params_nbar / 8)
  -> sp_matrix:matrix params_nbar params_n
  -> lbytes (params_logq * params_nbar * params_nbar / 8)
let crypto_kem_enc_ct_pack_c2 seed_e coins b sp_matrix =
  let v_matrix = frodo_mul_add_sb_plus_e_plus_mu b seed_e coins sp_matrix in
  let c2 = frodo_pack v_matrix params_logq in
  let v_matrix = clear_matrix v_matrix in
  c2

#set-options "--max_ifuel 1"

val crypto_kem_enc_ct:
    pk:lbytes crypto_publickeybytes
  -> g:lbytes (3 * crypto_bytes)
  -> coins:lbytes (params_nbar * params_nbar * params_extracted_bits / 8)
  -> ct:lbytes crypto_ciphertextbytes
  -> lbytes crypto_ciphertextbytes
let crypto_kem_enc_ct pk g coins ct = admit(); //FIXME
  let seed_a = Seq.sub pk 0 bytes_seed_a in
  let b = Seq.sub pk bytes_seed_a (crypto_publickeybytes - bytes_seed_a) in
  let seed_e = Seq.sub g 0 crypto_bytes in
  let d = Seq.sub g (2 * crypto_bytes) crypto_bytes in

  let sp_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_e (u16 4) in
  let c1 = crypto_kem_enc_ct_pack_c1 seed_a seed_e sp_matrix in
  let c2 = crypto_kem_enc_ct_pack_c2 seed_e coins b sp_matrix in

  let ct = update_ct c1 c2 d ct in
  let sp_matrix = clear_matrix sp_matrix in
  ct

#set-options "--max_ifuel 0"

val crypto_kem_enc:
    coins:lbytes bytes_mu
  -> pk:lbytes crypto_publickeybytes
  -> ct:lbytes crypto_ciphertextbytes
  -> ss:lbytes crypto_bytes
  -> tuple2 (lbytes crypto_ciphertextbytes) (lbytes crypto_bytes)
let crypto_kem_enc coins pk ct ss =
  expand_crypto_ciphertextbytes ();
  let pk_coins = Seq.create (crypto_publickeybytes + bytes_mu) (u8 0) in
  let pk_coins = update_sub pk_coins 0 crypto_publickeybytes pk in
  let pk_coins = update_sub pk_coins crypto_publickeybytes bytes_mu coins in
  let g = cshake_frodo (crypto_publickeybytes + bytes_mu) pk_coins (u16 3) (3 * crypto_bytes) in

  let ct = crypto_kem_enc_ct pk g coins ct in

  let c1Len = params_logq * params_nbar * params_n / 8 in
  let c2Len = params_logq * params_nbar * params_nbar / 8 in
  let c12 = Seq.sub ct 0 (c1Len + c2Len) in
  let kd = Seq.sub g crypto_bytes (crypto_bytes + crypto_bytes) in
  let ss = update_ss c12 kd ss in
  ct, ss
