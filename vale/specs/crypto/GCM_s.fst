module GCM_s

open Opaque_s
open Words_s
open Words.Seq_s
open Types_s
open AES_s
open GCTR_s
open GHash_s
open FStar.Seq
open FStar.Mul

unfold type gcm_plain_LE = gctr_plain_LE
unfold type gcm_auth_LE = gctr_plain_LE

#reset-options "--z3rlimit 30"
// little-endian, except for iv_BE
let gcm_encrypt_LE_def (alg:algorithm) (key:aes_key alg) (iv:seq16 nat8) (plain:seq nat8) (auth:seq nat8) :
  Pure (tuple2 (seq nat8) (seq nat8))
    (requires
      length plain <= pow2 39 - 256 /\
      length auth <= pow2 39 - 256
    )
    (ensures fun (c, t) -> True)
  =
  let key_LE = seq_nat8_to_seq_nat32_LE key in
  let iv_BE = be_bytes_to_quad32 iv in
  let h_LE = aes_encrypt_LE alg key_LE (Mkfour 0 0 0 0) in
  let j0_BE = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in

  let c = gctr_encrypt_LE (inc32 j0_BE 1) plain alg key_LE in

  // Sets the first 64-bit number to 8 * length plain, and the second to 8* length auth
  assert_norm (8 * (pow2 39 - 256) < pow2_64);
  let lengths_BE = insert_nat64 (insert_nat64 (Mkfour 0 0 0 0) (8 * length auth) 1) (8 * length plain) 0 in
  let lengths_LE = reverse_bytes_quad32 lengths_BE in

  let zero_padded_c_LE = le_bytes_to_seq_quad32 (pad_to_128_bits c) in
  let zero_padded_a_LE = le_bytes_to_seq_quad32 (pad_to_128_bits auth) in

  let hash_input_LE = append zero_padded_a_LE (append zero_padded_c_LE (create 1 lengths_LE)) in
  let s_LE = ghash_LE h_LE hash_input_LE in
  assert_norm (pow2_32 <= pow2 39 - 256);
  let t = gctr_encrypt_LE j0_BE (le_quad32_to_bytes s_LE) alg key_LE in

  (c, t)

//let gcm_encrypt_LE = make_opaque gcm_encrypt_LE_def
//REVIEW: unexpectedly, the following fails:
//  let fails () : Lemma (gcm_encrypt_LE == make_opaque gcm_encrypt_LE_def) = ()
//So we do this instead:
let gcm_encrypt_LE (alg:algorithm) (key:seq nat8) (iv:seq16 nat8) (plain:seq nat8) (auth:seq nat8) :
  Pure (tuple2 (seq nat8) (seq nat8))
    (requires
      is_aes_key alg key /\
      length plain <= pow2 39 - 256 /\
      length auth <= pow2 39 - 256
    )
    (ensures fun (c, t) -> True)
  =
  make_opaque (gcm_encrypt_LE_def alg key iv plain auth)

let gcm_decrypt_LE_def (alg:algorithm) (key:aes_key alg) (iv:seq16 nat8) (cipher:seq nat8) (auth:seq nat8) (tag:seq nat8) :
  Pure (tuple2 (seq nat8) (bool))
    (requires
      length cipher <= pow2 39 - 256 /\
      length auth <= pow2 39 - 256
    )
    (ensures fun (p, t) -> True)
  =
  let key_LE = seq_nat8_to_seq_nat32_LE key in
  let iv_BE = be_bytes_to_quad32 iv in
  let h_LE = aes_encrypt_LE alg key_LE (Mkfour 0 0 0 0) in
  let j0_BE = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in

  let p = gctr_encrypt_LE (inc32 j0_BE 1) cipher alg key_LE in   // TODO: Rename gctr_encrypt_LE to gctr_LE

  assert_norm (8 * (pow2 39 - 256) < pow2_64);
  let lengths_BE = insert_nat64 (insert_nat64 (Mkfour 0 0 0 0) (8 * length auth) 1) (8 * length cipher) 0 in
  let lengths_LE = reverse_bytes_quad32 lengths_BE in

  let zero_padded_c_LE = le_bytes_to_seq_quad32 (pad_to_128_bits cipher) in
  let zero_padded_a_LE = le_bytes_to_seq_quad32 (pad_to_128_bits auth) in

  let hash_input_LE = append zero_padded_a_LE (append zero_padded_c_LE (create 1 lengths_LE)) in
  let s_LE = ghash_LE h_LE hash_input_LE in
  assert_norm (pow2_32 <= pow2 39 - 256);
  let t = gctr_encrypt_LE j0_BE (le_quad32_to_bytes s_LE) alg key_LE in

  (p, t = tag)

let gcm_decrypt_LE (alg:algorithm) (key:seq nat8) (iv:seq16 nat8) (cipher:seq nat8) (auth:seq nat8) (tag:seq nat8) :
  Pure (tuple2 (seq nat8) (bool))
    (requires
      is_aes_key alg key /\
      length cipher <= pow2 39 - 256 /\
      length auth <= pow2 39 - 256
    )
    (ensures fun (p, t) -> True)
  =
  make_opaque (gcm_decrypt_LE_def alg key iv cipher auth tag)
