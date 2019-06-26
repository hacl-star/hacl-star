module Vale.AES.GCM_s

open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Def.Words.Seq_s
open Vale.Def.Types_s
open Vale.AES.AES_s
open Vale.AES.GCTR_s
open Vale.AES.GHash_s
open FStar.Seq
open FStar.Mul

unfold type gcm_plain_LE = gctr_plain_LE
unfold type gcm_auth_LE = gctr_plain_LE

#reset-options "--z3rlimit 30"

type supported_iv_LE:eqtype = iv:seq nat8 { 1 <= 8 * (length iv) /\ 8 * (length iv) < pow2_64 }

let compute_iv_BE (h_LE:quad32) (iv:supported_iv_LE) : quad32
  =
  if 8 * (length iv) = 96 then (
    let iv_LE = le_bytes_to_quad32 (pad_to_128_bits iv) in
    let iv_BE = reverse_bytes_quad32 iv_LE in
    let j0_BE = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in
    j0_BE
  ) else (
    let padded_iv_quads = le_bytes_to_seq_quad32 (pad_to_128_bits iv) in
    let length_BE = insert_nat64 (Mkfour 0 0 0 0) (8 * length iv) 0 in
    let length_LE = reverse_bytes_quad32 length_BE in
    let hash_input_LE = append padded_iv_quads (create 1 length_LE) in
    let hash_output_LE = ghash_LE h_LE hash_input_LE in
    reverse_bytes_quad32 hash_output_LE
  )

// little-endian 
let gcm_encrypt_LE_def (alg:algorithm) (key:aes_key alg) (iv:supported_iv_LE) (plain:seq nat8) (auth:seq nat8) :
  Pure (tuple2 (seq nat8) (seq nat8))
    (requires
      length plain < pow2_32 /\
      length auth < pow2_32
    )
    (ensures fun (c, t) -> True)
  =
  let key_LE = seq_nat8_to_seq_nat32_LE key in
  let h_LE = aes_encrypt_LE alg key_LE (Mkfour 0 0 0 0) in
  let j0_BE = compute_iv_BE h_LE iv in

  let c = gctr_encrypt_LE (inc32 j0_BE 1) plain alg key_LE in

  // Sets the first 64-bit number to 8 * length plain, and the second to 8* length auth
  let lengths_BE = insert_nat64 (insert_nat64 (Mkfour 0 0 0 0) (8 * length auth) 1) (8 * length plain) 0 in
  let lengths_LE = reverse_bytes_quad32 lengths_BE in

  let zero_padded_c_LE = le_bytes_to_seq_quad32 (pad_to_128_bits c) in
  let zero_padded_a_LE = le_bytes_to_seq_quad32 (pad_to_128_bits auth) in

  let hash_input_LE = append zero_padded_a_LE (append zero_padded_c_LE (create 1 lengths_LE)) in
  let s_LE = ghash_LE h_LE hash_input_LE in
  let t = gctr_encrypt_LE j0_BE (le_quad32_to_bytes s_LE) alg key_LE in

  (c, t)

//let gcm_encrypt_LE = make_opaque gcm_encrypt_LE_def
//REVIEW: unexpectedly, the following fails:
//  let fails () : Lemma (gcm_encrypt_LE == make_opaque gcm_encrypt_LE_def) = ()
//So we do this instead:
let gcm_encrypt_LE (alg:algorithm) (key:seq nat8) (iv:supported_iv_LE) (plain:seq nat8) (auth:seq nat8) :
  Pure (tuple2 (seq nat8) (seq nat8))
    (requires
      is_aes_key alg key /\
      length plain < pow2_32 /\
      length auth < pow2_32
    )
    (ensures fun (c, t) -> True)
  =
  make_opaque (gcm_encrypt_LE_def alg key iv plain auth)

let gcm_decrypt_LE_def (alg:algorithm) (key:aes_key alg) (iv:supported_iv_LE) (cipher:seq nat8) (auth:seq nat8) (tag:seq nat8) :
  Pure (tuple2 (seq nat8) (bool))
    (requires
      length cipher < pow2_32 /\
      length auth < pow2_32
    )
    (ensures fun (p, t) -> True)
  =
  let key_LE = seq_nat8_to_seq_nat32_LE key in
  let h_LE = aes_encrypt_LE alg key_LE (Mkfour 0 0 0 0) in
  let j0_BE = compute_iv_BE h_LE iv in

  let p = gctr_encrypt_LE (inc32 j0_BE 1) cipher alg key_LE in   // TODO: Rename gctr_encrypt_LE to gctr_LE

  let lengths_BE = insert_nat64 (insert_nat64 (Mkfour 0 0 0 0) (8 * length auth) 1) (8 * length cipher) 0 in
  let lengths_LE = reverse_bytes_quad32 lengths_BE in

  let zero_padded_c_LE = le_bytes_to_seq_quad32 (pad_to_128_bits cipher) in
  let zero_padded_a_LE = le_bytes_to_seq_quad32 (pad_to_128_bits auth) in

  let hash_input_LE = append zero_padded_a_LE (append zero_padded_c_LE (create 1 lengths_LE)) in
  let s_LE = ghash_LE h_LE hash_input_LE in
  let t = gctr_encrypt_LE j0_BE (le_quad32_to_bytes s_LE) alg key_LE in

  (p, t = tag)

let gcm_decrypt_LE (alg:algorithm) (key:seq nat8) (iv:supported_iv_LE) (cipher:seq nat8) (auth:seq nat8) (tag:seq nat8) :
  Pure (tuple2 (seq nat8) (bool))
    (requires
      is_aes_key alg key /\
      length cipher < pow2_32 /\
      length auth < pow2_32
    )
    (ensures fun (p, t) -> True)
  =
  make_opaque (gcm_decrypt_LE_def alg key iv cipher auth tag)
