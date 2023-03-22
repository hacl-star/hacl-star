module Vale.AES.GCM_BE_s

open Vale.Arch.Types
open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Def.Words.Seq_s
open Vale.Def.Words.Two_s
open Vale.Def.Words.Four_s
open Vale.Def.Types_s
open Vale.AES.AES_BE_s
open Vale.AES.GCTR_BE_s
open Vale.AES.GHash_BE_s
open FStar.Seq
open FStar.Mul

#reset-options "--z3rlimit 30"

type supported_iv_BE:eqtype = iv:seq nat8 { 1 <= 8 * (length iv) /\ 8 * (length iv) < pow2_64 }

let compute_iv_BE_def (h_BE:quad32) (iv:supported_iv_BE) : quad32
  =
  if 8 * (length iv) = 96 then (
    let iv_BE = be_bytes_to_quad32 (pad_to_128_bits iv) in
    let j0_BE = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in
    j0_BE
  ) else (
    let padded_iv_quads = be_bytes_to_seq_quad32 (pad_to_128_bits iv) in
    let length_BE = two_two_to_four (Mktwo (nat_to_two 32 0) (nat_to_two 32 (8 * length iv))) in
    let hash_input_BE = append padded_iv_quads (create 1 length_BE) in
    let hash_output_BE = ghash_BE h_BE hash_input_BE in
    hash_output_BE
  )
[@"opaque_to_smt"] let compute_iv_BE = opaque_make compute_iv_BE_def
irreducible let compute_iv_BE_reveal = opaque_revealer (`%compute_iv_BE) compute_iv_BE compute_iv_BE_def

let gcm_encrypt_BE_def (alg:algorithm) (key:seq nat8) (iv:supported_iv_BE) (plain:seq nat8) (auth:seq nat8) :
  Pure (seq nat8 & seq nat8)
    (requires
      is_aes_key alg key /\
      length plain < pow2_32 /\
      length auth < pow2_32
    )
    (ensures fun (c, t) -> True)
  =
  let key_BE = seq_nat8_to_seq_nat32_BE key in
  let h_BE = aes_encrypt_word alg key_BE (Mkfour 0 0 0 0) in
  let j0_BE = compute_iv_BE h_BE iv in

  let c = gctr_encrypt (inc32 j0_BE 1) plain alg key_BE in

  // Sets the first 64-bit number to 8 * length plain, and the second to 8* length auth
  let lengths_BE = two_two_to_four (Mktwo (nat_to_two 32 (8 * length auth)) (nat_to_two 32 (8 * length plain))) in

  let zero_padded_c_BE = be_bytes_to_seq_quad32 (pad_to_128_bits c) in
  let zero_padded_a_BE = be_bytes_to_seq_quad32 (pad_to_128_bits auth) in

  let hash_input_BE = append zero_padded_a_BE (append zero_padded_c_BE (create 1 lengths_BE)) in
  let s_BE = ghash_BE h_BE hash_input_BE in
  let t = gctr_encrypt j0_BE (be_quad32_to_bytes s_BE) alg key_BE in

  (c, t)
[@"opaque_to_smt"] let gcm_encrypt_BE = opaque_make gcm_encrypt_BE_def
irreducible let gcm_encrypt_BE_reveal = opaque_revealer (`%gcm_encrypt_BE) gcm_encrypt_BE gcm_encrypt_BE_def

let gcm_decrypt_BE_def (alg:algorithm) (key:seq nat8) (iv:supported_iv_BE) (cipher:seq nat8) (auth:seq nat8) (tag:seq nat8) :
  Pure (seq nat8 & bool)
    (requires
      is_aes_key alg key /\
      length cipher < pow2_32 /\
      length auth < pow2_32
    )
    (ensures fun (p, t) -> True)
  =
  let key_BE = seq_nat8_to_seq_nat32_BE key in
  let h_BE = aes_encrypt_word alg key_BE (Mkfour 0 0 0 0) in
  let j0_BE = compute_iv_BE h_BE iv in

  let p = gctr_encrypt (inc32 j0_BE 1) cipher alg key_BE in   // TODO: Rename gctr_encrypt to gctr

  let lengths_BE = two_two_to_four (Mktwo (nat_to_two 32 (8 * length auth)) (nat_to_two 32 (8 * length cipher))) in

  let zero_padded_c_BE = be_bytes_to_seq_quad32 (pad_to_128_bits cipher) in
  let zero_padded_a_BE = be_bytes_to_seq_quad32 (pad_to_128_bits auth) in

  let hash_input_BE = append zero_padded_a_BE (append zero_padded_c_BE (create 1 lengths_BE)) in
  let s_BE = ghash_BE h_BE hash_input_BE in
  let t = gctr_encrypt j0_BE (be_quad32_to_bytes s_BE) alg key_BE in

  (p, t = tag)
[@"opaque_to_smt"] let gcm_decrypt_BE = opaque_make gcm_decrypt_BE_def
irreducible let gcm_decrypt_BE_reveal = opaque_revealer (`%gcm_decrypt_BE) gcm_decrypt_BE gcm_decrypt_BE_def
