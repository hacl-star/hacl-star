module GCM

open Opaque_s
open Types_s
open Arch.Types
open GCM_s
open AES_s
open GCM_helpers
open GCTR_s
open GCTR
open GHash_s
open FStar.Mul
open FStar.Seq
open Words_s
open Words.Seq_s

let gcm_encrypt_LE_fst_helper (iv_enc iv_BE:quad32) (plain auth cipher:seq nat8) (alg:algorithm) (key:seq nat32) : Lemma
  (requires
    is_aes_key_LE alg key /\
    cipher == gctr_encrypt_LE iv_enc (make_gctr_plain_LE plain) alg key /\
    4096 * (length plain) < pow2_32 /\
    4096 * (length auth) < pow2_32 /\
    iv_enc == inc32 (Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3) 1
  )
  (ensures cipher == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth))
  =
  reveal_opaque (gcm_encrypt_LE_def alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth)
(*
  let s_key_LE = seq_nat8_to_seq_nat32_LE (seq_nat32_to_seq_nat8_LE key) in
  let s_iv_BE = be_bytes_to_quad32 (be_quad32_to_bytes iv_BE) in
  let s_j0_BE = Mkfour 1 s_iv_BE.lo1 s_iv_BE.hi2 s_iv_BE.hi3 in
  let s_cipher = fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth) in
  be_bytes_to_quad32_to_bytes iv_BE;
  assert (s_cipher == gctr_encrypt_LE (inc32 s_j0_BE 1) plain alg s_key_LE);
  assert (s_iv_BE == iv_BE);
  assert (s_key_LE == key);

  assert (gctr_encrypt_LE (inc32 s_j0_BE 1) plain alg s_key_LE ==
          gctr_encrypt_LE (inc32 s_j0_BE 1) plain alg key);
   assert (gctr_encrypt_LE (inc32 s_j0_BE 1) plain alg key ==
           gctr_encrypt_LE (inc32 s_j0_BE 1) (make_gctr_plain_LE plain) alg key);
  assert (gctr_encrypt_LE (inc32 s_j0_BE 1) (make_gctr_plain_LE plain) alg key ==
          gctr_encrypt_LE iv_enc (make_gctr_plain_LE plain) alg key);
  ()
*)

let gcm_encrypt_LE_snd_helper (iv_BE length_quad32 hash mac:quad32) (plain auth cipher:seq nat8) (alg:algorithm) (key:seq nat32) : Lemma
  (requires
    is_aes_key_LE alg key /\
    0 <= 8 * length plain /\ 8 * length plain < pow2_32 /\ // REVIEW
    0 <= 8 * length auth /\ 8 * length auth < pow2_32 /\   // REVIEW
    4096 * length plain < pow2_32 /\
    4096 * length auth < pow2_32 /\
    cipher == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth) /\
    length_quad32 == reverse_bytes_quad32 (Mkfour (8 * length plain) 0 (8 * length auth) 0) /\
    ( let h = aes_encrypt_LE alg key (Mkfour 0 0 0 0) in
      let auth_padded_quads = le_bytes_to_seq_quad32 (pad_to_128_bits auth) in
      let cipher_padded_quads = le_bytes_to_seq_quad32 (pad_to_128_bits cipher) in
      hash == ghash_LE h (append auth_padded_quads (append cipher_padded_quads (create 1 length_quad32))) /\
      le_quad32_to_bytes mac == gctr_encrypt_LE (Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3) (le_quad32_to_bytes hash) alg key)
  )
  (ensures le_quad32_to_bytes mac == snd (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth))
  =
  reveal_opaque (gcm_encrypt_LE_def alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth)
  //be_bytes_to_quad32_to_bytes iv_BE;
  //let t = snd (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) plain auth) in
  //()


let lemma_gcm_encrypt_decrypt_equiv (alg:algorithm) (key:seq nat32) (iv_BE:quad32) (plain cipher auth alleged_tag:seq nat8) : Lemma
  (requires
    is_aes_key_LE alg key /\
    4096 * length cipher < pow2_32 /\
    4096 * length auth < pow2_32 /\
    plain == fst (gcm_encrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) cipher auth)
  )
  (ensures plain == fst (gcm_decrypt_LE alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) cipher auth alleged_tag))
  =
  reveal_opaque (gcm_encrypt_LE_def alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) cipher auth);
  reveal_opaque (gcm_decrypt_LE_def alg (seq_nat32_to_seq_nat8_LE key) (be_quad32_to_bytes iv_BE) cipher auth alleged_tag);
  ()


let gcm_decrypt_LE_tag (alg:algorithm) (key:seq nat8) (iv:seq16 nat8) (cipher:seq nat8) (auth:seq nat8) :
  Pure (seq nat8)
    (requires
      is_aes_key alg key /\
      4096 * length cipher < pow2_32 /\
      4096 * length auth < pow2_32
    )
    (ensures fun t -> True)
  =
  let key_LE = seq_nat8_to_seq_nat32_LE key in
  let iv_BE = be_bytes_to_quad32 iv in
  let h_LE = aes_encrypt_LE alg key_LE (Mkfour 0 0 0 0) in
  let j0_BE = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in

  let lengths_BE = Mkfour (8 * length cipher) 0 (8 * length auth) 0 in
  let lengths_LE = reverse_bytes_quad32 lengths_BE in

  let zero_padded_c_LE = le_bytes_to_seq_quad32 (pad_to_128_bits cipher) in
  let zero_padded_a_LE = le_bytes_to_seq_quad32 (pad_to_128_bits auth) in

  let hash_input_LE = append zero_padded_a_LE (append zero_padded_c_LE (create 1 lengths_LE)) in
  let s_LE = ghash_LE h_LE hash_input_LE in
  let t = gctr_encrypt_LE j0_BE (le_quad32_to_bytes s_LE) alg key_LE in
  t


let decrypt_helper
  (alg:algorithm) (key:seq nat8) (iv:seq16 nat8) (cipher:seq nat8) (auth:seq nat8)
  (rax:nat64) (alleged_tag_quad computed_tag:quad32) : Lemma
  (requires
    is_aes_key alg key /\
    4096 * length cipher < pow2_32 /\
    4096 * length auth < pow2_32 /\
    (if alleged_tag_quad = computed_tag then rax = 0 else rax > 0) /\
    le_quad32_to_bytes computed_tag == gcm_decrypt_LE_tag alg key iv cipher auth
  )
  (ensures  (rax = 0) == snd (gcm_decrypt_LE alg key iv cipher auth (le_quad32_to_bytes alleged_tag_quad)))
  =
  reveal_opaque (gcm_decrypt_LE_def alg key iv cipher auth (le_quad32_to_bytes alleged_tag_quad));
  (*
  let b = snd (gcm_decrypt_LE alg key iv cipher auth (le_quad32_to_bytes alleged_tag_quad)) in
  let (_, ct) = gcm_decrypt_LE alg key iv cipher auth (le_quad32_to_bytes alleged_tag_quad) in

  assert (b = (ct = (le_quad32_to_bytes alleged_tag_quad)));
  assert (ct == le_quad32_to_bytes computed_tag);
  assert (b == (le_quad32_to_bytes computed_tag = le_quad32_to_bytes alleged_tag_quad));
  *)
  le_quad32_to_bytes_injective_specific alleged_tag_quad computed_tag;
  (*
  assert (b == (computed_tag = alleged_tag_quad));
  assert ((rax = 0) == (computed_tag = alleged_tag_quad));
  *)
  ()
