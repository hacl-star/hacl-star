module Spec.Cipher.Expansion

open Spec.Agile.Cipher

let vale_cipher_alg = a: cipher_alg { a == AES128 \/ a == AES256 }

let vale_alg_of_cipher_alg (a: cipher_alg { a == AES128 \/ a == AES256 }) =
  match a with
  | AES128 -> Vale.AES.AES_s.AES_128
  | AES256 -> Vale.AES.AES_s.AES_256

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

/// Length of Vale expanded keys, i.e. length of the expanded key (per NIST AES
/// specification) along with other precomputed things.
val vale_xkey_length (a: vale_cipher_alg): Lib.IntTypes.size_nat
let vale_xkey_length =
  function
  | AES128 -> 176 + 128 // Include the hashed keys here
  | AES256 -> 240 + 128 // Include the hashed keys here

/// Because seq_uint8_to_seq_nat8 does not take Lib.IntTypes.uint8
friend Lib.IntTypes

/// And the specification of the Vale key expansion.
val vale_aes_expansion (a: vale_cipher_alg) (key: key a):
  Lib.ByteSequence.lbytes (vale_xkey_length a)
let vale_aes_expansion a k =
  let open Vale.AES.AES_s in
  assert_norm (32 % 4 = 0);
  assert_norm (16 % 4 = 0);
  let k_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 k in
  let k_w = Vale.Def.Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
  let ekv_w = key_to_round_keys_LE (vale_alg_of_cipher_alg a) k_w in
  let ekv_nat = Vale.Def.Types_s.le_seq_quad32_to_bytes ekv_w in
  Vale.Def.Types_s.le_seq_quad32_to_bytes_length ekv_w;
  let ek = Vale.Def.Words.Seq_s.seq_nat8_to_seq_uint8 ekv_nat in
  let hkeys_quad = Vale.AES.OptPublic.get_hkeys_reqs (Vale.Def.Types_s.reverse_bytes_quad32 (
    aes_encrypt_LE (vale_alg_of_cipher_alg a) k_w (Vale.Def.Words_s.Mkfour 0 0 0 0))) in
  let hkeys = Vale.Def.Words.Seq_s.seq_nat8_to_seq_uint8 (Vale.Def.Types_s.le_seq_quad32_to_bytes hkeys_quad) in
  Seq.append ek hkeys

let _: squash (inversion cipher_alg) = allow_inversion cipher_alg
let _: squash (inversion impl) = allow_inversion impl

let xkey_length =
  function
  | CHACHA20 -> 32
  | AES128 -> 176
  | AES256 -> 240

let concrete_xkey_length (i: impl): nat =
  match i with
  | Vale_AES128
  | Vale_AES256 ->
      vale_xkey_length (cipher_alg_of_impl i)
  | Hacl_CHACHA20 -> 32

let concrete_expand i k =
  match i with
  | Hacl_CHACHA20 -> k
  | Vale_AES128 | Vale_AES256 ->
      let a = cipher_alg_of_impl i in
      vale_aes_expansion a k
