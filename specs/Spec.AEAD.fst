module Spec.AEAD

open FStar.Integers

module S = FStar.Seq

#set-options "--max_fuel 0 --max_ifuel 0"

friend Lib.IntTypes

let vale_alg_of_alg (a: alg { a = AES128_GCM \/ a = AES256_GCM }) =
  match a with
  | AES128_GCM -> AES_s.AES_128
  | AES256_GCM -> AES_s.AES_256

let expand #a k =
  match a with
  | CHACHA20_POLY1305 -> k
  | AES256_GCM | AES128_GCM ->
      let open AES_s in
      assert_norm (32 % 4 = 0);
      assert_norm (16 % 4 = 0);
      let k_nat = Words.Seq_s.seq_uint8_to_seq_nat8 k in
      let k_w = Words.Seq_s.seq_nat8_to_seq_nat32_LE k_nat in
      let ekv_w = key_to_round_keys_LE (vale_alg_of_alg a) k_w in
      let ekv_nat = Types_s.le_seq_quad32_to_bytes ekv_w in
      Types_s.le_seq_quad32_to_bytes_length ekv_w;
      let ek = Words.Seq_s.seq_nat8_to_seq_uint8 ekv_nat in
      let hkeys_quad = OptPublic.get_hkeys_reqs (Types_s.reverse_bytes_quad32 (
        aes_encrypt_LE (vale_alg_of_alg a) k_w (Words_s.Mkfour 0 0 0 0))) in
      let hkeys = Words.Seq_s.seq_nat8_to_seq_uint8 (Types_s.le_seq_quad32_to_bytes hkeys_quad) in
      Seq.append ek hkeys

// For gctr_encrypt_recursive and its pattern!
friend GCTR

#push-options "--max_ifuel 1"
let gcm_encrypt_tag_length alg key iv plain auth: Lemma
  (requires
    AES_s.is_aes_key alg key /\
    4096 * S.length plain < Words_s.pow2_32 /\
    4096 * S.length auth < Words_s.pow2_32)
  (ensures (
    let c, t = GCM_s.gcm_encrypt_LE alg key iv plain auth in
    S.length t = 16))
=
  Opaque_s.reveal_opaque (GCM_s.gcm_encrypt_LE_def alg key iv plain auth)

let gcm_encrypt_cipher_length alg key iv plain auth: Lemma
  (requires
    AES_s.is_aes_key alg key /\
    4096 * S.length plain < Words_s.pow2_32 /\
    4096 * S.length auth < Words_s.pow2_32)
  (ensures (
    let c, t = GCM_s.gcm_encrypt_LE alg key iv plain auth in
    S.length c = S.length plain))
=
  Opaque_s.reveal_opaque (GCM_s.gcm_encrypt_LE_def alg key iv plain auth)
#pop-options

let encrypt #a kv iv ad plain =
  match a with
  | CHACHA20_POLY1305 ->
      Spec.Chacha20Poly1305.aead_encrypt kv iv plain ad

  | AES128_GCM | AES256_GCM ->
      let kv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 kv in
      let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 iv in
      // the specification takes a seq16 for convenience, but actually discards
      // the trailing four bytes; we are, however, constrained by it and append
      // zeroes just to satisfy the spec
      let iv_nat = S.append iv_nat (S.create 4 0) in
      // `ad` is called `auth` in Vale world; "additional data", "authenticated
      // data", potato, potato
      let ad_nat = Words.Seq_s.seq_uint8_to_seq_nat8 ad in
      let plain_nat = Words.Seq_s.seq_uint8_to_seq_nat8 plain in
      assert (max_length a = pow2 20 - 1 - 16);
      assert_norm (4096 * (pow2 20 - 1 - 16) < Words_s.pow2_32);
      let cipher_nat, tag_nat =
        GCM_s.gcm_encrypt_LE (vale_alg_of_alg a) kv_nat iv_nat plain_nat ad_nat
      in
      let cipher = Words.Seq_s.seq_nat8_to_seq_uint8 cipher_nat in
      let tag = Words.Seq_s.seq_nat8_to_seq_uint8 tag_nat in
      gcm_encrypt_tag_length (vale_alg_of_alg a) kv_nat iv_nat plain_nat ad_nat;
      gcm_encrypt_cipher_length (vale_alg_of_alg a) kv_nat iv_nat plain_nat ad_nat;
      // one more spec discrepancy: Vale returns the cipher and tag separated,
      // while HACL* bundles them together; another arbitrary choice here
      Seq.append cipher tag

#push-options "--max_ifuel 1"
let gcm_decrypt_cipher_length alg key iv plain auth tag: Lemma
  (requires
    AES_s.is_aes_key alg key /\
    4096 * S.length plain < Words_s.pow2_32 /\
    4096 * S.length auth < Words_s.pow2_32)
  (ensures (
    let c, t = GCM_s.gcm_decrypt_LE alg key iv plain auth tag in
    S.length c = S.length plain))
=
  Opaque_s.reveal_opaque (GCM_s.gcm_decrypt_LE_def alg key iv plain auth tag)
#pop-options

// Note: bundling cipher and tag together is a pain...
let decrypt #a kv iv ad cipher =
  let tag = S.slice cipher (S.length cipher - tag_length a) (S.length cipher) in
  let cipher = S.slice cipher 0 (S.length cipher - tag_length a) in
  match a with
  | CHACHA20_POLY1305 ->
      Spec.Chacha20Poly1305.aead_decrypt kv iv cipher tag ad

  | AES128_GCM | AES256_GCM ->
      assert (max_length a = pow2 20 - 1 - 16);
      assert_norm (4096 * (pow2 20 - 1 - 16) < Words_s.pow2_32);
      let kv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 kv in
      let iv_nat = Words.Seq_s.seq_uint8_to_seq_nat8 iv in
      let iv_nat = S.append iv_nat (S.create 4 0) in
      let ad_nat = Words.Seq_s.seq_uint8_to_seq_nat8 ad in
      let cipher_nat = Words.Seq_s.seq_uint8_to_seq_nat8 cipher in
      let tag_nat = Words.Seq_s.seq_uint8_to_seq_nat8 tag in
      let plain_nat, success =
        GCM_s.gcm_decrypt_LE (vale_alg_of_alg a) kv_nat iv_nat cipher_nat ad_nat tag_nat
      in
      gcm_decrypt_cipher_length (vale_alg_of_alg a) kv_nat iv_nat cipher_nat ad_nat tag_nat;
      let plain = Words.Seq_s.seq_nat8_to_seq_uint8 plain_nat in
      if success then Some plain else None
