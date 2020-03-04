module Spec.Agile.AEAD

open FStar.Integers

module S = FStar.Seq

#set-options "--max_fuel 0 --max_ifuel 0"

let vale_alg_of_alg (a: alg { a = AES128_GCM \/ a = AES256_GCM }) =
  match a with
  | AES128_GCM -> Vale.AES.AES_s.AES_128
  | AES256_GCM -> Vale.AES.AES_s.AES_256

// For gctr_encrypt_recursive and its pattern!
friend Vale.AES.GCTR

#push-options "--max_ifuel 1"
let gcm_encrypt_tag_length alg key iv plain auth: Lemma
  (requires
    Vale.AES.AES_s.is_aes_key alg key /\
    S.length plain < Vale.Def.Words_s.pow2_32 /\
    S.length auth < Vale.Def.Words_s.pow2_32)
  (ensures (
    let c, t = Vale.AES.GCM_s.gcm_encrypt_LE alg key iv plain auth in
    S.length t = 16))
=
  Vale.AES.GCM_s.gcm_encrypt_LE_reveal ()

let gcm_encrypt_cipher_length alg key iv plain auth: Lemma
  (requires
    Vale.AES.AES_s.is_aes_key alg key /\
    S.length plain < Vale.Def.Words_s.pow2_32 /\
    S.length auth < Vale.Def.Words_s.pow2_32)
  (ensures (
    let c, t = Vale.AES.GCM_s.gcm_encrypt_LE alg key iv plain auth in
    S.length c = S.length plain))
=
  Vale.AES.GCM_s.gcm_encrypt_LE_reveal ()
#pop-options

// TODO remove me once seq_uint8_to_seq_nat8 takes Lib.IntTypes.uint8
friend Lib.IntTypes

let encrypt #a kv iv ad plain =
  match a with
  | CHACHA20_POLY1305 ->
      Spec.Chacha20Poly1305.aead_encrypt kv iv plain ad

  | AES128_GCM | AES256_GCM ->
      // This step needs friend'ing.
      let kv_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 kv in
      // The specification of gcm_encrypt_LE takes care of computing a valid
      // GCM iv from an arbitrary length iv. Hence the iv is the sequence of bytes
      let iv_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 iv in
      // `ad` is called `auth` in Vale world; "additional data", "authenticated
      // data", potato, potato
      let ad_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 ad in
      let plain_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 plain in
      let cipher_nat, tag_nat =
        Vale.AES.GCM_s.gcm_encrypt_LE (vale_alg_of_alg a) kv_nat iv_nat plain_nat ad_nat
      in
      let cipher = Vale.Def.Words.Seq_s.seq_nat8_to_seq_uint8 cipher_nat in
      let tag = Vale.Def.Words.Seq_s.seq_nat8_to_seq_uint8 tag_nat in
      gcm_encrypt_tag_length (vale_alg_of_alg a) kv_nat iv_nat plain_nat ad_nat;
      gcm_encrypt_cipher_length (vale_alg_of_alg a) kv_nat iv_nat plain_nat ad_nat;
      // one more spec discrepancy: Vale returns the cipher and tag separated,
      // while HACL* bundles them together; another arbitrary choice here
      Seq.append cipher tag

#push-options "--max_ifuel 1"
let gcm_decrypt_cipher_length alg key iv plain auth tag: Lemma
  (requires
    Vale.AES.AES_s.is_aes_key alg key /\
    S.length plain < Vale.Def.Words_s.pow2_32 /\
    S.length auth < Vale.Def.Words_s.pow2_32)
  (ensures (
    let c, t = Vale.AES.GCM_s.gcm_decrypt_LE alg key iv plain auth tag in
    S.length c = S.length plain))
=
  Vale.AES.GCM_s.gcm_decrypt_LE_reveal ()
#pop-options

// Note: bundling cipher and tag together is a pain...
#push-options "--z3rlimit 20"
let decrypt #a kv iv ad cipher =
  let tag = S.slice cipher (S.length cipher - tag_length a) (S.length cipher) in
  let cipher = S.slice cipher 0 (S.length cipher - tag_length a) in
  match a with
  | CHACHA20_POLY1305 ->
      Spec.Chacha20Poly1305.aead_decrypt kv iv cipher tag ad

  | AES128_GCM | AES256_GCM ->
      let kv_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 kv in
      let iv_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 iv in
      let ad_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 ad in
      let cipher_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 cipher in
      let tag_nat = Vale.Def.Words.Seq_s.seq_uint8_to_seq_nat8 tag in
      let plain_nat, success =
        Vale.AES.GCM_s.gcm_decrypt_LE (vale_alg_of_alg a) kv_nat iv_nat cipher_nat ad_nat tag_nat
      in
      gcm_decrypt_cipher_length (vale_alg_of_alg a) kv_nat iv_nat cipher_nat ad_nat tag_nat;
      let plain = Vale.Def.Words.Seq_s.seq_nat8_to_seq_uint8 plain_nat in
      if success then Some plain else None
#pop-options

// Admitted until we prove correctness of individual algorithms
let correctness #a k n aad p =
  admit()
