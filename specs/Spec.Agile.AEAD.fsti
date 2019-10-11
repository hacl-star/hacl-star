module Spec.Agile.AEAD

open FStar.Integers

module S = FStar.Seq

#set-options "--max_fuel 0 --max_ifuel 0"

// to be used via a module abbreviation, e.g. AEAD.alg
type alg =
  | AES128_GCM
  | AES256_GCM
  | CHACHA20_POLY1305
  // the algorithms below are used in TLS 1.3 but not yet supported by
  // EverCrypt or miTLS; they are included e.g. for parsing
  | AES128_CCM  // "Counter with CBC-Message Authentication Code"
  | AES256_CCM
  | AES128_CCM8 // variant with truncated 8-byte tags
  | AES256_CCM8

let _: squash (inversion alg) = allow_inversion alg

let is_supported_alg (a: alg): bool =
  match a with
  | AES128_GCM
  | AES256_GCM
  | CHACHA20_POLY1305 -> true
  | _ -> false

let supported_alg = a:alg { is_supported_alg a }

let cipher_alg_of_supported_alg (a: supported_alg): Spec.Agile.Cipher.cipher_alg =
  let open Spec.Agile.Cipher in
  match a with
  | AES128_GCM -> AES128
  | AES256_GCM -> AES256
  | CHACHA20_POLY1305 -> CHACHA20

// naming convention: length for nats, len for uint32s
let key_length (a: alg): nat =
  match a with
  | AES128_GCM
  | AES256_GCM
  | CHACHA20_POLY1305 -> Spec.Agile.Cipher.key_length (cipher_alg_of_supported_alg a)
  | AES128_CCM        -> 16
  | AES128_CCM8       -> 16
  | AES256_CCM        -> 32
  | AES256_CCM8       -> 32

let tag_length: alg -> nat =
  function
  | AES128_CCM8       ->  8
  | AES256_CCM8       ->  8
  | AES128_GCM        -> 16
  | AES256_GCM        -> 16
  | CHACHA20_POLY1305 -> 16
  | AES128_CCM        -> 16
  | AES256_CCM        -> 16

/// No sharing with Spec.Agile.Cipher, since AES-GCM offers IV reduction via the
/// GHASH function.
let iv_length (a: supported_alg) (len: nat) =
  match a with
  | AES128_GCM -> len > 0 /\ 8 * len <= pow2 64 - 1
  | AES256_GCM -> len > 0 /\ 8 * len <= pow2 64 - 1
  | CHACHA20_POLY1305 -> len == 12

// Maximum length for both plaintexts and additional data.
//
// Some notes:
// - we have both closed (HACL-style specs) and semi-open (Vale specs)
//   intervals; just picking one arbitrary choice here... see
//   https://github.com/mitls/mitls-papers/wiki/Discussion-to-Converge-on-Design-Decisions
//   for a failure to make decisions
// - because the specs for HACL* are very concrete, they limit the size
//   artificially; we could've limited each of cipher and ad to 16 * 2**31 (see
//   chacha block size) but instead have a smaller bound because of the size of arrays.
let max_length: supported_alg -> nat =
  function
  | CHACHA20_POLY1305 -> pow2 32 - 1 - 16
  | AES128_GCM | AES256_GCM -> pow2 32 - 1

let uint8 = Lib.IntTypes.uint8

// Proudly defining this type abbreviation for the tenth time in HACL*!
let lbytes (l:nat) = b:Seq.seq uint8 { Seq.length b = l }

// Note: using <= for maximum admissible lengths
// Note: not indexing the types over their lengths; we can use S.length in specs
let kv a = lbytes (key_length a)
let iv a = s:S.seq uint8 { iv_length a (S.length s) }
let ad a = s:S.seq uint8 { S.length s <= max_length a }
let plain (a: supported_alg) = s:S.seq uint8 { S.length s <= max_length a }
let cipher (a: supported_alg) = s:S.seq uint8 { S.length s >= tag_length a }

let cipher_length #a (p: plain a) =
  S.length p + tag_length a

// Convenient abbreviations
let encrypted #a (p: plain a) = c:cipher a { S.length c = cipher_length p }
let decrypted #a (c: cipher a) = p:plain a { S.length c = cipher_length p }

// Note: no GTot, specs need to be executable for testing

// Note: the spec starts with key expansion, but we don't reveal it here, and
// leave it up to EverCrypt.AEAD to rely on an abstract invariant to enforce
// that key expansion is performed first, so as not to do it on each encryption:
//
// let encrypt ... =
//   let ekv = expand ... in
//   <rest-of-encrypt>
//
// The implementation will friend this module, and expose expand as a stateful
// function, then will expose a function that does the <rest-of-encrypt> but
// still expresses its post-condition using Spec.Agile.AEAD.encrypt. So, encrypt takes
// a kv, not an ekv.

// Note: adopting the argument order of EverCrypt... which doesn't match other
// specs. Sigh.
val encrypt: #(a: supported_alg) -> kv a -> iv a -> ad a -> p:plain a -> encrypted p
val decrypt: #(a: supported_alg) -> kv a -> iv a -> ad a ->
  c:cipher a { S.length c <= max_length a + tag_length a} ->
  option (decrypted c)

val correctness: #a:supported_alg -> k:kv a -> n:iv a -> aad:ad a -> p:plain a ->
  Lemma (decrypt k n aad (encrypt k n aad p) == Some p)
