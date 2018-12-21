module Spec.AEAD

open FStar.Integers

module S = FStar.Seq

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

let supported_alg (a: alg): bool =
  match a with
  | AES128_GCM
  | AES256_GCM
  | CHACHA20_POLY1305 -> true
  | _ -> false

// naming convention: length for nats, len for uint32s
let key_length: alg -> nat =
  function
  | AES128_GCM        -> 16
  | AES256_GCM        -> 32
  | CHACHA20_POLY1305 -> 32
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

let iv_length (a: alg): nat =
  12

// TODO
val max_plain_length: alg -> nat

// TODO: move to a shared place
let lbytes (l:nat) = b:Seq.seq UInt8.t { Seq.length b = l }

// Question: <= max_plain_length or <? I think <= is better?
// Note: not indexing the types over their lengths; we can use S.length in specs
let kv a = lbytes (key_length a)
let iv a = lbytes (iv_length a)
let plain a = s:S.seq UInt8.t { S.length s <= max_plain_length a }
let cipher a = s:S.seq UInt8.t { S.length s >= tag_length a }

// TODO
val cipher_length: #a -> plain a -> nat
val plain_length: #a -> cipher a -> nat

// Convenient abbreviations
let encrypted #a (p: plain a) = c:cipher a { S.length c = cipher_length p }
let decrypted #a (c: cipher a) = p:plain a { S.length p = plain_length p }

// Note: no GTot, specs need to be executable for testing

val ekv (a: alg): Type0

// Note: expand corresponds to the "beginning" of the spec of encrypt. We know
// nothing about it, even though, under this interface:
//
// let encrypt ... =
//   let ekv = expand ... in
//   <rest-of-encrypt>
//
// The implementation will friend this module, and expose expand as a stateful
// function, then will expose a function that does the <rest-of-encrypt> but
// still expresses its post-condition using Spec.AEAD.encrypt. So, encrypt takes
// a kv, not an ekv.

val expand: #a -> kv a -> ekv a
val encrypt: #a -> kv a -> iv a -> ad a -> p:plain a -> encrypted p
val decrypt: #a -> kv a -> iv a -> ad a -> c:cipher a -> option (decrypted c)
