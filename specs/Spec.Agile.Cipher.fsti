module Spec.Agile.Cipher

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 1"

/// This module is concerned with defining an agile stream cipher, i.e. a
/// function that given: a suitably extended key; an iv (nonce); a counter,
/// produces a fresh block.
///
/// TODO: share definitions with Spec.AEAD, in particular definitions of nonce,
/// key, key expansion, etc.

type cipher_alg =
  | AES128
  | AES256
  | CHACHA20

/// The AES spec itself is agile; this is the same nested agility technique used
/// for SHA2 vs. MD.
let aes_alg_of_alg (a: cipher_alg { a = AES128 \/ a = AES256 }) =
  match a with
  | AES128 -> Spec.AES.AES128
  | AES256 -> Spec.AES.AES256

/// Algorithms may (AES) or may not (Chacha) require a preliminary round of key expansion.
let xkey (a: cipher_alg) =
  match a with
  | AES128 | AES256 -> Spec.AES.aes_xkey (aes_alg_of_alg a)
  | CHACHA20 -> Spec.Chacha20.key

/// Trying to enforce conventions: lengths for nats (spec); len for machine
/// integers (runtime).
let block_length (a:cipher_alg) =
  match a with
  | AES128 | AES256 -> 16
  | CHACHA20 -> 64

/// Type abbreviations.
let block a = lbytes (block_length a)

let ctr = size_nat

let nonce_bound (a: cipher_alg) (n_len: nat): Type0 =
  match a with
  | AES128 | AES256 -> n_len <= block_length a
  | CHACHA20 -> n_len == 12

let nonce a = b:bytes { nonce_bound a (length b) }

val ctr_block (a: cipher_alg) (k: xkey a) (iv: nonce a) (c: ctr): block a

/// A stream of pseudo-random bytes, starting from counter zero. The length is
/// artificially constrained to be < 2^32.
let ctr_stream (a: cipher_alg) (k: xkey a) (iv: nonce a) (len: size_nat):
  b:bytes { length b = len }
=
  // JP: useful? be overconservative and always do + 1? would necessitate a
  // little bit of reasoning on the implementation side, perhaps better to have
  // a tighter bound here
  let n_blocks: n:nat { n * block_length a >= len } =
    if len % block_length a = 0 then
      len / block_length a
    else
      len / block_length a + 1
  in
  let (), blocks = generate_blocks
    (block_length a)
    max_size_t
    n_blocks
    (fun _ -> unit) // extra cruft; no accumulator here
    (fun i _ -> (), ctr_block a k iv i )
    ()
  in
  Seq.slice blocks 0 len

/// Possible addition: ctr_stream_n, which generates ``len`` bytes starting from
/// counter ``n`` (or, possibly, from bytes ``n``). I don't think it's necessary
/// to have that one to properly specify ``EverCrypt.CTR``.
