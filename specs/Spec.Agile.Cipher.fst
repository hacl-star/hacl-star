module Spec.Agile.Cipher

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 1"

/// This module is concerned with defining an agile block cipher, i.e. a
/// function that given a block and a suitably extended key produces a fresh
/// block.

type cipher_alg =
  | AES128
  | AES256
  | CHACHA20

/// The AES spec itself is agile; this is the same technique used for SHA2 vs. MD.
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

let block_t a = lbytes (block_length a)

let block (a:cipher_alg) (s:xkey a) (b: block_t a): block_t a =
  match a with
  | AES128 | AES256 -> Spec.AES.aes_encrypt_block (aes_alg_of_alg a) s b
  | CHACHA20 ->
      let open Spec.Chacha20 in
      let b = uints_from_bytes_le #U32 #SEC b in
      let b = sum_state (rounds b) b in
      uints_to_bytes_le b
