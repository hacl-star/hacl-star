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

let aes_ctr_block_add_counter (block: lbytes 16) (incr:size_nat): Tot (lbytes 16) =
  let n = nat_from_bytes_be block in
  let n' = (n + incr) % pow2 128 in
  nat_to_bytes_be 16 n'

/// A block is a function of key, iv, counter.
let ctr_block (a: cipher_alg) (k: xkey a) (iv: nonce a) (c: ctr): block a =
  match a with
  | AES128 | AES256 ->
      let open Spec.AES in
      let open Lib.LoopCombinators in
      let block = create 16 (u8 0) in
      let block = repeati #(lbytes 16) (length iv) (fun i b -> b.[i] <- Seq.index iv i) block in
      let block = aes_ctr_block_add_counter block c in
      aes_encrypt_block (aes_alg_of_alg a) k block

  | CHACHA20 ->
      let open Spec.Chacha20 in
      let block = chacha20_init k iv c in
      let block' = rounds block in
      uints_to_bytes_le (sum_state block block')
