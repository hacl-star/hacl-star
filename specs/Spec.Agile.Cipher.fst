module Spec.Agile.Cipher

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 1"

let force_flush_interleaving = ()

let aes_ctr_block_add_counter (block: lbytes 16) (incr:size_nat): Tot (lbytes 16) =
  let n = nat_from_bytes_be block in
  let n' = (n + incr) % pow2 128 in
  nat_to_bytes_be 16 n'

let xkey (a: cipher_alg) =
  match a with
  | AES128 | AES256 -> Spec.AES.aes_xkey (aes_alg_of_alg a)
  | CHACHA20 -> Spec.Chacha20.key

/// As specified by the NIST. Other implementations (e.g. Vale) may perform
/// other steps beyond key expansion but this is an implementation detail.
let expand (a: cipher_alg) (k: key a): xkey a =
  match a with
  | AES128 | AES256 -> Spec.AES.aes_key_expansion (aes_alg_of_alg a) k
  | CHACHA20 -> k

/// A block is a function of key, iv, counter.
let ctr_block (a: cipher_alg) (k: key a) (iv: nonce a) (c: ctr): block a =
  let k = expand a k in
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
