module Spec.Agile.CTR

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Spec.Agile.Cipher

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 1"

// So that clients don't need to open both modules
include Spec.Agile.Cipher

let key_length (a: cipher_alg) =
  match a with
  | AES128 | AES256 -> Spec.AES.key_size (aes_alg_of_alg a)
  | CHACHA20 -> Spec.Chacha20.size_key

let key (a: cipher_alg) =
  match a with
  | AES128 | AES256 -> Spec.AES.aes_key (aes_alg_of_alg a)
  | CHACHA20 -> Spec.Chacha20.key

let expand (a: cipher_alg) (k: key a): xkey a =
  match a with
  | AES128 | AES256 -> Spec.AES.aes_key_expansion (aes_alg_of_alg a) k
  | CHACHA20 -> k

val counter_mode:
  a:cipher_alg ->
  k:key a ->
  n:nonce a ->
  plain:bytes { length plain <= max_size_t } ->
  Tot (cipher:bytes { length cipher = length plain })
let counter_mode a k n plain =
  let xk = expand a k in
  let stream = ctr_stream a xk n (length plain) in
  map2 ( ^. ) (plain <: lbytes (length plain)) (stream <: lbytes (length plain))
