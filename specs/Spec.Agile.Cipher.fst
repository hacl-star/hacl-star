module Spec.Agile.Cipher

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 1"

type cipher_alg = 
  | AES128
  | CHACHA20


let state (a:cipher_alg) = 
  match a with
  | AES128 -> Spec.AES.aes_ctr_state Spec.AES.AES128
  | CHACHA20 -> Spec.Chacha20.state

let key_len (a:cipher_alg) =
  match a with
  | AES128 -> 16
  | CHACHA20 -> 32

let counter_max (a:cipher_alg) =
  match a with
  | AES128 -> max_size_t
  | CHACHA20 -> max_size_t

let block_len (a:cipher_alg) =
  match a with
  | AES128 -> 16
  | CHACHA20 -> 64

let nonce_len (a:cipher_alg) = 
  match a with
  | AES128 -> n_len:size_nat{n_len <= block_len a}
  | CHACHA20 -> n_len:size_nat{n_len == 12}

let init (a:cipher_alg) (k:lbytes (key_len a)) (n_len:nonce_len a)  (n:lbytes n_len) : state a =
  match a with
  | AES128 -> Spec.AES.aes_ctr_init Spec.AES.AES128 k n_len n
  | CHACHA20 -> Spec.Chacha20.chacha20_init k n 0

let set_counter (a:cipher_alg) (s:state a) (n:size_nat) : state a =
  match a with
  | AES128 -> Spec.AES.aes_ctr_set_counter Spec.AES.AES128 s n
  | CHACHA20 -> Spec.Chacha20.chacha20_set_counter s n

let key_block (a:cipher_alg) (s:state a) : lbytes (block_len a) = 
  match a with
  | AES128 -> Spec.AES.aes_ctr_current_key_block Spec.AES.AES128 s
  | CHACHA20 -> Spec.Chacha20.chacha20_key_block s

