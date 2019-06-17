module Spec.Agile.Cipher

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 1"

type cipher_alg =
  | AES128
  | AES256
  | CHACHA20

let aes_alg_of_alg (a: cipher_alg { a = AES128 \/ a = AES256 }) =
  match a with
  | AES128 -> Spec.AES.AES128
  | AES256 -> Spec.AES.AES128

let state (a:cipher_alg) =
  match a with
  | AES128 | AES256 -> Spec.AES.aes_ctr_state (aes_alg_of_alg a)
  | CHACHA20 -> Spec.Chacha20.state

let key_len (a:cipher_alg) =
  match a with
  | AES128 | AES256 -> Spec.AES.key_size (aes_alg_of_alg a)
  | CHACHA20 -> 32

let counter_max (a:cipher_alg) =
  match a with
  | AES128 | AES256 -> max_size_t
  | CHACHA20 -> max_size_t

let block_len (a:cipher_alg) =
  match a with
  | AES128 | AES256 -> 16
  | CHACHA20 -> 64

let nonce_bound (a: cipher_alg) (n_len: nat): Type0 =
  match a with
  | AES128 | AES256 -> n_len <= block_len a
  | CHACHA20 -> n_len == 12

let nonce_len (a:cipher_alg) =
  n_len:size_nat { nonce_bound a n_len }

let init (a:cipher_alg) (k:lbytes (key_len a)) (n_len:nonce_len a) (n:lbytes n_len) (c:size_nat) : state a =
  match a with
  | AES128 | AES256 -> Spec.AES.aes_ctr_init (aes_alg_of_alg a) k n_len n c
  | CHACHA20 -> Spec.Chacha20.chacha20_init k n c

let add_counter (a:cipher_alg) (s:state a) (n:size_nat) : state a =
  match a with
  | AES128 | AES256 -> Spec.AES.aes_ctr_add_counter (aes_alg_of_alg a) s n
  | CHACHA20 -> Spec.Chacha20.chacha20_add_counter s n

let key_block (a:cipher_alg) (s:state a) : lbytes (block_len a) =
  match a with
  | AES128 | AES256 -> Spec.AES.aes_ctr_current_key_block (aes_alg_of_alg a) s
  | CHACHA20 -> Spec.Chacha20.chacha20_key_block s
