module Spec.Agile.HMAC

open Spec.Hash.Definitions
open Lib.IntTypes

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"

let lbytes (l:nat) = b:bytes {Seq.length b = l}

let keysized (a:hash_alg) (l:nat) =
  l `less_than_max_input_length` a /\
  l + block_length a < pow2 32

val wrap
  (a: fixed_len_alg)
  (key: bytes{Seq.length key `less_than_max_input_length` a})
  : lbytes (block_length a)

let xor (x: uint8) (v: bytes) : lbytes (Seq.length v) =
  Spec.Loops.seq_map (logxor x) v

val hmac:
  a: fixed_len_alg ->
  key: bytes ->
  data: bytes ->
  Pure (lbytes (hash_length a))
    (requires keysized a (Seq.length key) /\
      (Seq.length data + block_length a) `less_than_max_input_length` a)
    (ensures fun _ -> True)
