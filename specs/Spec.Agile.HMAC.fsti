module Spec.Agile.HMAC

open Spec.Hash.Definitions
open Lib.IntTypes

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

let lbytes (l:nat) = b:bytes {Seq.length b = l}

let keysized (a:hash_alg) (l:nat) =
  l <= max_input_length a /\
  l + block_length a < pow2 32

val hmac:
  a: hash_alg ->
  key: bytes ->
  data: bytes ->
  Pure (lbytes (hash_length a))
    (requires keysized a (Seq.length key) /\
      Seq.length data + block_length a <= max_input_length a)
    (ensures fun _ -> True)
