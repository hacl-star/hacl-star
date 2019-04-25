module Spec.HMAC

open Spec.Hash.Definitions
open Lib.IntTypes

let is_supported_alg = function
  | SHA1 | SHA2_256 | SHA2_384 | SHA2_512 -> true
  | _ -> false

let lbytes (l:nat) = b:bytes {Seq.length b = l}

let keysized (a:hash_alg) (l:nat) =
  l < max_input_length a /\
  l + block_length a < pow2 32

(* ghost specification; its algorithmic definition is given in the .fst *)
val hmac:
  a: hash_alg -> //18-07-09 can't mix refinements and erasure??
  key: bytes{ keysized a (Seq.length key) } ->
  data: bytes{ Seq.length data + block_length a < max_size_t } ->
  Tot (lbytes (hash_length a))
