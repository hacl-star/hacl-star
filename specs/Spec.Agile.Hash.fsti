module Spec.Agile.Hash

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


type algorithm =
  | UNSAFE_HASH_MD5
  | UNSAFE_HASH_SHA1
  | HASH_SHA2_224
  | HASH_SHA2_256
  | HASH_SHA2_384
  | HASH_SHA2_512

(* Definition of the abstract state *)
val state: a:algorithm -> Type0

(* Functions to access algorithm parameters *)
inline_for_extraction
let size_block (a:algorithm) : Tot size_nat =
  match a with
  | UNSAFE_HASH_MD5 -> 64
  | UNSAFE_HASH_SHA1 -> 64
  | HASH_SHA2_224 -> 64
  | HASH_SHA2_256 -> 64
  | HASH_SHA2_384 -> 128
  | HASH_SHA2_512 -> 128

inline_for_extraction
let size_hash (a:algorithm) : Tot size_nat =
  match a with
  | UNSAFE_HASH_MD5 -> 16
  | UNSAFE_HASH_SHA1 -> 20
  | HASH_SHA2_224 -> 28
  | HASH_SHA2_256 -> 32
  | HASH_SHA2_384 -> 48
  | HASH_SHA2_512 -> 64

inline_for_extraction
let size_hash_w : size_nat = 8

inline_for_extraction
let max_input (a:algorithm) : Tot nat =
  match a with
  | UNSAFE_HASH_MD5 -> pow2 61 - 1
  | UNSAFE_HASH_SHA1 -> pow2 61 - 1
  | HASH_SHA2_224 -> pow2 61 - 1
  | HASH_SHA2_256 -> pow2 61 - 1
  | HASH_SHA2_384 -> pow2 125 - 1
  | HASH_SHA2_512 -> pow2 125 - 1


(* Incremental API *)
val init: a:algorithm -> Tot (state a)

val update_block: a:algorithm -> lbytes (size_block a) -> state a -> Tot (state a)

val update_last: a:algorithm -> prev:nat -> len:nat{len <= size_block a /\ prev % size_block a = 0 /\ len + prev <= max_input a} -> last:lbytes len -> state a -> Tot (state a)

val finish: a:algorithm -> st:state a -> Tot (lbytes (size_hash a))

(* Hash function onetime *)
val hash: a:algorithm -> input:bytes{length input <= max_input a} -> Tot (lbytes (size_hash a))

