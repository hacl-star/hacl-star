module Spec.SHA2Again

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module C = Spec.SHA2Again.Constants
module S = FStar.Seq

(** Constants, types and helpers *)

(* List the Hash algorithms *)
type hash_alg =
  | SHA2_224
  | SHA2_256
  | SHA2_384
  | SHA2_512

(* Define the maximum input length in bytes *)
let max_input8: hash_alg -> Tot nat = function
  | SHA2_224 | SHA2_256 -> pow2 61
  | SHA2_384 | SHA2_512 -> pow2 125

(* Defines the size of the word for each algorithm *)
let size_word: hash_alg -> Tot nat = function
  | SHA2_224 | SHA2_256 -> 4
  | SHA2_384 | SHA2_512 -> 8

(* Number of words for a block size *)
let size_block_w = 16

(* Define the size block in bytes *)
let size_block a =
  let open FStar.Mul in
  size_word a * size_block_w

(* Number of words for intermediate hash *)
let size_hash_w = 8

(* Number of words for final hash *)
inline_for_extraction
let size_hash_final_w: hash_alg -> Tot nat = function
  | SHA2_224 -> 7
  | SHA2_256 -> 8
  | SHA2_384 -> 6
  | SHA2_512 -> 8

(* Define the final hash length in bytes *)
let size_hash a =
  let open FStar.Mul in
  size_word a * size_hash_final_w a


(** Input format: bytes *)

type bytes =
  m:S.seq UInt8.t

(* Bytes that are a multiple of the block length. *)
let bytes_blocks a =
  l:bytes { S.length l % size_block a = 0 }

let bytes_hash a =
  b:bytes { S.length b = size_hash a }


(** Incremental, abstract API *)

(* The NIST specification. *)
val hash: a:hash_alg -> input:bytes { S.length input < max_input8 a } -> bytes_hash a

(* The abstract, incremental state after hashing b bytes *)
val hashing: a:hash_alg -> l:bytes_blocks a -> Type0

(* The abstract, incremental state after calling compress_last *)
val hashed: a:hash_alg -> l:bytes { S.length l < max_input8 a } -> Type0

val init: a:hash_alg -> hashing a Seq.empty

val compress: a:hash_alg ->
  l:bytes_blocks a ->
  h:hashing a l ->
  l':bytes_blocks a ->
  hashing a (S.append l l')

val compress_last:
  a:hash_alg ->
  l:bytes_blocks a ->
  h:hashing a l ->
  l': bytes { S.length l + S.length l' < max_input8 a } ->
  hashed a (S.append l l')

val extract:
  a:hash_alg ->
  l:bytes { S.length l < max_input8 a } ->
  h:hashed a l ->
  b:bytes { b = hash a l }
