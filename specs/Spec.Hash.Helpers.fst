module Spec.Hash.Helpers

(* This module contains shared definitions across all hash algorithms. It
 * defines a common, shared `hash_alg` type, along with word sizes, type of the
 * working state, and other helpers. It also defines the type of the core functions
 * init / update / pad / finish that any algorithm must implement in order to be
 * turned into a complete hash construction. *)

(** Helpers for sizes, definition of the working state, etc. *)

(* All the hash algorithms currently supported by our specifications. *)
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

(* Number of words for intermediate hash *)
let size_hash_w = 8

inline_for_extraction
let word: hash_alg -> Tot Type0 = function
  | SHA2_224 | SHA2_256 -> UInt32.t
  | SHA2_384 | SHA2_512 -> UInt64.t

(* The working state *)
let hash_w a = m:Seq.seq (word a) {Seq.length m = size_hash_w}


(** The data format taken and returned by the hash specifications. *)

(* Input data. *)
type bytes =
  m:Seq.seq UInt8.t

(* Input data, multiple of a block length. *)
let bytes_blocks a =
  l:bytes { Seq.length l % size_block a = 0 }

(* Output data, i.e. the final hash (tag). *)
let bytes_hash a =
  b:bytes { Seq.length b = size_hash a }


(** The types for the core functions *)

let init_t (a: hash_alg) =
  hash_w a

let update_t (a: hash_alg) =
  h:hash_w a ->
  l:bytes { Seq.length l = size_block a } ->
  h':hash_w a

let pad_t (a: hash_alg) =
  l:nat { l < max_input8 a } ->
  b:bytes { (Seq.length b + l) % size_block a = 0 }

let finish_t (a: hash_alg) =
  h:hash_w a ->
  bytes_hash a
