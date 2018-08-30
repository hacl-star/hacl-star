module Spec.Hash.Padding

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module E = FStar.Kremlin.Endianness
module S = FStar.Seq

open Spec.Hash.Helpers

(** This module contains specifications shared across all the Merkle-Damgård
    constructions. *)

(** Padding *)

let pad (a:hash_alg)
  (total_len:nat{total_len < max_input8 a}):
  Tot (b:bytes{(S.length b + total_len) % size_block a = 0})
=
  let open FStar.Mul in
  let firstbyte = S.create 1 0x80uy in
  let zeros = S.create (pad0_length a total_len) 0uy in
  let total_len_bits = total_len * 8 in
  // Saves the need for high fuel + makes hint replayable.
  max_input_size_len a;
  let encodedlen = E.n_to_be (size_len_ul_8 a) (total_len * 8) in
  S.(firstbyte @| zeros @| encodedlen)


(** Extracting the hash, which we call "finish" *)

(* Unflatten the hash from the sequence of words to bytes up to the correct size *)
let finish (a:sha2_alg) (hashw:hash_w a): Tot (hash:bytes{S.length hash = (size_hash a)}) =
  let hash_final_w = S.slice hashw 0 (size_hash_final_w a) in
  words_to_be a hash_final_w
