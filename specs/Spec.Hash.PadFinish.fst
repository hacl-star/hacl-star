module Spec.Hash.PadFinish

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module E = FStar.Kremlin.Endianness
module S = FStar.Seq

open Spec.Hash.Lemmas0
open Spec.Hash.Definitions

(** This module contains specifications shared across all the Merkle-Damgård
    constructions. *)

(** Padding *)

let pad (a:hash_alg)
  (total_len:nat{total_len < max_input_length a}):
  Tot (b:bytes{(S.length b + total_len) % block_length a = 0})
=
  let open FStar.Mul in
  let firstbyte = S.create 1 0x80uy in
  let zeros = S.create (pad0_length a total_len) 0uy in
  let total_len_bits = total_len * 8 in
  // Saves the need for high fuel + makes hint replayable.
  max_input_size_len a;
  let encodedlen =
    match a with
    | MD5 -> E.n_to_le (len_len a) (total_len * 8)
    | _ -> E.n_to_be (len_len a) (total_len * 8)
  in
  S.(firstbyte @| zeros @| encodedlen)


(** Extracting the hash, which we call "finish" *)

(* Unflatten the hash from the sequence of words to bytes up to the correct size *)
let finish (a:hash_alg) (hashw:words_state a): Tot (hash:bytes{S.length hash = (hash_length a)}) =
  let hash_final_w = S.slice hashw 0 (hash_word_length a) in
  bytes_of_words a hash_final_w
