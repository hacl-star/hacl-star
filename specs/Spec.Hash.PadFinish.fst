module Spec.Hash.PadFinish

module S = FStar.Seq
open Lib.IntTypes
open Lib.ByteSequence

open Spec.Hash.Lemmas0
open Spec.Hash.Definitions

(** This module contains specifications shared across all the Merkle-Damgård
    constructions. *)

(** Padding *)

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 10"

let pad (a:hash_alg)
  (total_len:nat{total_len <= max_input_length a}):
  Tot (b:bytes{(S.length b + total_len) % block_length a = 0})
=
  let open FStar.Mul in
  let firstbyte = S.create 1 (u8 0x80) in
  let zeros = S.create (pad0_length a total_len) (u8 0) in
  let total_len_bits = total_len * 8 in
  // Saves the need for high fuel + makes hint replayable.
  max_input_size_len a;
  let encodedlen : lbytes (len_length a) =
    match a with
    | MD5 -> Lib.ByteSequence.uint_to_bytes_le (secret (nat_to_len a (total_len * 8)))
    | _ -> Lib.ByteSequence.uint_to_bytes_be (secret (nat_to_len a (total_len * 8)))
  in
  S.(firstbyte @| zeros @| encodedlen)


(** Extracting the hash, which we call "finish" *)

(* Unflatten the hash from the sequence of words to bytes up to the correct size *)
let finish (a:hash_alg) (hashw:words_state a): Tot (hash:lbytes (hash_length a)) =
  let hash_final_w = S.slice hashw 0 (hash_word_length a) in
  bytes_of_words a #(hash_word_length a) hash_final_w
