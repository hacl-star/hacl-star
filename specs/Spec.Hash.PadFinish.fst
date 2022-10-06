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

let pad_md (a:md_alg)
  (total_len:nat{total_len `less_than_max_input_length` a}):
  Tot (b:bytes{(S.length b + total_len) % block_length a = 0})
  = let open FStar.Mul in
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

let pad (a:md_alg)
  (total_len:nat{total_len `less_than_max_input_length` a}):
  Tot (b:bytes{(S.length b + total_len) % block_length a = 0})
= pad_md a total_len

(** Extracting the hash, which we call "finish" *)

(* Unflatten the hash from the sequence of words to bytes up to the correct size *)
let finish_md (a:md_alg) (hashw:words_state a): Tot (lbytes (hash_length a)) =
  let hashw, extra = hashw in
  let hash_final_w = S.slice hashw 0 (hash_word_length a) in
  bytes_of_words a #(hash_word_length a) hash_final_w

let finish_blake (a:blake_alg) (hashw:words_state a): Tot (lbytes (hash_length a)) =
  let alg = to_blake_alg a in
  Spec.Blake2.blake2_finish alg (fst hashw) (Spec.Blake2.max_output alg)

let finish_sha3 (a: sha3_alg) (s: words_state a): Tot (lbytes (hash_length a)) =
  match a with
  | SHA3_256 ->
      let rateInBytes = 1088 / 8 in
      let outputByteLen = 32 in
      let s, _ = s in
      Spec.SHA3.squeeze s rateInBytes outputByteLen

(* Note that the ``extra_state`` in the ``words_state`` parameter is useless -
 * we use this fact pervasively in the proofs and some definitions by providing
 * dummy extra-states when we don't manipulate "full" words states *)
let finish (a:hash_alg) (hashw:words_state a): Tot (lbytes (hash_length a)) =
  if is_blake a then
    finish_blake a hashw
  else if is_sha3 a then
    finish_sha3 a hashw
  else
    finish_md a hashw
