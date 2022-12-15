module Spec.Hash.PadFinish

module S = FStar.Seq
open Lib.IntTypes
open Lib.ByteSequence

open Spec.Hash.Lemmas0
open Spec.Hash.Definitions

(** This module contains two things.
 - First, a Merkle-Damgard padding scheme for the MD hashes ONLY (md5, sha1, sha2)
 - Second, a "finish" operation that extracts the final hash from the internal
   state, defined for any hash.

 In Spec.Agile.Hash, the one-shot hash for MD hashes is defined pad,
 update_multi, finish.

 The incremental specification (in lemmas/Spec.Hash.Incremental.Definitions)
 introduces a notion of "update_last" and then defines the hash as update_multi,
 update_last, finish, relying on the various definitions for finish here,
 including those for non-MD hashes.
*)

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
  let hash_final_w = S.slice hashw 0 (hash_word_length a) in
  bytes_of_words a #(hash_word_length a) hash_final_w

let finish_blake (a:blake_alg) (hash:words_state a): Tot (lbytes (hash_length a)) =
  let alg = to_blake_alg a in
  Spec.Blake2.blake2_finish alg hash (Spec.Blake2.max_output alg)

let finish_sha3 (a: sha3_alg) (s: words_state a): Tot (lbytes (hash_length a)) =
  match a with
  | SHA3_256 ->
      let rateInBytes = 1088 / 8 in
      let outputByteLen = 32 in
      Spec.SHA3.squeeze s rateInBytes outputByteLen

let finish (a:hash_alg) (hashw:words_state a): Tot (lbytes (hash_length a)) =
  if is_blake a then
    finish_blake a hashw
  else if is_sha3 a then
    finish_sha3 a hashw
  else
    finish_md a hashw
