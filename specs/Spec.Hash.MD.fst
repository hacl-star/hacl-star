module Spec.Hash.MD

module S = FStar.Seq
open Lib.IntTypes
open Lib.ByteSequence

open Spec.Hash.Definitions

(** This module contains a Merkle-Damgard padding scheme for the
    MD hashes ONLY (md5, sha1, sha2)

 In Spec.Agile.Hash, the one-shot hash for MD hashes is defined pad,
 update_multi, finish.
*)

#push-options "--fuel 2 --ifuel 0"
(* A useful lemma for all the operations that involve going from bytes to bits. *)
let max_input_size_len (a: hash_alg{is_md a}): Lemma
  (ensures FStar.Mul.(Some ?.v (max_input_length a) * 8 + 8 = pow2 (len_length a * 8)))
=
  let open FStar.Mul in
  assert_norm (Some?.v (max_input_length a) * 8 + 8 = pow2 (len_length a * 8))
#pop-options

(** Padding *)

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

let pad (a:md_alg)
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
