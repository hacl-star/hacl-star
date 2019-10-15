module Spec.Agile.HKDF

open FStar.Integers
open Spec.Hash.Definitions

/// FUNCTIONAL SPECIFICATION:
///
/// * extraction is just HMAC using the salt as key and the input
///   keying materials as text.
///
/// * expansion does its own formatting of input key materials.

open FStar.Seq

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

let extract = Spec.Agile.HMAC.hmac

module Seq = Lib.Sequence
open Lib.IntTypes

(** See https://tools.ietf.org/html/rfc5869#section-2.3 *)
let expand a prk info len =
  let open Spec.Agile.HMAC in
  // n = ceil(len / hash_length a)
  let n = 1 + (len - 1) / hash_length a in
  let last, okm = 
    Seq.generate_blocks (hash_length a) n n 
      (fun i -> Seq.lseq uint8 (if i = 0 then 0 else hash_length a))
      (fun i last ->
        let t = hmac a prk (last @| info @| Seq.create 1 (u8 i)) in
        t, t)
      FStar.Seq.empty
  in
  Seq.sub #uint8 #(n * hash_length a) okm 0 len
