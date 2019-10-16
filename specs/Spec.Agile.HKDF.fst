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
  let tlen = hash_length a in
  let n = len / tlen in
  let tag, output = 
    Seq.generate_blocks tlen n n 
      (fun i -> Seq.lseq uint8 (if i = 0 then 0 else tlen))
      (fun i tag ->
        let t = hmac a prk (tag @| info @| Seq.create 1 (u8 (i + 1))) in
        t, t)
      FStar.Seq.empty
  in
  if n * tlen < len then
    let t = hmac a prk (tag @| info @| Seq.create 1 (u8 (n + 1))) in
    output @| Seq.sub #_ #tlen t 0 (len - (n * tlen))
  else
    output
