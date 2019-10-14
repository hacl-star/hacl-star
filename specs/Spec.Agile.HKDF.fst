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

// [a, prk, info] are fixed.
// [required] is the number of bytes to be extracted
// [count] is the number of extracted blocks so far
// [last] is empty for count=0 then set to the prior tag for chaining.
let rec expand0 :
  a: hash_alg ->
  prk: bytes ->
  info: bytes ->
  required: nat ->
  count: nat ->
  last: bytes ->
  Pure (lbytes required)
    (requires
     (let chainLength = if count = 0 then 0 else hash_length a in
      HMAC.keysized a (Seq.length prk) /\
      Seq.length last = chainLength /\
      hash_length a + length info + 1 + block_length a <= max_input_length a /\
      count < 255 /\
      required <= (255 - count) * hash_length a))
    (ensures fun _ -> True)
=
  fun a prk info required count last ->
  let count = count + 1 in
  let text = last @| info @| Seq.create 1 (Lib.IntTypes.u8 count) in
  let tag = Spec.Agile.HMAC.hmac a prk text in
  if required <= hash_length a
  then fst (split tag required)
  else tag @| expand0 a prk info (required - hash_length a) count tag

let expand a prk info required =
  expand0 a prk info required 0 Seq.empty
