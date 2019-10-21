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

/// HKDF-Expand(PRK, info, L)
///
///   N = ceil(L/HashLen)
///   T = T(1) | T(2) | T(3) | ... | T(N)
///   OKM = first L octets of T
///
///   where:
///   T(0) = empty string (zero length)
///   T(1) = HMAC-Hash(PRK, T(0) | info | 0x01)
///   T(2) = HMAC-Hash(PRK, T(1) | info | 0x02)
///   T(3) = HMAC-Hash(PRK, T(2) | info | 0x03)
///
/// See https://tools.ietf.org/html/rfc5869#section-2.3

/// The type of T(i) is [a_spec a i]
let a_spec (a:hash_alg) (i:nat) =
  Seq.lseq uint8 (if i = 0 then 0 else hash_length a)

/// The main loop that computes T(i)
val expand_loop:
    a:hash_alg
  -> prk:bytes
  -> info:bytes
  -> n:nat
  -> i:nat{i < n}
  -> a_spec a i
  -> Pure (a_spec a (i + 1) & Seq.lseq uint8 (hash_length a))
    (requires
      hash_length a <= Seq.length prk /\
      HMAC.keysized a (Seq.length prk) /\
      hash_length a + Seq.length info + 1 + block_length a <= max_input_length a /\
      n <= 255)
    (ensures fun _ -> True)
let expand_loop a prk info n i tag =
  let t = Spec.Agile.HMAC.hmac a prk (tag @| info @| Seq.create 1 (u8 (i + 1))) in
  t, t

/// Expands first computes T(0) | T(1) | ... | T(floor(L/HashLen)) in a loop and then
/// if needed computes T(N) and appends as many bytes as required to complete OKM
let expand a prk info len =
  let open Spec.Agile.HMAC in
  let tlen = hash_length a in
  let n = len / tlen in
  let tag, output =
    Seq.generate_blocks tlen n n (a_spec a) (expand_loop a prk info n) FStar.Seq.empty
  in
  if n * tlen < len then
    let t = hmac a prk (tag @| info @| Seq.create 1 (u8 (n + 1))) in
    output @| Seq.sub #_ #tlen t 0 (len - (n * tlen))
  else
    output
