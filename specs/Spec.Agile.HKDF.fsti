module Spec.Agile.HKDF

open FStar.Mul
open Spec.Hash.Definitions

let lbytes (l:nat) = b:bytes {Seq.length b = l}

val extract:
  a: hash_alg ->
  key: bytes ->
  data: bytes ->
  Pure (lbytes (hash_length a))
    (requires
      Spec.Agile.HMAC.keysized a (Seq.length key) /\
      Seq.length data + block_length a <= max_input_length a)
    (ensures fun _ -> True)

val expand:
  a: hash_alg ->
  prk: bytes ->
  info: bytes ->
  len: nat ->
  Pure (lbytes len)
    (requires
      hash_length a <= Seq.length prk /\
      HMAC.keysized a (Seq.length prk) /\
      hash_length a + Seq.length info + 1 + block_length a <= max_input_length a /\
      len <= 255 * hash_length a)
    (ensures fun _ -> True)
