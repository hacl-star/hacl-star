module Spec.Agile.HKDF

open FStar.Mul
open Spec.Hash.Definitions

let lbytes (l:nat) = b:bytes {Seq.length b = l}

let extract_ikm_length_pred (a:hash_alg) (ikm_length:nat) =
  ikm_length + block_length a <= max_input_length a

val extract:
  a: hash_alg ->
  key: bytes ->
  data: bytes ->
  Pure (lbytes (hash_length a))
    (requires
      Spec.Agile.HMAC.keysized a (Seq.length key) /\
      extract_ikm_length_pred a (Seq.length data))
    (ensures fun _ -> True)

let expand_info_length_pred (a:hash_alg) (info_length:nat) =
  hash_length a + info_length + 1 + block_length a <= max_input_length a

let expand_output_length_pred (a:hash_alg) (len:nat) =
  len <= 255 * hash_length a

val expand:
  a: hash_alg ->
  prk: bytes ->
  info: bytes ->
  len: nat ->
  Pure (lbytes len)
    (requires
      hash_length a <= Seq.length prk /\
      HMAC.keysized a (Seq.length prk) /\
      expand_info_length_pred a (Seq.length info) /\
      expand_output_length_pred a len)
    (ensures fun _ -> True)
