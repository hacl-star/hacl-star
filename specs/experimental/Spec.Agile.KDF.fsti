module Spec.Agile.KDF

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module Hash = Spec.Agile.Hash
module HMAC = Spec.Agile.HMAC


val build_label:
    secret: bytes
  -> label: bytes{length label <= maxint U8}
  -> context: bytes{length context <= maxint U8
                 /\ numbytes U16 + numbytes U8 + length label + numbytes U8 + length context <= max_size_t}
  -> len: nat{len <= maxint U16} ->
  Tot (lbytes (numbytes U16 + numbytes U8 + length label + numbytes U8 + length context))


val expand_label:
    a: Hash.algorithm
  -> secret: bytes{length secret <= Hash.max_input a}
  -> label: bytes{length label <= maxint U8}
  -> context: bytes{
    let size_hkdf_label = numbytes U16 + numbytes U8 + length label + numbytes U8 + length context in
    length context <= maxint U8
  /\ length secret + size_hkdf_label + 1 + Hash.size_hash a + Hash.size_block a <= Hash.max_input a}
  -> len: nat{len <= maxint U16 /\ len < 255 * Hash.size_hash a} ->
  Tot (lbytes len)


val expand_derive_secret:
    a: Hash.algorithm
  -> secret: bytes{length secret <= Hash.max_input a}
  -> label: bytes{length label <= maxint U8}
  -> context: bytes{
    let size_hkdf_label = numbytes U16 + numbytes U8 + length label + numbytes U8 + Hash.size_hash a in
    length context <= maxint U8
  /\ length secret + size_hkdf_label + 1 + Hash.size_hash a + Hash.size_block a <= Hash.max_input a} ->
  Tot (lbytes (Hash.size_hash a))
