module Spec.HKDF

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module Hash = Spec.Hash
module HMAC = Spec.HMAC


val hkdf_extract:
    a:Hash.algorithm
  -> salt: bytes{length salt <= Hash.max_input a}
  -> ikm: bytes{length salt + length ikm + Hash.size_block a <= Hash.max_input a
        /\ Hash.size_hash a + length ikm + Hash.size_block a <= Hash.max_input a} ->
  Tot (lbytes (Hash.size_hash a))


val hkdf_expand:
    a:Hash.algorithm
  -> prk:bytes{length prk <= Hash.max_input a}
  -> info: bytes{length info + Hash.size_hash a + 1 <= max_size_t (* BB. FIXME, this is required by create *)
              /\ length prk + length info + 1 + Hash.size_hash a + Hash.size_block a <= Hash.max_input a}
  -> len:size_nat{len < 255 * Hash.size_hash a} ->
  Tot (lbytes len)


val hkdf_build_label:
    secret: bytes
  -> label: bytes{length label <= maxint U8}
  -> context: bytes{length context <= maxint U8
                 /\ numbytes U16 + numbytes U8 + length label + numbytes U8 + length context <= max_size_t}
  -> len: nat{len <= maxint U16} ->
  Tot (lbytes (numbytes U16 + numbytes U8 + length label + numbytes U8 + length context))


val hkdf_expand_label:
    a: Hash.algorithm
  -> secret: bytes{length secret <= Hash.max_input a}
  -> label: bytes{length label <= maxint U8}
  -> context: bytes{
    let size_hkdf_label = numbytes U16 + numbytes U8 + length label + numbytes U8 + length context in
    length context <= maxint U8
  /\ length secret + size_hkdf_label + 1 + Hash.size_hash a + Hash.size_block a <= Hash.max_input a}
  -> len: nat{len <= maxint U16 /\ len < 255 * Hash.size_hash a} ->
  Tot (lbytes len)


val hkdf_expand_derive_secret:
    a: Hash.algorithm
  -> secret: bytes{length secret <= Hash.max_input a}
  -> label: bytes{length label <= maxint U8}
  -> context: bytes{
    let size_hkdf_label = numbytes U16 + numbytes U8 + length label + numbytes U8 + Hash.size_hash a in
    length context <= maxint U8
  /\ length secret + size_hkdf_label + 1 + Hash.size_hash a + Hash.size_block a <= Hash.max_input a} ->
  Tot (lbytes (Hash.size_hash a))
