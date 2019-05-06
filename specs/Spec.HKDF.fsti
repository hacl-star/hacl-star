module Spec.HKDF

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module Hash = Spec.Hash.Definitions
module HMAC = Spec.HMAC


val hkdf_extract:
    a:Hash.hash_alg
  -> salt: bytes{length salt  + Hash.block_length a < Hash.max_input_length a}
  -> ikm: bytes{length salt + length ikm + Hash.block_length a < max_size_t
        /\ Hash.hash_length a + length ikm + Hash.block_length a < max_size_t} ->
  Tot (lbytes (Hash.hash_length a))


val hkdf_expand:
    a:Hash.hash_alg
  -> prk:bytes{length prk < Hash.max_input_length a}
  -> info: bytes{length info + Hash.hash_length a + 1 < max_size_t (* BB. FIXME, this is required by create *)
              /\ length prk + length info + 1 + Hash.hash_length a + Hash.block_length a < max_size_t}
  -> len:size_nat{len < 255 * Hash.hash_length a} ->
  Tot (lbytes len)


val hkdf_build_label:
    secret: bytes
  -> label: bytes{length label <= maxint U8}
  -> context: bytes{length context <= maxint U8
                 /\ numbytes U16 + numbytes U8 + length label + numbytes U8 + length context <= max_size_t}
  -> len: nat{len <= maxint U16} ->
  Tot (lbytes (numbytes U16 + numbytes U8 + length label + numbytes U8 + length context))


val hkdf_expand_label:
    a: Hash.hash_alg
  -> secret: bytes{length secret < Hash.max_input_length a}
  -> label: bytes{length label <= maxint U8}
  -> context: bytes{
    let size_hkdf_label = numbytes U16 + numbytes U8 + length label + numbytes U8 + length context in
    length context < maxint U8
  /\ length secret + size_hkdf_label + 1 + Hash.hash_length a + Hash.block_length a < max_size_t}
  -> len: nat{len <= maxint U16 /\ len < 255 * Hash.hash_length a} ->
  Tot (lbytes len)

val hkdf_expand_derive_secret:
    a: Hash.hash_alg
  -> secret: bytes{length secret < Hash.max_input_length a}
  -> label: bytes{length label <= maxint U8}
  -> context: bytes{
    let size_hkdf_label = numbytes U16 + numbytes U8 + length label + numbytes U8 + Hash.hash_length a in
    length context <= maxint U8
  /\ length secret + size_hkdf_label + 1 + Hash.hash_length a + Hash.block_length a < max_size_t} ->
  Tot (lbytes (Hash.hash_length a))
