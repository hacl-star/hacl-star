module Spec.Agile.HKDF

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Hash.Definitions
module Hash = Spec.Agile.Hash
module HMAC = Spec.Agile.HMAC


val hkdf_extract:
    a:hash_alg
  -> salt: bytes{HMAC.keysized a (Seq.length salt)}
  -> ikm: bytes{length ikm + block_length a <= max_input_length a
        /\ (* hash_length a +  *)length ikm + block_length a <= max_input_length a} ->
  Tot (lbytes (hash_length a))


val hkdf_expand:
    a:hash_alg
  -> prk:bytes{HMAC.keysized a (Seq.length prk)}
  -> info: bytes{length info + hash_length a + 1 <= max_size_t (* BB. FIXME, this is required by create *)
              /\ length info + 1 + hash_length a + block_length a <= max_input_length a}
  -> len:size_nat{len < 255 * hash_length a} ->
  Tot (lbytes len)


val hkdf_build_label:
    secret: bytes
  -> label: bytes{length label <= maxint U8}
  -> context: bytes{length context <= maxint U8
                 /\ numbytes U16 + numbytes U8 + length label + numbytes U8 + length context <= max_size_t}
  -> len: nat{len <= maxint U16} ->
  Tot (lbytes (numbytes U16 + numbytes U8 + length label + numbytes U8 + length context))


val hkdf_expand_label:
    a: hash_alg
  -> secret: bytes{HMAC.keysized a (Seq.length secret)}
  -> label: bytes{length label <= maxint U8}
  -> context: bytes{
    let size_hkdf_label = numbytes U16 + numbytes U8 + length label + numbytes U8 + length context in
    length context <= maxint U8
  /\ length secret + size_hkdf_label + 1 + hash_length a + block_length a <= max_input_length a}
  -> len: nat{len <= maxint U16 /\ len < 255 * hash_length a} ->
  Tot (lbytes len)


val hkdf_expand_derive_secret:
    a: hash_alg
  -> secret: bytes{HMAC.keysized a (Seq.length secret)}
  -> label: bytes{length label <= maxint U8}
  -> context: bytes{
    let size_hkdf_label = numbytes U16 + numbytes U8 + length label + numbytes U8 + hash_length a in
    length context <= maxint U8
  /\ length secret + size_hkdf_label + 1 + hash_length a + block_length a <= max_input_length a} ->
  Tot (lbytes (hash_length a))
