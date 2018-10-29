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
