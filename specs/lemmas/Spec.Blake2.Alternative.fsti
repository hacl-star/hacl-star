module Spec.Blake2.Alternative

open Spec.Blake2

open Lib.IntTypes
open Lib.ByteSequence
open Lib.Sequence

let blake2_update'
  (a:alg)
  (kk:size_nat{kk <= max_key a})
  (k:lbytes kk)
  (d:bytes{if kk = 0 then length d <= max_limb a else length d + (size_block a) <= max_limb a})
  (s:state a): Tot (state a)
= let ll = length d in
  let key_block: bytes = if kk > 0 then blake2_key_block a kk k else Seq.empty in
  blake2_update_blocks a 0 (key_block `Seq.append` d) s

val lemma_spec_equivalence_update:
    a:alg
  -> kk:size_nat{kk <= max_key a}
  -> k:lbytes kk
  -> d:bytes{if kk = 0 then length d <= max_limb a else length d + (size_block a) <= max_limb a}
  -> s:state a ->
  Lemma (blake2_update a kk k d s `Seq.equal` blake2_update' a kk k d s)
