module Hacl.Spec.P256.Felem

open Lib.IntTypes
open Lib.Buffer
open Lib.Sequence
open Lib.ByteSequence
open FStar.HyperStack
open FStar.HyperStack.All
open Spec.P256.Definitions

inline_for_extraction
let felem = lbuffer uint64 (size 4)
inline_for_extraction 
let widefelem = lbuffer uint64 (size 8)


let as_nat (h:mem) (e:felem) : GTot nat =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  as_nat4 (s0, s1, s2, s3)


let as_nat_il (h:mem) (e:glbuffer uint64 (size 4)) : GTot nat =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  as_nat4 (s0, s1, s2, s3)



let wide_as_nat (h:mem) (e:widefelem) : GTot nat =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  let s5 = s.[5] in
  let s6 = s.[6] in
  let s7 = s.[7] in
  wide_as_nat4 (s0, s1, s2, s3, s4, s5, s6, s7)


inline_for_extraction
type point = lbuffer uint64 (size 12)

type scalar = lbuffer uint8 (size 32)

open Lib.ByteSequence

val lemma_core_0: a:lbuffer uint64 (size 4) -> h:mem
  -> Lemma (nat_from_intseq_le (as_seq h a) == as_nat h a)

let lemma_core_0 a h = 
  let k = as_seq h a in 
  let z = nat_from_intseq_le k in 
    nat_from_intseq_le_slice_lemma k 1;
    nat_from_intseq_le_lemma0 (Seq.slice k 0 1);
  let k1 = Seq.slice k 1 4 in 
    nat_from_intseq_le_slice_lemma #_ #_ #3 k1 1;
    nat_from_intseq_le_lemma0 (Seq.slice k1 0 1);
  let k2 = Seq.slice k1 1 3 in 
    nat_from_intseq_le_slice_lemma #_ #_ #2 k2 1;
    nat_from_intseq_le_lemma0 (Seq.slice k2 0 1);
    nat_from_intseq_le_lemma0 (Seq.slice k2 1 2)


val lemma_core_1: a:lbuffer uint64 (size 4) -> h:mem ->
  Lemma (nat_from_bytes_le (uints_to_bytes_le (as_seq h a)) == as_nat h a)


let lemma_core_1 a h= 
  lemma_core_0 a h;
  lemma_nat_from_to_intseq_le_preserves_value #U64 #SEC 4 (as_seq h a);
  let n = nat_from_intseq_le (as_seq h a) in 
  uints_to_bytes_le_nat_lemma #U64 #SEC 4 n;
  lemma_nat_to_from_bytes_le_preserves_value #SEC (uints_to_bytes_le #U64 #SEC #4 (as_seq h a)) 32 (as_nat h a)
