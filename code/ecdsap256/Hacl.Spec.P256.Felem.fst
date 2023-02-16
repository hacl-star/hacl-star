module Hacl.Spec.P256.Felem

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.Sequence
open Lib.ByteSequence

open Spec.P256.Definitions

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

inline_for_extraction
let felem = lbuffer uint64 (size 4)
inline_for_extraction
let widefelem = lbuffer uint64 (size 8)
inline_for_extraction
type point = lbuffer uint64 (size 12)
inline_for_extraction
type scalar = lbuffer uint8 (size 32)


let as_nat (h:mem) (e:felem) : GTot nat =
  let s = as_seq h e in
  as_nat4 (s.[0], s.[1], s.[2], s.[3])


let as_nat_il (h:mem) (e:glbuffer uint64 (size 4)) : GTot nat =
  let s = as_seq h e in
  as_nat4 (s.[0], s.[1], s.[2], s.[3])


let wide_as_nat (h:mem) (e:widefelem) : GTot nat =
  let s = as_seq h e in
  wide_as_nat4 (s.[0], s.[1], s.[2], s.[3], s.[4], s.[5], s.[6], s.[7])


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
