module Hacl.Impl.ECDSA.P256SHA256.Common

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.Buffer
open Lib.IntTypes
open Lib.ByteBuffer 
open Lib.ByteSequence

open Hacl.Spec.P256 
open Hacl.Spec.P256.Definitions

open Hacl.Spec.ECDSAP256.Definition

open Hacl.Impl.LowLevel
open Hacl.Impl.ECDSA.MontgomeryMultiplication


#set-options "--z3rlimit 100"

val changeEndian: i: felem -> Stack unit 
  (requires fun h -> live h i)
  (ensures fun h0 _ h1 -> modifies1 i h0 h1 /\ as_seq h1 i == Hacl.Spec.ECDSA.changeEndian (as_seq h0 i)) 

let changeEndian i = 
  let zero = index i (size 0) in 
  let one = index i (size 1) in 
  let two = index i (size 2) in 
  let three = index i (size 3) in 
  upd i (size 0) three;
  upd i (size 1) two; 
  upd i (size 2) one;
  upd i (size 3) zero


val toUint64ChangeEndian: i: lbuffer uint8 (32ul) -> o: felem ->  Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> 
    modifies (loc o) h0 h1 /\ 
    as_seq h1 o == Hacl.Spec.ECDSA.changeEndian(Lib.ByteSequence.uints_from_bytes_be #_ #_ #4 (as_seq h0 i))
  )

let toUint64ChangeEndian i o = 
  Lib.ByteBuffer.uints_from_bytes_be o i;
  changeEndian o


val toUint64: i: lbuffer uint8 (32ul) -> o: felem -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> 
    modifies (loc o) h0 h1 /\ 
    as_seq h1 o == Lib.ByteSequence.uints_from_bytes_le (as_seq h0 i)
  )

let toUint64 i o = 
  Lib.ByteBuffer.uints_from_bytes_le o i


val toUint8: i: felem ->  o: lbuffer uint8 (32ul) -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> 
    modifies (loc o) h0 h1 /\ 
    as_seq h1 o == Lib.ByteSequence.uints_to_bytes_le #_ #_ #4 (as_seq h0 i)
  )

let toUint8 i o = 
  Lib.ByteBuffer.uints_to_bytes_le (size 4) o i


val lemma_core_0: a: lbuffer uint64 (size 4) -> h: mem -> Lemma (nat_from_intseq_le (as_seq h a) == as_nat h a)

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


val lemma_core_1: a: lbuffer uint64 (size 4) -> h: mem -> 
  Lemma (nat_from_bytes_le (Lib.ByteSequence.uints_to_bytes_le (as_seq h a)) == as_nat h a)

let lemma_core_1 a h= 
  let open Lib.ByteSequence in 
  lemma_core_0 a h;
  lemma_nat_from_to_intseq_le_preserves_value #U64 #SEC 4 (as_seq h a);
  let n = nat_from_intseq_le (as_seq h a) in 
  uints_to_bytes_le_nat_lemma #U64 #SEC 4 n;
  lemma_nat_to_from_bytes_le_preserves_value #SEC (uints_to_bytes_le #U64 #SEC #4 (as_seq h a)) 32 (as_nat h a)
