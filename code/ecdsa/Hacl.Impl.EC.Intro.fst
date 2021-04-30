module Hacl.Impl.EC.Intro

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Spec.ECC.Curves

open Lib.Loops
open FStar.Mul


val toUint8: #c: curve -> i: felem c -> o: lbuffer uint8 (getCoordinateLenU c) -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ as_seq h1 o == Lib.ByteSequence.uints_to_bytes_be (as_seq h0 i))

let toUint8 #c i o =
  let len = getCoordinateLenU64 c in 
  Lib.ByteBuffer.uints_to_bytes_be len o i


#set-options " --z3rlimit 200"

val changeEndianStep: #c: curve -> i: nat {i <= v (getCoordinateLenU64 c) / 2} 
  -> b0: felem_seq c 
  -> Tot (b1: felem_seq c {
    let len = v (getCoordinateLenU64 c) in 
    let lenR = len - i - 1 in 
    Lib.Sequence.index b0 i == Lib.Sequence.index b1 lenR /\ (
    forall (j: nat). (j < len /\ j <> lenR /\ j <> i) ==> Lib.Sequence.index b1 j == Lib.Sequence.index b0 j)})

let changeEndianStep #c i b =
  let len = v (getCoordinateLenU64 c) in 
  let lenRight = len - 1 - i in 
  let left = Lib.Sequence.index b i in 
  let right = Lib.Sequence.index b lenRight in 
  let b1 = Lib.Sequence.upd b i right in 
  let b2 = Lib.Sequence.upd b1 lenRight left in 
  b2


val changeEndian_spec: #c: curve -> b0: felem_seq c -> Tot (b1: felem_seq c 
  {forall (j: nat). (j < v (getCoordinateLenU64 c)) ==> Lib.Sequence.index b0 j == 
  Lib.Sequence.index b1 (v (getCoordinateLenU64 c) - j - 1)})

let changeEndian_spec #c b =
  let len = getCoordinateLenU64 c in 
  let lenByTwo = v len / 2 in
  
  let pred (i: nat {i <= lenByTwo}) (b1: felem_seq c) =  
    (forall (j: nat). (j >= i /\ j <= v len - 1 - i) ==> Lib.Sequence.index b1 j == Lib.Sequence.index b j) /\ 
    (forall (j: nat). (j > v len - 1 - i /\ j < v len) ==> Lib.Sequence.index b1 (v len - j - 1) == Lib.Sequence.index b j) /\ 
    (forall (j: nat). (j < i) ==> Lib.Sequence.index b1 (v len - j - 1) == Lib.Sequence.index b j) in 

  Lib.LoopCombinators.repeati_inductive lenByTwo pred (fun i b0 -> changeEndianStep #c i b0) b


let changedEndian_ #c (i : Lib.Sequence.lseq uint64 (v (getCoordinateLenU64 c))) 
  (o: Lib.Sequence.lseq uint64 (v (getCoordinateLenU64 c))) = 
  forall (j: nat). (j < v (getCoordinateLenU64 c)) ==> 
    Lib.Sequence.index i j == Lib.Sequence.index o (v (getCoordinateLenU64 c) - j - 1)

val changeEndian: #c: curve -> i: felem c -> Stack unit 
  (requires fun h -> live h i)
  (ensures  fun h0 _ h1 -> modifies1 i h0 h1 /\ changedEndian_ (as_seq h0 i) (as_seq h1 i))

let changeEndian #c b =
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  let lenByTwo = shift_right len 1ul in 

   [@inline_let]
  let inv h (i: nat { i <= uint_v lenByTwo}) = live h b /\ modifies (loc b) h0 h /\ (
    let b1 = as_seq h b in 
    let b0 = as_seq h0 b in 
    (forall (j: nat). (j >= i /\ j <= v len - 1 - i) ==> Lib.Sequence.index b1 j == Lib.Sequence.index b0 j) /\ 
    (forall (j: nat). (j > v len - 1 - i /\ j < v len) ==> Lib.Sequence.index b1 (v len - j - 1) == Lib.Sequence.index b0 j) /\ 
    (forall (j: nat). (j < i) ==> Lib.Sequence.index b1 (v len - j - 1) == Lib.Sequence.index b0 j)) in 

  for 0ul lenByTwo inv (fun i -> 
    let lenRight = getCoordinateLenU64 c -. (size 1) -. i in 
    let left = index b i in 
    let right = index b lenRight in 
    upd b i right;
    upd b lenRight left)


val toUint64ChangeEndian: #c: curve -> i: lbuffer uint8 (getCoordinateLenU c) -> o: felem c -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1  /\
    changedEndian_ (as_seq h1 o) (Lib.ByteSequence.uints_from_bytes_be (as_seq h0 i)))

let toUint64ChangeEndian #c i o = 
  let len : FStar.UInt32.t = getCoordinateLenU64 c in 
  Lib.ByteBuffer.uints_from_bytes_be #U64 #SEC #len o i;
  changeEndian o


open Lib.ByteSequence

val lemma_lseq_nat_from_bytes_: #l: size_nat -> a: Lib.Sequence.lseq uint64 l -> i: nat {i > 0 /\ i <= l} ->
  Lemma (Lib.ByteSequence.nat_from_intseq_le (Lib.Sequence.slice a 0 i) == lseq_as_nat_ a i)

let rec lemma_lseq_nat_from_bytes_ #l a i = 
  let sl = Lib.Sequence.slice a 0 i in 
  match i with 
  |1 -> nat_from_intseq_le_lemma0 sl; lseq_as_nat_first a
  |_ -> lemma_lseq_nat_from_bytes_ a (i - 1);
    let i1 = i - 1 in 
    nat_from_intseq_le_slice_lemma a i1;
    nat_from_intseq_le_slice_lemma sl (i - 1);
    nat_from_intseq_le_lemma0 (Lib.Sequence.slice sl i1 i); 
    lseq_as_nat_definiton a i


val lemma_lseq_nat_from_bytes: #l: size_nat {l > 0} -> a: Lib.Sequence.lseq uint64 l -> 
  Lemma (Lib.ByteSequence.nat_from_intseq_le a == lseq_as_nat a)

let lemma_lseq_nat_from_bytes #l a = lemma_lseq_nat_from_bytes_ #l a l


val lemma_lseq_nat_from_bytes_test_: #c: curve
  -> a: Lib.Sequence.lseq uint64 (v (getCoordinateLenU64 c))
  -> b: Lib.Sequence.lseq uint64 (v (getCoordinateLenU64 c)) {changedEndian_ a b}
  -> i: nat {i > 0 /\ i <= (v (getCoordinateLenU64 c))} ->
  Lemma (let len = v (getCoordinateLenU64 c) in 
    Lib.ByteSequence.nat_from_intseq_be (Lib.Sequence.slice b (len - i) len) == lseq_as_nat_ a i)


let rec lemma_lseq_nat_from_bytes_test_ #c a b i = 
  let open Lib.Sequence in 
  let open FStar.Mul in 
  let len = v (getCoordinateLenU64 c) in 
  match i with
  |1 -> let sl = Lib.Sequence.slice b (len - i) len  in  nat_from_intseq_be_lemma0 sl; lseq_as_nat_first a
  |_ -> lemma_lseq_nat_from_bytes_test_ #c a b (i - 1);
    let sl = Lib.Sequence.slice b (len - i) len  in  
    let i1 = i - 1 in 
    lseq_as_nat_definiton a i;

    nat_from_intseq_be_slice_lemma sl 1;
    nat_from_intseq_be_lemma0 (Lib.Sequence.slice sl 0 1);
    Seq.lemma_index_slice b (len - i) len 0


val lemma_lseq_nat_from_bytes_test: #c: curve
  -> a: Lib.Sequence.lseq uint64 (v (getCoordinateLenU64 c))
  -> b: Lib.Sequence.lseq uint64 (v (getCoordinateLenU64 c)) {changedEndian_ a b} ->
  Lemma (Lib.ByteSequence.nat_from_intseq_be b == lseq_as_nat a)

let lemma_lseq_nat_from_bytes_test #c a b = 
  lemma_lseq_nat_from_bytes_test_ #c a b (v (getCoordinateLenU64 c))


val lemma_change_endian: #c: curve
  -> a: Lib.Sequence.lseq uint64 (v (getCoordinateLenU64 c))
  -> b: Lib.Sequence.lseq uint64 (v (getCoordinateLenU64 c)) -> 
  Lemma 
  (requires (Hacl.Impl.EC.Intro.changedEndian_ #c a b))
  (ensures (nat_from_intseq_le a == nat_from_intseq_be b))

let lemma_change_endian #c a b = 
  lemma_lseq_nat_from_bytes a;
  lemma_lseq_nat_from_bytes_test #c a b



