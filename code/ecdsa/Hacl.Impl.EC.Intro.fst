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


let changedEndian #c (i : Lib.Sequence.lseq uint64 (v (getCoordinateLenU64 c))) 
  (o: Lib.Sequence.lseq uint64 (v (getCoordinateLenU64 c))) = 
  forall (j: nat). (j < v (getCoordinateLenU64 c)) ==> 
    Lib.Sequence.index i j == Lib.Sequence.index o (v (getCoordinateLenU64 c) - j - 1)

val changeEndian: #c: curve -> i: felem c -> Stack unit 
  (requires fun h -> live h i)
  (ensures  fun h0 _ h1 -> modifies1 i h0 h1 /\ changedEndian (as_seq h0 i) (as_seq h1 i))

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

(*
val changeEndianLemma: #c: curve -> k: Lib.Sequence.lseq uint64 (getCoordinateLen c) -> Lemma
  (Lib.ByteSequence.nat_from_intseq_le (changeEndian #c k) == Lib.ByteSequence.nat_from_intseq_be k)

let changeEndianLemma #c k = ()


val changeEndianLemmaI: #c: curve -> a: nat {a < pow2 (getPower c)} -> Lemma
  (changeEndian #c (Lib.ByteSequence.nat_to_intseq_le (uint_v (getCoordinateLenU64 c)) a) == Lib.ByteSequence.nat_to_intseq_be (uint_v (getCoordinateLenU64 c)) a)

let changeEndianLemmaI #c a = 
  let open Lib.ByteSequence in 
  let len = getCoordinateLenU64 c in
  let a0 = nat_to_intseq_le #U64 #SEC 4 a in
  index_nat_to_intseq_le #U64 #SEC  4 a 0;
  index_nat_to_intseq_le #U64 #SEC  4 a 1;
  index_nat_to_intseq_le #U64 #SEC  4 a 2;
  index_nat_to_intseq_le #U64 #SEC  4 a 3;

  index_nat_to_intseq_be #U64 #SEC 4 a 0;
  index_nat_to_intseq_be #U64 #SEC 4 a 2;
  index_nat_to_intseq_be #U64 #SEC 4 a 3;
  index_nat_to_intseq_be #U64 #SEC 4 a 1;


  assert(Lib.Sequence.index #_ #4 (changeEndian #c (nat_to_intseq_le #U64 #SEC 4 a)) 3 == Lib.Sequence.index #_ #4 (nat_to_intseq_be #U64 #SEC 4 a) 3);

  assert(Lib.Sequence.index #_ #4 (changeEndian #c (nat_to_intseq_le #U64 #SEC 4 a)) 2 == Lib.Sequence.index #_ #4 (nat_to_intseq_be #U64 #SEC 4 a) 2);

  assert(Lib.Sequence.index #_ #4 (changeEndian #c (nat_to_intseq_le #U64 #SEC 4 a)) 1 == Lib.Sequence.index #_ #4 (nat_to_intseq_be #U64 #SEC 4 a) 1);

  assert(Lib.Sequence.index #_ #4 (changeEndian #c (nat_to_intseq_le #U64 #SEC 4 a)) 0 == Lib.Sequence.index #_ #4 (nat_to_intseq_be #U64 #SEC 4 a) 0);
  eq_intro (changeEndian #c (nat_to_intseq_le #U64 #SEC 4 a)) (nat_to_intseq_be 4 a) 


val changeEndian_le_be: #c: curve -> a:nat{a < pow2 (getPower c)} -> Lemma
  (Lib.ByteSequence.uints_to_bytes_be (changeEndian #c (Lib.ByteSequence.nat_to_intseq_le (uint_v (getCoordinateLenU64 c)) a)) == Lib.ByteSequence.nat_to_bytes_be (getCoordinateLen c) a)

let changeEndian_le_be #c a =
  changeEndianLemmaI #c a;
  Lib.ByteSequence.uints_to_bytes_be_nat_lemma #U64 #SEC (uint_v (getCoordinateLenU64 c)) a
*)


val toUint64ChangeEndian: #c: curve -> i: lbuffer uint8 (getCoordinateLenU c) -> o: felem c -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1  /\
    changedEndian (as_seq h1 o) (Lib.ByteSequence.uints_from_bytes_be (as_seq h0 i)))

let toUint64ChangeEndian #c i o = 
  let len : FStar.UInt32.t = getCoordinateLenU64 c in 
  Lib.ByteBuffer.uints_from_bytes_be #U64 #SEC #len o i;
  changeEndian o

