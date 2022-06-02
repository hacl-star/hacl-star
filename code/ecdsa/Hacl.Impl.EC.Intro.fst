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


#set-options " --z3rlimit 100 --max_fuel 0 --max_ifuel 0"


inline_for_extraction noextract
val toUint8: #c: curve -> i: felem c -> o: lbuffer uint8 (getCoordinateLenU c) -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ as_seq h1 o == Lib.ByteSequence.uints_to_bytes_be (as_seq h0 i))

let toUint8 #c i o =
  let len = getCoordinateLenU64 c in 
  Lib.ByteBuffer.uints_to_bytes_be len o i


let changedEndian_ #l (i: Lib.Sequence.lseq uint64 l) (o: Lib.Sequence.lseq uint64 l) = 
  forall (j: nat). (j < l) ==> Lib.Sequence.index i j == Lib.Sequence.index o (l - j - 1)


#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

inline_for_extraction
val changeEndian: #c: curve -> i: felem c -> Stack unit 
  (requires fun h -> live h i)
  (ensures  fun h0 _ h1 -> modifies (loc i) h0 h1 /\ changedEndian_ #(v (getCoordinateLenU64 c)) (as_seq h0 i) (as_seq h1 i))

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
    upd b lenRight left
  )

#pop-options


open Lib.ByteSequence

val lemma_lseq_nat_from_bytes_: #l: size_nat -> #t:inttype{unsigned t} -> a: Lib.Sequence.lseq (uint_t t SEC) l
  -> i: nat {i > 0 /\ i <= l} ->
  Lemma (Lib.ByteSequence.nat_from_intseq_le (Lib.Sequence.slice a 0 i) == lseq_as_nat_ a i)

let rec lemma_lseq_nat_from_bytes_ #l #t a i = 
  let sl = Lib.Sequence.slice a 0 i in 
  match i with 
  |1 -> nat_from_intseq_le_lemma0 sl; lseq_as_nat_first a
  |_ -> lemma_lseq_nat_from_bytes_ a (i - 1);
    let i1 = i - 1 in 
    nat_from_intseq_le_slice_lemma a i1;
    nat_from_intseq_le_slice_lemma sl (i - 1);
    nat_from_intseq_le_lemma0 (Lib.Sequence.slice sl i1 i); 
    lseq_as_nat_definiton a i


val lemma_lseq_nat_from_bytes: #l: size_nat {l > 0} -> #t:inttype{unsigned t} -> a: Lib.Sequence.lseq (uint_t t SEC) l -> 
  Lemma (Lib.ByteSequence.nat_from_intseq_le a == lseq_as_nat a)

let lemma_lseq_nat_from_bytes #l a = lemma_lseq_nat_from_bytes_ #l a l


val lemma_lseq_nat_from_bytes_test_: #c: curve -> #l: size_nat {l > 0}
  -> a: Lib.Sequence.lseq uint64 l
  -> b: Lib.Sequence.lseq uint64 l {changedEndian_  #l a b}
  -> i: nat {i > 0 /\ i <= l} ->
  Lemma (Lib.ByteSequence.nat_from_intseq_be (Lib.Sequence.slice b (l - i) l) == lseq_as_nat_ a i)


let rec lemma_lseq_nat_from_bytes_test_ #c #len a b i = 
  let open Lib.Sequence in 
  let open FStar.Mul in 
  match i with
  |1 -> let sl = Lib.Sequence.slice b (len - i) len in nat_from_intseq_be_lemma0 sl; lseq_as_nat_first a
  |_ -> 
    lemma_lseq_nat_from_bytes_test_ #c a b (i - 1);
    let sl : Lib.Sequence.lseq uint64 i = Lib.Sequence.slice b (len - i) len  in  
    let i1 = i - 1 in 
    lseq_as_nat_definiton a i;
    nat_from_intseq_be_slice_lemma #_ #_ #i sl 1;
    nat_from_intseq_be_lemma0 (Lib.Sequence.slice sl 0 1);
    Seq.lemma_index_slice b (len - i) len 0;

    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 
    assert_by_tactic (i1 * 64 == 64 * i1) canon


val lemma_lseq_nat_from_bytes_test: #c: curve -> #l: size_nat {l > 0}
  -> a: Lib.Sequence.lseq uint64 l
  -> b: Lib.Sequence.lseq uint64 l {changedEndian_ #l a b} ->
  Lemma (Lib.ByteSequence.nat_from_intseq_be b == lseq_as_nat a)

let lemma_lseq_nat_from_bytes_test #c #l a b = 
  lemma_lseq_nat_from_bytes_test_ #c #l a b l


val lemma_change_endian: #c: curve -> #l: size_nat {l > 0}
  -> a: Lib.Sequence.lseq uint64 l
  -> b: Lib.Sequence.lseq uint64 l -> 
  Lemma 
  (requires (changedEndian_  #l a b))
  (ensures (nat_from_intseq_le a == nat_from_intseq_be b))

let lemma_change_endian #c a b = 
  lemma_lseq_nat_from_bytes a;
  lemma_lseq_nat_from_bytes_test #c a b


let changeEndian_u8 len n = nat_from_bytes_be (nat_to_bytes_le #SEC len n)

inline_for_extraction noextract
val toUint64ChangeEndian_: #c: curve -> i: lbuffer uint8 (getCoordinateLenU c) -> o: felem c -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1  /\
    nat_from_bytes_be (as_seq h0 i) == as_nat c h1 o /\
    changedEndian_  #(v (getCoordinateLenU64 c))  (as_seq h1 o) (Lib.ByteSequence.uints_from_bytes_be (as_seq h0 i)))

let toUint64ChangeEndian_ #c i o = 
    let h0 = ST.get() in 
    let open Lib.ByteSequence in 
  let len : FStar.UInt32.t = getCoordinateLenU64 c in 
  Lib.ByteBuffer.uints_from_bytes_be #U64 #SEC #len o i;
  changeEndian o;
    let h1 = ST.get() in 
  
  lemma_lseq_nat_from_bytes_test #c (as_seq h1 o) (uints_from_bytes_be (as_seq h0 i));
  uints_from_bytes_be_nat_lemma #U64 #_ #(v (getCoordinateLenU64 c)) (as_seq h0 i)


[@CInline]
let toUint64ChangeEndian_p256 = toUint64ChangeEndian_ #P256
[@CInline]
let toUint64ChangeEndian_p384 = toUint64ChangeEndian_ #P384(* 
[@CInline]
let toUint64ChangeEndian_generic = toUint64ChangeEndian_ #Default *)


inline_for_extraction noextract
val toUint64ChangeEndian: #c: curve -> i: lbuffer uint8 (getCoordinateLenU c) -> o: felem c -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1  /\
    nat_from_bytes_be (as_seq h0 i) == as_nat c h1 o /\
    changedEndian_  #(v (getCoordinateLenU64 c))  (as_seq h1 o) (Lib.ByteSequence.uints_from_bytes_be (as_seq h0 i)))

let toUint64ChangeEndian #c i o = 
  match c with
  | P256 -> toUint64ChangeEndian_p256 i o
  | P384 -> toUint64ChangeEndian_p384 i o
  (* | Default -> toUint64ChangeEndian_generic i o  /  *)
