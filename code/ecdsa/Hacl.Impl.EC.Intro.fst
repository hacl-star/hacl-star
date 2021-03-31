module Hacl.Impl.EC.Intro

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Hacl.Lemmas.P256

open Spec.ECC
open Spec.ECC.Curves

open FStar.Math
open FStar.Math.Lemmas
open FStar.Mul

open FStar.Tactics
open FStar.Tactics.Canon

open Hacl.Impl.P256.LowLevel
open Hacl.Impl.P384.LowLevel
open Hacl.Impl.EC.Masking

open Lib.IntTypes.Intrinsics


open Lib.Loops

open Hacl.Bignum

open Lib.ByteBuffer



val toUint8: #c: curve -> i: felem c -> o: lbuffer uint8 (getCoordinateLenU c) -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ as_seq h1 o == Lib.ByteSequence.uints_to_bytes_be (as_seq h0 i))

let toUint8 #c i o =
  match c with
  |P256 -> Lib.ByteBuffer.uints_to_bytes_be (getCoordinateLenU64 c) o i
  |P384 -> Lib.ByteBuffer.uints_to_bytes_be (getCoordinateLenU64 c) o i
  |_ -> Lib.ByteBuffer.uints_to_bytes_be (getCoordinateLenU64 c) o i


val changeEndian: #c: curve -> i: felem c -> Stack unit 
  (requires fun h -> live h i)
  (ensures  fun h0 _ h1 -> modifies1 i h0 h1 /\ 
    as_seq h1 i == Hacl.Spec.EC.Definition.changeEndian (as_seq h0 i) /\
    as_nat c h1 i < pow2 (getPower c)) 


val toUint64ChangeEndian: #c: curve -> i: lbuffer uint8 (getCoordinateLenU c) -> o: felem c -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\
    as_seq h1 o == Hacl.Spec.EC.Definition.changeEndian (
    Lib.ByteSequence.uints_from_bytes_be (as_seq h0 i)))


let changeEndian #c b =
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  let lenByTwo = shift_right len 1ul in 

  [@inline_let]
  let spec h0 = Hacl.Spec.EC.Definition.changeEndianStep #c  in 
  admit();
   [@inline_let]
  let acc (h: mem) : GTot (felem_seq c) = as_seq h b in 
  Lib.LoopCombinators.eq_repeati0 256 (spec h0) (acc h0);

   [@inline_let]
  let inv h (i: nat { i <= uint_v lenByTwo}) = live h b /\ modifies (loc b) h0 h /\
    (forall (j: nat {j < i}). 
      let leftStart = Lib.Sequence.index (as_seq h0 b) j in 
      let rightIndex = v len - 1 - j in 
      let rightStart = Lib.Sequence.index (as_seq h0 b) rightIndex in 

      let leftH = Lib.Sequence.index (as_seq h b) j in 
      let rightH = Lib.Sequence.index (as_seq h b) rightIndex in 

      uint_v leftStart == uint_v rightH /\
      uint_v rightStart == uint_v leftH) /\
    (forall (j: nat {j >= i && j < v lenByTwo}).
      Lib.Sequence.index (as_seq h0 b) j == Lib.Sequence.index (as_seq h b) j) /\
    (forall (j: nat {j >= v lenByTwo &&  j <= v len - 1 - i}).
      Lib.Sequence.index (as_seq h0 b) j == Lib.Sequence.index (as_seq h b) j) in 
  for 0ul lenByTwo inv (fun i -> 
    let h_0 = ST.get() in 
    
    let left = index b i in 
    let rightIndex = len -. 1ul -. i in 
    let right = index b rightIndex in 
    upd b i right;
    upd b rightIndex left
    
    );
    let h1 = ST.get() in 
    assert(
      forall (j: nat {j < v (shift_right len 1ul)}). 
      
      let leftStart = Lib.Sequence.index (as_seq h0 b) j in 
      let rightIndex = v len - 1 - j in 
      let rightStart = Lib.Sequence.index (as_seq h0 b) rightIndex in 

      let leftH = Lib.Sequence.index (as_seq h1 b) j in 
      let rightH = Lib.Sequence.index (as_seq h1 b) rightIndex in 

      uint_v leftStart == uint_v rightH /\
      uint_v rightStart == uint_v leftH);
      
  
    admit()
  

val toUint64CEP256: i:lbuffer uint8 (getScalarLen P256) -> o: felem P256 -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures  fun h0 _ h1 ->
    modifies (loc o) h0 h1  /\
    as_seq h1 o == Hacl.Spec.EC.Definition.changeEndian (
      Lib.ByteSequence.uints_from_bytes_be (as_seq h0 i)))

let toUint64CEP256 i o = 
  Lib.ByteBuffer.uints_from_bytes_be o i;
  changeEndian o


val toUint64CEP384: i:lbuffer uint8 (getScalarLen P384) -> o: felem P384 -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures  fun h0 _ h1 ->
    modifies (loc o) h0 h1  /\
    as_seq h1 o == Hacl.Spec.EC.Definition.changeEndian (
      Lib.ByteSequence.uints_from_bytes_be (as_seq h0 i)))

let toUint64CEP384 i o = 
  Lib.ByteBuffer.uints_from_bytes_be o i;
  changeEndian o


let toUint64ChangeEndian #c i o =
  match c with 
  |P256 -> toUint64CEP256 i o
  |P384 -> toUint64CEP384 i o
