module Hacl.Impl.P256.Q.BrTU

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.P256.Arithmetics

open Lib.Buffer
open Hacl.Impl.P256.LowLevel

open Spec.P256.Definitions
open Spec.P256.Lemmas

open Hacl.Impl.P256.Q.PrimitivesMasking


val toUInt64Widefelem: i: lbuffer uint8 (size 32) -> o: widefelem -> Stack unit 
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> True)

let toUInt64Widefelem i o = 
  let o = sub o (size 0) (size 4) in 
  toUint64ChangeEndian i o (*
  Lib.ByteBuffer.uints_from_bytes_be o i;
  changeEndian o *)


val toUInt8WideFelem: i: widefelem -> o: lbuffer uint8 (size 33) -> Stack unit 
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> True)

let toUInt8WideFelem i o = 
  let i1 = sub i (size 4) (size 4) in 
  changeEndian8 i;
  let o1 = sub o (size 1) (size 32) in 
  Lib.ByteBuffer.uints_to_bytes_be (size 4) o1 i1
  

val uploadOrder: a: widefelem -> Stack unit
  (requires fun h -> live h a)
  (ensures fun h0 _ h1 -> True)

let uploadOrder a = 
  upd a (size 0) (u64 17562291160714782033);
  upd a (size 1) (u64 13611842547513532036);
  upd a (size 2) (u64 18446744073709551615);
  upd a (size 3) (u64 18446744069414584320)


val uploadTwoOrder: a: widefelem -> Stack unit 
  (requires fun h -> live h a)
  (ensures fun h0 _ h1 -> True)

let uploadTwoOrder a = 
  upd a (size 0) (u64 16677838247720012450);
  upd a (size 1) (u64 8776941021317512457);
  upd a (size 2) (u64 18446744073709551615);
  upd a (size 3) (u64 18446744065119617025);
  upd a (size 4) (u64 1)


val brTu: s: lbuffer uint8 (size 32) -> newScalar: lbuffer uint8 (size 33) -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


let brTu s newScalar = 
  push_frame();
    let bufferSAsUint64 = create (size 8) (u64 0) in 
      toUInt64Widefelem s bufferSAsUint64;
      
    let buffferWideOrderForMask = create (size 8) (u64 0) in 
      uploadOrder buffferWideOrderForMask;

    (* or add4 *)
    
    add8 bufferSAsUint64 buffferWideOrderForMask buffferWideOrderForMask;
    let mask = (u64 0xffffffffffffffff) +. index buffferWideOrderForMask (size 4) in 
    

    let bufferWideOrder = create (size 8) (u64 0) in 

    uploadOrder bufferWideOrder;
    uploadTwoOrder buffferWideOrderForMask;

    cswap8 bufferWideOrder buffferWideOrderForMask mask;
  
    add8 bufferSAsUint64 bufferWideOrder bufferSAsUint64;
    let carry = (to_u8 (index bufferSAsUint64 (size 4))) in 

    cswap8 bufferWideOrder buffferWideOrderForMask mask;

    toUInt8WideFelem bufferSAsUint64 newScalar;
    upd newScalar (size 0) carry;

  pop_frame()
