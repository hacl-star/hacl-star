module Hacl.Impl.P256.Q.PrimitivesMasking

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.P256.Arithmetics

open Lib.Buffer
open Hacl.Impl.P256.LowLevel

open Spec.P256.Definitions
open Spec.P256.Lemmas


(** This is unused *)
inline_for_extraction noextract
val cmovznz: a: uint64 -> b: uint64 -> mask: uint64 {uint_v mask = 0 \/ uint_v mask = pow2 64 - 1} -> 
  Tot (r: uint64 {if uint_v mask = 0 then uint_v r = uint_v a else uint_v r = uint_v b})

let cmovznz a b mask = 
  lemma_xor_copy_cond a b mask;
  logxor a (logand mask (logxor a b))



val cmovznz4: out: felem -> x: felem -> y: felem -> mask: uint64 -> Stack unit
  (requires fun h -> as_nat h x < prime256 /\ as_nat h y < prime256 /\
    live h out /\ live h x /\ live h y /\ (uint_v mask == 0 \/ uint_v mask = pow2 64 - 1))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ as_nat h1 out < prime256 /\ (
    if v mask = 0
      then as_nat h1 out == as_nat h0 x
      else 
	as_nat h1 out == as_nat h0 y))

let cmovznz4 out x y mask = 
  let h0 = ST.get() in 
  
  let out_0 = index out (size 0) in 
  let out_1 = index out (size 1) in 
  let out_2 = index out (size 2) in 
  let out_3 = index out (size 3) in  

  let mask = eq_mask mask (u64 0) in 
  
  let r0 = logor (logand x.(size 0) mask) (logand y.(size 0) (lognot mask)) in 
  let r1 = logor (logand x.(size 1) mask) (logand y.(size 1) (lognot mask)) in 
  let r2 = logor (logand x.(size 2) mask) (logand y.(size 2) (lognot mask)) in 
  let r3 = logor (logand x.(size 3) mask) (logand y.(size 3) (lognot mask)) in 

  upd out (size 0) r0;
  upd out (size 1) r1;
  upd out (size 2) r2;
  upd out (size 3) r3;

  let x = as_seq h0 x in 
  let y = as_seq h0 y in 
  cmovznz4_lemma mask (Seq.index y 0) (Seq.index x 0);
  cmovznz4_lemma mask (Seq.index y 1) (Seq.index x 1);
  cmovznz4_lemma mask (Seq.index y 2) (Seq.index x 2);
  cmovznz4_lemma mask (Seq.index y 3) (Seq.index x 3)




assume val cswap8:  x: widefelem -> y: widefelem -> mask: uint64 -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)



assume val toUint64Widefelem: s: lbuffer uint8 (size 32) -> to: widefelem -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

assume val toUInt8WideFelem: a: widefelem -> to: lbuffer uint8 (size 33) -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

assume val uploadOrder: a: widefelem -> Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


assume val uploadTwoOrder: a: widefelem -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)



val brTu: s: lbuffer uint8 (size 32) -> newScalar: lbuffer uint8 (size 33) -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


let brTu s newScalar = 
  push_frame();
    let bufferSAsUint64 = create (size 8) (u64 0) in 
      toUint64Widefelem s bufferSAsUint64;
      
    let buffferWideOrderForMask = create (size 8) (u64 0) in 
      uploadOrder buffferWideOrderForMask;

    (* or add4 *)
    add8 bufferSAsUint64 buffferWideOrderForMask buffferWideOrderForMask;
    let mask = index buffferWideOrderForMask (size 5) in 
    

    let bufferWideOrder = create (size 8) (u64 0) in 
    let bufferWide2Order = create (size 8) (u64 0) in 

    uploadOrder bufferWideOrder;
    uploadTwoOrder bufferWide2Order;

    cswap8 bufferWideOrder bufferWide2Order mask;
   
    
    add8 bufferSAsUint64 bufferWideOrder bufferSAsUint64;
    toUInt8WideFelem bufferSAsUint64 newScalar;

  pop_frame()

    
  
