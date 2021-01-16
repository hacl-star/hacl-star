module Hacl.Impl.ScalarMultiplication.WNAF


open FStar.HyperStack.All
open FStar.HyperStack

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes

open Lib.Buffer

open Lib.IntTypes.Intrinsics
open Hacl.Impl.P256.Q.PrimitivesMasking


let dradix_wnaf = (u64 64)

let dradix = (u64 32)

let radix = (u64 5)

inline_for_extraction noextract
val scalar_rwnaf : out: lbuffer uint64 (size 104) -> scalar: lbuffer uint8 (size 32) -> 
  Stack unit 
    (requires fun h -> live h out /\ live h scalar)
    (ensures fun h0 _ h1 -> True)


let scalar_rwnaf out scalar = 
  push_frame();
  
 let window = create (size 1) (logor (u64 1) (logand (to_u64 (index scalar (size 0))) (dradix_wnaf -! (u64 1))))  in 
 let d = create (size 1) (u64 0) in 

 let r = create (size 1) (u64 0) in 
 let r1 = create (size 1) (u64 0) in 

 let h0 = ST.get() in 
 let inv h1 (i:nat) = live h1 window /\ live h1 out in  

  Lib.Loops.for 0ul 51ul inv
    (fun i ->

      let h0 = ST.get() in 
      assume (live h0 window);
      let wAsVariable : uint64 = index window (size 0) in 
      
      let w = logand wAsVariable  (dradix_wnaf -! (u64 1)) in 
	let dToUpload = logand wAsVariable (dradix_wnaf -! (u64 1)) -! dradix in 
      upd d (size 0) dToUpload;
      let c = sub_borrow_u64 (u64 0) w dradix r in 
      let c1 = sub_borrow_u64 (u64 0) (u64 0) (index r (size 0)) r1 in 
      let cAsFlag = (u64 0xffffffff) +! c in 
      let r3 = cmovznz2 (index r (size 0)) (index r1 (size 0)) cAsFlag in 
      upd out (size 2 *! i) r3;
      upd out (size 2 *! i +! 1) c;


      let wStart = wAsVariable -! (index d (size 0)) in 
      let windowTemp = shift_right wStart radix in  
      () 


    );

pop_frame()
  



