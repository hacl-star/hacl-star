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


(* Originally lives in P256.Core *)
(* this piece of code is taken from Hacl.Curve25519 *)
(* changed Endian for Scalar Bit access *)

inline_for_extraction
val scalar_bit:
    s:lbuffer_t MUT uint8 (size 32)
  -> n:size_t{v n < 256}
  -> Stack uint64
    (requires fun h0 -> live h0 s)
    (ensures  fun h0 r h1 -> h0 == h1 /\  v r <= 1)

let scalar_bit s n =
  let h0 = ST.get () in
  mod_mask_lemma ((Lib.Sequence.index (as_seq h0 s) (31 - v n / 8)) >>. (n %. 8ul)) 1ul;
  assert_norm (1 = pow2 1 - 1);
  assert (v (mod_mask #U8 #SEC 1ul) == v (u8 1)); 
  to_u64 ((s.(n /. 8ul) >>. (n %. 8ul)) &. u8 1)



inline_for_extraction noextract
let dradix_wnaf = (u64 64)
inline_for_extraction noextract
let dradix = (u64 32)
inline_for_extraction noextract
let radix = (u64 5)

inline_for_extraction noextract
val scalar_rwnaf : out: lbuffer uint64 (size 104) -> scalar: lbuffer uint8 (size 32) -> 
  Stack unit 
    (requires fun h -> live h out /\ live h scalar)
    (ensures fun h0 _ h1 -> True)


let scalar_rwnaf out scalar = 
  push_frame();

  let in0 = index scalar (size 0) in 
  let windowStartValue =  (logor (u64 1) (logand (to_u64 in0) (dradix_wnaf -! (u64 1))))  in 
  
 let window = create (size 1) windowStartValue in 

 let r = create (size 1) (u64 0) in 
 let r1 = create (size 1) (u64 0) in 

 let h0 = ST.get() in 
 let inv h1 (i:nat) = live h1 window /\ live h1 out in  

  Lib.Loops.for 0ul 51ul inv
    (fun i ->

      let h0 = ST.get() in 

      let wVar : uint64 = index window (size 0) in 
      
      let w = logand wVar  (dradix_wnaf -! (u64 1)) in 
      
      let d = logand wVar (dradix_wnaf -! (u64 1)) -! dradix in 

      let c = sub_borrow_u64 (u64 0) w dradix r in 
      let c1 = sub_borrow_u64 (u64 0) (u64 0) (index r (size 0)) r1 in 
      
      let cAsFlag = (u64 0xffffffff) +! c in 
      let r3 = cmovznz2 (index r (size 0)) (index r1 (size 0)) cAsFlag in 
      
      upd out (size 2 *! i) r3;
      upd out (size 2 *! i +! 1) c;


      let wStart = shift_right (wVar -! d) radix in 
      let w0 = wStart +! (shift_left (scalar_bit scalar ((size 1 +! i) *! radix +! (size 1))) (size 1)) in 
      let w0 = w0 +! (shift_left (scalar_bit scalar ((size 1 +! i) *! radix +! (size 2))) (size 2)) in 
      let w0 = w0 +! (shift_left (scalar_bit scalar ((size 1 +! i) *! radix +! (size 3))) (size 3)) in 
      let w0 = w0 +! (shift_left (scalar_bit scalar ((size 1 +! i) *! radix +! (size 4))) (size 4)) in 
      let w0 = w0 +! (shift_left (scalar_bit scalar ((size 1 +! i) *! radix +! (size 5))) (size 5)) in

      upd window (size 0) w0


    );

    upd out (size 102) (index window (size 0));

pop_frame()
  



