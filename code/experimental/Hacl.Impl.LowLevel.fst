module Hacl.Impl.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Mul

open Hacl.Spec.P384.Definition
open Lib.IntTypes.Intrinsics


#set-options " --z3rlimit 100 --ifuel  0 --fuel 0"
inline_for_extraction noextract
val add6_0: x: felem6_buffer -> y: felem6_buffer-> result: felem6_buffer -> Stack uint64 
  (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result)
  (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ 
    v c <= 1 /\
    (
      let r0 = Lib.Sequence.index (as_seq h1 result) 0 in 
      let r1 = Lib.Sequence.index (as_seq h1 result) 1 in 
      let r2 = Lib.Sequence.index (as_seq h1 result) 2 in 
  
      let a0 = Lib.Sequence.index (as_seq h0 x) 0 in 
      let a1 = Lib.Sequence.index (as_seq h0 x) 1 in 
      let a2 = Lib.Sequence.index (as_seq h0 x) 2 in 

      let b0 = Lib.Sequence.index (as_seq h0 y) 0 in 
      let b1 = Lib.Sequence.index (as_seq h0 y) 1 in 
      let b2 = Lib.Sequence.index (as_seq h0 y) 2 in 

      let r3_0 = Lib.Sequence.index (as_seq h0 result) 3 in 
      let r3_1 = Lib.Sequence.index (as_seq h1 result) 3 in 
      
      let r4_0 = Lib.Sequence.index (as_seq h0 result) 4 in 
      let r4_1 = Lib.Sequence.index (as_seq h1 result) 4 in 
      
      let r5_0 = Lib.Sequence.index (as_seq h0 result) 5 in 
      let r5_1 = Lib.Sequence.index (as_seq h1 result) 5 in 

      v r0 + v r1 * pow2 (1 * 64) + v r2 * pow2 (2 * 64) + v c * pow2 (3 * 64) ==
      v a0 + v b0 + v a1 * pow2 64 + v b1 * pow2 64 + v a2 * pow2 (2 * 64) + v b2 * pow2 (2 * 64) /\

      r3_0 == r3_1 /\ r4_0 == r4_1 /\ r5_0 == r5_1

    )
  )

let add6_0 x y result =
  let h0 = ST.get() in 
  assert_norm (pow2 64 * pow2 64 = pow2 (2 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 (3 * 64));
  let r0 = sub result (size 0) (size 1) in 
  let r1 = sub result (size 1) (size 1) in 
  let r2 = sub result (size 2) (size 1) in 

  let r3 = sub result (size 3) (size 1) in 
  let r4 = sub result (size 4) (size 1) in 
  let r5 = sub result (size 5) (size 1) in 

  assert(Lib.Sequence.index (as_seq h0 r3) 0 == Lib.Sequence.index (as_seq h0 result) 3);
  assert(Lib.Sequence.index (as_seq h0 r4) 0 == Lib.Sequence.index (as_seq h0 result) 4);
  assert(Lib.Sequence.index (as_seq h0 r5) 0 == Lib.Sequence.index (as_seq h0 result) 5);

  assert(let r4_0 = as_seq h0 r1 in let r0_ = as_seq h0 result in Seq.index r0_ 1 == Seq.index r4_0 0);
  assert(let r5_0 = as_seq h0 r2 in let r0_ = as_seq h0 result in Seq.index r0_ 2 == Seq.index r5_0 0);

  let cc0 = add_carry_u64 (u64 0) x.(0ul) y.(0ul) r0 in 
  let cc1 = add_carry_u64 cc0 x.(1ul) y.(1ul) r1 in 
  let cc2 = add_carry_u64 cc1 x.(2ul) y.(2ul) r2 in 
  
  cc2

inline_for_extraction noextract
val add6_1: x: felem6_buffer -> y: felem6_buffer -> result: felem6_buffer -> cc2: uint64 -> 
  Stack uint64 
  (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\
    eq_or_disjoint y result /\ v cc2 <= 1)
  (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ 
    uint_v c <= 1 /\
    (
      let r0_0 = Lib.Sequence.index (as_seq h0 result) 0 in 
      let r0_1 = Lib.Sequence.index (as_seq h1 result) 0 in 
      
      let r1_0 = Lib.Sequence.index (as_seq h0 result) 1 in 
      let r1_1 = Lib.Sequence.index (as_seq h1 result) 1 in 
      
      let r2_0 = Lib.Sequence.index (as_seq h0 result) 2 in 
      let r2_1 = Lib.Sequence.index (as_seq h1 result) 2 in 
	   
      let r3 = Lib.Sequence.index (as_seq h1 result) 3 in 
      let r4 = Lib.Sequence.index (as_seq h1 result) 4 in 
      let r5 = Lib.Sequence.index (as_seq h1 result) 5 in 
  
      let a3 = Lib.Sequence.index (as_seq h0 x) 3 in 
      let a4 = Lib.Sequence.index (as_seq h0 x) 4 in 
      let a5 = Lib.Sequence.index (as_seq h0 x) 5 in 

      let b3 = Lib.Sequence.index (as_seq h0 y) 3 in 
      let b4 = Lib.Sequence.index (as_seq h0 y) 4 in 
      let b5 = Lib.Sequence.index (as_seq h0 y) 5 in 
  
      v r3 * pow2 (3 * 64) + v r4 * pow2 (4 * 64) + v r5 * pow2 (5 * 64) + v c * pow2 (6 * 64) ==
      v a3 * pow2 (3 * 64) + v b3 * pow2 (3 * 64) + v a4 * pow2 (4 * 64) + v b4 * pow2 (4 * 64) + v a5 * pow2 (5 * 64) + v b5 * pow2 (5 * 64) + uint_v cc2 * pow2 (3 * 64) /\
      r0_0 == r0_1 /\ r1_0 == r1_1 /\ r2_0 == r2_1
    )
  )

let add6_1 x y result cc2 =
  let h0 = ST.get() in 
  
  assert_norm (pow2 64 * pow2 64 = pow2 (2 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 (3 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (4 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (5 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));

  let r0 = sub result (size 0) (size 1) in 
  let r1 = sub result (size 1) (size 1) in 
  let r2 = sub result (size 2) (size 1) in 

  let r3 = sub result (size 3) (size 1) in 
  let r4 = sub result (size 4) (size 1) in 
  let r5 = sub result (size 5) (size 1) in 

  let cc3 = add_carry_u64 cc2 x.(3ul) y.(3ul) r3 in 
  let cc4 = add_carry_u64 cc3 x.(4ul) y.(4ul) r4 in 
  let cc5 = add_carry_u64 cc4 x.(5ul) y.(5ul) r5 in 

  let h1 = ST.get() in 


  assert(let r3_0 = as_seq h0 r3 in let r0_ = as_seq h0 result in Seq.index r0_ 3 == Seq.index r3_0 0);   
  assert(let r4_0 = as_seq h0 r4 in let r0_ = as_seq h0 result in Seq.index r0_ 4 == Seq.index r4_0 0);
  assert(let r5_0 = as_seq h0 r5 in let r0_ = as_seq h0 result in Seq.index r0_ 5 == Seq.index r5_0 0);

  assert(Lib.Sequence.index (as_seq h0 r0) 0 == Lib.Sequence.index (as_seq h0 result) 0);
  assert(Lib.Sequence.index (as_seq h0 r1) 0 == Lib.Sequence.index (as_seq h0 result) 1);
  assert(Lib.Sequence.index (as_seq h0 r2) 0 == Lib.Sequence.index (as_seq h0 result) 2);


  cc5



val add6: x: felem6_buffer -> y: felem6_buffer -> result: felem6_buffer -> 
  Stack uint64
    (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result)
    (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ v c <= 1 /\ 
      as_nat6 h1 result + v c * pow2 (6 * 64) == as_nat6 h0 x + as_nat6 h0 y)   


let add6 x y result =    
  let cc2 = add6_0 x y result in 
  add6_1 x y result cc2
