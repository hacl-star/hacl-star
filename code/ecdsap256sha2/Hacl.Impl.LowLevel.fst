module Hacl.Impl.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.P256.Definitions
open Spec.P256.Lemmas
open Spec.ECDSA

open FStar.Math
open FStar.Math.Lemmas
open FStar.Mul

open FStar.Tactics
open FStar.Tactics.Canon 

open Spec.P256.Lemmas
open Lib.IntTypes.Intrinsics

#reset-options "--z3rlimit 400"

val eq0_u64: a: uint64 -> Tot (r: uint64 {if uint_v a = 0 then uint_v r == pow2 64 - 1 else uint_v r == 0})

let eq0_u64 a = 
  eq_mask_lemma a (u64 0);
  eq_mask a (u64 0)


val eq1_u64: a: uint64 -> Tot (r: uint64 {if uint_v a = 0 then uint_v r == 0 else uint_v r == pow2 64 - 1})

let eq1_u64 a = 
  neq_mask_lemma a (u64 0);
  neq_mask a (u64 0)


val isZero_uint64_CT:  f: felem -> Stack uint64
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ (if as_nat h0 f = 0 then uint_v r == pow2 64 - 1 else uint_v r == 0))
 
let isZero_uint64_CT f = 
  let a0 = index f (size 0) in 
  let a1 = index f (size 1) in 
  let a2 = index f (size 2) in 
  let a3 = index f (size 3) in 
  
  let r0 = eq_mask a0 (u64 0) in 
  let r1 = eq_mask a1 (u64 0) in 
  let r2 = eq_mask a2 (u64 0) in 
  let r3 = eq_mask a3 (u64 0) in 
  
  let r01 = logand r0 r1 in 
     logand_lemma r0 r1; 
  let r23 = logand r2 r3 in 
     logand_lemma r2 r3;
  let r = logand r01 r23 in 
    logand_lemma r01 r23;
  r


val compare_felem: a: felem -> b: felem -> Stack uint64
  (requires fun h -> live h a /\ live h b) 
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ (if as_nat h0 a = as_nat h0 b then uint_v r == pow2 64 - 1 else uint_v r = 0))

let compare_felem a b = 
  let a_0 = index a (size 0) in 
  let a_1 = index a (size 1) in 
  let a_2 = index a (size 2) in 
  let a_3 = index a (size 3) in 

  let b_0 = index b (size 0) in 
  let b_1 = index b (size 1) in 
  let b_2 = index b (size 2) in 
  let b_3 = index b (size 3) in 

  let r_0 = eq_mask a_0 b_0 in 
      eq_mask_lemma a_0 b_0;
  let r_1 = eq_mask a_1 b_1 in 
      eq_mask_lemma a_1 b_1;
  let r_2 = eq_mask a_2 b_2 in 
      eq_mask_lemma a_2 b_2;
  let r_3 = eq_mask a_3 b_3 in 
      eq_mask_lemma a_3 b_3;
  
  let r01 = logand r_0 r_1 in 
      logand_lemma r_0 r_1;
  let r23 = logand r_2 r_3 in 
      logand_lemma r_2 r_3;
  
  let r = logand r01 r23 in 
      logand_lemma r01 r23;
      lemma_equality (a_0, a_1, a_2, a_3) (b_0, b_1, b_2, b_3); 
  r

inline_for_extraction noextract
val load_buffer8: 
  a0: uint64 -> a1: uint64 -> 
  a2: uint64 -> a3: uint64 -> 
  a4: uint64 -> a5: uint64 -> 
  a6: uint64 -> a7: uint64 ->  
  o: lbuffer uint64 (size 8) -> 
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ wide_as_nat h1 o == wide_as_nat4 (a0, a1, a2, a3, a4, a5, a6, a7))

let load_buffer8 a0 a1 a2 a3 a4 a5 a6 a7  o = 
    let h0 = ST.get() in 
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (5 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (7 * 64));

  upd o (size 0) a0;
  upd o (size 1) a1;
  upd o (size 2) a2;
  upd o (size 3) a3;
  
  upd o (size 4) a4;
  upd o (size 5) a5;
  upd o (size 6) a6;
  upd o (size 7) a7

(** This is unused *)
inline_for_extraction noextract
val copy_conditional_u64: a: uint64 -> b: uint64 -> mask: uint64 {uint_v mask = 0 \/ uint_v mask = pow2 64 - 1} -> 
  Tot (r: uint64 {if uint_v mask = 0 then uint_v r = uint_v a else uint_v r = uint_v b})

let copy_conditional_u64 a b mask = 
  lemma_xor_copy_cond a b mask;
  logxor a (logand mask (logxor a b))

val copy_conditional: out: felem -> x: felem -> mask: uint64{uint_v mask = 0 \/ uint_v mask = pow2 64 - 1} -> Stack unit 
  (requires fun h -> live h out /\ live h x)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
    (if uint_v mask = 0 then as_seq h1 out == as_seq h0 out else as_seq h1 out == as_seq h0 x)
  ) 

let copy_conditional out x mask = 
    let h0 = ST.get() in 
  let out_0 = index out (size 0) in 
  let out_1 = index out (size 1) in 
  let out_2 = index out (size 2) in 
  let out_3 = index out (size 3) in 

  let x_0 = index x (size 0) in 
  let x_1 = index x (size 1) in 
  let x_2 = index x (size 2) in 
  let x_3 = index x (size 3) in 

  let r_0 = logxor out_0 (logand mask (logxor out_0 x_0)) in 
  let r_1 = logxor out_1 (logand mask (logxor out_1 x_1)) in 
  let r_2 = logxor out_2 (logand mask (logxor out_2 x_2)) in 
  let r_3 = logxor out_3 (logand mask (logxor out_3 x_3)) in 

  lemma_xor_copy_cond out_0 x_0 mask;
  lemma_xor_copy_cond out_1 x_1 mask;
  lemma_xor_copy_cond out_2 x_2 mask;
  lemma_xor_copy_cond out_3 x_3 mask;

  upd out (size 0) r_0;
  upd out (size 1) r_1;
  upd out (size 2) r_2;
  upd out (size 3) r_3;
    let h1 = ST.get() in 

  lemma_eq_funct_ (as_seq h1 out) (as_seq h0 out);
  lemma_eq_funct_ (as_seq h1 out) (as_seq h0 x)

(*
(* Non constant-time implementations of add_carry_u64 and sub_borrow_u64
   with the same specification as functions in Lib.IntTypes.Intrinsics *)

inline_for_extraction noextract
let eq_u64_nCT a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a =^ u64_to_UInt64 b)

inline_for_extraction noextract
val lt_u64:a:uint64 -> b:uint64 -> Tot bool
let lt_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a <^ u64_to_UInt64 b)

inline_for_extraction noextract
val le_u64:a:uint64 -> b:uint64 -> Tot bool
let le_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a <=^ u64_to_UInt64 b)

val add_carry_u64_nCT: cin:uint64 -> x:uint64 -> y:uint64 -> r:lbuffer uint64 (size 1) ->
  Stack uint64
    (requires fun h -> live h r /\ v cin <= 1)
    (ensures  fun h0 c h1 ->
      modifies1 r h0 h1 /\ v c <= 1 /\
      (let r = Seq.index (as_seq h1 r) 0 in
       v r + v c * pow2 64 == v x + v y + v cin))

let add_carry_u64_nCT cin x y result1 =
  let res1 = x +. cin in
  let mask1 = res1 `lt_mask` cin in
  lt_mask_lemma res1 cin;
  let c = copy_conditional_u64 (u64 0) (u64 1) mask1 in
  let res = res1 +. y in
  let mask2 = res `lt_mask` res1 in
  lt_mask_lemma res res1;
  result1.(0ul) <- res;
  let c1 = copy_conditional_u64 (u64 0) (u64 1) mask2 in
  c +. c1

val sub_borrow_u64_nCT: cin:uint64 -> x:uint64 -> y:uint64 -> r:lbuffer uint64 (size 1) ->
  Stack uint64
    (requires fun h -> live h r /\ v cin <= 1)
    (ensures  fun h0 c h1 ->
      modifies1 r h0 h1 /\
      (let r = Seq.index (as_seq h1 r) 0 in
       v r - v c * pow2 64 == v x - v y - v cin))

let sub_borrow_u64_nCT cin x y result1 =
  let res = x -. y -. cin in
  let c =
    if eq_u64_nCT cin (u64 1) then
      if le_u64 x y then u64 1 else u64 0
    else
      if lt_u64 x y then u64 1 else u64 0
  in
  result1.(0ul) <- res;
  c
*)

val add4: x: felem -> y: felem -> result: felem -> 
  Stack uint64
    (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result)
    (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ v c <= 1 /\ 
      as_nat h1 result + v c * pow2 256 == as_nat h0 x + as_nat h0 y)   

let add4 x y result =    
  let h0 = ST.get() in
  
  let r0 = sub result (size 0) (size 1) in 
  let r1 = sub result (size 1) (size 1) in 
  let r2 = sub result (size 2) (size 1) in 
  let r3 = sub result (size 3) (size 1) in 

    assert(let r1_0 = as_seq h0 r1 in let r0_ = as_seq h0 result in Seq.index r0_ 1 == Seq.index r1_0 0);
    assert(let r2_0 = as_seq h0 r2 in let r0_ = as_seq h0 result in Seq.index r0_ 2 == Seq.index r2_0 0);
    assert(let r3_0 = as_seq h0 r3 in let r0_ = as_seq h0 result in Seq.index r0_ 3 == Seq.index r3_0 0);   

    
  let cc0 = add_carry_u64 (u64 0) x.(0ul) y.(0ul) r0 in 
  let cc1 = add_carry_u64 cc0 x.(1ul) y.(1ul) r1 in 
  let cc2 = add_carry_u64 cc1 x.(2ul) y.(2ul) r2 in 
  let cc3 = add_carry_u64 cc2 x.(3ul) y.(3ul) r3 in 

  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);

  cc3


val add4_with_carry: c: uint64 ->  x: felem -> y: felem -> result: felem -> 
  Stack uint64
    (requires fun h -> uint_v c <= 1 /\ live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ 
      eq_or_disjoint y result)
    (ensures fun h0 carry h1 -> modifies (loc result) h0 h1 /\ uint_v carry <= 1 /\ 
      as_nat h1 result + v carry * pow2 256 == as_nat h0 x + as_nat h0 y + uint_v c)   

let add4_with_carry c x y result =    
    let h0 = ST.get() in
  
    let r0 = sub result (size 0) (size 1) in 
    let r1 = sub result (size 1) (size 1) in 
    let r2 = sub result (size 2) (size 1) in 
    let r3 = sub result (size 3) (size 1) in 
    
    let cc = add_carry_u64 c x.(0ul) y.(0ul) r0 in 
    let cc = add_carry_u64 cc x.(1ul) y.(1ul) r1 in 
    let cc = add_carry_u64 cc x.(2ul) y.(2ul) r2 in 
    let cc = add_carry_u64 cc x.(3ul) y.(3ul) r3 in   
    
      assert(let r1_0 = as_seq h0 r1 in let r0_ = as_seq h0 result in Seq.index r0_ 1 == Seq.index r1_0 0);
      assert(let r2_0 = as_seq h0 r2 in let r0_ = as_seq h0 result in Seq.index r0_ 2 == Seq.index r2_0 0);
      assert(let r3_0 = as_seq h0 r3 in let r0_ = as_seq h0 result in Seq.index r0_ 3 == Seq.index r3_0 0);

      assert_norm (pow2 64 * pow2 64 = pow2 128);
      assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
      assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    
    cc


#reset-options "--z3rlimit 1000"
val add8: x: widefelem -> y: widefelem -> result: widefelem -> Stack uint64 
  (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result)
  (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ v c <= 1 /\ 
    wide_as_nat h1 result + v c * pow2 512 == wide_as_nat h0 x + wide_as_nat h0 y)

let add8 x y result = 
  let h0 = ST.get() in 
    let a0 = sub x (size 0) (size 4) in 
    let a1 = sub x (size 4) (size 4) in 
    let b0 = sub y (size 0) (size 4) in 
    let b1 = sub y (size 4) (size 4) in 

    let c0 = sub result (size 0) (size 4) in 
    let c1 = sub result (size 4) (size 4) in 

    let carry0 = add4 a0 b0 c0 in
      let h1 = ST.get() in 
    let carry1 = add4_with_carry carry0 a1 b1 c1 in 
      let h2 = ST.get() in 	
      assert(as_nat h2 c1 =  - uint_v carry1 * pow2 256 + as_nat h1 a1 + as_nat h1 b1 + uint_v carry0);
      assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
      assert_norm (pow2 256 * pow2 256 = pow2 512);
  
      assert(Lib.Sequence.index (as_seq h2 result) 4 == Lib.Sequence.index (as_seq h2 c1) 0);
      assert(Lib.Sequence.index (as_seq h2 result) 5 == Lib.Sequence.index (as_seq h2 c1) 1);
      assert(Lib.Sequence.index (as_seq h2 result) 6 == Lib.Sequence.index (as_seq h2 c1) 2);
      assert(Lib.Sequence.index (as_seq h2 result) 7 == Lib.Sequence.index (as_seq h2 c1) 3);

      assert_by_tactic (as_nat h2 c1 * pow2 64 * pow2 64 * pow2 64 * pow2 64 == as_nat h2 c1 * pow2 256) canon;
      assert_by_tactic (as_nat h2 a1 * pow2 64 * pow2 64 * pow2 64 * pow2 64 == as_nat h2 a1 * pow2 256) canon;
  
      assert_by_tactic ((- uint_v carry1 * pow2 256 + as_nat h1 a1 + as_nat h1 b1 + uint_v carry0) * pow2 256 == - uint_v carry1 * pow2 256 * pow2 256 + as_nat h1 a1 * pow2 256 + as_nat h1 b1 * pow2 256 + uint_v carry0 * pow2 256) canon;

      lemma_ll0 (uint_v (Lib.Sequence.index (as_seq h0 a1) 0)) (uint_v (Lib.Sequence.index (as_seq h0 a1) 1)) (uint_v (Lib.Sequence.index (as_seq h0 a1) 2)) (uint_v (Lib.Sequence.index (as_seq h0 a1) 3));
      lemma_ll0 (uint_v (Lib.Sequence.index (as_seq h0 b1) 0)) (uint_v (Lib.Sequence.index (as_seq h0 b1) 1)) (uint_v (Lib.Sequence.index (as_seq h0 b1) 2)) (uint_v (Lib.Sequence.index (as_seq h0 b1) 3));

    carry1


val add4_variables: x: felem -> cin: uint64 {uint_v cin <=1} ->  y0: uint64 -> y1: uint64 -> y2: uint64 -> y3: uint64 -> 
  result: felem -> 
  Stack uint64
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
    (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ v c <= 1 /\  
      as_nat h1 result  + uint_v c * pow2 256 == as_nat h0 x + uint_v y0 + uint_v y1 * pow2 64 + uint_v y2 * pow2 128 + uint_v y3 * pow2 192 + uint_v cin)   

let add4_variables x cin y0 y1 y2 y3 result = 
    let h0 = ST.get() in 
    
    let r0 = sub result (size 0) (size 1) in      
    let r1 = sub result (size 1) (size 1) in 
    let r2 = sub result (size 2) (size 1) in 
    let r3 = sub result (size 3) (size 1) in 

    let cc = add_carry_u64 cin x.(0ul) y0 r0 in 
    let cc = add_carry_u64 cc x.(1ul) y1 r1 in 
    let cc = add_carry_u64 cc x.(2ul) y2 r2 in 
    let cc = add_carry_u64 cc x.(3ul) y3 r3 in 
      

  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    
    assert(let r1_0 = as_seq h0 r1 in let r0_ = as_seq h0 result in Seq.index r0_ 1 == Seq.index r1_0 0);
    assert(let r2_0 = as_seq h0 r2 in let r0_ = as_seq h0 result in Seq.index r0_ 2 == Seq.index r2_0 0);
    assert(let r3_0 = as_seq h0 r3 in let r0_ = as_seq h0 result in Seq.index r0_ 3 == Seq.index r3_0 0);
    cc

val sub4_il: x: felem -> y: ilbuffer uint64 (size 4) -> result: felem -> 
  Stack uint64
    (requires fun h -> live h x /\ live h y /\ live h result /\ disjoint x result /\ disjoint y result)
    (ensures fun h0 c h1 -> modifies1 result h0 h1 /\ v c <= 1 /\
      (
 	as_nat h1 result - v c * pow2 256 == as_nat h0 x  - as_nat_il h0 y /\
	(if uint_v c = 0 then as_nat h0 x >= as_nat_il h0 y else as_nat h0 x < as_nat_il h0 y)
      )
   )

let sub4_il x y result = 
    let r0 = sub result (size 0) (size 1) in 
    let r1 = sub result (size 1) (size 1) in 
    let r2 = sub result (size 2) (size 1) in 
    let r3 = sub result (size 3) (size 1) in 

    let cc = sub_borrow_u64 (u64 0) x.(size 0) y.(size 0) r0 in 
    let cc = sub_borrow_u64 cc x.(size 1) y.(size 1) r1 in 
    let cc = sub_borrow_u64 cc x.(size 2) y.(size 2) r2 in 
    let cc = sub_borrow_u64 cc x.(size 3) y.(size 3) r3 in 

      assert_norm (pow2 64 * pow2 64 = pow2 128);
      assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
      assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    
    cc


val sub4: x: felem -> y:felem -> result: felem -> 
  Stack uint64
    (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result)
    (ensures fun h0 c h1 -> modifies1 result h0 h1 /\ v c <= 1 /\ as_nat h1 result - v c * pow2 256 == as_nat h0 x - as_nat h0 y)

let sub4 x y result = 
  let h0 = ST.get() in 
	
  let r0 = sub result (size 0) (size 1) in 
  let r1 = sub result (size 1) (size 1) in 
  let r2 = sub result (size 2) (size 1) in 
  let r3 = sub result (size 3) (size 1) in 
      
  let cc = sub_borrow_u64 (u64 0) x.(size 0) y.(size 0) r0 in 
  let cc = sub_borrow_u64 cc x.(size 1) y.(size 1) r1 in 
  let cc = sub_borrow_u64 cc x.(size 2) y.(size 2) r2 in 
  let cc = sub_borrow_u64 cc x.(size 3) y.(size 3) r3 in 
    
    assert(let r1_0 = as_seq h0 r1 in let r0_ = as_seq h0 result in Seq.index r0_ 1 == Seq.index r1_0 0);
    assert(let r2_0 = as_seq h0 r2 in let r0_ = as_seq h0 result in Seq.index r0_ 2 == Seq.index r2_0 0);
    assert(let r3_0 = as_seq h0 r3 in let r0_ = as_seq h0 result in Seq.index r0_ 3 == Seq.index r3_0 0);

    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    
  cc


val mul64: x: uint64 -> y: uint64 -> result: lbuffer uint64 (size 1) -> temp: lbuffer uint64 (size 1) ->
  Stack unit
    (requires fun h -> live h result /\ live h temp /\ disjoint result temp)
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc temp) h0 h1 /\ 
    (
      let h0 = Seq.index (as_seq h1 temp) 0 in 
      let result = Seq.index (as_seq h1 result) 0 in 
      uint_v result + uint_v h0 * pow2 64 = uint_v x * uint_v y     
      )
    )

let mul64 x y result temp = 
  let res = mul64_wide x y in 
  let l0, h0 = to_u64 res, to_u64 (res >>. 64ul) in 
  upd result (size 0) l0;
  upd temp (size 0) h0


val mult64_0: x: felem -> u: uint64 -> result: lbuffer uint64 (size 1) -> temp: lbuffer uint64 (size 1) -> Stack unit 
  (requires fun h -> live h x /\ live h result /\ live h temp /\ disjoint result temp)
  (ensures fun h0 _ h1 -> 
    let result_ = Seq.index (as_seq h1 result) 0 in 
    let c = Seq.index (as_seq h1 temp) 0 in 
    let f0 = Seq.index (as_seq h0 x) 0 in 
    uint_v result_ + uint_v c * pow2 64 = uint_v f0 * uint_v u /\ modifies (loc result |+| loc temp) h0 h1)

let mult64_0 x u result temp = 
  let f0 = index x (size 0) in 
  mul64 f0 u result temp


val mult64_0il: x: ilbuffer uint64 (size 4) -> u: uint64 -> result:  lbuffer uint64 (size 1) -> temp: lbuffer uint64 (size 1) -> Stack unit 
  (requires fun h -> live h x /\ live h result /\ live h temp /\ disjoint result temp)
  (ensures fun h0 _ h1 -> 
    let result_ = Seq.index (as_seq h1 result) 0 in 
    let c = Seq.index (as_seq h1 temp) 0 in 
    let f0 = Seq.index (as_seq h0 x) 0 in 
    uint_v result_ + uint_v c * pow2 64 = uint_v f0 * uint_v u /\ modifies (loc result |+| loc temp) h0 h1)

let mult64_0il x u result temp = 
  let f0 = index x (size 0) in 
  mul64 f0 u result temp


val mult64_c: x: uint64 -> u: uint64 -> cin: uint64{uint_v cin <= 1} -> result: lbuffer uint64 (size 1) -> temp: lbuffer uint64 (size 1) -> Stack uint64 
  (requires fun h -> live h result /\ live h temp /\ disjoint result temp)
  (ensures fun h0 c2 h1 -> modifies (loc result |+| loc temp) h0 h1 /\ uint_v c2 <= 1 /\
    (
      let r = Seq.index (as_seq h1 result) 0 in 
      let h1 = Seq.index (as_seq h1 temp) 0 in 
      let h0 = Seq.index (as_seq h0 temp) 0 in 
      uint_v r + uint_v c2 * pow2 64 == uint_v x * uint_v u - uint_v h1 * pow2 64 + uint_v h0 + uint_v cin)
)

let mult64_c x u cin result temp = 
  let h = index temp (size 0) in 
  mul64 x u result temp;
  let l = index result (size 0) in     
  add_carry_u64 cin l h result


val mul1_il: f:  ilbuffer uint64 (size 4) -> u: uint64 -> result: lbuffer uint64 (size 4) -> Stack uint64
  (requires fun h -> live h result /\ live h f)
  (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ 
    as_nat_il h0 f * uint_v u = uint_v c * pow2 256 + as_nat h1 result /\ 
    as_nat_il h0 f * uint_v u < pow2 320 /\
    uint_v c < pow2 64 - 1 
  )


let mul1_il f u result = 
  push_frame();

    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);  
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 320); 

  let temp = create (size 1) (u64 0) in 

  let f0 = index f (size 0) in 
  let f1 = index f (size 1) in 
  let f2 = index f (size 2) in 
  let f3 = index f (size 3) in 
    
  let o0 = sub result (size 0) (size 1) in 
  let o1 = sub result (size 1) (size 1) in 
  let o2 = sub result (size 2) (size 1) in 
  let o3 = sub result (size 3) (size 1) in 
    
    let h0 = ST.get() in 
  mult64_0il f u o0 temp;
    let h1 = ST.get() in 
  let c1 = mult64_c f1 u (u64 0) o1 temp in 
    let h2 = ST.get() in 
  let c2 = mult64_c f2 u c1 o2 temp in 
    let h3 = ST.get() in 
  let c3 = mult64_c f3 u c2 o3 temp in 
    let h4 = ST.get() in 
  let temp0 = index temp (size 0) in 
    lemma_low_level0 (uint_v(Seq.index (as_seq h1 o0) 0)) (uint_v (Seq.index (as_seq h2 o1) 0)) (uint_v (Seq.index (as_seq h3 o2) 0)) (uint_v (Seq.index (as_seq h4 o3) 0)) (uint_v f0) (uint_v f1) (uint_v f2) (uint_v f3) (uint_v u) (uint_v (Seq.index (as_seq h2 temp) 0)) (uint_v c1) (uint_v c2) (uint_v c3) (uint_v (Seq.index (as_seq h3 temp) 0)) (uint_v temp0); 
    
  mul_lemma_4 (as_nat_il h0 f) (uint_v u) (pow2 256 - 1) (pow2 64 - 1);
  assert_norm((pow2 256 - 1) * (pow2 64 - 1) == pow2 320 - pow2 256 - pow2 64 + 1);
  assert_norm((pow2 320 - pow2 256) / pow2 256 == pow2 64 - 1);

  pop_frame();  
  c3 +! temp0


val mul1: f:  lbuffer uint64 (size 4) -> u: uint64 -> result: lbuffer uint64 (size 4) -> Stack uint64
  (requires fun h -> live h result /\ live h f)
  (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ 
    as_nat h0 f * uint_v u = uint_v c * pow2 256 + as_nat h1 result /\ 
    as_nat h0 f * uint_v u < pow2 320 /\
    uint_v c < pow2 64 - 1
  )


let mul1 f u result = 
  push_frame();

    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);  
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 320); 

  let temp = create (size 1) (u64 0) in 

  let f0 = index f (size 0) in 
  let f1 = index f (size 1) in 
  let f2 = index f (size 2) in 
  let f3 = index f (size 3) in 
    
  let o0 = sub result (size 0) (size 1) in 
  let o1 = sub result (size 1) (size 1) in 
  let o2 = sub result (size 2) (size 1) in 
  let o3 = sub result (size 3) (size 1) in 
    
    let h0 = ST.get() in 
  mult64_0 f u o0 temp;
    let h1 = ST.get() in 
  let c1 = mult64_c f1 u (u64 0) o1 temp in 
    let h2 = ST.get() in 
  let c2 = mult64_c f2 u c1 o2 temp in 
    let h3 = ST.get() in 
  let c3 = mult64_c f3 u c2 o3 temp in 
    let h4 = ST.get() in 
  let temp0 = index temp (size 0) in 
    lemma_low_level0 (uint_v(Seq.index (as_seq h1 o0) 0)) (uint_v (Seq.index (as_seq h2 o1) 0)) (uint_v (Seq.index (as_seq h3 o2) 0)) (uint_v (Seq.index (as_seq h4 o3) 0)) (uint_v f0) (uint_v f1) (uint_v f2) (uint_v f3) (uint_v u) (uint_v (Seq.index (as_seq h2 temp) 0)) (uint_v c1) (uint_v c2) (uint_v c3) (uint_v (Seq.index (as_seq h3 temp) 0)) (uint_v temp0); 
    
  mul_lemma_4 (as_nat h0 f) (uint_v u) (pow2 256 - 1) (pow2 64 - 1);
  assert_norm((pow2 256 - 1) * (pow2 64 - 1) == pow2 320 - pow2 256 - pow2 64 + 1);
  assert_norm((pow2 320 - pow2 256) / pow2 256 == pow2 64 - 1);

  pop_frame();  
  c3 +! temp0


val mul1_add: f1: felem -> u2: uint64 -> f3: felem -> result: felem -> 
  Stack uint64 
  (requires fun h -> live h f1 /\ live h f3 /\ live h result /\ eq_or_disjoint f3 result /\ disjoint f1 result)
  (ensures fun h0 c h1 -> modifies (loc result) h0 h1  /\
    as_nat h1 result + uint_v c * pow2 256 == as_nat h0 f1 * uint_v u2 + as_nat h0 f3 )

let mul1_add f1 u2 f3 result = 
  push_frame();
    let temp = create (size 4) (u64 0) in 
  let c = mul1 f1 u2 temp in 
  let c3 = add4 temp f3 result in 
  pop_frame();  
  c +! c3

#reset-options "--z3rlimit 1000"
val mul: f: felem -> r: felem -> out: widefelem
  -> Stack unit
    (requires fun h -> live h out /\ live h f /\ live h r)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\ wide_as_nat h1 out = as_nat h0 r * as_nat h0 f)
      
let mul f r out =
  push_frame();
    let temp = create (size 8) (u64 0) in 
    
  let f0 = f.(0ul) in
  let f1 = f.(1ul) in
  let f2 = f.(2ul) in
  let f3 = f.(3ul) in

    let h0 = ST.get() in 
  let b0 = sub temp (size 0) (size 4) in 
  let c0 = mul1 r f0 b0 in 
    upd temp (size 4) c0;

    let h1 = ST.get() in 
    let bk0 = sub temp (size 0) (size 1) in 
  let b1 = sub temp (size 1) (size 4) in   
  let c1 = mul1_add r f1 b1 b1 in 
      upd temp (size 5) c1; 
    let h2 = ST.get() in
      assert(Lib.Sequence.index (as_seq h1 bk0) 0 == Lib.Sequence.index (as_seq h1 temp) 0);

      let bk1 = sub temp (size 0) (size 2) in 
  let b2 = sub temp (size 2) (size 4) in 
  let c2 = mul1_add r f2 b2 b2 in 
    upd temp (size 6) c2;
    
    let h3 = ST.get() in 

    assert(Lib.Sequence.index (as_seq h2 bk1) 0 == Lib.Sequence.index (as_seq h2 temp) 0);
    assert(Lib.Sequence.index (as_seq h2 bk1) 1 == Lib.Sequence.index (as_seq h2 temp) 1);
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);

     let bk2 = sub temp (size 0) (size 3) in 
  let b3 = sub temp (size 3) (size 4) in 
  let c3 = mul1_add r f3 b3 b3 in 
    upd temp (size 7) c3;

    assert(Lib.Sequence.index (as_seq h3 bk2) 0 == Lib.Sequence.index (as_seq h3 temp) 0);
    assert(Lib.Sequence.index (as_seq h3 bk2) 1 == Lib.Sequence.index (as_seq h3 temp) 1);
    assert(Lib.Sequence.index (as_seq h3 bk2) 2 == Lib.Sequence.index (as_seq h3 temp) 2);

  assert_by_tactic (as_nat h0 r * (uint_v f2 * pow2 64 * pow2 64) == as_nat h0 r * uint_v f2 * pow2 64 * pow2 64) canon;
  assert_by_tactic (as_nat h0 r * (uint_v f0) == as_nat h0 r * uint_v f0) canon;
  assert_by_tactic (as_nat h0 r * (uint_v f1 * pow2 64) == as_nat h0 r * uint_v f1 * pow2 64) canon;
  assert_by_tactic (as_nat h0 r * (uint_v f3 * pow2 64 * pow2 64 * pow2 64) == as_nat h0 r * uint_v f3 * pow2 64 * pow2 64 * pow2 64) canon;

  dist_lemma_0 (as_nat h0 r) (uint_v f2 * pow2 64 * pow2 64) (uint_v f1 * pow2 64) (uint_v f0) (uint_v f3 * pow2 64 * pow2 64 * pow2 64);

  copy out temp; 
  
  pop_frame()


val lemma_320: a: uint64 -> b: uint64 -> c: uint64 -> d: uint64 -> u: uint64 -> Lemma 
  (uint_v u * uint_v a +  (uint_v u * uint_v b) * pow2 64 + (uint_v u * uint_v c) * pow2 64 * pow2 64 + (uint_v u * uint_v d) * pow2 64 * pow2 64 * pow2 64 < pow2 320)
  
let lemma_320 a b c d u = 
  assert(uint_v u <= pow2 64 - 1);
  assert(uint_v d <= pow2 64 - 1);
  assert(uint_v u * uint_v d <= (pow2 64 - 1) * (pow2 64 - 1));

  assert_norm((pow2 64 - 1) * (pow2 64 - 1) +  
    ((pow2 64 - 1) * (pow2 64 - 1)) * pow2 64 + 
    ((pow2 64 - 1) * (pow2 64 - 1)) * pow2 64 * pow2 64 + 
    ((pow2 64 - 1) * (pow2 64 - 1)) * pow2 64 * pow2 64 * pow2 64 < pow2 320)


val lemma_320_64:a: uint64 -> b: uint64 -> c: uint64 -> d: uint64 -> e: uint64 -> u: uint64 -> Lemma 
  (uint_v u * uint_v a +  (uint_v u * uint_v b) * pow2 64 + (uint_v u * uint_v c) * pow2 64 * pow2 64 + (uint_v u * uint_v d) * pow2 64 * pow2 64 * pow2 64 + uint_v e  < pow2 320)
  
let lemma_320_64 a b c d e u = 
  assert(uint_v u <= pow2 64 - 1);
  assert(uint_v a <= pow2 64 - 1);
  assert(uint_v b <= pow2 64 - 1);
  assert(uint_v c <= pow2 64 - 1);
  assert(uint_v d <= pow2 64 - 1);
  assert(uint_v e <= pow2 64 - 1);

  assert(uint_v u *  uint_v a <= (pow2 64 - 1) * (pow2 64 - 1));
  assert(uint_v u * uint_v b <= (pow2 64 - 1) * (pow2 64 - 1));
  assert(uint_v u * uint_v c <= (pow2 64 - 1) * (pow2 64 - 1));
  assert(uint_v u * uint_v d <= (pow2 64 - 1) * (pow2 64 - 1));
  

  assert(
    (uint_v u * uint_v a) +  
    (uint_v u * uint_v b) * pow2 64 + 
    (uint_v u * uint_v c) * pow2 64 * pow2 64 + 
    (uint_v u * uint_v d) * pow2 64 * pow2 64 * pow2 64 + uint_v e <= (
  (pow2 64 - 1) * (pow2 64 - 1) + 
  (pow2 64 - 1) * (pow2 64 - 1) * pow2 64 +
  (pow2 64 - 1) * (pow2 64 - 1) * pow2 64 * pow2 64 + 
  (pow2 64 - 1) * (pow2 64 - 1) * pow2 64 * pow2 64 * pow2 64 + (pow2 64 - 1)));

  assert_norm((pow2 64 - 1) * (pow2 64 - 1) +  
    ((pow2 64 - 1) * (pow2 64 - 1)) * pow2 64 + 
    ((pow2 64 - 1) * (pow2 64 - 1)) * pow2 64 * pow2 64 + 
    ((pow2 64 - 1) * (pow2 64 - 1)) * pow2 64 * pow2 64 * pow2 64 + (pow2 64 - 1) < pow2 320)



val sq0: f:  lbuffer uint64 (size 4) -> result: lbuffer uint64 (size 4) -> memory: lbuffer uint64 (size 12) -> temp: lbuffer uint64 (size 5) -> Stack uint64
  (requires fun h -> live h result /\ live h f /\ live h memory /\ live h temp /\ disjoint result temp
    /\ disjoint result memory /\ disjoint memory temp 
 )
  (ensures fun h0 c h1 -> modifies (loc result |+| loc memory |+| loc temp) h0 h1 /\ 
    (
      let f0 = Lib.Sequence.index (as_seq h0 f) 0 in 
      as_nat h1 result + uint_v c * pow2 64 * pow2 64 * pow2 64 * pow2 64  = uint_v f0 * as_nat h0 f

    ) /\


    (

      let f = as_seq h0 f in 
      let f0 = Lib.Sequence.index f 0 in 
      let f1 = Lib.Sequence.index f 1 in 
      let f2 = Lib.Sequence.index f 2 in 
      let f3 = Lib.Sequence.index f 3 in 
    
      let memory = as_seq h1 memory in 
      let m0 = Lib.Sequence.index memory 0 in 
      let m1 = Lib.Sequence.index memory 1 in 
      let m2 = Lib.Sequence.index memory 2 in 
      let m3 = Lib.Sequence.index memory 3 in 
      let m4 = Lib.Sequence.index memory 4 in 
      let m5 = Lib.Sequence.index memory 5 in 

      uint_v m0 + uint_v m1 * pow2 64 == uint_v f0 * uint_v f1 /\
      uint_v m2 + uint_v m3 * pow2 64 == uint_v f0 * uint_v f2 /\
      uint_v m4 + uint_v m5 * pow2 64 == uint_v f0 * uint_v f3
    )
 )


let sq0 f result memory temp = 
  let h0 = ST.get() in 
  
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);  
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 320); 

  let f0 = index f (size 0) in 
  let f1 = index f (size 1) in 
  let f2 = index f (size 2) in 
  let f3 = index f (size 3) in 
    
  let o0 = sub result (size 0) (size 1) in 
  let o1 = sub result (size 1) (size 1) in 
  let o2 = sub result (size 2) (size 1) in 
  let o3 = sub result (size 3) (size 1) in 

  let temp = sub temp (size 0) (size 1) in 

  mul64 f0 f0 o0 temp;
 
  let h_0 = index temp (size 0) in 
  mul64 f0 f1 o1 temp;
  let l = index o1 (size 0) in   
  upd memory (size 0) l;
  upd memory (size 1) (index temp (size 0));  
    
  let c1 = add_carry_u64 (u64 0) l h_0 o1 in 
  let h_1 = index temp (size 0) in 
  

  mul64 f0 f2 o2 temp; 
  let l = index o2 (size 0) in   
  upd memory (size 2) l;
  upd memory (size 3) (index temp (size 0));

  let c2 = add_carry_u64 c1 l h_1 o2 in
  let h_2 = index temp (size 0) in 

  mul64 f0 f3 o3 temp;
  let l = index o3 (size 0) in     
  upd memory (size 4) l;
  upd memory (size 5) (index temp (size 0));
  let c3 = add_carry_u64 c2 l h_2 o3 in
  
  let h5 = ST.get() in 
  let temp0 = index temp (size 0) in
  let r = c3 +! temp0 in 

  assert(uint_v (Lib.Sequence.index (as_seq h5 o0) 0) + uint_v h_0 * pow2 64 = uint_v f0 * uint_v f0);
  assert(uint_v (Lib.Sequence.index (as_seq h5 o1) 0) + uint_v c1 * pow2 64 + uint_v h_1 * pow2 64 - uint_v h_0 = uint_v f0 * uint_v f1);
  assert(uint_v (Lib.Sequence.index (as_seq h5 o2) 0) + uint_v c2 * pow2 64 - uint_v h_1 - uint_v c1 + uint_v h_2 * pow2 64 = uint_v f0 * uint_v f2);
  assert(uint_v (Lib.Sequence.index (as_seq h5 o3) 0) + uint_v c3 * pow2 64 - uint_v c2 - uint_v h_2 + uint_v temp0 * pow2 64 = uint_v f0 * uint_v f3);

  lemma_320 f0 f0 f1 f2 f3;


  calc (==) {
    uint_v f0 * as_nat h0 f;
    (==)
      {
	  assert(as_nat h0 f ==  uint_v f0 +  uint_v f1 * pow2 64 + uint_v f2 * pow2 64 * pow2 64 + 
	  uint_v f3 * pow2 64 * pow2 64 * pow2 64)
      }
    uint_v f0 * (uint_v f0 +  uint_v f1 * pow2 64 + uint_v f2 * pow2 64 * pow2 64 + uint_v f3 * pow2 64 * pow2 64 * pow2 64);
      (==)
      {
	assert_by_tactic (uint_v f0 * (uint_v f0 +  uint_v f1 * pow2 64 + uint_v f2 * pow2 64 * pow2 64 + uint_v f3 * pow2 64 * pow2 64 * pow2 64) == uint_v f0 * uint_v f0 +  uint_v f0 * uint_v f1 * pow2 64 + uint_v f0 * uint_v f2 * pow2 64 * pow2 64 + uint_v f0 * uint_v f3 * pow2 64 * pow2 64 * pow2 64) canon}
    
    uint_v f0 * uint_v f0 +  uint_v f0 * uint_v f1 * pow2 64 + uint_v f0 * uint_v f2 * pow2 64 * pow2 64 + uint_v f0 * uint_v f3 * pow2 64 * pow2 64 * pow2 64;};

    assert(
      uint_v (Lib.Sequence.index (as_seq h5 o0) 0) +
      uint_v (Lib.Sequence.index (as_seq h5 o1) 0) * pow2 64 +             
      uint_v (Lib.Sequence.index (as_seq h5 o2) 0) * pow2 64 * pow2 64 + 
      uint_v (Lib.Sequence.index (as_seq h5 o3) 0) * pow2 64 * pow2 64 * pow2 64 + 
      uint_v r * pow2 64 * pow2 64 * pow2 64 * pow2 64  =

      uint_v f0 * uint_v f0 +  
      uint_v f0 * uint_v f1 * pow2 64 + 
      uint_v f0 * uint_v f2 * pow2 64 * pow2 64 + 
      uint_v f0 * uint_v f3 * pow2 64 * pow2 64 * pow2 64);

  r

val sq1: f: felem -> f4: felem -> result: felem -> memory: lbuffer uint64 (size 12) -> 
  temp: lbuffer uint64 (size 5) -> 
  Stack uint64 
  (requires fun h -> live h f /\ live h f4 /\ live h result /\ live h temp /\ eq_or_disjoint f4 result /\ disjoint f4 memory /\ disjoint f4 temp /\ disjoint f result /\ live h memory /\ disjoint temp result /\ disjoint memory temp /\ disjoint memory result /\
  (
    let f = as_seq h f in 
    let f0 = Lib.Sequence.index f 0 in 
    let f1 = Lib.Sequence.index f 1 in 
    let f2 = Lib.Sequence.index f 2 in 
    let f3 = Lib.Sequence.index f 3 in 
    
    let memory = as_seq h memory in 
    let m0 = Lib.Sequence.index memory 0 in 
    let m1 = Lib.Sequence.index memory 1 in 
    let m2 = Lib.Sequence.index memory 2 in 
    let m3 = Lib.Sequence.index memory 3 in 
    let m4 = Lib.Sequence.index memory 4 in 
    let m5 = Lib.Sequence.index memory 5 in 

    uint_v m0 + uint_v m1 * pow2 64 == uint_v f0 * uint_v f1 /\
    uint_v m2 + uint_v m3 * pow2 64 == uint_v f0 * uint_v f2 /\
    uint_v m4 + uint_v m5 * pow2 64 == uint_v f0 * uint_v f3
    ) 
  )
  (ensures fun h0 c h1 -> modifies (loc result |+| loc memory |+| loc temp) h0 h1 /\
  (

      let f0 = Lib.Sequence.index (as_seq h0 f) 0 in 
      let f1 = Lib.Sequence.index (as_seq h0 f) 1  in 
      let f2 = Lib.Sequence.index (as_seq h0 f) 2 in 
      let f3 = Lib.Sequence.index (as_seq h0 f) 3 in 
    
      let memory = as_seq h1 memory in 
      let m0 = Lib.Sequence.index memory 0 in 
      let m1 = Lib.Sequence.index memory 1 in 
      let m2 = Lib.Sequence.index memory 2 in 
      let m3 = Lib.Sequence.index memory 3 in 
      let m4 = Lib.Sequence.index memory 4 in 
      let m5 = Lib.Sequence.index memory 5 in 
      let m6 = Lib.Sequence.index memory 6 in 
      let m7 = Lib.Sequence.index memory 7 in 
      let m8 = Lib.Sequence.index memory 8 in 
      let m9 = Lib.Sequence.index memory 9 in 

      uint_v m0 + uint_v m1 * pow2 64 == uint_v f0 * uint_v f1 /\
      uint_v m2 + uint_v m3 * pow2 64 == uint_v f0 * uint_v f2 /\
      uint_v m4 + uint_v m5 * pow2 64 == uint_v f0 * uint_v f3 /\
      
      uint_v m6 + uint_v m7 * pow2 64 == uint_v f1 * uint_v f2 /\
      uint_v m8 + uint_v m9 * pow2 64 == uint_v f1 * uint_v f3 /\

      as_nat h1 result + uint_v c * pow2 256 = uint_v f1 * as_nat h0 f + as_nat h0 f4
    ) 
  )

val lemma_320_1: a: nat -> b: nat -> c: nat {c < pow2 64} -> d: nat {d < pow2 256} -> e: nat {e < pow2 256 /\ a + b * pow2 256 = c * d + e}  -> Lemma (b < pow2 64)

let lemma_320_1 a b c d e = 
  assert_norm ((pow2 64 - 1) * (pow2 256 - 1) + pow2 256 < pow2 320);
  assert(c <= pow2 64 - 1);
  assert(d <= pow2 256 - 1);
  assert(c * d <= (pow2 64 - 1) * (pow2 256 - 1));
  assert(c * d + e < pow2 320);
  assert(b * pow2 256 < pow2 320);
  lemma_div_lt_nat (b * pow2 256) 320 256;
  assert(((b * pow2 256) / pow2 256) < pow2 64);
  pow2_multiplication_division_lemma_1 b 256 256;
  assert((b * pow2 256) / pow2 256 = b);
  assert(b < pow2 64)


let sq1 f f4 result memory tempBuffer = 
  let h0 = ST.get() in 
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  
  let temp = sub tempBuffer (size 0) (size 1) in 
  let tempBufferResult = sub tempBuffer  (size 1) (size 4) in 

  let f0 = index f (size 0) in 
  let f1 = index f (size 1) in 
  let f2 = index f (size 2) in 
  let f3 = index f (size 3) in 
    
  let o0 = sub tempBufferResult (size 0) (size 1) in 
  let o1 = sub tempBufferResult (size 1) (size 1) in 
  let o2 = sub tempBufferResult (size 2) (size 1) in 
  let o3 = sub tempBufferResult (size 3) (size 1) in 

  upd o0 (size 0) (index memory (size 0));
  let h_0 = index memory (size 1) in 
  mul64 f1 f1 o1 temp;
  let l = index o1 (size 0) in     
  let c1 = add_carry_u64 (u64 0) l h_0 o1 in 
  let h_1 = index temp (size 0) in 

  mul64 f1 f2 o2 temp;
  let l = index o2 (size 0) in  
  upd memory (size 6) l;
  upd memory (size 7) (index temp (size 0));
  let c2 = add_carry_u64 c1 l h_1 o2 in
  let h_2 = index temp (size 0) in   


  mul64 f1 f3 o3 temp;
  let l = index o3 (size 0) in  
  upd memory (size 8) l;
  upd memory (size 9) (index temp (size 0));
  let c3 = add_carry_u64 c2 l h_2 o3 in
  let h_3 = index temp (size 0) in 

    let h6 = ST.get() in 
    
  calc (==) {
    uint_v f1 * as_nat h0 f;
    (==) { }
    uint_v f1 * (uint_v f0 +  uint_v f1 * pow2 64 + uint_v f2 * pow2 64 * pow2 64 + uint_v f3 * pow2 64 * pow2 64 * pow2 64);
    (==)

    {
      assert_by_tactic (uint_v f1 * (uint_v f0 +  uint_v f1 * pow2 64 + uint_v f2 * pow2 64 * pow2 64 + uint_v f3 * pow2 64 * pow2 64 * pow2 64) == 
	uint_v f0 * uint_v f1 +  
	uint_v f1 * uint_v f1 * pow2 64 + 
	uint_v f2 * uint_v f1 * pow2 64 * pow2 64 + 
	uint_v f3 * uint_v f1 * pow2 64 * pow2 64 * pow2 64) canon}
   as_nat h6 tempBufferResult + (uint_v c3 + uint_v h_3) * (pow2 64 * pow2 64 * pow2 64 * pow2 64);
   (==)
   {
     assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256)
   }

   as_nat h6 tempBufferResult + (uint_v c3 + uint_v h_3) * pow2 256;
   };


  let c4 = add4 tempBufferResult f4 result in   
  let h7 = ST.get() in 

  assert_by_tactic (uint_v c4 * pow2 256 + (uint_v c3 + uint_v h_3) * pow2 256 = 
    (uint_v c4 + uint_v c3 + uint_v h_3) * pow2 256) canon;

  lemma_320_1 (as_nat h7 result) (uint_v c4 + uint_v c3 + uint_v h_3) (uint_v f1) (as_nat h0 f) (as_nat h0 f4);

  c3 +! h_3 +! c4


val sq2: f: felem -> f4: felem -> result: felem  -> memory: lbuffer uint64 (size 12) -> temp: lbuffer uint64 (size 5) -> 
  Stack uint64 
  (requires fun h -> live h f /\ live h f4 /\ live h result /\ live h temp /\ live h memory /\ eq_or_disjoint f4 result /\ disjoint f4 memory /\ disjoint f4 temp /\ disjoint f result /\ disjoint temp result /\ disjoint memory temp /\ disjoint memory result /\
    (

      let f0 = Lib.Sequence.index (as_seq h f) 0 in 
      let f1 = Lib.Sequence.index (as_seq h f) 1  in 
      let f2 = Lib.Sequence.index (as_seq h f) 2 in 
      let f3 = Lib.Sequence.index (as_seq h f) 3 in 
    
      let memory = as_seq h memory in 
      let m2 = Lib.Sequence.index memory 2 in 
      let m3 = Lib.Sequence.index memory 3 in 
      let m4 = Lib.Sequence.index memory 4 in 
      let m5 = Lib.Sequence.index memory 5 in 
      let m6 = Lib.Sequence.index memory 6 in 
      let m7 = Lib.Sequence.index memory 7 in 
      let m8 = Lib.Sequence.index memory 8 in 
      let m9 = Lib.Sequence.index memory 9 in 

      uint_v m2 + uint_v m3 * pow2 64 == uint_v f0 * uint_v f2 /\
      uint_v m4 + uint_v m5 * pow2 64 == uint_v f0 * uint_v f3 /\
      
      uint_v m6 + uint_v m7 * pow2 64 == uint_v f1 * uint_v f2 /\
      uint_v m8 + uint_v m9 * pow2 64 == uint_v f1 * uint_v f3 
    )
)
 (ensures fun h0 c h1 -> modifies (loc result |+| loc memory |+| loc temp) h0 h1   /\
       (

      let f0 = Lib.Sequence.index (as_seq h0 f) 0 in 
      let f1 = Lib.Sequence.index (as_seq h0 f) 1  in 
      let f2 = Lib.Sequence.index (as_seq h0 f) 2 in 
      let f3 = Lib.Sequence.index (as_seq h0 f) 3 in 
    
      let memory = as_seq h1 memory in 
      let m4 = Lib.Sequence.index memory 4 in 
      let m5 = Lib.Sequence.index memory 5 in 
      let m8 = Lib.Sequence.index memory 8 in 
      let m9 = Lib.Sequence.index memory 9 in 
      let m10 = Lib.Sequence.index memory 10 in 
      let m11 = Lib.Sequence.index memory 11 in 

      uint_v m4 + uint_v m5 * pow2 64 == uint_v f0 * uint_v f3 /\
      uint_v m8 + uint_v m9 * pow2 64 == uint_v f1 * uint_v f3 /\ 
      uint_v m10 + uint_v m11 * pow2 64 == uint_v f2 * uint_v f3 /\
      as_nat h1 result + uint_v c * pow2 256 = uint_v f2 * as_nat h0 f + as_nat h0 f4
    )  
 )


let sq2 f f4 result memory tempBuffer = 
  let h0 = ST.get() in 
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  
  let temp = sub tempBuffer (size 0) (size 1) in 
  let tempBufferResult = sub tempBuffer  (size 1) (size 4) in 

  let f0 = index f (size 0) in 
  let f1 = index f (size 1) in 
  let f2 = index f (size 2) in 
  let f3 = index f (size 3) in 
    
  let o0 = sub tempBufferResult (size 0) (size 1) in 
  let o1 = sub tempBufferResult (size 1) (size 1) in 
  let o2 = sub tempBufferResult (size 2) (size 1) in 
  let o3 = sub tempBufferResult (size 3) (size 1) in 

  upd o0 (size 0) (index memory (size 2)); 
  let h_0 = index memory (size 3) in 

  upd o1 (size 0) (index memory (size 6));
  
  let l = index o1 (size 0) in     
  let c1 = add_carry_u64 (u64 0) l h_0 o1 in 
  let h_1 = index memory (size 7) in 


  mul64 f2 f2 o2 temp;
  let l = index o2 (size 0) in 

  let c2 = add_carry_u64 c1 l h_1 o2 in
  let h_2 = index temp (size 0) in 

  mul64 f2 f3 o3 temp; 
  let l = index o3 (size 0) in   
  
  upd memory (size 10) l;
  upd memory (size 11) (index temp (size 0));

  let c3 = add_carry_u64 c2 l h_2 o3 in
  let h_3 = index temp (size 0) in 

    let h6 = ST.get() in 

    calc (==) {

    uint_v f2 * as_nat h0 f;
    (==) {}
    uint_v f2 * (uint_v f0 +  uint_v f1 * pow2 64 + uint_v f2 * pow2 64 * pow2 64 + uint_v f3 * pow2 64 * pow2 64 * pow2 64);
    (==)
    {
      assert_by_tactic (uint_v f2 * (uint_v f0 +  uint_v f1 * pow2 64 + uint_v f2 * pow2 64 * pow2 64 + uint_v f3 * pow2 64 * pow2 64 * pow2 64) == 
	uint_v f0 * uint_v f2 +  
	uint_v f1 * uint_v f2 * pow2 64 + 
	uint_v f2 * uint_v f2 * pow2 64 * pow2 64 + 
	uint_v f3 * uint_v f2 * pow2 64 * pow2 64 * pow2 64) canon}
   as_nat h6 tempBufferResult + (uint_v c3 + uint_v h_3) * (pow2 64 * pow2 64 * pow2 64 * pow2 64);
   (==)
   {
     assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256)
   }

   as_nat h6 tempBufferResult + (uint_v c3 + uint_v h_3) * pow2 256;
   };


  let c4 = add4 tempBufferResult f4 result in  
  let h7 = ST.get() in 

  assert_by_tactic (uint_v c4 * pow2 256 + (uint_v c3 + uint_v h_3) * pow2 256 = 
    (uint_v c4 + uint_v c3 + uint_v h_3) * pow2 256) canon;

  lemma_320_1 (as_nat h7 result) (uint_v c4 + uint_v c3 + uint_v h_3) (uint_v f2) (as_nat h0 f) (as_nat h0 f4);

  c3 +! h_3 +! c4


val sq3: f: felem -> f4: felem -> result: felem -> memory: lbuffer uint64 (size 12) -> temp: lbuffer uint64 (size 5) -> 
  Stack uint64 
  (requires fun h -> live h f /\ live h f4 /\ live h result /\ live h temp /\ live h memory /\ eq_or_disjoint f4 result /\ disjoint f4 memory /\ disjoint f4 temp /\ disjoint f result /\ disjoint temp result /\ disjoint memory temp /\ disjoint memory result /\
  (

      let f0 = Lib.Sequence.index (as_seq h f) 0 in 
      let f1 = Lib.Sequence.index (as_seq h f) 1  in 
      let f2 = Lib.Sequence.index (as_seq h f) 2 in 
      let f3 = Lib.Sequence.index (as_seq h f) 3 in 
    
      let memory = as_seq h memory in 
      let m4 = Lib.Sequence.index memory 4 in 
      let m5 = Lib.Sequence.index memory 5 in 
      let m8 = Lib.Sequence.index memory 8 in 
      let m9 = Lib.Sequence.index memory 9 in 
      let m10 = Lib.Sequence.index memory 10 in 
      let m11 = Lib.Sequence.index memory 11 in 

      uint_v m4 + uint_v m5 * pow2 64 == uint_v f0 * uint_v f3 /\
      uint_v m8 + uint_v m9 * pow2 64 == uint_v f1 * uint_v f3 /\ 
      uint_v m10 + uint_v m11 * pow2 64 == uint_v f2 * uint_v f3
    )  
)
  (ensures fun h0 c h1 -> modifies (loc result |+| loc memory |+| loc temp) h0 h1 /\
    (
      let f3 = Lib.Sequence.index (as_seq h0 f) 3 in 
      as_nat h1 result + uint_v c * pow2 256 = uint_v f3 * as_nat h0 f + as_nat h0 f4
    )
  )


let sq3 f f4 result memory tempBuffer = 
  let h0 = ST.get() in 
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  
  let temp = sub tempBuffer (size 0) (size 1) in 
  let tempBufferResult = sub tempBuffer  (size 1) (size 4) in 

  let f0 = index f (size 0) in 
  let f1 = index f (size 1) in 
  let f2 = index f (size 2) in 
  let f3 = index f (size 3) in 
    
  let o0 = sub tempBufferResult (size 0) (size 1) in 
  let o1 = sub tempBufferResult (size 1) (size 1) in 
  let o2 = sub tempBufferResult (size 2) (size 1) in 
  let o3 = sub tempBufferResult (size 3) (size 1) in 

  upd o0 (size 0) (index memory (size 4));
  let h = index memory (size 5) in 

  upd o1 (size 0) (index memory (size 8));
  let l = index o1 (size 0) in     
  let c1 = add_carry_u64 (u64 0) l h o1 in 
  let h = index memory (size 9) in 

  upd o2 (size 0) (index memory (size 10));
  let l = index o2 (size 0) in     
  let c2 = add_carry_u64 c1 l h o2 in
  let h = index memory (size 11) in 
  
  mul64 f3 f3 o3 temp;
  let l = index o3 (size 0) in     
  let c3 = add_carry_u64 c2 l h o3 in
  let h_3 = index temp (size 0) in 

    let h6 = ST.get() in 

    calc (==) {

    uint_v f3 * as_nat h0 f;
    (==) {}
    uint_v f3 * (uint_v f0 +  uint_v f1 * pow2 64 + uint_v f2 * pow2 64 * pow2 64 + uint_v f3 * pow2 64 * pow2 64 * pow2 64);
    (==)
    {
      assert_by_tactic (uint_v f3 * (uint_v f0 +  uint_v f1 * pow2 64 + uint_v f2 * pow2 64 * pow2 64 + uint_v f3 * pow2 64 * pow2 64 * pow2 64) == 
	uint_v f0 * uint_v f3 +  
	uint_v f1 * uint_v f3 * pow2 64 + 
	uint_v f2 * uint_v f3 * pow2 64 * pow2 64 + 
	uint_v f3 * uint_v f3 * pow2 64 * pow2 64 * pow2 64) canon}
   as_nat h6 tempBufferResult + (uint_v c3 + uint_v h_3) * (pow2 64 * pow2 64 * pow2 64 * pow2 64);
   (==)
   {
     assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256)
   }

   as_nat h6 tempBufferResult + (uint_v c3 + uint_v h_3) * pow2 256;
   };


  let c4 = add4 tempBufferResult f4 result in 

  let h7 = ST.get() in 

  assert_by_tactic (uint_v c4 * pow2 256 + (uint_v c3 + uint_v h_3) * pow2 256 = 
    (uint_v c4 + uint_v c3 + uint_v h_3) * pow2 256) canon;

  lemma_320_1 (as_nat h7 result) (uint_v c4 + uint_v c3 + uint_v h_3) (uint_v f3) (as_nat h0 f) (as_nat h0 f4);
  c3 +! h_3 +! c4


#reset-options "--z3rlimit 300"
val sq: f: felem -> out: widefelem -> Stack unit
    (requires fun h -> live h out /\ live h f /\ eq_or_disjoint f out)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\ wide_as_nat h1 out = as_nat h0 f * as_nat h0 f)
      
let sq f out =
  push_frame();
      assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);

  let wb = create (size 25) (u64 0) in 
  
  let temp = sub wb (size 0) (size 8) in 
  let tb = sub wb (size 8) (size 5) in 
  let memory = sub wb (size 13) (size 12) in 
   
  let f0 = f.(0ul) in
  let f1 = f.(1ul) in
  let f2 = f.(2ul) in
  let f3 = f.(3ul) in
  let b0 = sub temp (size 0) (size 4) in
    
    let h0 = ST.get() in
  let c0 = sq0 f b0 memory tb in 
 
    upd temp (size 4) c0;
    let h1 = ST.get() in

    let bk0 = sub temp (size 0) (size 1) in 
    assert(Lib.Sequence.index (as_seq h1 bk0) 0 == Lib.Sequence.index (as_seq h1 temp) 0); 

  let b1 = sub temp (size 1) (size 4) in
  let c1 = sq1 f b1 b1 memory tb in 
    upd temp (size 5) c1; 
    let h2 = ST.get() in 
    
    let bk1 = sub temp (size 0) (size 2) in 
    assert(Lib.Sequence.index (as_seq h2 bk1) 0 == Lib.Sequence.index (as_seq h2 temp) 0);
    assert(Lib.Sequence.index (as_seq h2 bk1) 1 == Lib.Sequence.index (as_seq h2 temp) 1);

  let b2 = sub temp (size 2) (size 4) in 
  let c2 = sq2 f b2 b2 memory tb in 
    upd temp (size 6) c2;

    let h3 = ST.get() in 
     let bk2 = sub temp (size 0) (size 3) in 
     
    assert(Lib.Sequence.index (as_seq h3 bk2) 0 == Lib.Sequence.index (as_seq h3 temp) 0);
    assert(Lib.Sequence.index (as_seq h3 bk2) 1 == Lib.Sequence.index (as_seq h3 temp) 1);
    assert(Lib.Sequence.index (as_seq h3 bk2) 2 == Lib.Sequence.index (as_seq h3 temp) 2);

  let b3 = sub temp (size 3) (size 4) in 
  let c3 = sq3 f b3 b3 memory tb in 
    upd temp (size 7) c3;

    let h4 = ST.get() in 

 assert(
    uint_v f0 * as_nat h0 f + 
    uint_v f1 * as_nat h0 f * pow2 64 + 
    uint_v f2 * as_nat h0 f * pow2 64 * pow2 64 + 
    uint_v f3 * as_nat h0 f * pow2 64 * pow2 64 * pow2 64 = 
    

    as_nat h4 b3  * pow2 64 * pow2 64 * pow2 64 + 
    uint_v (Lib.Sequence.index (as_seq h4 temp) 7) * pow2 64 * pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 +
    uint_v (Lib.Sequence.index (as_seq h4 temp) 2) * pow2 64 * pow2 64 + 
    uint_v (Lib.Sequence.index (as_seq h4 temp) 1) * pow2 64 + 
    uint_v (Lib.Sequence.index (as_seq h4 temp) 0));


    calc (==) {
    as_nat h4 b3  * pow2 64 * pow2 64 * pow2 64 + 
    uint_v (Lib.Sequence.index (as_seq h4 temp) 7) * pow2 64 * pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 +
    uint_v (Lib.Sequence.index (as_seq h4 temp) 2) * pow2 64 * pow2 64 + 
    uint_v (Lib.Sequence.index (as_seq h4 temp) 1) * pow2 64 + 
    uint_v (Lib.Sequence.index (as_seq h4 temp) 0);
    (==) {}
    wide_as_nat h4 temp;};

  calc (==)
    {

    as_nat h0 f * as_nat h0 f;
    (==) {assert_by_tactic (
    uint_v f0 * as_nat h0 f + 
    uint_v f1 * as_nat h0 f * pow2 64 + 
    uint_v f2 * as_nat h0 f * pow2 64 * pow2 64 + 
    uint_v f3 * as_nat h0 f * pow2 64 * pow2 64 * pow2 64 == as_nat h0 f * (uint_v f0 + uint_v f1 * pow2 64 + uint_v f2 * pow2 64 * pow2 64 + uint_v f3 * pow2 64 * pow2 64 * pow2 64)) canon}

    uint_v f0 * as_nat h0 f + 
    uint_v f1 * as_nat h0 f * pow2 64 + 
    uint_v f2 * as_nat h0 f * pow2 64 * pow2 64 + 
    uint_v f3 * as_nat h0 f * pow2 64 * pow2 64 * pow2 64;
    };


  copy out temp; 
    let h5 = ST.get() in 
    assert(modifies (loc wb) h0 h4);
    assert(modifies (loc out) h4 h5);
  pop_frame()


 val cmovznz4: cin: uint64 -> x: felem -> y: felem -> result: felem ->
  Stack unit
    (requires fun h -> live h x /\ live h y /\ live h result /\ disjoint x result /\ eq_or_disjoint y result)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ 
      (if uint_v cin = 0 then as_nat h1 result == as_nat h0 x else as_nat h1 result == as_nat h0 y))

let cmovznz4 cin x y r =  
  let h0 = ST.get() in 
  let mask = neq_mask cin (u64 0) in 
  let r0 = logor (logand y.(size 0) mask) (logand x.(size 0) (lognot mask)) in 
  let r1 = logor (logand y.(size 1) mask) (logand x.(size 1) (lognot mask)) in 
  let r2 = logor (logand y.(size 2) mask) (logand x.(size 2) (lognot mask)) in 
  let r3 = logor (logand y.(size 3) mask) (logand x.(size 3) (lognot mask)) in 
  
  upd r (size 0) r0;
  upd r (size 1) r1;
  upd r (size 2) r2;
  upd r (size 3) r3;

    let x = as_seq h0 x in 
    let y = as_seq h0 y in 
    
    cmovznz4_lemma cin (Seq.index x 0) (Seq.index y 0);
    cmovznz4_lemma cin (Seq.index x 1) (Seq.index y 1);
    cmovznz4_lemma cin (Seq.index x 2) (Seq.index y 2);
    cmovznz4_lemma cin (Seq.index x 3) (Seq.index y 3)


val shift_256_impl: i: felem -> o: lbuffer uint64 (size 8) -> 
  Stack unit 
    (requires fun h -> live h i /\ live h o /\ disjoint i o)
    (ensures fun h0 _ h1 -> modifies1 o h0 h1 /\ 
      (
	let o = as_seq h1 o in 
	felem_seq_as_nat_8 o == as_nat h0 i * pow2 256 
      )
    )

let shift_256_impl i o = 
  upd o (size 0) (u64 0);
  upd o (size 1) (u64 0);
  upd o (size 2) (u64 0);
  upd o (size 3) (u64 0);
  upd o (size 4) i.(size 0);
  upd o (size 5) i.(size 1);
  upd o (size 6) i.(size 2);
  upd o (size 7) i.(size 3);

  assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);
  assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64= pow2 (5 * 64));
  assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
  assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64));
  assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 * pow2 64 = pow2 (8 * 64))


#reset-options "--z3rlimit 200"
inline_for_extraction noextract
val mod64: a: widefelem -> Stack uint64 
  (requires fun h -> live h a) 
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\  wide_as_nat h1 a % pow2 64 = uint_v r)

let mod64 a = index a (size 0)


val shortened_mul: a: ilbuffer uint64 (size 4) -> b: uint64 -> result: widefelem -> Stack unit
  (requires fun h -> live h a /\ live h result /\ wide_as_nat h result = 0)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat_il h0 a * uint_v b = wide_as_nat h1 result /\ 
    wide_as_nat h1 result < pow2 320)

let shortened_mul a b result = 
  let result04 = sub result (size 0) (size 4) in 
  let result48 = sub result (size 4) (size 4) in 
  let c = mul1_il a b result04 in 
    let h0 = ST.get() in 
  upd result (size 4) c;
  
    assert(Lib.Sequence.index (as_seq h0 result) 5 == Lib.Sequence.index (as_seq h0 result48) 1);
    assert(Lib.Sequence.index (as_seq h0 result) 6 == Lib.Sequence.index (as_seq h0 result48) 2);
    assert(Lib.Sequence.index (as_seq h0 result) 7 == Lib.Sequence.index (as_seq h0 result48) 3);

    assert_norm( pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256)
   

val shift8: t: widefelem -> t1: widefelem -> Stack unit 
  (requires fun h -> live h t /\ live h t1 /\ eq_or_disjoint t t1)
  (ensures fun h0 _ h1 -> modifies (loc t1) h0 h1 /\ wide_as_nat h0 t / pow2 64 = wide_as_nat h1 t1)

let shift8 t out = 
  let t1 = index t (size 1) in 
  let t2 = index t (size 2) in 
  let t3 = index t (size 3) in 
  let t4 = index t (size 4) in 
  let t5 = index t (size 5) in 
  let t6 = index t (size 6) in 
  let t7 = index t (size 7) in 

  upd out (size 0) t1;
  upd out (size 1) t2;
  upd out (size 2) t3;
  upd out (size 3) t4;
  upd out (size 4) t5;
  upd out (size 5) t6;
  upd out (size 6) t7;
  upd out (size 7) (u64 0)

(* this piece of code is taken from Hacl.Curve25519 *)
inline_for_extraction noextract
val scalar_bit:
    #buf_type: buftype -> 
    s:lbuffer_t buf_type uint8 (size 32)
  -> n:size_t{v n < 256}
  -> Stack uint64
    (requires fun h0 -> live h0 s)
    (ensures  fun h0 r h1 -> h0 == h1 /\
      r == ith_bit (as_seq h0 s) (v n) /\ v r <= 1)
      
let scalar_bit #buf_type s n =
  let h0 = ST.get () in
  mod_mask_lemma ((Lib.Sequence.index (as_seq h0 s) (v n / 8)) >>. (n %. 8ul)) 1ul;
  assert_norm (1 = pow2 1 - 1);
  assert (v (mod_mask #U8 #SEC 1ul) == v (u8 1));
  to_u64 ((s.(n /. 8ul) >>. (n %. 8ul)) &. u8 1)


val uploadOneImpl: f: felem -> Stack unit
  (requires fun h -> live h f)
  (ensures fun h0 _ h1 -> as_nat h1 f == 1 /\ modifies (loc f) h0 h1)
  
let uploadOneImpl f = 
  upd f (size 0) (u64 1);
  upd f (size 1) (u64 0);
  upd f (size 2) (u64 0);
  upd f (size 3) (u64 0)


val toUint64: i: lbuffer uint8 (32ul) -> o: felem -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> 
    modifies (loc o) h0 h1 /\ 
    as_seq h1 o == Lib.ByteSequence.uints_from_bytes_be (as_seq h0 i)
  )

let toUint64 i o = 
  Lib.ByteBuffer.uints_from_bytes_be o i


val toUint8: i: felem ->  o: lbuffer uint8 (32ul) -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> 
    modifies (loc o) h0 h1 /\ 
    as_seq h1 o == Lib.ByteSequence.uints_to_bytes_be #_ #_ #4 (as_seq h0 i)
  )

let toUint8 i o = 
  Lib.ByteBuffer.uints_to_bytes_be (size 4) o i


val toUint8LE: i: felem ->  o: lbuffer uint8 (32ul) -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> 
    modifies (loc o) h0 h1 /\ 
    as_seq h1 o == Lib.ByteSequence.uints_to_bytes_le #_ #_ #4 (as_seq h0 i)
  )

let toUint8LE i o = 
  Lib.ByteBuffer.uints_to_bytes_le (size 4) o i

