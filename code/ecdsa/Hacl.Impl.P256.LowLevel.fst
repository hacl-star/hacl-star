module Hacl.Impl.P256.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Hacl.Lemmas.P256
(* open Spec.ECDSA.Lemmas *)
open Spec.ECC
open Spec.ECC.Curves
open Spec.ECDSA

open FStar.Math
open FStar.Math.Lemmas
open FStar.Mul

open FStar.Tactics
open FStar.Tactics.Canon 

(* open Spec.ECC.Lemmas *)
open Lib.IntTypes.Intrinsics

#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"


val add_dep_prime_p256: x: felem P256 -> t: uint64 {uint_v t == 0 \/ uint_v t == 1} ->
  result: felem P256 -> 
  Stack uint64
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
    (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ (
      if uint_v t = 1 then 
	as_nat P256 h1 result + uint_v c * pow2 256 == as_nat P256 h0 x + prime256
      else
	as_nat P256 h1 result  == as_nat P256 h0 x))  

let add_dep_prime_p256 x t result = 
  let h0 = ST.get() in 

  let y0 = (u64 0) -. t in 
  let y1 = ((u64 0) -. t) >>. (size 32) in 
  let y2 = u64 0 in 
  let y3 = t -. (t <<. (size 32)) in 

  let r0 = sub result (size 0) (size 1) in      
  let r1 = sub result (size 1) (size 1) in 
  let r2 = sub result (size 2) (size 1) in 
  let r3 = sub result (size 3) (size 1) in 

  let cc = add_carry_u64 (u64 0) x.(0ul) y0 r0 in 
  let cc = add_carry_u64 cc x.(1ul) y1 r1 in 
  let cc = add_carry_u64 cc x.(2ul) y2 r2 in 
  let cc = add_carry_u64 cc x.(3ul) y3 r3 in     

  let h1 = ST.get() in 
  assert_norm(18446744073709551615 + 4294967295 * pow2 64 + 18446744069414584321 * pow2 192 = prime256);

  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    
  assert(let r1_0 = as_seq h0 r1 in let r0_ = as_seq h0 result in Seq.index r0_ 1 == Seq.index r1_0 0);
  assert(let r2_0 = as_seq h0 r2 in let r0_ = as_seq h0 result in Seq.index r0_ 2 == Seq.index r2_0 0);
  assert(let r3_0 = as_seq h0 r3 in let r0_ = as_seq h0 result in Seq.index r0_ 3 == Seq.index r3_0 0); 

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


inline_for_extraction noextract
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


inline_for_extraction noextract
val shortened_mul_prime256: #c: curve -> b: uint64 -> result: widefelem c -> Stack unit
  (requires fun h -> (*live h result /\ wide_as_nat h result < pow2 320) *) True)
  (ensures fun h0 _ h1 -> (* modifies (loc result) h0 h1 /\ 
    wide_as_nat h1 result < pow2 320 *) True
  )

let shortened_mul_prime256 u result = 
    assert_norm( pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 == pow2 320);
  let result04 = sub result (size 0) (size 4) in 
  let result48 = sub result (size 4) (size 4) in 
  
    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);

  let temp = create (size 1) (u64 0) in 

  let f0 = (u64 0xffffffffffffffff) in 
  let f1 = (u64 0xffffffff) in 
  (* let f2 = index f (size 2) in *)
  let f3 = (u64 0xffffffff00000001) in 
    
  let o0 = sub result (size 0) (size 1) in 
  let o1 = sub result (size 1) (size 1) in 
  let o2 = sub result (size 2) (size 1) in 
  let o3 = sub result (size 3) (size 1) in 
    
    let h0 = ST.get() in 
  mul64 f0 u o0 temp;


    let h1 = ST.get() in 
  let c1 = mult64_c f1 u (u64 0) o1 temp in 
    let h2 = ST.get() in 
  let h = index temp (size 0) in 

  upd temp (size 0) (u64 0);
  upd o2 (size 0) (u64 0);
  
  add_carry_u64_void c1 (u64 0) h o2;
    let h3 = ST.get() in 
  let c3 = mult64_c f3 u (u64 0) o3 temp in 
    let h4 = ST.get() in 
  let temp0 = index temp (size 0) in 
    (* lemma_low_level0 (uint_v(Seq.index (as_seq h1 o0) 0)) (uint_v (Seq.index (as_seq h2 o1) 0)) (uint_v (Seq.index (as_seq h3 o2) 0)) (uint_v (Seq.index (as_seq h4 o3) 0)) (uint_v f0) (uint_v f1) (uint_v f2) (uint_v f3) (uint_v u) (uint_v (Seq.index (as_seq h2 temp) 0)) (uint_v c1) (uint_v c2) (uint_v c3) (uint_v (Seq.index (as_seq h3 temp) 0)) (uint_v temp0);  
    
  mul_lemma_4 (as_nat_il h0 f) (uint_v u) (pow2 256 - 1) (pow2 64 - 1);
  assert_norm((pow2 256 - 1) * (pow2 64 - 1) == pow2 320 - pow2 256 - pow2 64 + 1);
  assert_norm((pow2 320 - pow2 256) / pow2 256 == pow2 64 - 1);

*)
  upd result (size 4) (c3 +! temp0);
  
    assert(Lib.Sequence.index (as_seq h0 result) 5 == Lib.Sequence.index (as_seq h0 result48) 1);
    assert(Lib.Sequence.index (as_seq h0 result) 6 == Lib.Sequence.index (as_seq h0 result48) 2);
    assert(Lib.Sequence.index (as_seq h0 result) 7 == Lib.Sequence.index (as_seq h0 result48) 3)

   
