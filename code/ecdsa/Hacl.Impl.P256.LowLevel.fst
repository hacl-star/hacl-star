module Hacl.Impl.P256.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Hacl.EC.Lemmas
open Spec.ECC
open Spec.ECC.Curves
open Spec.ECDSA

open FStar.Math
open FStar.Math.Lemmas
open FStar.Mul

open FStar.Tactics
open FStar.Tactics.Canon 

open Lib.IntTypes.Intrinsics


#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"


val lemma_lseq_nat_instant_4: a: Lib.Sequence.lseq uint64 4 -> Lemma (
  lseq_as_nat a == 
    v (Lib.Sequence.index a 0) * pow2 (64 * 0) + 
    v (Lib.Sequence.index a 1) * pow2 (64 * 1) + 
    v (Lib.Sequence.index a 2) * pow2 (64 * 2) +
    v (Lib.Sequence.index a 3) * pow2 (64 * 3))

let lemma_lseq_nat_instant_4 a = 
  lseq_as_nat_definiton a 4;
  lseq_as_nat_definiton a 3;
  lseq_as_nat_definiton a 2;
  lseq_as_nat_definiton a 1;
  lseq_as_nat_last a


val lemma_lseq_nat_instant_5: a: Lib.Sequence.lseq uint64 8 -> Lemma (
  lseq_as_nat_ a 5 == 
    v (Lib.Sequence.index a 0) * pow2 (64 * 0) + 
    v (Lib.Sequence.index a 1) * pow2 (64 * 1) + 
    v (Lib.Sequence.index a 2) * pow2 (64 * 2) +
    v (Lib.Sequence.index a 3) * pow2 (64 * 3) + 
    v (Lib.Sequence.index a 4) * pow2 (64 * 4))

let lemma_lseq_nat_instant_5 a = 
  lseq_as_nat_definiton a 5;
  lseq_as_nat_definiton a 4;
  lseq_as_nat_definiton a 3;
  lseq_as_nat_definiton a 2;
  lseq_as_nat_definiton a 1;
  lseq_as_nat_last a

val lemma_lseq_nat_instant_8: a: Lib.Sequence.lseq uint64 8 -> Lemma (
  lseq_as_nat a == 
    v (Lib.Sequence.index a 0) * pow2 (64 * 0) + 
    v (Lib.Sequence.index a 1) * pow2 (64 * 1) + 
    v (Lib.Sequence.index a 2) * pow2 (64 * 2) +
    v (Lib.Sequence.index a 3) * pow2 (64 * 3) + 
    v (Lib.Sequence.index a 4) * pow2 (64 * 4) +
    v (Lib.Sequence.index a 5) * pow2 (64 * 5) +
    v (Lib.Sequence.index a 6) * pow2 (64 * 6) +
    v (Lib.Sequence.index a 7) * pow2 (64 * 7))

let lemma_lseq_nat_instant_8 a = 
  lseq_as_nat_definiton a 8;
  lseq_as_nat_definiton a 7;
  lseq_as_nat_definiton a 6;
  lseq_as_nat_definiton a 5;
  lseq_as_nat_definiton a 4;
  lseq_as_nat_definiton a 3;
  lseq_as_nat_definiton a 2;
  lseq_as_nat_definiton a 1;
  lseq_as_nat_last a


inline_for_extraction noextract
val add_dep_prime_p256: x: felem P256 -> t: uint64 {uint_v t == 0 \/ uint_v t == 1} -> result: felem P256 -> 
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

  lemma_lseq_nat_instant_4 (as_seq h0 x);
  lemma_lseq_nat_instant_4 (as_seq h1 result);

  cc

inline_for_extraction noextract
val mul64: x: uint64 -> y: uint64 -> result: lbuffer uint64 (size 1) -> temp: lbuffer uint64 (size 1) ->
  Stack unit (requires fun h -> live h result /\ live h temp /\ disjoint result temp)
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc temp) h0 h1 /\ (
    let h0 = Seq.index (as_seq h1 temp) 0 in 
    let result = Seq.index (as_seq h1 result) 0 in 
    uint_v result + uint_v h0 * pow2 64 = uint_v x * uint_v y))

let mul64 x y result temp = 
  let res = mul64_wide x y in 
  let l0, h0 = to_u64 res, to_u64 (res >>. 64ul) in 
  upd result (size 0) l0;
  upd temp (size 0) h0


inline_for_extraction noextract
val mult64_c: x: uint64 -> u: uint64 -> cin: uint64{uint_v cin <= 1} -> result: lbuffer uint64 (size 1) 
  -> temp: lbuffer uint64 (size 1) -> 
  Stack uint64 
  (requires fun h -> live h result /\ live h temp /\ disjoint result temp)
  (ensures fun h0 c2 h1 -> modifies (loc result |+| loc temp) h0 h1 /\ uint_v c2 <= 1 /\ (
    let r = Seq.index (as_seq h1 result) 0 in 
    let h1 = Seq.index (as_seq h1 temp) 0 in 
    let h0 = Seq.index (as_seq h0 temp) 0 in 
    uint_v r + uint_v c2 * pow2 64 == uint_v x * uint_v u - uint_v h1 * pow2 64 + uint_v h0 + uint_v cin))

let mult64_c x u cin result temp = 
  let h = index temp (size 0) in 
  mul64 x u result temp;
  let l = index result (size 0) in     
  add_carry_u64 cin l h result

inline_for_extraction noextract
val shortened_mul_prime256: b: uint64 -> result: widefelem P256 -> Stack unit
  (requires fun h -> live h result /\ wide_as_nat P256 h result < pow2 (64 * 5))
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ wide_as_nat P256 h1 result < pow2 (64 * 5) /\
    lseq_as_nat (as_seq h1 result) = v b * prime256 )

let shortened_mul_prime256 u result = 
  push_frame();
    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 == pow2 320);
  let result04 = sub result (size 0) (size 4) in 
  let result48 = sub result (size 4) (size 4) in 
  let result58 = sub result (size 5) (size 3) in 

  let temp = create (size 1) (u64 0) in 

  let f0 = (u64 0xffffffffffffffff) in 
  let f1 = (u64 0xffffffff) in 
  let f3 = (u64 0xffffffff00000001) in 
    
  let o0 = sub result (size 0) (size 1) in 
  let o1 = sub result (size 1) (size 1) in 
  let o2 = sub result (size 2) (size 1) in 
  let o3 = sub result (size 3) (size 1) in 
  let o4 = sub result (size 4) (size 1) in 
    
    let h0 = ST.get() in 
  mul64 f0 u o0 temp;
    let h1 = ST.get() in 
  let c1 = mult64_c f1 u (u64 0) o1 temp in 
    let h2 = ST.get() in 
    
  let h = index temp (size 0) in 
  upd o2 (size 0) (h +! c1);
      let h3 = ST.get() in 
  mul64 f3 u o3 o4;
    let h4 = ST.get() in 
  pop_frame();

  let o0_0 = v (Lib.Sequence.index (as_seq h1 o0) 0) in 
  let o1_0 = v (Lib.Sequence.index (as_seq h2 o1) 0) in 
  let o2_0 = v (Lib.Sequence.index (as_seq h3 o2) 0) in 
  let o3_0 = v (Lib.Sequence.index (as_seq h4 o3) 0) in 
  let o4_0 = v (Lib.Sequence.index (as_seq h4 o4) 0) in 


  lemma_lseq_nat_instant_8 (as_seq h0 result);
  Hacl.Spec.EC.Definition.lemma_test (as_seq h0 result) 5;
  
  assert_norm (v f0 + v f1 * pow2 64 + v f3 * pow2 64 * pow2 64 * pow2 64 == prime256);

  lemma_lseq_nat_instant_8 (as_seq h4 result);

  
  assert(Lib.Sequence.index (as_seq h0 result) 5 == Lib.Sequence.index (as_seq h0 result48) 1);
  assert(Lib.Sequence.index (as_seq h0 result) 6 == Lib.Sequence.index (as_seq h0 result48) 2);
  assert(Lib.Sequence.index (as_seq h0 result) 7 == Lib.Sequence.index (as_seq h0 result48) 3);

  assert(Lib.Sequence.index (as_seq h0 result) 5 == Lib.Sequence.index (as_seq h0 result58) 0);
  assert(Lib.Sequence.index (as_seq h0 result) 6 == Lib.Sequence.index (as_seq h0 result58) 1);
  assert(Lib.Sequence.index (as_seq h0 result) 7 == Lib.Sequence.index (as_seq h0 result58) 2);
  
  lseq_as_nat_definiton (Lib.Sequence.sub (as_seq h4 result) 5 3) 1;
  lseq_as_nat_definiton (Lib.Sequence.sub (as_seq h4 result) 5 3) 2;
  lseq_as_nat_definiton (Lib.Sequence.sub (as_seq h4 result) 5 3) 3
