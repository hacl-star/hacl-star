module Hacl.Impl.P384.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Spec.ECC
open Spec.ECC.Curves

open FStar.Math
open FStar.Math.Lemmas
open FStar.Mul

open Lib.IntTypes.Intrinsics

open Hacl.Bignum


#set-options "--z3rlimit 200 --fuel 1 --ifuel 1"

val lemma_lseq_nat_instant_6: a: Lib.Sequence.lseq uint64 6 -> Lemma (
  lseq_as_nat a == 
    v (Lib.Sequence.index a 0) * pow2 (64 * 0) + 
    v (Lib.Sequence.index a 1) * pow2 (64 * 1) + 
    v (Lib.Sequence.index a 2) * pow2 (64 * 2) +
    v (Lib.Sequence.index a 3) * pow2 (64 * 3) + 
    v (Lib.Sequence.index a 4) * pow2 (64 * 4) + 
    v (Lib.Sequence.index a 5) * pow2 (64 * 5))

let lemma_lseq_nat_instant_6 a = 
  lseq_as_nat_definiton a 6;
  lseq_as_nat_definiton a 5;
  lseq_as_nat_definiton a 4;
  lseq_as_nat_definiton a 3;
  lseq_as_nat_definiton a 2;
  lseq_as_nat_definiton a 1;
  lseq_as_nat_last a

inline_for_extraction noextract
val add6: x: felem P384 -> y: felem P384 -> result: felem P384 -> 
  Stack uint64
  (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result /\ 
    eq_or_disjoint x y)
  (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ v c <= 1 /\ 
    as_nat P384 h1 result + v c * pow2 (64 * 6) == as_nat P384 h0 x + as_nat P384 h0 y)   

let add6 x y result = 
    let h0 = ST.get() in    
  Hacl.Spec.Bignum.bn_add_lemma (as_seq h0 x) (as_seq h0 y);
  bn_add_eq_len (size 6) x y result


val lemma_t_computation_p384: t: uint64 {uint_v t == 0 \/ uint_v t == 1} ->
  Lemma (
    let t0 = (u64 0) -. t in 
    let t1 = t0 -. t in 
    let t2 = t0 <<. (size 32) in 
    let t3 = ((u64 0) -. t) >>. (size 32) in 
  
    let s = uint_v t3 + uint_v t2 * pow2 64 + uint_v t1 * pow2 (64 * 2) + uint_v t0 * pow2 (64 * 3) + 
      uint_v t0 * pow2 (64 * 4) + uint_v t0 * pow2 (64 * 5) in
    if uint_v t = 1 then s == prime384 else s == 0)
      
let lemma_t_computation_p384 t = 
  assert_norm(0xffffffff + 0xffffffff00000000 * pow2 64 + 0xfffffffffffffffe * pow2 (64 * 2) + 
    0xffffffffffffffff * pow2 (64 * 3) + 0xffffffffffffffff * pow2 (64 * 4) + 0xffffffffffffffff * pow2 (64 * 5) == prime384)


inline_for_extraction noextract
val add_dep_prime_p384: x: felem P384 -> t: uint64 {uint_v t == 0 \/ uint_v t == 1} -> result: felem P384 -> 
  Stack uint64
  (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
  (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ (
    if uint_v t = 1 then 
      as_nat P384 h1 result + uint_v c * pow2 (6 * 64) == as_nat P384 h0 x + prime384
    else
      as_nat P384 h1 result == as_nat P384 h0 x))  

let add_dep_prime_p384 x t result = 
  push_frame();
    let h0 = ST.get() in 
  let b = create (size 6) (u64 0) in 
    
  let t3 = (u64 0) -. t in 
  let t2 = t3 -. t in 
  let t1 = t3 <<. (size 32) in 
  let t0 = ((u64 0) -. t) >>. (size 32) in 
  
  upd b (size 0) t0;
  upd b (size 1) t1;
  upd b (size 2) t2;
  upd b (size 3) t3;
  upd b (size 4) t3;
  upd b (size 5) t3;
  lemma_t_computation_p384 t;
    let h1 = ST.get() in 
    lemma_lseq_nat_instant_6 (as_seq h1 b);
  let r = add6 x b result in 
    let h2 = ST.get() in 
  lseq_upperbound (as_seq h0 x);   
  pop_frame();
  r
 
