
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


val add6: x: felem P384 -> y: felem P384 -> result: felem P384 -> 
  Stack uint64
    (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result)
    (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ v c <= 1 /\ 
      as_nat P384 h1 result + v c * pow2 384 == as_nat P384 h0 x + as_nat P384 h0 y)   

let add6 x y result = 
  bn_add_eq_len (size 6) x y result


(* 
val lemma_t_computation_p384: t: uint64 {uint_v t == 0 \/ uint_v t == 1} ->
  Lemma
    (
      let t0 = (u64 0) -. t in 
      let t1 = t0 -. t in 
      let t2 = t0 <<. (size 32) in 
      let t3 = ((u64 0) -. t) >>. (size 32) in 
  
      let s = uint_v t3 + uint_v t2 * pow2 64 + uint_v t1 * pow2 128 + 
  uint_v t0 * pow2 192 + uint_v t0 * pow2 256 + uint_v t0 * pow2 320 in
      if uint_v t = 1 then s == prime384 else s == 0)
      

let lemma_t_computation_p384 t = 
  assert_norm(0xffffffff + 0xffffffff00000000 * pow2 64 + 0xfffffffffffffffe * pow2 128 + 
    0xffffffffffffffff * pow2 192 +  0xffffffffffffffff * pow2 256 +  0xffffffffffffffff * pow2 320 == prime384)
 *)


(* replace with tempBuffer *)
val add_dep_prime_p384: x: felem P384 -> t: uint64 {uint_v t == 0 \/ uint_v t == 1} ->
  result: felem P384 -> 
  Stack uint64
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
    (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ (
      if uint_v t = 1 then 
        as_nat P384 h1 result + uint_v c * pow2 384 == as_nat P384 h0 x + prime384
      else
        as_nat P384 h1 result  == as_nat P384 h0 x))  

let add_dep_prime_p384 x t result = 
  push_frame();
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

  let r = add6 x b result in 
  pop_frame();
  r
 
