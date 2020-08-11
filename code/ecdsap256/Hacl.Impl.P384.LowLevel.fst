module Hacl.Impl.P384.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definition
open Spec.P256

open FStar.Math
open FStar.Math.Lemmas
open FStar.Mul

open Lib.IntTypes.Intrinsics


val add6: x: felem P384 -> y: felem P384 -> result: felem P384 -> 
  Stack uint64
    (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result)
    (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ v c <= 1 /\ 
      as_nat P384 h1 result + v c * pow2 384 == as_nat P384 h0 x + as_nat P384 h0 y)   

let add6 x y result = admit()

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

val add_dep_prime_p384: x: felem P384 -> t: uint64 {uint_v t == 0 \/ uint_v t == 1} ->
  result: felem P384 -> 
  Stack uint64
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
    (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ (
      if uint_v t = 1 then 
  as_nat P384 h1 result + uint_v c * pow2 384 == as_nat P384 h0 x + prime384
      else
  as_nat P384 h1 result  == as_nat P384 h0 x))  


val sub6: x: felem P384 -> y:felem P384 -> result: felem P384 -> 
  Stack uint64
    (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result)
    (ensures fun h0 c h1 -> modifies1 result h0 h1 /\ v c <= 1 /\ 
      as_nat P384 h1 result - v c * pow2 384 == as_nat P384 h0 x - as_nat P384 h0 y)

let sub6 x y result = admit()

val sub6_il: x: felem P384 -> y: glbuffer uint64 (size 6) -> result: felem P384 -> 
  Stack uint64
  (requires fun h -> live h x /\ live h y /\ live h result /\ disjoint x result /\ disjoint result y)
  (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ v c <= 1 /\ (
    as_nat P384 h1 result - v c * pow2 384 == as_nat P384 h0 x  - as_nat_il P384 h0 y /\
    (
      if uint_v c = 0 
	then as_nat P384 h0 x >= as_nat_il P384 h0 y 
      else 
	as_nat P384 h0 x < as_nat_il P384 h0 y)))

let sub6_il x y result = admit()


val mul_p384: f: felem P384 -> r: felem P384 -> out: widefelem P384 -> 
  Stack unit
    (requires fun h -> live h out /\ live h f /\ live h r /\ disjoint r out)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
      wide_as_nat P384 h1 out = as_nat P384 h0 r * as_nat P384 h0 f)

let mul_p384 f r out = admit()


val square_p384: f: felem P384 -> out: widefelem P384 -> Stack unit
    (requires fun h -> live h out /\ live h f /\ eq_or_disjoint f out)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
      wide_as_nat P384 h1 out = as_nat P384 h0 f * as_nat P384 h0 f)

let square_p384 f out = admit()

