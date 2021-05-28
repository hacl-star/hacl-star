module Hacl.Impl.EC.ScalarMultiplication.WNAF

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Hacl.Impl.EC.MontgomeryLadder
open Spec.ECC.Curves
open Spec.ECC
  


inline_for_extraction noextract
let dradix_wnaf = (u64 64)
inline_for_extraction noextract
let dradix : (a: size_t)= (u32 32)
noextract
let lenPrecompWnaf = 16
inline_for_extraction noextract
let radix = (u64 5)

open FStar.Mul

#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0" 


val uploadOne: #c: curve -> gen: point c -> b: lbuffer uint64 (getPointLenU64 c *. 16ul) -> Stack unit 
  (requires fun h -> live h gen /\ live h b /\ disjoint gen b /\ point_eval c h gen)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ (
    let pointZero = gsub b (size 0) (getPointLenU64 c) in 
    let gen = point_as_nat c h0 gen in 
    point_eval c h1 pointZero /\ (
    pointEqual (point_as_nat c h1 pointZero) (point_mult #c 1 gen))))

let uploadOne #c gen b = 
  assume (v (getPointLenU64 c) <= v (getPointLenU64 c *. dradix >>. 1ul));
  let zeroP = sub b (size 0) (getPointLenU64 c) in 
  copy zeroP gen 
  

let post_precomp_wnaf #c (b: Lib.Sequence.lseq uint64 (v (getPointLenU64 c) * lenPrecompWnaf)) (generator : point_seq c) = 
  let len = v (getPointLenU64 c) in
  let generator = point_seq_as_nat c generator in 
  forall (i: nat {i >= 0 && i < lenPrecompWnaf}). 
    let pointZero = point_seq_as_nat c (Lib.Sequence.sub b (i * len) len) in 
    pointEqual pointZero (point_mult #c (i + 1) generator) 



(*
val precomp_wnaf: lbuffer uint64 ((getPointLenU64 P256 *. dradix) >>. 1ul) -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> 


let precomp_wnaf b = admit()
