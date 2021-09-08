 module Hacl.Impl.EC.ScalarMultiplication.Radix

(*open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Hacl.Impl.EC.MontgomeryLadder
open Spec.ECC.Curves
open Spec.ECC


inline_for_extraction noextract
let radix = 4ul

let lenPrecompRadix = size (pow2 (v radix))

open FStar.Mul
#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0" 


let post_precomp_radix #c (b: Lib.Sequence.lseq uint64 (v (getPointLenU64 c) * v lenPrecompRadix)) generator = 
  let len = v (getPointLenU64 c) in
  let generator = point_seq_as_nat c generator in 
  forall (i: nat {i >= 0 && i < v lenPrecompRadix}). 
    let pointZero = point_seq_as_nat c (Lib.Sequence.sub b (i * len) len) in 
    pointEqual pointZero (point_mult #c i generator) 


val generatePrecomputedTableRadix: #c: curve 
  -> generator: point c
  -> b: lbuffer uint64 (getPointLenU64 c *.lenPrecompRadix) -> 
  Stack unit  
  (requires fun h -> live h generator /\ live h b /\ disjoint generator b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ post_precomp_radix #c (as_seq h1 b) (as_seq h0 generator))


let generatePrecomputedTableRadix #c generator b = admit()
 *)