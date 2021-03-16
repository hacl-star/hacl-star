module Hacl.Impl.EC.P521.Reduction

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes 
open FStar.Math.Lemmas
open FStar.Math.Lib
open Lib.Buffer

open Hacl.SolinasReduction.Lemmas
open Hacl.Impl.P256.LowLevel 

open Spec.P256
open Hacl.Spec.P256.Definition
open FStar.Mul

open Hacl.Impl.EC.MontgomeryMultiplication


let coordinate521 = 9ul
let prime521 = pow2 521 - 1

assume val lemma_test: #l: size_nat -> c: curve ->  a: Lib.Sequence.lseq uint64 l -> i: nat {i <= l} -> 
  Lemma (ensures (
    let a0 = Lib.Sequence.sub a 0 i in 
    let a1 = Lib.Sequence.sub a i (l - i) in 
    lseq_as_nat a = lseq_as_nat a0 + pow2 (64 * i) * lseq_as_nat a1))
    (decreases (l - i))


val reduction_p521: i: lbuffer uint64 (coordinate521 *. 2ul) -> o: lbuffer uint64 coordinate521 -> 
  Stack unit
    (requires fun h -> live h i /\ live h o /\ disjoint i o /\ lseq_as_nat (as_seq h i) < prime521 * prime521)
    (ensures fun h0 _ h1 -> modifies1 o h0 h1 /\ 
      lseq_as_nat (as_seq h0 i) % prime521 == lseq_as_nat (as_seq h1 i))

let reduction_p521 i o = 
  let t0 = sub i (size 0) coordinate521 in 
  let t1 = sub i coordinate521 coordinate521 in 

  lemma_test 

  admit()


(* INPUT: An integer c = (c1041,..., c2, c1, c0) in base 2 with 0 ≤ c < p2
521.
OUTPUT: c mod p521.
1. Define 521-bit integers:
s1 = (c1041,..., c523, c522, c521),
s2 = (c520,..., c2, c1, c0).
2. Return(s1 +s2 mod p521). *)
