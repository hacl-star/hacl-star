module Hacl.Impl.EC.P521.Reduction

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes 
open FStar.Math.Lemmas
open FStar.Math.Lib
open Lib.Buffer

open Hacl.Impl.P256.LowLevel 

open Spec.P256
open Hacl.Spec.P256.Definition
open FStar.Mul

open Hacl.Impl.EC.MontgomeryMultiplication.Lemmas

#set-options " --z3rlimit 200" 


let coordinate521 = 9ul
let prime521 = pow2 521 - 1

let felem = lbuffer uint64 (coordinate521)
let widefelem = lbuffer uint64 (coordinate521 *. 2ul)

assume val felem_add: a: felem -> b: felem -> out: felem ->  Stack unit
    (requires (fun h -> 
      live h a /\ live h b /\ live h out /\ eq_or_disjoint a out /\  eq_or_disjoint b out /\
      lseq_as_nat (as_seq h a) < prime521 /\ lseq_as_nat (as_seq h b) < prime521))
    (ensures (fun h0 _ h1 -> 
      modifies (loc out) h0 h1 /\ 
      lseq_as_nat (as_seq h1 out) == (lseq_as_nat (as_seq h0 a) + lseq_as_nat (as_seq h1 b)) % prime521))


assume val reduction_prime_2prime:  x: felem-> result: felem -> 
  Stack unit
    (requires fun h -> 
      live h x /\ live h result /\ eq_or_disjoint x result)
    (ensures fun h0 _ h1 -> 
      modifies (loc result) h0 h1 /\ lseq_as_nat (as_seq h1 result) == lseq_as_nat (as_seq h0 x) % prime521)



val lemma_second_word_reduction: t0: Lib.Sequence.lseq uint64 (v coordinate521) -> t1: Lib.Sequence.lseq uint64 (v coordinate521) -> 
  Lemma 
    (requires (lseq_as_nat t0 + pow2 (64 * v coordinate521) * lseq_as_nat t1 < prime521 * pow2 (64 * v coordinate521)))
    (ensures(lseq_as_nat t1 < prime521))


let lemma_second_word_reduction t0 t1 = 
  lseq_upperbound t0;
  assert(lseq_as_nat t1 < prime521)


val getZeroWord: i: widefelem -> o: felem -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1)

let getZeroWord i o = 
  copy o (sub i (size 0) (size 9));
  let o8 = index o (size 8) in 
  let o8Updated = logand (u64 0x00000000000002ff) o8 in 
  upd o (size 8) o8Updated
  
  (* 576 bits copies *)


val getFirstWord: i: widefelem -> o: felem -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let getFirstWord i o = 
  let flag0 = u64 0xfffffffffffffd00 in 
  let flag1 = u64 0x00000000000002ff in 
  let i0 = index i (size 9) in 
  let i1 = index i (size 10) in 

  let i0_ = logand i0 flag0 in 
  let i1_ = logand i1 flag1 in 

  let o0 = logxor i0_ i1_ in 
  upd o (size 0) o0



val reduction_p521: i: widefelem -> o: felem -> 
  Stack unit
    (requires fun h -> live h i /\ live h o /\ disjoint i o /\ lseq_as_nat (as_seq h i) < prime521 * pow2 (64 * v coordinate521))
    (ensures fun h0 _ h1 -> modifies1 o h0 h1 /\ 
      lseq_as_nat (as_seq h0 i) % prime521 == lseq_as_nat (as_seq h1 o))

let reduction_p521 i o = 
  push_frame();
    let a0 = create (size 9) (u64 0) in 
    let a1 = create (size 9) (u64 0) in 
    let a2 = create (size 9) (u64 0) in 

  getZeroWord i a0;
  getFirstWord i a1;
  getFirstWord i a2;
  




  felem_add a0 a1 o;
  felem_add o a2 o;


  admit()


(* INPUT: An integer c = (c1041,..., c2, c1, c0) in base 2 with 0 ≤ c < p2
521.
OUTPUT: c mod p521.
1. Define 521-bit integers:
s1 = (c1041,..., c523, c522, c521),
s2 = (c520,..., c2, c1, c0).
2. Return(s1 +s2 mod p521). *)
