module Hacl.Impl.EC.P521.Reduction

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes 
open FStar.Math.Lemmas
open FStar.Math.Lib
open Lib.Buffer

open Hacl.Impl.P256.LowLevel 

open Spec.ECC
open Spec.ECC.Curves
open Hacl.Spec.EC.Definition
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


#set-options " --z3rlimit 500" 

assume val getZeroWord0: a: Lib.Sequence.lseq uint64 8 -> o8: nat -> Lemma ((lseq_as_nat a + (o8 % pow2 9) * pow2 (64 * 8)) < pow2 521)

val getZeroWord: i: lbuffer uint64 (size 27) -> o: lbuffer uint64 (size 9) -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ lseq_as_nat (as_seq h1 o) == lseq_as_nat (as_seq h0 i) % pow2 521)

let getZeroWord i o = 
    let h0 = ST.get() in 
    let iR = sub i (size 0) (size 9) in 
    let iCopy = sub i (size 0) (size 8) in 
    let oCopy = sub o (size 0) (size 8) in 
    let oMaskCopy = sub o (size 8) (size 1) in 
  copy oCopy iCopy;
  let o8 = index i (size 8) in 
    let h1 = ST.get() in 
  let o8Updated = logand o8 (u64 0x1ff) in 
  upd o (size 8) o8Updated;
    assert_norm (pow2 9 - 1 == 0x1ff);
    logand_mask o8 (u64 0x1ff) 9;
    let h2 = ST.get() in 
  lemma_test #9 (as_seq h2 o) 8; 
  lemma_test (as_seq h1 iR) 8;
  lseq_as_nat_first (as_seq h2 oMaskCopy);
  lseq_as_nat_first (Lib.Sequence.sub (as_seq h2 iR) 8 1);

  lemma_test (as_seq h0 i) 9; 
  pow2_plus (64 * 8 + 9) (64 - 9);
  
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  assert_by_tactic (pow2 (64 * 8 + 9) * pow2 (64 - 9) * lseq_as_nat (Lib.Sequence.sub (as_seq h0 i) 9 (27 - 9)) ==
    (pow2 (64 - 9) * lseq_as_nat (Lib.Sequence.sub (as_seq h0 i) 9 (27 - 9))) * pow2 (64 * 8 + 9)) canon;

  modulo_addition_lemma (lseq_as_nat (as_seq h0 iR)) (pow2 (64 * 8 + 9)) (pow2 (64 - 9) * lseq_as_nat (Lib.Sequence.sub (as_seq h0 i) 9 (27 - 9))) ;

  lemma_mod_add_distr (lseq_as_nat (as_seq h0 iCopy)) (pow2 (64 * 8) * v o8) (pow2 521);

  pow2_plus (64 * 8) 9;
  modulo_scale_lemma (v o8) (pow2 (64 * 8)) (pow2 9);
  getZeroWord0 (as_seq h0 iCopy) (v o8);
  small_mod ((lseq_as_nat (as_seq h0 iCopy) + (v o8 % pow2 9) * pow2 (64 * 8))) (pow2 521);
  
  assert(lseq_as_nat (as_seq h2 o) == lseq_as_nat (as_seq h0 i) % pow2 521)


val getFirstWord: i: lbuffer uint64 (size 27) -> o: lbuffer uint64 (size 9) -> Stack unit 
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1)

let getFirstWord i o = 
  let h0 = ST.get() in 
  let inv h (j: nat) = live h i /\ live h o /\ modifies (loc o) h0 h in 
  Lib.Loops.for 0ul 8ul inv (fun j -> 
    let i0 = index i (size 8 *! size 1 +! j) in 
    let i1 = index i (size 8 *! size 1 +! size 1 +! j) in 
    let i0 = shift_right i0 (size 9) in 
      shift_right_lemma i0 (size 9);
    let i1U = Lib.IntTypes.shift_left i1 (size 55) in 
      shift_left_lemma i1 (size 55);
    let o0 = logxor i0 i1U in 
    upd o j o0);
  let o8 = index o (size 8) in 
  let o8Updated = logand o8 (u64 0x1ff) in 
  upd o (size 8) o8Updated


val getSecondWord: i: lbuffer uint64 (size 27) -> o: lbuffer uint64 (size 9) -> Stack unit 
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1)

let getSecondWord i o = 
  let h0 = ST.get() in 
  let inv h (j: nat) = live h i /\ live h o /\ modifies (loc o) h0 h in 
  Lib.Loops.for 0ul 8ul inv (fun j -> 
    let i0 = index i (size 8 *! size 2 +! j) in 
    let i1 = index i (size 8 *! size 2 +! size 1 +! j) in 
    let i0 = shift_right i0 (size 18) in 
      shift_right_lemma i0 (size 18);
    let i1U = Lib.IntTypes.shift_left i1 (size 46) in 
      shift_left_lemma i1 (size 46);
    let o0 = logxor i0 i1U in 
    upd o j o0);
  let o8 = index o (size 8) in 
  let o8Updated = logand o8 (u64 0x1ff) in 
  upd o (size 8) o8Updated

    
val reduction_p521: i: widefelem -> o: felem -> 
  Stack unit
    (requires fun h -> live h i /\ live h o /\ disjoint i o /\ lseq_as_nat (as_seq h i) < prime521 * pow2 (64 * v coordinate521))
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1)

let reduction_p521 i o = 
  push_frame();
    let a0 = create (size 9) (u64 0) in 
    let a1 = create (size 9) (u64 0) in 
    let a2 = create (size 9) (u64 0) in 
    let a3 = create (size 27) (u64 0) in 
      let a3Part = sub a3 (size 0) (size 18) in 
      
  copy a3Part i; 

  getZeroWord a3 a0;
  getFirstWord a3 a1;
  getSecondWord a3 a2;
    let h1 = ST.get() in 
    assume (lseq_as_nat (as_seq h1 a0) < prime521);
    assume (lseq_as_nat (as_seq h1 a1) < prime521);
    assume (lseq_as_nat (as_seq h1 a2) < prime521);

(*   felem_add a0 a1 o;
  felem_add o a2 o; *)
  pop_frame()


(* INPUT: An integer c = (c1041,..., c2, c1, c0) in base 2 with 0 ≤ c < p2
521.
OUTPUT: c mod p521.
1. Define 521-bit integers:
s1 = (c1041,..., c523, c522, c521),
s2 = (c520,..., c2, c1, c0).
2. Return(s1 +s2 mod p521). *)
