module Hacl.Bignum.Fsum

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Fsum

module U32 = FStar.UInt32


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

private val fsum_spec_unrolled:
  s:seqelem -> s':seqelem{red s len /\ red s' len} ->
  Tot (s'':seqelem{let open FStar.Seq in
    index s'' 0 == index s 0 +^ index s' 0 /\
    index s'' 1 == index s 1 +^ index s' 1 /\
    index s'' 2 == index s 2 +^ index s' 2 /\
    index s'' 3 == index s 3 +^ index s' 3 /\
    index s'' 4 == index s 4 +^ index s' 4})
  (decreases ctr)
private let fsum_spec_unrolled s s' =
  let open FStar.Seq in
  let a0 = index s 0 in let b0 = index s' 0 in
  let a1 = index s 1 in let b1 = index s' 1 in
  let a2 = index s 2 in let b2 = index s' 2 in
  let a3 = index s 3 in let b3 = index s' 3 in
  let a4 = index s 4 in let b4 = index s' 4 in
  let s'' = s in
  let s'' = upd s'' 0 (a0 +^ b0) in
  let s'' = upd s'' 1 (a1 +^ b1) in
  let s'' = upd s'' 2 (a2 +^ b2) in
  let s'' = upd s'' 3 (a3 +^ b3) in
  let s'' = upd s'' 4 (a4 +^ b4) in
  s''


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

private let lemma_fsum_spec_equivalence (s:seqelem) (s':seqelem{red s len /\ red s' len}) :
  Lemma (fsum_spec s s' len == fsum_spec_unrolled s s')
  = 
  let s1 = fsum_spec s s' len in
  let s2 = fsum_spec_unrolled s s' in
  cut (forall (i:nat). {:pattern (Seq.index s2 i)} i < len
    ==> v (Seq.index s2 i) = v (Seq.index s i) + v (Seq.index s' i));
  cut (forall (i:nat). {:pattern (Seq.index s1 i)} i < len
    ==> v (Seq.index s1 i) = v (Seq.index s i) + v (Seq.index s' i));
  Seq.lemma_eq_intro s1 s2


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"


let red_c h (f:felem) ctr = live h f /\ red (as_seq h f) ctr

[@"substitute"]
inline_for_extraction val fsum_:
  a:felem ->
  b:felem{disjoint a b} ->
  i:ctr{U32.v i <= len} -> // Dummy argument to match the framework
  Stack unit
    (requires (fun h -> red_c h a len /\ red_c h b len))
    (ensures (fun h0 _ h1 -> red_c h0 a len /\ red_c h0 b len /\ live h1 a /\ modifies_1 a h0 h1
      /\ as_seq h1 a == fsum_spec (as_seq h0 a) (as_seq h0 b) len))
[@"substitute"]
inline_for_extraction let rec fsum_ a b i =
  let h0 = ST.get() in
  let a0 = a.(0ul) in 
  let b0 = b.(0ul) in
  let a1 = a.(1ul) in 
  let b1 = b.(1ul) in
  let a2 = a.(2ul) in 
  let b2 = b.(2ul) in
  let a3 = a.(3ul) in 
  let b3 = b.(3ul) in
  let a4 = a.(4ul) in 
  let b4 = b.(4ul) in
  a.(0ul) <- a0 +^ b0;
  a.(1ul) <- a1 +^ b1;
  a.(2ul) <- a2 +^ b2;
  a.(3ul) <- a3 +^ b3;
  a.(4ul) <- a4 +^ b4;
  let h1 = ST.get() in
  cut (as_seq h1 a == fsum_spec_unrolled (as_seq h0 a) (as_seq h0 b));
  lemma_fsum_spec_equivalence (as_seq h0 a) (as_seq h0 b)
