module Hacl.Bignum.Fdifference

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Fdifference

module U32 = FStar.UInt32


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

private val fdifference_spec_unrolled:
  s:seqelem -> s':seqelem{gte_limbs s s' len} ->
  Tot (s'':seqelem{let open FStar.Seq in
    index s'' 0 == index s' 0 -^ index s 0 /\
    index s'' 1 == index s' 1 -^ index s 1 /\
    index s'' 2 == index s' 2 -^ index s 2 /\
    index s'' 3 == index s' 3 -^ index s 3 /\
    index s'' 4 == index s' 4 -^ index s 4})
  (decreases ctr)
private let fdifference_spec_unrolled s s' =
  let open FStar.Seq in
  let a0 = index s 0 in let b0 = index s' 0 in
  let a1 = index s 1 in let b1 = index s' 1 in
  let a2 = index s 2 in let b2 = index s' 2 in
  let a3 = index s 3 in let b3 = index s' 3 in
  let a4 = index s 4 in let b4 = index s' 4 in
  let s'' = s in
  let s'' = upd s'' 0 (b0 -^ a0) in
  let s'' = upd s'' 1 (b1 -^ a1) in
  let s'' = upd s'' 2 (b2 -^ a2) in
  let s'' = upd s'' 3 (b3 -^ a3) in
  let s'' = upd s'' 4 (b4 -^ a4) in
  s''


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

private let lemma_fdifference_spec_equivalence (s:seqelem) (s':seqelem{gte_limbs s s' len}) :
  Lemma (fdifference_spec s s' len == fdifference_spec_unrolled s s')
  = 
  let s1 = fdifference_spec s s' len in
  let s2 = fdifference_spec_unrolled s s' in
  cut (forall (i:nat). {:pattern (Seq.index s2 i)} i < len
    ==> v (Seq.index s2 i) = v (Seq.index s' i) - v (Seq.index s i));
  cut (forall (i:nat). {:pattern (Seq.index s1 i)} i < len
    ==> v (Seq.index s1 i) = v (Seq.index s' i) - v (Seq.index s i));
  Seq.lemma_eq_intro s1 s2


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

let gte_limbs_c h (a:felem) h' (b:felem) (l:nat{l <= len}) : GTot Type0 =
  live h a /\ live h' b /\ gte_limbs (as_seq h a) (as_seq h' b) l


[@"substitute"]
inline_for_extraction val fdifference_:
  a:felem ->
  b:felem{disjoint a b} ->
  i:ctr{U32.v i <= len} ->
  Stack unit
    (requires (fun h -> gte_limbs_c h a h b len))
    (ensures (fun h0 _ h1 -> gte_limbs_c h0 a h0 b len /\ live h1 a /\ modifies_1 a h0 h1
      /\ as_seq h1 a == fdifference_spec (as_seq h0 a) (as_seq h0 b) len))
[@"substitute"]
inline_for_extraction let rec fdifference_ a b i =
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
  a.(0ul) <- b0 -^ a0;
  a.(1ul) <- b1 -^ a1;
  a.(2ul) <- b2 -^ a2;
  a.(3ul) <- b3 -^ a3;
  a.(4ul) <- b4 -^ a4;
  let h1 = ST.get() in
  cut (as_seq h1 a == fdifference_spec_unrolled (as_seq h0 a) (as_seq h0 b));
  lemma_fdifference_spec_equivalence (as_seq h0 a) (as_seq h0 b)
