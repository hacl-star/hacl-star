module Impl.Kyber2.Arithmetic.Sums

//open FStar.Tactics.Typeclasses

//open Lib.Arithmetic.Group
//open Lib.Arithmetic.Ring

module Group = Impl.Kyber2.Group
module MGroup = Impl.Kyber2.GroupMontgomery

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST

module ST = FStar.HyperStack.ST
module Buf = Lib.Buffer
module Seq = Lib.Sequence
open Lib.Sequence

#reset-options "--z3rlimit 300 --max_fuel 1 --max_ifuel 1"

let sum_n #n l output =
  let h0 = ST.get () in
  output.(size 0) <- Group.zero_t;
  Lib.Arithmetic.Sums.sum_n_zero_elements_is_id #Spec.Kyber2.Group.t #Spec.Kyber2.Group.monoid_plus_t (Seq.sub h0.[|l|] 0 0);
  Lib.Loops.for (size 0) n
    (fun h i ->
      (live h l /\ live h output /\ Buf.disjoint l output /\ h.[|output|].[0] == Lib.Arithmetic.Sums.sum_n #Spec.Kyber2.Group.t #Spec.Kyber2.Group.monoid_plus_t (Seq.sub h.[|l|] 0 i) /\ modifies1 output h0 h))
    (fun i ->
      let h = ST.get () in
      Lib.Arithmetic.Sums.sum_n_simple_lemma2 #Spec.Kyber2.Group.t #Spec.Kyber2.Group.monoid_plus_t (Seq.sub h.[|l|] 0 (v i + 1));
    eq_intro (Seq.sub h.[|l|] 0 (v i)) (Seq.sub (Seq.sub h.[|l|] 0 (v i + 1)) 0 (v i));
    output.(size 0) <- Group.plus_t (output.(size 0)) l.(i));
  let h1 = ST.get () in
  eq_intro (Seq.sub h1.[|l|] 0 (v n)) h1.[|l|]

#reset-options "--z3rlimit 500 --max_fuel 1 --max_ifuel 1"

let sum_n_montgomery #n l output =
  let h0 = ST.get () in
  output.(size 0) <- MGroup.zero_m;
  assert_norm(MGroup.to_t MGroup.zero_m == Group.zero_t);
  Lib.Arithmetic.Sums.sum_n_zero_elements_is_id #Spec.Kyber2.Group.t #Spec.Kyber2.Group.monoid_plus_t (Seq.sub (Seq.map MGroup.to_t h0.[|l|]) 0 0);
  Lib.Loops.for (size 0) n
    (fun h i ->
      (live h l /\ live h output /\ Buf.disjoint l output /\ MGroup.to_t (h.[|output|].[0]) == Lib.Arithmetic.Sums.sum_n #Spec.Kyber2.Group.t #Spec.Kyber2.Group.monoid_plus_t (Seq.sub (Seq.map MGroup.to_t h.[|l|]) 0 i) /\ modifies1 output h0 h))
    (fun i ->
      let h = ST.get () in
      Lib.Arithmetic.Sums.sum_n_simple_lemma2 #Spec.Kyber2.Group.t #Spec.Kyber2.Group.monoid_plus_t (Seq.sub (Seq.map MGroup.to_t h.[|l|]) 0 (v i + 1));
      eq_intro (Seq.sub (Seq.map MGroup.to_t h.[|l|]) 0 (v i)) (Seq.sub (Seq.sub (Seq.map MGroup.to_t h.[|l|]) 0 (v i + 1)) 0 (v i));
      output.(size 0) <- MGroup.plus_m (output.(size 0)) l.(i));
  let h1 = ST.get () in
  eq_intro (Seq.sub (Seq.map MGroup.to_t h1.[|l|]) 0 (v n)) (Seq.map MGroup.to_t h1.[|l|])

#reset-options "--z3rlimit 400 --max_fuel 1 --max_ifuel 1"

let sum_n_cbd l output =
  let h0 = ST.get () in
  output.(size 0) <- (i16 0);
  Lib.Arithmetic.Sums.sum_n_zero_elements_is_id #Spec.Kyber2.Group.t #Spec.Kyber2.Group.monoid_plus_t (Seq.sub (Seq.map Group.int16_to_t (Seq.map to_i16 h0.[|l|])) 0 0);
  Lib.Loops.for (size 0) (size params_eta)
    (fun h i ->
      (live h l /\ live h output /\ Buf.disjoint l output /\ sint_v (h.[|output|].[0]) >= 0 /\ sint_v (h.[|output|].[0]) <= i /\ Group.int16_to_t (h.[|output|].[0]) == Lib.Arithmetic.Sums.sum_n #Spec.Kyber2.Group.t #Spec.Kyber2.Group.monoid_plus_t (Seq.sub (Seq.map Group.int16_to_t (Seq.map to_i16 h.[|l|])) 0 i) /\ modifies1 output h0 h))
    (fun i ->
      let h = ST.get () in
      Lib.Arithmetic.Sums.sum_n_simple_lemma2 #Spec.Kyber2.Group.t #Spec.Kyber2.Group.monoid_plus_t (Seq.sub (Seq.map Group.int16_to_t (Seq.map to_i16 h.[|l|])) 0 (v i + 1));
      eq_intro (Seq.sub (Seq.map Group.int16_to_t (Seq.map to_i16 h.[|l|])) 0 (v i)) (Seq.sub (Seq.sub (Seq.map Group.int16_to_t (Seq.map to_i16 h.[|l|])) 0 (v i + 1)) 0 (v i));
      assert_norm(params_eta < maxint S16);
      assert_norm(v i +1 < maxint S16);
      assert_norm(minint S16 <= 0);
      assert(sint_v h.[|output|].[0] + uint_v h.[|l|].[v i] <= (v i) + 1);
      assert(sint_v h.[|output|].[0] + uint_v h.[|l|].[v i] >= 0);
      assert(range (sint_v h.[|output|].[0] + uint_v h.[|l|].[v i]) S16);
      let a:(a:int16{range (v h.[|output|].[0] + v a) S16}) = to_i16 l.(i) in
      let b:(b:int16{v b == v h.[|output|].[0]}) = output.(size 0) in
      output.(size 0) <- b +! a);
  let h1 = ST.get () in
  eq_intro (Seq.sub (Seq.map Group.int16_to_t (Seq.map to_i16 h1.[|l|])) 0 params_eta) (Seq.map Group.int16_to_t (Seq.map to_i16 h1.[|l|]))
