module Impl.Kyber2.Arithmetic.Sums

//open FStar.Tactics.Typeclasses

//open Lib.Arithmetic.Group
//open Lib.Arithmetic.Ring

module Group = Impl.Kyber2.Group
module MGroup = Impl.Kyber2.GroupMontgomery

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST

open FStar.Mul
open FStar.Math.Lemmas
open Spec.Powtwo.Lemmas
open Spec.Kyber2.Lemmas
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

#reset-options "--z3rlimit 500 --max_fuel 1 --max_ifuel 1"
val sum_n_montgommery_no_plus_m_inner:
  #n:size_t{v n < pow2 (params_logr-1)}
  -> h_:mem
  -> l:lbuffer (MGroup.montgomery_t) n
  -> output:lbuffer (x:int32{- params_q * pow2 (params_logr-1) <= sint_v x /\ sint_v x < params_q * pow2 (params_logr -1)}) (size 1)
  -> i:size_t{0 <= v i /\ v i < v n}
  -> Stack unit (requires fun h -> (live h l /\ live h output /\ Buf.disjoint l output /\ (sint_v h.[|output|].[0] >= - params_q * (v i)) /\ (sint_v h.[|output|].[0] <= params_q * (v i)) /\ MGroup.int32_to_t (h.[|output|].[0]) == Lib.Arithmetic.Sums.sum_n #Spec.Kyber2.Group.t #Spec.Kyber2.Group.monoid_plus_t (Seq.sub (Seq.map MGroup.to_t h.[|l|]) 0 (v i)) /\ modifies1 output h_ h)) (ensures fun h0 _ h1 -> (live h1 l /\ live h1 output /\ Buf.disjoint l output /\ (sint_v h1.[|output|].[0] >= - params_q * (v i + 1)) /\ (sint_v h1.[|output|].[0] <= params_q * (v i + 1)) /\ MGroup.int32_to_t (h1.[|output|].[0]) == Lib.Arithmetic.Sums.sum_n #Spec.Kyber2.Group.t #Spec.Kyber2.Group.monoid_plus_t (Seq.sub (Seq.map MGroup.to_t h1.[|l|]) 0 (v i + 1)) /\ modifies1 output h_ h1))

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --query_stats"

let cast_range a t : Lemma (requires range a t) (ensures a @%. t = a) =
  pow2_le_compat (bits t) (bits t -1);
  pow2_double_mult (bits t - 1);
  cancel_mul_div (pow2 (bits t - 1)) 2;
  assert(a < modulus t);
  if (a>=0) then modulo_lemma a (modulus t)
  else begin
    pow2_double_sum (bits t - 1);
    assert(pow2 (bits t - 1) <= a + modulus t);
    modulo_lemma (a + modulus t) (modulus t);
    lemma_mod_plus a 1 (modulus t)
    end

let sum_n_montgommery_no_plus_m_inner #n h0 l output i =
  let h = ST.get () in
  Lib.Arithmetic.Sums.sum_n_simple_lemma2 #Spec.Kyber2.Group.t #Spec.Kyber2.Group.monoid_plus_t (Seq.sub (Seq.map MGroup.to_t h.[|l|]) 0 (v i + 1));
  eq_intro (Seq.sub (Seq.map MGroup.to_t h.[|l|]) 0 (v i)) (Seq.sub (Seq.sub (Seq.map MGroup.to_t h.[|l|]) 0 (v i + 1)) 0 (v i));
  let k:(x:int32{- params_q * v i <= v x /\ v x <= params_q * v i}) = output.(0ul) in
  assert( v k + v h.[|l|].[v i] <= params_q * (v i + 1) /\ - params_q * (v i + 1) <= v k + v h.[|l|].[v i]);
  assert(range (v k + v h.[|l|].[v i]) S32);
  FStar.Math.Lemmas.lemma_mult_lt_left params_q (v i + 1) (pow2 (params_logr-1));
  let li:(y:MGroup.montgomery_t{range (v k + v y) S32}) = l.(i) in
  assert_norm(range (v li) S32);
  cast_range (v li) S32;
  MGroup.plus_lemma_int32_2 k li (k +! to_i32 li);
  assert(MGroup.int32_to_t (k +! to_i32 li) == Group.plus_t (MGroup.int32_to_t k) (MGroup.to_t li));
  output.(0ul) <- k +! to_i32 li

let sum_n_montgomery_no_plus_m #n l output =
  let h0 = ST.get () in
  output.(size 0) <- i32 0;
  assert_norm(MGroup.int32_to_t (i32 0) == Group.zero_t);
  assert_norm (0 <= params_q * 0 /\ 0 >= - params_q * 0);
  Lib.Arithmetic.Sums.sum_n_zero_elements_is_id #Spec.Kyber2.Group.t #Spec.Kyber2.Group.monoid_plus_t (Seq.sub (Seq.map MGroup.to_t h0.[|l|]) 0 0);
  Lib.Loops.for (size 0) n
    (fun h i ->
      (live h l /\ live h output /\ Buf.disjoint l output /\ (sint_v h.[|output|].[0] >= - params_q * i) /\ (sint_v h.[|output|].[0] <= params_q * i) /\ MGroup.int32_to_t (h.[|output|].[0]) == Lib.Arithmetic.Sums.sum_n #Spec.Kyber2.Group.t #Spec.Kyber2.Group.monoid_plus_t (Seq.sub (Seq.map MGroup.to_t h.[|l|]) 0 i) /\ modifies1 output h0 h))
    (fun i -> sum_n_montgommery_no_plus_m_inner h0 l output i);
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
