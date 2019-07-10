module Impl.Kyber2.GroupMontgomery

open Lib.Arithmetic.Group
open Lib.IntTypes
open FStar.Math.Lemmas
open Lib.ModularArithmetic.Lemmas
open FStar.Mul
open Spec.Kyber2.Params
open Spec.Kyber2.Reduce

module Group = Impl.Kyber2.Group
module MGroup = Spec.Kyber2.GroupMontgomery
module SpecGroup = Spec.Kyber2.Group

type montgomery_t = y:int16{ sint_v y <= params_q /\ sint_v y >= - params_q}

inline_for_extraction
let zero_m : montgomery_t = MGroup.zero_m

inline_for_extraction
let one_m : montgomery_t = MGroup.one_m

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let from_t (x:Group.t) : Pure montgomery_t (requires True) (ensures fun r -> r == MGroup.from_t x) =
  montgomery_reduce_int32 ((to_i32 x) *! (i32 params_mont2))

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"


let to_t (x:montgomery_t) : Pure Group.t (requires True) (ensures fun r -> r == MGroup.to_t #r (from_t r)) =
  let mr = montgomery_reduce_int32 (to_i32 x) in
  csubq_int16 (mr +! i16 params_q)

let to_t_lemma (x:montgomery_t) : Lemma (ensures (sint_v x % params_q = (SpecGroup.v (to_t x) * pow2 params_logr) % params_q /\ to_t x == MGroup.to_t #(to_t x) x)) =
  let mr = montgomery_reduce_int32 (to_i32 x) in
  let r = to_t x in
  assert((sint_v mr * pow2 params_logr) % params_q = sint_v x % params_q);
  MGroup.lemma_equality3 (sint_v mr) (sint_v x);
  lemma_mod_plus (sint_v mr) 1 params_q;
  MGroup.lemma_equality3 (sint_v r) (sint_v x)


#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq' --query_stats"

let plus_m (x:montgomery_t) (y:montgomery_t) : Pure montgomery_t (requires True) (ensures fun r -> to_t r == Group.plus_t (to_t x) (to_t y)) =
  assert_norm (2 * params_q < maxint S16 /\ - 2 * params_q > minint S16);
  assert_norm(range (sint_v x + sint_v y) S16);
  let br () : GTot montgomery_t = barrett_reduce_int16 (x +! y) in
  assert(sint_v (br ()) % params_q = (sint_v x + sint_v y) % params_q);
  modulo_distributivity (sint_v x) (sint_v y) params_q;
  to_t_lemma (br ());
  to_t_lemma x;
  to_t_lemma y;
  modulo_distributivity (SpecGroup.v (to_t x) * pow2 params_logr) (SpecGroup.v (to_t y) * pow2 params_logr) params_q;
  assert((SpecGroup.v (to_t (br ())) * pow2 params_logr) % params_q = ((SpecGroup.v (to_t x) * pow2 params_logr) + (SpecGroup.v (to_t y) * pow2 params_logr)) % params_q);
  distributivity_add_left (SpecGroup.v (to_t x)) (SpecGroup.v (to_t y)) (pow2 params_logr);
  MGroup.lemma_equality1 (SpecGroup.v (to_t (br ()))) (SpecGroup.v (to_t x) + SpecGroup.v (to_t y));
  modulo_lemma (SpecGroup.v (to_t (br ()))) params_q;
  SpecGroup.plus_lemma_t (to_t x) (to_t y);
  barrett_reduce_int16 (x +! y)

#reset-options "--z3rlimit 2000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let mul_m (x:montgomery_t) (y:montgomery_t) : Pure montgomery_t (requires True) (ensures fun r -> to_t r == Group.mul_t (to_t x) (to_t y)) =
  assert_norm (range (sint_v x) S32);
  assert_norm (range (sint_v y) S32);
  assert_norm (sint_v x * sint_v y <= params_q * params_q);
  assert_norm ( - params_q * params_q <= sint_v x * sint_v y);
  assert_norm ( params_q * params_q < params_q * pow2 (params_logr-1));
  assert_norm ( - params_q * pow2 (params_logr - 1) <= - params_q * params_q);
  assert_norm ( params_q * params_q <= maxint S32);
  assert_norm ( minint S32 <= - params_q * params_q);
  assert (range (sint_v x * sint_v y) S32);
  assert_norm ( - params_q * pow2 (params_logr-1) <= sint_v x * sint_v y /\ sint_v x * sint_v y < params_q * pow2 (params_logr -1));
  let mr () : GTot montgomery_t = montgomery_reduce_int32 ((to_i32 x) *! (to_i32 y)) in
  mul_lemma (to_i32 x) (to_i32 y);
  assert((sint_v (mr ()) * pow2 params_logr) % params_q = (sint_v x * sint_v y) % params_q);
  lemma_mod_mul_distr_l (sint_v x) (sint_v y) params_q;
  let x' () : GTot Group.t = to_t x in
  to_t_lemma x;
  lemma_mod_mul_distr_l (SpecGroup.v (x' ()) * pow2 params_logr) (sint_v y) params_q;
  paren_mul_right (SpecGroup.v (x' ())) (pow2 params_logr) (sint_v y);
  swap_mul (pow2 params_logr) (sint_v y);
  paren_mul_right (SpecGroup.v (x' ())) (sint_v y) (pow2 params_logr);
  lemma_mod_mul_distr_l (SpecGroup.v (x' ()) * sint_v y) (pow2 params_logr) params_q;
  MGroup.lemma_equality1 (sint_v (mr ())) (SpecGroup.v (x' ()) * sint_v y);
  lemma_mod_mul_distr_r (SpecGroup.v (x' ())) (sint_v y) params_q;
  let y' () : GTot Group.t = to_t y in
  let mr' () : GTot Group.t = to_t (mr ()) in
  to_t_lemma y;
  to_t_lemma (mr ());
  lemma_mod_mul_distr_r (SpecGroup.v (x' ())) (SpecGroup.v (y' ()) * pow2 params_logr) params_q;
  paren_mul_right (SpecGroup.v (x' ())) (SpecGroup.v (y' ())) (pow2 params_logr);
  MGroup.lemma_equality1 (SpecGroup.v (mr' ())) (SpecGroup.v (x' ()) * SpecGroup.v (y' ()));
  SpecGroup.mul_lemma_t (x' ()) (y' ());
  modulo_lemma (SpecGroup.v (mr' ())) params_q;
  montgomery_reduce_int32 ((to_i32 x) *! (to_i32 y))

let opp_m (x:montgomery_t) : Pure montgomery_t (requires True) (ensures fun r -> to_t r == Group.opp_t (to_t x)) =
  assert_norm (range (-sint_v x) S16);
  let x' () : GTot Group.t = to_t x in
  SpecGroup.opp_lemma_t (x' ());
  to_t_lemma x;
  lemma_mod_sub_distr 0 (sint_v x) params_q;
  lemma_mod_sub_distr 0 (SpecGroup.v (x' ()) * pow2 params_logr) params_q;
  lemma_mod_mul_distr_l (- SpecGroup.v (x' ())) (pow2 params_logr) params_q;
  to_t_lemma (zero_m -! x);
  MGroup.lemma_equality1 (SpecGroup.v (to_t (zero_m -! x))) (- SpecGroup.v (x' ()));
  zero_m -! x

#reset-options "--z3rlimit 2000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let rec exp_m (x:montgomery_t) (n:size_t) : Pure (montgomery_t) (requires True) (ensures fun r -> to_t r == Group.exp_t (to_t x) n) (decreases (v n)) =
  if (n =. (size 0)) then (assert_norm(to_t one_m == Group.one_t); one_m)
  else
  let b = exp_m x (n /. (size 2)) in
  let b2 = mul_m b b in
  if (n %. (size 2) =. (size 0)) then b2 else mul_m x b2
