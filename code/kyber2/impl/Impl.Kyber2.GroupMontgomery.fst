module Impl.Kyber2.GroupMontgomery

open Lib.Arithmetic.Group
open Lib.IntTypes
open FStar.Math.Lemmas
open Lib.ModularArithmetic.Lemmas
open FStar.Mul
open Spec.Kyber2.Params
open Spec.Kyber2.Reduce
open Spec.Powtwo.Lemmas
open Spec.Kyber2.Lemmas

module Group = Impl.Kyber2.Group
module MGroup = Spec.Kyber2.GroupMontgomery
module SpecGroup = Spec.Kyber2.Group

type montgomery_t = y:int16{ sint_v y <= params_q /\ sint_v y >= - params_q}

inline_for_extraction
let zero_m : montgomery_t = MGroup.zero_m

inline_for_extraction
let one_m : montgomery_t = MGroup.one_m

#reset-options "--z3rlimit 500 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let from_t (x:Group.t) : Pure montgomery_t (requires True) (ensures fun r -> r == MGroup.from_t x) =
  montgomery_reduce_int32 ((to_i32 x) *! (i32 params_mont2))

let from_cbd (x:uint16{0 <= uint_v x /\ uint_v x < 19* params_q}) : Pure montgomery_t (requires True) (ensures fun r -> sint_v r % params_q == sint_v (MGroup.from_t (SpecGroup.uint16_to_t x)) % params_q) =
  assert_norm(19 * params_q * params_mont2 < params_q * pow2 15);
  assert_norm(19 * params_q * params_mont2 < pow2 31);
  FStar.Math.Lemmas.lemma_mult_le_right params_mont2 (uint_v x) (19*params_q);
  FStar.Math.Lemmas.lemma_mult_le_right params_mont2 0 (uint_v x);
  FStar.Math.Lemmas.modulo_lemma (uint_v x % params_q) params_q;
  let r2 () : GTot montgomery_t = MGroup.from_t (Group.uint16_to_t x) in
  assert((sint_v (r2 ()) * pow2 params_logr) % params_q = (SpecGroup.v (Group.uint16_to_t x) * params_mont2) % params_q);
  FStar.Math.Lemmas.lemma_mod_mul_distr_l (SpecGroup.v (Group.uint16_to_t x)) params_mont2 params_q;
  FStar.Math.Lemmas.lemma_mod_mul_distr_l (uint_v x) params_mont2 params_q;
  assert((sint_v (r2 ()) * pow2 params_logr) % params_q = (uint_v x * params_mont2) % params_q);
  let r () : GTot montgomery_t = montgomery_reduce_int32 ((to_i32 x) *! (i32 params_mont2)) in
  assert((sint_v (r ()) * pow2 params_logr) % params_q = (uint_v x * params_mont2) % params_q);
  MGroup.lemma_equality1 (sint_v (r ())) (sint_v (r2 ()));
  montgomery_reduce_int32 ((to_i32 x) *! (i32 params_mont2))

#reset-options "--z3rlimit 500 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"


let to_t (x:montgomery_t) : Pure Group.t (requires True) (ensures fun r -> r == MGroup.to_t #r (from_t r)) =
  let mr = montgomery_reduce_int32 (to_i32 x) in
  csubq_int16 (mr +! i16 params_q)

let int16_to_t (x:int16) : Pure Group.t (requires True) (ensures fun r -> r == MGroup.to_t #r (from_t r)) =
  FStar.Math.Lemmas.pow2_lt_compat 31 15;
  assert_norm(range (sint_v x) S32);
  let mr = montgomery_reduce_int32 (to_i32 x) in
  csubq_int16 (mr +! i16 params_q)

let int32_to_t (x:int32) : Pure Group.t (requires (- params_q * pow2 (params_logr-1) <= sint_v x /\ sint_v x < params_q * pow2 (params_logr -1))) (ensures fun r -> r == MGroup.to_t #r (from_t r)) =
  FStar.Math.Lemmas.pow2_lt_compat 31 15;
  assert_norm(range (sint_v x) S32);
  let mr = montgomery_reduce_int32 x in
  csubq_int16 (mr +! i16 params_q)

let to_t_lemma (x:montgomery_t) : Lemma (ensures (sint_v x % params_q = (SpecGroup.v (to_t x) * pow2 params_logr) % params_q /\ to_t x == MGroup.to_t #(to_t x) x)) =
  let mr = montgomery_reduce_int32 (to_i32 x) in
  let r = to_t x in
  assert((sint_v mr * pow2 params_logr) % params_q = sint_v x % params_q);
  MGroup.lemma_equality3 (sint_v mr) (sint_v x);
  lemma_mod_plus (sint_v mr) 1 params_q;
  MGroup.lemma_equality3 (sint_v r) (sint_v x)

let from_cbd_to_t_lemma (x:uint16{0 <= uint_v x /\ uint_v x < 19* params_q}) : Lemma (to_t (from_cbd x) == SpecGroup.uint16_to_t x) =
  to_t_lemma (from_cbd x);
  MGroup.lemma_equality1 (SpecGroup.v (to_t (from_cbd x))) (SpecGroup.v (SpecGroup.uint16_to_t x));
  FStar.Math.Lemmas.modulo_lemma (SpecGroup.v (to_t (from_cbd x))) params_q;
  FStar.Math.Lemmas.modulo_lemma (SpecGroup.v (to_t (SpecGroup.uint16_to_t x))) params_q

let int16_to_t_lemma (x:int16) : Lemma (ensures (sint_v x % params_q = (SpecGroup.v (int16_to_t x) * pow2 params_logr) % params_q)) =
  FStar.Math.Lemmas.pow2_lt_compat 31 15;
  assert_norm(sint_v x @%. S32 == sint_v x);
  let mr = montgomery_reduce_int32 (to_i32 x) in
  let r = int16_to_t x in
  assert((sint_v mr * pow2 params_logr) % params_q = sint_v x % params_q);
  MGroup.lemma_equality3 (sint_v mr) (sint_v x);
  lemma_mod_plus (sint_v mr) 1 params_q;
  MGroup.lemma_equality3 (sint_v r) (sint_v x)

let int32_to_t_lemma (x:int32) : Lemma (requires (- params_q * pow2 (params_logr-1) <= sint_v x /\ sint_v x < params_q * pow2 (params_logr -1))) (ensures (sint_v x % params_q = (SpecGroup.v (int32_to_t x) * pow2 params_logr) % params_q)) =
  FStar.Math.Lemmas.pow2_lt_compat 31 15;
  assert_norm(sint_v x @%. S32 == sint_v x);
  let mr = montgomery_reduce_int32 (to_i32 x) in
  let r = int32_to_t x in
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

let plus_lemma_int32 (x:int32) (y:int32) (z:int32) : Lemma (requires (range (sint_v x + sint_v y) S32 /\ - params_q * pow2 (params_logr-1) <= sint_v x /\ sint_v x < params_q * pow2 (params_logr -1)) /\ (- params_q * pow2 (params_logr-1) <= sint_v y /\ sint_v y < params_q * pow2 (params_logr -1)) /\ (- params_q * pow2 (params_logr-1) <= sint_v x + sint_v y /\ sint_v x + sint_v y < params_q * pow2 (params_logr -1)) /\ sint_v z == sint_v x + sint_v y) (ensures (int32_to_t z == Group.plus_t (int32_to_t x) (int32_to_t y))) =
  modulo_distributivity (sint_v x) (sint_v y) params_q;
  int32_to_t_lemma z;
  int32_to_t_lemma x;
  int32_to_t_lemma y;
  modulo_distributivity (SpecGroup.v (int32_to_t x) * pow2 params_logr) (SpecGroup.v (int32_to_t y) * pow2 params_logr) params_q;
  assert((SpecGroup.v (int32_to_t z) * pow2 params_logr) % params_q = ((SpecGroup.v (int32_to_t x) * pow2 params_logr) + (SpecGroup.v (int32_to_t y) * pow2 params_logr)) % params_q);
  distributivity_add_left (SpecGroup.v (int32_to_t x)) (SpecGroup.v (int32_to_t y)) (pow2 params_logr);
  MGroup.lemma_equality1 (SpecGroup.v (int32_to_t z)) (SpecGroup.v (int32_to_t x) + SpecGroup.v (int32_to_t y));
  modulo_lemma (SpecGroup.v (int32_to_t z)) params_q;
  SpecGroup.plus_lemma_t (int32_to_t x) (int32_to_t y)

let plus_lemma_int16 (x:int16) (y:int16) (z:int16): Lemma (requires (range (sint_v x + sint_v y) S16 /\ sint_v z == sint_v x + sint_v y)) (ensures (int16_to_t (x +! y) == Group.plus_t (int16_to_t x) (int16_to_t y))) =
  modulo_distributivity (sint_v x) (sint_v y) params_q;
  int16_to_t_lemma z;
  int16_to_t_lemma x;
  int16_to_t_lemma y;
  modulo_distributivity (SpecGroup.v (int16_to_t x) * pow2 params_logr) (SpecGroup.v (int16_to_t y) * pow2 params_logr) params_q;
  assert((SpecGroup.v (int16_to_t z) * pow2 params_logr) % params_q = ((SpecGroup.v (int16_to_t x) * pow2 params_logr) + (SpecGroup.v (int16_to_t y) * pow2 params_logr)) % params_q);
  distributivity_add_left (SpecGroup.v (int16_to_t x)) (SpecGroup.v (int16_to_t y)) (pow2 params_logr);
  MGroup.lemma_equality1 (SpecGroup.v (int16_to_t z)) (SpecGroup.v (int16_to_t x) + SpecGroup.v (int16_to_t y));
  modulo_lemma (SpecGroup.v (int16_to_t z)) params_q;
  SpecGroup.plus_lemma_t (int16_to_t x) (int16_to_t y)

let plus_lemma_int16_2 (x:int16) (y:montgomery_t) (z:int16): Lemma (requires (range (sint_v x + sint_v y) S16 /\ sint_v z == sint_v x + sint_v y)) (ensures (int16_to_t (x +! y) == Group.plus_t (int16_to_t x) (to_t y))) = plus_lemma_int16 x y z

let plus_lemma_int32_2 (x:int32) (y:montgomery_t) (z:int32) : Lemma (requires (range (sint_v x + sint_v y) S32 /\ - params_q * pow2 (params_logr-1) <= sint_v x /\ sint_v x < params_q * pow2 (params_logr -1)) /\ (- params_q * pow2 (params_logr-1) <= sint_v x + sint_v y /\ sint_v x + sint_v y < params_q * pow2 (params_logr -1) /\ sint_v z == sint_v x + sint_v y)) (ensures (int32_to_t (x +! to_i32 y) == Group.plus_t (int32_to_t x) (to_t y))) = plus_lemma_int32 x (to_i32 y) z

#reset-options "--z3rlimit 2000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let mul_range_lemma_m (x:int16{sint_v x > - pow2 15}) (y:montgomery_t) : Lemma (range (sint_v x * sint_v y) S32 /\  - params_q * pow2 (params_logr-1) <= sint_v x * sint_v y /\ sint_v x * sint_v y < params_q * pow2 (params_logr -1) ) =
  if (sint_v x >= 0) then begin
    lemma_mult_le_left (sint_v x) (sint_v y) (params_q);
    lemma_mult_le_left (sint_v x) (- params_q) (sint_v y);
    assert(sint_v x * (- params_q) <= sint_v x * sint_v y /\ sint_v x * sint_v y <= sint_v x * params_q);
    swap_neg_mul (sint_v x) params_q;
    lemma_mult_le_right (params_q) (- pow2 15) (- sint_v x);
    lemma_mult_le_right (params_q) (sint_v x) (pow2 15 -1);
    assert_norm(params_q * pow2 15 < pow2 31);
    assert(range (sint_v x * sint_v y) S32)
    end
  else begin
    lemma_mult_le_left (- sint_v x) (- sint_v y) (params_q);
    lemma_mult_le_left (- sint_v x) (- params_q) (sint_v y);
    assert(- sint_v x * (- params_q) <= sint_v x * sint_v y /\ sint_v x * sint_v y <= - sint_v x * params_q);
    swap_neg_mul (- sint_v x) (params_q);
    lemma_mult_le_right (params_q) (- pow2 15) (- sint_v x);
    lemma_mult_le_right (params_q) ( - sint_v x) (pow2 15 - 1);
    assert_norm(params_q * pow2 15 < pow2 31);
    assert(range (sint_v x * sint_v y) S32)
    end

let mul_range_lemma (x:int16) (y:int16) : Lemma (range (sint_v x * sint_v y) S32) =
  if (sint_v x >= 0) then begin
    lemma_mult_le_left (sint_v x) (sint_v y) (pow2 15);
    lemma_mult_le_left (sint_v x) (- pow2 15) (sint_v y);
    assert(sint_v x * (- pow2 15) <= sint_v x * sint_v y /\ sint_v x * sint_v y <= sint_v x * pow2 15);
    swap_neg_mul (sint_v x) (pow2 15);
    lemma_mult_le_right (pow2 15) (- pow2 15) (- sint_v x);
    lemma_mult_le_right (pow2 15) (sint_v x) (pow2 15);
    pow2_plus 15 15;
    pow2_lt_compat 31 30;
    assert(range (sint_v x * sint_v y) S32)
    end
  else begin
    lemma_mult_le_left (- sint_v x) (- sint_v y) (pow2 15);
    lemma_mult_le_left (- sint_v x) (- pow2 15) (sint_v y);
    assert(- sint_v x * (- pow2 15) <= sint_v x * sint_v y /\ sint_v x * sint_v y <= - sint_v x * pow2 15);
    swap_neg_mul (- sint_v x) (pow2 15);
    lemma_mult_le_right (pow2 15) (- pow2 15) (- sint_v x);
    lemma_mult_le_right (pow2 15) (sint_v x) (pow2 15);
    pow2_plus 15 15;
    pow2_lt_compat 31 30;
    assert(range (sint_v x * sint_v y) S32)
    end

let mul_m (x:montgomery_t) (y:montgomery_t) : Pure montgomery_t (requires True) (ensures fun r -> to_t r == Group.mul_t (to_t x) (to_t y)) =
  assert_norm(-pow2 15 < - params_q);
  mul_range_lemma_m x y;
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

let mul_m_int16 (x:int16{sint_v x > pow2 15}) (y:montgomery_t) : Pure montgomery_t (requires True) (ensures fun r -> to_t r == Group.mul_t (int16_to_t x) (to_t y)) =
  assert_norm(-pow2 15 < - params_q);
  mul_range_lemma_m x y;
  let mr () : GTot montgomery_t = montgomery_reduce_int32 ((to_i32 x) *! (to_i32 y)) in
  mul_lemma (to_i32 x) (to_i32 y);
  assert((sint_v (mr ()) * pow2 params_logr) % params_q = (sint_v x * sint_v y) % params_q);
  lemma_mod_mul_distr_l (sint_v x) (sint_v y) params_q;
  let x' () : GTot Group.t = int16_to_t x in
  to_t_lemma x;
  lemma_mod_mul_distr_l (SpecGroup.v (x' ()) * pow2 params_logr) (sint_v y) params_q;
  paren_mul_right (SpecGroup.v (x' ())) (pow2 params_logr) (sint_v y);
  swap_mul (pow2 params_logr) (sint_v y);
  paren_mul_right (SpecGroup.v (x' ())) (sint_v y) (pow2 params_logr);
  lemma_mod_mul_distr_l (SpecGroup.v (x' ()) * sint_v y) (pow2 params_logr) params_q;
  MGroup.lemma_equality1 (sint_v (mr ())) (SpecGroup.v (x' ()) * sint_v y);
  lemma_mod_mul_distr_r (SpecGroup.v (x' ())) (sint_v y) params_q;
  let y' () : GTot Group.t = int16_to_t y in
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
