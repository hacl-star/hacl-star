module Spec.Kyber2.Group

open Lib.Arithmetic.Group
open Lib.IntTypes
open FStar.Math.Lemmas
open Lib.ModularArithmetic.Lemmas
open FStar.Mul
open Spec.Kyber2.Params
open Spec.Kyber2.Reduce

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --print_universes --using_facts_from '* -FStar.Seq'"

type t = x:int16{sint_v x >= 0 /\ sint_v x < params_q}

inline_for_extraction
let mk_t (x:nat{x<params_q}) : t = assert_norm (params_q < maxint S16); i16 x

inline_for_extraction
let zero_t = mk_t 0

inline_for_extraction
let one_t = mk_t 1

let v (x:t) : (y:nat{y< params_q}) = sint_v x

let v_injective (a:t) : Lemma (mk_t (v a) == a) = ()

inline_for_extraction
let int16_to_t (x:int16) : Pure t (requires True) (ensures fun r -> v r == sint_v x % params_q) =
  assert_norm (-params_q > minint S16);
  csubq_int16 (barrett_reduce_int16 x)


#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1 --print_universes --using_facts_from '* -FStar.Seq'"

inline_for_extraction
let uint16_to_t (x:uint16) : Pure t (requires True) (ensures fun r -> v r == uint_v x % params_q) =
  assert (sint_v (division_by_q_int32 (to_i32 x)) == uint_v x / params_q);
  euclidean_division_definition (uint_v x) params_q;
  assert (sint_v (to_i32 x) - (sint_v (division_by_q_int32 (to_i32 x)) * params_q) == uint_v x % params_q);
  assert_norm (range (uint_v x % params_q) S16);
  to_i16 ((to_i32 x) -! (division_by_q_int32 (to_i32 x) *! (i32 params_q)))

inline_for_extraction
let plus_t (x:t) (y:t) : t =
  assert_norm (0 > minint S16 /\ 2 * params_q < maxint S16);
  csubq_int16 (x +! y)

let plus_lemma_t (x:t) (y:t) : Lemma (v (plus_t x y) = (v x + v y) % params_q) =
  assert_norm (0 > minint S16 /\ 2 * params_q < maxint S16)

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --print_universes --using_facts_from '* -FStar.Seq'"

inline_for_extraction
let mul_t (x:t) (y:t) : t =
  assert_norm ( 0 <= v x * v y);
  assert_norm (v x * v y <= v x * params_q);
  assert_norm (v x * params_q < params_q * params_q);
  assert (v x * v y < params_q * params_q);
  assert_norm (params_q * params_q <= maxint S32);
  assert (range (v x * v y) S32);
  int16_to_t (montgomery_reduce_int32 (Lib.IntTypes.mul (to_i32 (montgomery_reduce_int32 (Lib.IntTypes.mul (to_i32 x) (to_i32 y)))) (i32 params_mont2)))

#reset-options "--z3rlimit 1000 --max_fuel 0 --max_ifuel 0 --print_universes --using_facts_from '* -FStar.Seq'"

let mul_lemma_t (x:t) (y:t) : Lemma (v (mul_t x y) = (v x * v y) % params_q) =
  assert_norm (0 > minint S32 /\ 0 > minint S16 /\ 2*params_q < maxint S16 /\ params_q * params_q < maxint S32);
  assert_norm ( 0 <= v x * v y);
  assert_norm (v x * v y <= v x * params_q);
  assert_norm (v x * params_q < params_q * params_q);
  assert (v x * v y < params_q * params_q);
  let mr1:int16 = montgomery_reduce_int32 (Lib.IntTypes.mul (to_i32 x) (to_i32 y)) in
  assert ((sint_v mr1 * pow2 params_logr) % params_q = (v x * v y) % params_q);
  let a:int32 = Lib.IntTypes.mul (to_i32 mr1) (i32 params_mont2) in
  assert (sint_v a = sint_v mr1 * params_mont2);
  let mr2:int16 = montgomery_reduce_int32 a in
  assert ((sint_v mr2 * pow2 params_logr) % params_q = (sint_v mr1 * params_mont2) % params_q);
  lemma_mod_mul_distr_l (sint_v mr2 * pow2 params_logr) params_rinv params_q;
  paren_mul_right (sint_v mr2) (pow2 params_logr) params_rinv;
  assert_norm (((pow2 params_logr) * params_rinv) % params_q = 1);
  lemma_mod_mul_distr_r (sint_v mr2) ((pow2 params_logr) * params_rinv) params_q;
  assert ((((sint_v mr2 * pow2 params_logr) % params_q) * params_rinv) % params_q = sint_v mr2 % params_q);
  assert_norm (params_q > 0);
  lemma_mod_mul_distr_l (sint_v mr1 * params_mont2) params_rinv params_q;
  paren_mul_right (sint_v mr1) params_mont2 params_rinv;
  lemma_mod_mul_distr_r (sint_v mr1) (params_mont2 * params_rinv) params_q;
  assert_norm ((params_mont2 * params_rinv) % params_q = (pow2 params_logr) % params_q );
  lemma_mod_mul_distr_r (sint_v mr1) (pow2 params_logr) params_q;
  assert ((((sint_v mr1 * params_mont2) % params_q) * params_rinv) % params_q = (sint_v mr1 * pow2 params_logr) % params_q);
  assert (sint_v mr2 % params_q = (sint_v mr1 * pow2 params_logr) % params_q);
  assert (sint_v mr2 % params_q = (v x * v y) % params_q)

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --print_universes --using_facts_from '* -FStar.Seq'"

let lemma_plus_assoc_t (x:t) (y:t) (z:t) : Lemma (plus_t (plus_t x y) z == plus_t x (plus_t y z)) =
  plus_lemma_t x y;
  plus_lemma_t y z;
  plus_lemma_t (plus_t x y) z;
  plus_lemma_t x (plus_t y z);
  modular_add_associativity_lemma #params_q (v x) (v y) (v z)

let lemma_mul_assoc_t (x:t) (y:t) (z:t) : Lemma (mul_t (mul_t x y) z == mul_t x (mul_t y z)) =
  mul_lemma_t x y;
  mul_lemma_t y z;
  mul_lemma_t (mul_t x y) z;
  mul_lemma_t x (mul_t y z);
  modular_mul_associativity_lemma #params_q (v x) (v y) (v z)

let lemma_zero1_t (x:t) : Lemma (plus_t zero_t x == x) =
  plus_lemma_t zero_t x

let lemma_zero2_t (x:t) : Lemma (plus_t x zero_t == x) =
  plus_lemma_t x zero_t

let lemma_one1_t (x:t) : Lemma (mul_t one_t x == x) =
  mul_lemma_t one_t x

let lemma_one2_t (x:t) : Lemma (mul_t x one_t == x) =
  mul_lemma_t x one_t

instance monoid_plus_t : monoid t =
  {
    id = zero_t;
    op = plus_t;
    lemma_assoc = lemma_plus_assoc_t;
    lemma_id1 = lemma_zero1_t;
    lemma_id2 = lemma_zero2_t;
  }

instance monoid_mul_t : monoid t =
  {
    id = one_t;
    op = mul_t;
    lemma_assoc = lemma_mul_assoc_t;
    lemma_id1 = lemma_one1_t;
    lemma_id2 = lemma_one2_t;
  }

inline_for_extraction
let opp_t (x:t) : t =
  assert_norm(params_q < maxint S16);
  csubq_int16 (Lib.IntTypes.sub (i16 params_q) x)

let opp_lemma_t (x:t) : Lemma (v (opp_t x) = (- v x) % params_q) =
  assert_norm(params_q < maxint S16);
  sub_lemma (i16 params_q) x;
  if (v x = 0) then assert (i16 params_q -! x == i16 params_q) else
  lemma_mod_sub_1 (v x) params_q

let lemma_plus_opp1_t (x:t) : Lemma (plus_t x (opp_t x) == zero_t) =
  opp_lemma_t x;
  plus_lemma_t x (opp_t x)

let lemma_plus_opp2_t (x:t) : Lemma (plus_t (opp_t x) x == zero_t) =
  opp_lemma_t x;
  plus_lemma_t (opp_t x) x

instance group_t : group t =
  {
    m = monoid_plus_t;
    sym = opp_t;
    lemma_sym1 = lemma_plus_opp1_t;
    lemma_sym2 = lemma_plus_opp2_t;
  }

let lemma_plus_swap_t (x:t) (y:t) : Lemma (plus_t x y == plus_t y x) =
  plus_lemma_t x y;
  plus_lemma_t y x

instance abelian_group_t : abelian_group t =
  {
    g = group_t;
    lemma_swap = lemma_plus_swap_t;
  }

