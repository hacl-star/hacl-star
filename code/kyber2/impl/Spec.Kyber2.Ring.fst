module Spec.Kyber2.Ring

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring

open Lib.ModularArithmetic.Lemmas
open FStar.Mul
open Spec.Kyber2.Params
open Spec.Kyber2.Group

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --print_universes --using_facts_from '* -FStar.Seq'"

let lemma_distr_left_t (x:t) (y:t) (z:t) : Lemma (mul_t x (plus_t y z) == plus_t (mul_t x y) (mul_t x z)) =
  mul_lemma_t x (plus_t y z);
  plus_lemma_t y z;
  mul_lemma_t x y;
  mul_lemma_t x z;
  plus_lemma_t (mul_t x y) (mul_t x z);
  modular_mul_add_distrib_left_lemma #params_q (v x) (v y) (v z)

let lemma_distr_right_t (x:t) (y:t) (z:t) : Lemma (mul_t (plus_t y z) x == plus_t (mul_t y x) (mul_t z x)) =
  mul_lemma_t (plus_t y z) x;
  plus_lemma_t y z;
  mul_lemma_t y x;
  mul_lemma_t z x;
  plus_lemma_t (mul_t y x) (mul_t z x);
  modular_mul_add_distrib_lemma #params_q (v y) (v z) (v x)

inline_for_extraction
instance ring_t : ring t =
  {
    add_ag = abelian_group_t;
    mul_m = monoid_mul_t;
    lemma_distr_left = lemma_distr_left_t;
    lemma_distr_right = lemma_distr_right_t;
  }

let lemma_mul_swap_t (x:t) (y:t) : Lemma (mul_t x y == mul_t y x) =
  mul_lemma_t x y;
  mul_lemma_t y x

inline_for_extraction
instance commutative_ring_t : commutative_ring t =
  {
    r = ring_t;
    lemma_mul_swap = lemma_mul_swap_t;
  }

let minus_lemma_t (x:t) (y:t) : Lemma (Group.v (minus x y) = (Group.v x - Group.v y) % params_q) =
  plus_lemma_t x (opp_t y);
  opp_lemma_t y;
  FStar.Math.Lemmas.lemma_mod_plus_distr_r (Group.v x) (- Group.v y) params_q
