module Lib.Arithmetic.Ring.Uint_t

open Lib.Arithmetic.Group
open Lib.Arithmetic.Group.Uint_t
open Lib.Arithmetic.Ring
open Lib.IntTypes
open Lib.ModularArithmetic.Lemmas

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --print_universes --using_facts_from '* -FStar.Seq'"

  
let lemma_distr_left_uint (#t:inttype{t<>U128}) (#l:secrecy_level) (x:uint_t t l) (y:uint_t t l) (z:uint_t t l) : Lemma (mul_uint x (plus_uint y z) == plus_uint (mul_uint x y) (mul_uint x z)) =
  mul_mod_lemma x (plus_uint y z);
  add_mod_lemma y z;
  modular_mul_add_distrib_left_lemma #(modulus t) (uint_v x) (uint_v y) (uint_v z);
  mul_mod_lemma x y;
  mul_mod_lemma x z;
  add_mod_lemma (mul_uint x y) (mul_uint x z)

let lemma_distr_right_uint (#t:inttype{t<>U128}) (#l:secrecy_level) (x:uint_t t l) (y:uint_t t l) (z:uint_t t l) : Lemma (mul_uint (plus_uint y z) x == plus_uint (mul_uint y x) (mul_uint z x)) =
  mul_mod_lemma (plus_uint y z) x;
  add_mod_lemma y z;
  modular_mul_add_distrib_lemma #(modulus t) (uint_v y) (uint_v z) (uint_v x);
  mul_mod_lemma y x;
  mul_mod_lemma z x;
  add_mod_lemma (mul_uint y x) (mul_uint z x)

instance ring_uint_t : (#t:inttype{t<>U128}) -> (#l:secrecy_level) -> ring (uint_t t l) =
  fun #t #l -> {
    add_ag = abelian_group_uint_t;
    mul_m = monoid_mul_uint_t;
    lemma_distr_left = lemma_distr_left_uint;
    lemma_distr_right = lemma_distr_right_uint;
  }

let lemma_mul_swap_uint (#t:inttype{t<>U128}) (#l:secrecy_level) (x:uint_t t l) (y:uint_t t l) : Lemma (mul_uint x y == mul_uint y x) =
  mul_mod_lemma x y;
  modular_mul_swap_lemma #(modulus t) (uint_v x) (uint_v y);
  mul_mod_lemma y x
  

instance commutative_ring_uint_t : (#t:inttype{t<>U128}) -> (#l:secrecy_level) -> commutative_ring (uint_t t l) =
  fun #t #l -> {
    r = ring_uint_t;
    lemma_mul_swap = lemma_mul_swap_uint;
  }
