module Lib.Arithmetic.Ring.Uint_t

open Lib.Arithmetic.Ring
open Lib.IntTypes
open Lib.ModularArithmetic.Lemmas

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --print_universes --using_facts_from '* -FStar.Seq'"


let zero_uint (#t:inttype) (#l:secrecy_level) : uint_t t l = nat_to_uint 0

let one_uint (#t:inttype) (#l:secrecy_level) : uint_t t l = nat_to_uint 1

let plus_uint (#t:inttype) (#l:secrecy_level) = add_mod #t #l

let minus_uint (#t:inttype) (#l:secrecy_level) = sub_mod #t #l

let mul_uint (#t:inttype{t<>U128}) (#l:secrecy_level) = mul_mod #t #l

let opp_uint (#t:inttype) (#l:secrecy_level) = minus_uint #t #l zero_uint

let lemma_plus_assoc_uint (#t:inttype) (#l:secrecy_level) (x:uint_t t l) (y:uint_t t l) (z:uint_t t l) : Lemma (plus_uint (plus_uint x y) z == plus_uint x (plus_uint y z)) =
  add_mod_lemma (plus_uint x y) z;
  add_mod_lemma x y;
  modular_add_associativity_lemma #(modulus t) (uint_v x) (uint_v y) (uint_v z);
  add_mod_lemma y z;
  add_mod_lemma x (plus_uint y z)
  
let lemma_plus_swap_uint (#t:inttype) (#l:secrecy_level) (x:uint_t t l) (y:uint_t t l) : Lemma (plus_uint x y == plus_uint y x) =
  add_mod_lemma x y;
  modular_add_swap_lemma #(modulus t) (uint_v x) (uint_v y);
  add_mod_lemma y x
  
let lemma_plus_opp1_uint (#t:inttype) (#l:secrecy_level) (x:uint_t t l) : Lemma (plus_uint x (opp_uint x) == zero_uint) =
  add_mod_lemma x (opp_uint x);
  sub_mod_lemma zero_uint x

let lemma_plus_opp2_uint (#t:inttype) (#l:secrecy_level) (x:uint_t t l) : Lemma (plus_uint (opp_uint x) x == zero_uint) =
  lemma_plus_swap_uint (opp_uint x) x;
  lemma_plus_opp1_uint x
  
let lemma_mul_assoc_uint (#t:inttype{t<>U128}) (#l:secrecy_level) (x:uint_t t l) (y:uint_t t l) (z:uint_t t l) : Lemma (mul_uint (mul_uint x y) z == mul_uint x (mul_uint y z)) =
  mul_mod_lemma (mul_uint x y) z;
  mul_mod_lemma x y;
  modular_mul_associativity_lemma #(modulus t) (uint_v x) (uint_v y) (uint_v z);
  mul_mod_lemma y z;
  mul_mod_lemma x (mul_uint y z)
  
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

let lemma_zero1_uint (#t:inttype) (#l:secrecy_level) (x:uint_t t l) : Lemma (plus_uint zero_uint x == x) =
  add_mod_lemma zero_uint x

let lemma_zero2_uint (#t:inttype) (#l:secrecy_level) (x:uint_t t l) : Lemma (plus_uint x zero_uint == x) =
  lemma_plus_swap_uint x zero_uint;
  lemma_zero1_uint x
  
let lemma_one1_uint (#t:inttype{t<>U128}) (#l:secrecy_level) (x:uint_t t l) : Lemma (mul_uint one_uint x == x) =
  mul_mod_lemma one_uint x

let lemma_one2_uint (#t:inttype{t<>U128}) (#l:secrecy_level) (x:uint_t t l) : Lemma (mul_uint x one_uint == x) =
  mul_mod_lemma x one_uint

let lemma_mul_swap_uint (#t:inttype{t<>U128}) (#l:secrecy_level) (x:uint_t t l) (y:uint_t t l) : Lemma (mul_uint x y == mul_uint y x) =
  mul_mod_lemma x y;
  modular_mul_swap_lemma #(modulus t) (uint_v x) (uint_v y);
  mul_mod_lemma y x
  
instance ring_uint_t : (#t:inttype{t<>U128}) -> (#l:secrecy_level) -> ring (uint_t t l) =
  fun #t #l -> {
    zero = zero_uint;
    one = one_uint;
    plus = plus_uint;
    minus = minus_uint;
    mul = mul_uint;
    opp = opp_uint;
    lemma_plus_assoc = lemma_plus_assoc_uint;
    lemma_plus_swap = lemma_plus_swap_uint;
    lemma_plus_opp1 = lemma_plus_opp1_uint;
    lemma_plus_opp2 = lemma_plus_opp2_uint;
    lemma_mul_assoc = lemma_mul_assoc_uint;
    lemma_distr_left = lemma_distr_left_uint;
    lemma_distr_right = lemma_distr_right_uint;
    lemma_zero1 = lemma_zero1_uint;
    lemma_zero2 = lemma_zero2_uint;
    lemma_one1 = lemma_one1_uint;
    lemma_one2 = lemma_one2_uint;
}

instance commutative_ring_uint_t : (#t:inttype{t<>U128}) -> (#l:secrecy_level) -> commutative_ring (uint_t t l) =
  fun #t #l -> {
    r = ring_uint_t;
    lemma_mul_swap = lemma_mul_swap_uint;
  }
