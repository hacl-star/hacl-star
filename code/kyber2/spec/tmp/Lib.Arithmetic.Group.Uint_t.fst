module Lib.Arithmetic.Group.Uint_t

open Lib.Arithmetic.Group
open Lib.IntTypes
open Lib.ModularArithmetic.Lemmas

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --print_universes --using_facts_from '* -FStar.Seq'"


let zero_uint (#t:inttype) (#l:secrecy_level) : uint_t t l = nat_to_uint 0

let one_uint (#t:inttype) (#l:secrecy_level) : uint_t t l = nat_to_uint 1

let plus_uint (#t:inttype) (#l:secrecy_level) = add_mod #t #l

let mul_uint (#t:inttype{t<>U128}) (#l:secrecy_level) = mul_mod #t #l

let lemma_plus_assoc_uint (#t:inttype) (#l:secrecy_level) (x:uint_t t l) (y:uint_t t l) (z:uint_t t l) : Lemma (plus_uint (plus_uint x y) z == plus_uint x (plus_uint y z)) =
  add_mod_lemma (plus_uint x y) z;
  add_mod_lemma x y;
  modular_add_associativity_lemma #(modulus t) (uint_v x) (uint_v y) (uint_v z);
  add_mod_lemma y z;
  add_mod_lemma x (plus_uint y z)

let lemma_mul_assoc_uint (#t:inttype{t<>U128}) (#l:secrecy_level) (x:uint_t t l) (y:uint_t t l) (z:uint_t t l) : Lemma (mul_uint (mul_uint x y) z == mul_uint x (mul_uint y z)) =
  mul_mod_lemma (mul_uint x y) z;
  mul_mod_lemma x y;
  modular_mul_associativity_lemma #(modulus t) (uint_v x) (uint_v y) (uint_v z);
  mul_mod_lemma y z;
  mul_mod_lemma x (mul_uint y z)

let lemma_zero1_uint (#t:inttype) (#l:secrecy_level) (x:uint_t t l) : Lemma (plus_uint zero_uint x == x) =
  add_mod_lemma zero_uint x

let lemma_zero2_uint (#t:inttype) (#l:secrecy_level) (x:uint_t t l) : Lemma (plus_uint x zero_uint == x) =
  add_mod_lemma x zero_uint
  
let lemma_one1_uint (#t:inttype{t<>U128}) (#l:secrecy_level) (x:uint_t t l) : Lemma (mul_uint one_uint x == x) =
  mul_mod_lemma one_uint x

let lemma_one2_uint (#t:inttype{t<>U128}) (#l:secrecy_level) (x:uint_t t l) : Lemma (mul_uint x one_uint == x) =
  mul_mod_lemma x one_uint

instance monoid_plus_uint_t: (#t:inttype) -> (#l:secrecy_level) -> monoid (uint_t t l) =
  fun #t #l -> {
    id = zero_uint;
    op = plus_uint;
    lemma_assoc = lemma_plus_assoc_uint;
    lemma_id1 = lemma_zero1_uint;
    lemma_id2 = lemma_zero2_uint;
 }

instance monoid_mul_uint_t: (#t:inttype{t<>U128}) -> (#l:secrecy_level) -> monoid (uint_t t l) =
  fun #t #l -> {
    id = one_uint;
    op = mul_uint;
    lemma_assoc = lemma_mul_assoc_uint;
    lemma_id1 = lemma_one1_uint;
    lemma_id2 = lemma_one2_uint;
 }

let opp_uint (#t:inttype) (#l:secrecy_level) = sub_mod #t #l zero_uint

let lemma_plus_opp1_uint (#t:inttype) (#l:secrecy_level) (x:uint_t t l) : Lemma (plus_uint x (opp_uint x) == zero_uint) =
  add_mod_lemma x (opp_uint x)

let lemma_plus_opp2_uint (#t:inttype) (#l:secrecy_level) (x:uint_t t l) : Lemma (plus_uint (opp_uint x) x == zero_uint) =
  add_mod_lemma (opp_uint x) x

instance group_uint_t: (#t:inttype) -> (#l:secrecy_level) -> group (uint_t t l) =
  fun #t #l -> {
    m = monoid_plus_uint_t;
    sym = opp_uint;
    lemma_sym1 = lemma_plus_opp1_uint;
    lemma_sym2 = lemma_plus_opp2_uint;
  }

let lemma_plus_swap_uint (#t:inttype) (#l:secrecy_level) (x:uint_t t l) (y:uint_t t l) : Lemma (plus_uint x y == plus_uint y x) =
  add_mod_lemma x y;
  modular_add_swap_lemma #(modulus t) (uint_v x) (uint_v y);
  add_mod_lemma y x

instance abelian_group_uint_t: (#t:inttype) -> (#l:secrecy_level) -> abelian_group (uint_t t l) =
  fun #t #l -> {
    g = group_uint_t;
    lemma_swap = lemma_plus_swap_uint;
  }
