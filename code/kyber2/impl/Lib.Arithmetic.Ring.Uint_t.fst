module Lib.Arithmetic.Ring.Uint_t

open Lib.Arithmetic.Group
open Lib.Arithmetic.Group.Uint_t
open Lib.Arithmetic.Ring
open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Mul
open Lib.ModularArithmetic.Lemmas

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --print_universes --using_facts_from '* -FStar.Seq'"

  
let lemma_distr_left_uint (#t:inttype{t<>U128}) (#l:secrecy_level) (x:uint_t t l) (y:uint_t t l) (z:uint_t t l) : Lemma (mul_uint x (plus_uint y z) == plus_uint (mul_uint x y) (mul_uint x z)) =
  mul_mod_lemma x (plus_uint y z);
  add_mod_lemma y z;
  mul_mod_lemma x y;
  mul_mod_lemma x z;
  add_mod_lemma (mul_uint x y) (mul_uint x z);
  let t' = modulus t in let x' = uint_v x in let y' = uint_v y in let z' = uint_v z in
  (match t with
  |S8 |S16 |S32 |S64 -> 
    let s = if (uint_v (x*.(y +. z)) >= 0) then uint_v (x*.(y +.z)) else uint_v (x*.(y +.z)) + t' in
    assert(s = ((x'*uint_v (y +. z))) % t');
    if (uint_v (y +. z) >= 0) then ()
    else 
      (assert(s = (x' * ((y' + z')%t' - t')) % t');
       lemma_mod_mul_distr_r x' ((y'+z')%t' - t') t';
       lemma_mod_sub ((y'+z')%t') t' 1;
       lemma_mod_mul_distr_r x' ((y'+z')%t') t');
    lemma_mod_mul_distr_r x' (y' + z') t';
    distributivity_add_right x' y' z';
    lemma_mod_add_distr (x'*y') (x'*z') t';
    lemma_mod_add_distr ((x'*z')%t') (x'*y') t';
    assert(s = ((x'*y')%t' + (x'*z')%t')%t');
    if (uint_v (x *. y) < 0) then
      (assert(s= ((uint_v (x*.y) + t') + (x'*z')%t')%t');
       lemma_mod_add_distr ((x'*z')%t') (uint_v (x*.y) + t') t';
       lemma_mod_plus (uint_v (x*.y)) 1 t';
       lemma_mod_add_distr ((x'*z')%t') (uint_v (x*.y)) t');
    assert(s= (uint_v (x*.y) + (x'*z')%t') %t');
    if (uint_v (x *. z) < 0) then
      (assert(s= (uint_v (x*.y) + (uint_v (x*.z)+t'))%t');
       lemma_mod_add_distr (uint_v (x*.y)) (uint_v (x*.z) + t') t';
       lemma_mod_plus (uint_v (x*.z)) 1 t';
       lemma_mod_add_distr (uint_v (x*.y)) (uint_v (x*.z)) t')
  |_ -> modular_mul_add_distrib_left_lemma #(modulus t) (uint_v x) (uint_v y) (uint_v z))

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --print_universes --using_facts_from '* -FStar.Seq'"

let lemma_distr_right_uint (#t:inttype{t<>U128}) (#l:secrecy_level) (x:uint_t t l) (y:uint_t t l) (z:uint_t t l) : Lemma (mul_uint (plus_uint y z) x == plus_uint (mul_uint y x) (mul_uint z x)) =
  mul_mod_lemma (plus_uint y z) x;
  add_mod_lemma y z;
  mul_mod_lemma y x;
  mul_mod_lemma z x;
  add_mod_lemma (mul_uint y x) (mul_uint z x);
  let t' = modulus t in let x' = uint_v x in let y' = uint_v y in let z' = uint_v z in
  (match t with
  |S8 |S16 |S32 |S64 -> 
    let s = if (uint_v ((y +. z)*.x) >= 0) then uint_v ((y +.z)*.x) else uint_v ((y +.z)*.x) + t' in
    assert(s = ((uint_v (y +. z)) * x') % t');
    if (uint_v (y +. z) >= 0) then ()
    else 
      (assert(s = (((y' + z')%t' - t') * x') % t');
       lemma_mod_mul_distr_l ((y'+z')%t' - t') x' t';
       lemma_mod_sub ((y'+z')%t') t' 1;
       lemma_mod_mul_distr_l ((y'+z')%t') x' t');
    lemma_mod_mul_distr_l (y' + z') x' t';
    distributivity_add_left y' z' x';
    lemma_mod_add_distr (y'*x') (z'*x') t';
    lemma_mod_add_distr ((z'*x')%t') (y'*x') t';
    assert(s = ((y'*x')%t' + (z'*x')%t')%t');
    if (uint_v (y *. x) < 0) then
      (assert(s= ((uint_v (y*.x) + t') + (z'*x')%t')%t');
       lemma_mod_add_distr ((z'*x')%t') (uint_v (y*.x) + t') t';
       lemma_mod_plus (uint_v (y*.x)) 1 t';
       lemma_mod_add_distr ((z'*x')%t') (uint_v (y*.x)) t');
    assert(s= (uint_v (y*.x) + (z'*x')%t') %t');
    if (uint_v (z *. x) < 0) then
      (assert(s= (uint_v (y*.x) + (uint_v (z*.x)+t'))%t');
       lemma_mod_add_distr (uint_v (y*.x)) (uint_v (z*.x) + t') t';
       lemma_mod_plus (uint_v (z*.x)) 1 t';
       lemma_mod_add_distr (uint_v (y*.x)) (uint_v (z*.x)) t')
  |_ -> modular_mul_add_distrib_lemma #(modulus t) (uint_v y) (uint_v z) (uint_v x))
  
instance ring_uint_t : (#t:inttype{t<>U128}) -> (#l:secrecy_level) -> ring (uint_t t l) =
  fun #t #l -> {
    add_ag = abelian_group_uint_t;
    mul_m = monoid_mul_uint_t;
    lemma_distr_left = lemma_distr_left_uint;
    lemma_distr_right = lemma_distr_right_uint;
  }

let lemma_mul_swap_uint (#t:inttype{t<>U128}) (#l:secrecy_level) (x:uint_t t l) (y:uint_t t l) : Lemma (mul_uint x y == mul_uint y x) =
  mul_mod_lemma x y;
  mul_mod_lemma y x
  

instance commutative_ring_uint_t : (#t:inttype{t<>U128}) -> (#l:secrecy_level) -> commutative_ring (uint_t t l) =
  fun #t #l -> {
    r = ring_uint_t;
    lemma_mul_swap = lemma_mul_swap_uint;
  }
