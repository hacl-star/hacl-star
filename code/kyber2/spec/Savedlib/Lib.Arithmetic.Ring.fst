module Lib.Arithmetic.Ring

open FStar.Math.Lemmas
open FStar.Mul

open Lib.ModularArithmetic.Lemmas
open Lib.ModularArithmetic

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --print_universes --using_facts_from '* -FStar.Seq'"

class ring (a:Type0) = {
  zero : a;
  one : a;
  plus : a -> a -> a;
  minus : a -> a -> a;
  mul: a -> a -> a;
  opp : a -> a;
  lemma_plus_assoc: (x:a) -> (y:a) -> (z:a) -> Lemma (plus (plus x y) z == plus x (plus y z));
  lemma_plus_swap: (x:a) -> (y:a) -> Lemma (plus x y == plus y x);
  lemma_plus_opp1: (x:a) -> Lemma (plus x (opp x) == zero);
  lemma_plus_opp2: (x:a) -> Lemma (plus (opp x) x == zero);
  lemma_mul_assoc: (x:a) -> (y:a) -> (z:a) -> Lemma (mul (mul x y) z == mul x (mul y z));
  lemma_distr_left: (x:a) -> (y:a) -> (z:a) -> Lemma (mul x (plus y z) == plus (mul x y) (mul x z));
  lemma_distr_right: (x:a) -> (y:a) -> (z:a) -> Lemma (mul (plus y z) x == plus (mul y x) (mul z x));
  lemma_zero1: (x:a) -> Lemma (plus zero x == x);
  lemma_zero2: (x:a) -> Lemma (plus x zero == x);
  lemma_one1: (x:a) -> Lemma (mul one x == x);
  lemma_one2: (x:a) -> Lemma (mul x one == x);
}

class commutative_ring (a:Type0) = {
  r:ring a;
  lemma_mul_swap: (x:a) -> (y:a) -> Lemma (r.mul x y == r.mul y x);
}


instance ring_int : ring int =
  { zero = 0;
    one = 1;
    plus = ( + );
    minus = (fun x y -> (x - y));
    mul = (fun x y -> x * y);
    opp = (fun x -> - x);
    lemma_plus_assoc = (fun x y z -> ());
    lemma_plus_swap = (fun x y -> ());
    lemma_plus_opp1 = (fun x -> ());
    lemma_plus_opp2 = (fun x -> ());
    lemma_mul_assoc = (fun x y z -> (paren_add_left x y z; paren_add_right x y z));
    lemma_distr_left = distributivity_add_right;
    lemma_distr_right = (fun x y z -> distributivity_add_left y z x);
    lemma_zero1 = (fun x -> ());
    lemma_zero2 = (fun x -> ());
    lemma_one1 = (fun x -> ());
    lemma_one2 = (fun x -> ());
    }

instance commutative_ring_int : commutative_ring int =
  { r = ring_int;
    lemma_mul_swap = (fun x y -> ());
   }
   
instance ring_mod : #(q:pos) -> ring (field q) =
  fun #q -> {
    zero = 0;
    one = if q = 1 then 0 else 1;
    plus = modular_add #q;
    minus = modular_sub;
    mul = modular_mul;
    opp = modular_sub #q 0;
    lemma_plus_assoc = modular_add_associativity_lemma;
    lemma_plus_swap = modular_add_swap_lemma;
    lemma_plus_opp1 = (fun x -> ());
    lemma_plus_opp2 = (fun x -> ());
    lemma_mul_assoc = modular_mul_associativity_lemma;
    lemma_distr_left = modular_mul_add_distrib_left_lemma;
    lemma_distr_right = (fun x y z -> modular_mul_add_distrib_lemma y z x);
    lemma_zero1 = (fun x -> ());
    lemma_zero2 = (fun x -> ());
    lemma_one1 = (fun x -> ());
    lemma_one2 = (fun x -> ());
}

instance commutative_ring_mod : (#q:pos) -> commutative_ring (field q) = 
  fun #q -> {
    r = ring_mod;
    lemma_mul_swap = modular_mul_swap_lemma;
    }


let lemma_zero_absorb1 (#a:Type0) [|ring a|] (x:a) : Lemma (mul zero x == zero) =
  lemma_zero1 (mul x x);
  lemma_zero1 x;
  lemma_distr_right x zero x;
  lemma_plus_opp1 (mul x x);
  lemma_plus_assoc (mul zero x) (mul x x) (opp (mul x x));
  lemma_zero2 (mul zero x)

let lemma_zero_absorb2 (#a:Type0) [|ring a|] (x:a) : Lemma (mul x zero == zero) =
  lemma_zero2 (mul x x);
  lemma_zero2 x;
  lemma_distr_left x x zero;
  lemma_plus_opp2 (mul x x);
  lemma_plus_assoc (opp (mul x x)) (mul x x) (mul x zero);
  lemma_zero1 (mul x zero)

