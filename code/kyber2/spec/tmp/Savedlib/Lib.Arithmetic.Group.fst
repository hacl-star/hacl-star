module Lib.Arithmetic.Group

open FStar.Math.Lemmas
open FStar.Mul
open FStar.Tactics.Typeclasses

class monoid (a:Type0) = {
  id: a;
  op: a -> a -> a;
  lemma_assoc : (x:a) -> (y:a) -> (z:a) -> Lemma (op (op x y) z == op x (op y z));
  lemma_id1: (x:a) -> Lemma (op id x == x);
  lemma_id2: (x:a) -> Lemma (op x id == x);
}

(*class mul_monoid (a:Type0) = {
  one: a;
  mul: a -> a -> a;
  lemma_mul_assoc : (x:a) -> (y:a) -> (z:a) -> Lemma (mul (mul x y) z == mul x (mul y z));
  lemma_one1: (x:a) -> Lemma (mul one x == x);
  lemma_one2: (x:a) -> Lemma (mul x one == x);
}*)

class group (a:Type0) = {
  m: monoid a;
  sym: a -> a;
  lemma_sym1: (x:a) -> Lemma (m.op x (sym x) == m.id);
  lemma_sym2: (x:a) -> Lemma (m.op (sym x) x == m.id);
}

class abelian_group (a:Type0) = {
  g: group a;
  lemma_swap: (x:a) -> (y:a) -> Lemma (g.m.op x y == g.m.op y x)
}

(*class additive_abelian_group (a:Type0) = {
  zero: a;
  plus: a -> a -> a;
  minus: a -> a -> a;
  opp: a -> a;
  lemma_plus_assoc: (x:a) -> (y:a) -> (z:a) -> Lemma (plus (plus x y) z == plus x (plus y z));
  lemma_plus_swap: (x:a) -> (y:a) -> Lemma (plus x y == plus y x);
  lemma_plus_opp1: (x:a) -> Lemma (plus x (opp x) == zero);
  lemma_plus_opp2: (x:a) -> Lemma (plus (opp x) x == zero);
  lemma_zero1: (x:a) -> Lemma (plus zero x == x);
  lemma_zero2: (x:a) -> Lemma (plus x zero == x);
 }*)

