module Lib.Arithmetic.Ring.Sequence

open FStar.Math.Lemmas
open Lib.IntTypes
open FStar.Mul

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring
open Lib.Sequence

open Lib.Arithmetic.Group.Sequence

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --print_universes --using_facts_from '* -FStar.Seq'"

let plus_lseq (#a:Type0) [|ring a|] (#len:size_nat) = op_lseq #a #add_ag.g.m #len
let mul_lseq (#a:Type0) [|ring a|] (#len:size_nat) = op_lseq #a #mul_m #len

let lemma_distr_left_lseq (#a:Type0) [| ring a |] (#len:size_nat) (x:lseq a len) (y:lseq a len) (z:lseq a len) : Lemma (mul_lseq x (plus_lseq y z) == plus_lseq (mul_lseq x y) (mul_lseq x z)) =
  let customprop (k:nat{k<len}) : Type0 = ((mul_lseq x (plus_lseq y z)).[k] == (plus_lseq (mul_lseq x y) (mul_lseq x z)).[k]) in
  let customlemma (k:nat{k<len}) : Lemma (customprop k) =
    lemma_distr_left #a x.[k] y.[k] z.[k] in
  FStar.Classical.forall_intro customlemma;
  eq_intro (mul_lseq x (plus_lseq y z)) (plus_lseq (mul_lseq x y) (mul_lseq x z));
  eq_elim (mul_lseq x (plus_lseq y z)) (plus_lseq (mul_lseq x y) (mul_lseq x z))
  
let lemma_distr_right_lseq (#a:Type0) [| ring a |] (#len:size_nat) (x:lseq a len) (y:lseq a len) (z:lseq a len) : Lemma (mul_lseq (plus_lseq y z) x == plus_lseq (mul_lseq y x) (mul_lseq z x)) =
  let customprop (k:nat{k<len}) : Type0 = ((mul_lseq (plus_lseq y z) x).[k] == (plus_lseq (mul_lseq y x) (mul_lseq z x)).[k]) in
  let customlemma (k:nat{k<len}) : Lemma (customprop k) =
    lemma_distr_right #a x.[k] y.[k] z.[k] in
  FStar.Classical.forall_intro customlemma;
  eq_intro (mul_lseq (plus_lseq y z) x) (plus_lseq (mul_lseq y x) (mul_lseq z x));
  eq_elim (mul_lseq (plus_lseq y z) x) (plus_lseq (mul_lseq y x) (mul_lseq z x))
  
instance ring_lseq: (#a:Type0) -> (#[FStar.Tactics.Typeclasses.tcresolve ()] r:ring a) -> (#len:size_nat) -> ring (lseq a len) =
  fun #a #r #len ->
    {
    add_ag = abelian_group_lseq #a #r.add_ag;
    mul_m = monoid_lseq #a #r.mul_m;
    lemma_distr_left = lemma_distr_left_lseq;
    lemma_distr_right = lemma_distr_right_lseq;
}

let lemma_mul_swap_lseq (#a:Type0) [|commutative_ring a|] (#len:size_nat) (x:lseq a len) (y:lseq a len) : Lemma (mul_lseq #a #r x y == mul_lseq #a #r y x) =
  let mul_lseq = mul_lseq #a #r in
  let customprop (k:nat{k<len}) : Type0 = ((mul_lseq x y).[k] == (mul_lseq y x).[k]) in
  let customlemma (k:nat{k<len}) : Lemma (customprop k) =
    lemma_mul_swap #a x.[k] y.[k] in
  FStar.Classical.forall_intro customlemma;
  eq_intro (mul_lseq x y) (mul_lseq y x);
  eq_elim (mul_lseq x y) (mul_lseq y x)

instance commutative_ring_lseq: (#a:Type0) -> (#[FStar.Tactics.Typeclasses.tcresolve ()] cr:commutative_ring a) -> (#len:size_nat) -> commutative_ring(lseq a len) =
  fun #a #cr #len ->
    {r = ring_lseq #a #cr.r;
    lemma_mul_swap = lemma_mul_swap_lseq #a #cr;
}
