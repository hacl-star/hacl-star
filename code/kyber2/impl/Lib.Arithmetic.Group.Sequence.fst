module Lib.Arithmetic.Group.Sequence

open FStar.Math.Lemmas
open Lib.IntTypes
open FStar.Mul

open Lib.Arithmetic.Group
open Lib.Sequence

let id_lseq (#a:Type0) [| monoid a |] (#len:size_nat) = create len (id #a)

let op_lseq (#a:Type0) [| monoid a |] (#len:size_nat) = Lib.Sequence.map2 #a #a #a #len (op)

let lemma_assoc_lseq (#a:Type0) [| monoid a |] (#len:size_nat) (x:lseq a len) (y:lseq a len) (z:lseq a len) : Lemma (op_lseq (op_lseq x y) z == op_lseq x (op_lseq y z)) =
  let customprop (k:nat{k<len}) : Type0 = ((op_lseq (op_lseq x y) z).[k] == (op_lseq x (op_lseq y z)).[k]) in
  let customlemma (k:nat{k<len}) : Lemma (customprop k) =
    lemma_assoc #a x.[k] y.[k] z.[k] in
  FStar.Classical.forall_intro customlemma;
  eq_intro (op_lseq (op_lseq x y) z) (op_lseq x (op_lseq y z));
  eq_elim (op_lseq (op_lseq x y) z) (op_lseq x (op_lseq y z))

let lemma_id1_lseq (#a:Type0) [| monoid a |] (#len:size_nat) (x:lseq a len) : Lemma (op_lseq id_lseq x == x) =
  let customprop (k:nat{k<len}) : Type0 = ((op_lseq id_lseq x).[k] == x.[k]) in
  let customlemma (k:nat{k<len}) : Lemma (customprop k) =
    lemma_id1 #a x.[k] in
  FStar.Classical.forall_intro customlemma;
  eq_intro (op_lseq id_lseq x) x;
  eq_elim (op_lseq id_lseq x) x


let lemma_id2_lseq (#a:Type0) [| monoid a |] (#len:size_nat) (x:lseq a len) : Lemma (op_lseq x id_lseq == x) =
  let customprop (k:nat{k<len}) : Type0 = ((op_lseq x id_lseq).[k] == x.[k]) in
  let customlemma (k:nat{k<len}) : Lemma (customprop k) =
    lemma_id2 #a x.[k] in
  FStar.Classical.forall_intro customlemma;
  eq_intro (op_lseq x id_lseq) x;
  eq_elim (op_lseq x id_lseq) x

instance monoid_lseq : (#a:Type0) -> (#[FStar.Tactics.Typeclasses.tcresolve ()] m:monoid a) -> (#len:size_nat) -> monoid (lseq a len) =
  fun #a #m #len ->
    {
      id = id_lseq;
      op = op_lseq;
      lemma_assoc = lemma_assoc_lseq;
      lemma_id1 = lemma_id1_lseq;
      lemma_id2 = lemma_id2_lseq;
    }

let sym_lseq (#a:Type0) [| group a |] (#len:size_nat) = Lib.Sequence.map #a #a #len (sym)  

let lemma_sym1_lseq (#a:Type0) [|group a|] (#len:size_nat) (x:lseq a len) : Lemma (op_lseq #a #m x (sym_lseq x) == id_lseq #a #m) =
  let customprop (k:nat{k<len}) : Type0 = ((op_lseq #a #m x (sym_lseq x)).[k] == (id_lseq #a #m #len).[k]) in
  let customlemma (k:nat{k<len}) : Lemma (customprop k) =
    lemma_sym1 #a x.[k] in
  FStar.Classical.forall_intro customlemma;
  eq_intro (op_lseq #a #m x (sym_lseq x)) (id_lseq #a #m);
  eq_elim (op_lseq #a #m x (sym_lseq x)) (id_lseq #a #m)

let lemma_sym2_lseq (#a:Type0) [|group a|] (#len:size_nat) (x:lseq a len) : Lemma (op_lseq #a #m (sym_lseq x) x == id_lseq #a #m) =
  let customprop (k:nat{k<len}) : Type0 = ((op_lseq #a #m (sym_lseq x) x).[k] == (id_lseq #a #m #len).[k]) in
  let customlemma (k:nat{k<len}) : Lemma (customprop k) =
    lemma_sym2 #a x.[k] in
  FStar.Classical.forall_intro customlemma;
  eq_intro (op_lseq #a #m (sym_lseq x) x) (id_lseq #a #m);
  eq_elim (op_lseq #a #m (sym_lseq x) x) (id_lseq #a #m)

instance group_lseq : (#a:Type0) -> (#[FStar.Tactics.Typeclasses.tcresolve ()] g:group a) -> (#len:size_nat) -> group (lseq a len) =
  fun #a #g #len ->
    {
      m = monoid_lseq #a #g.m;
      sym = sym_lseq;
      lemma_sym1 = lemma_sym1_lseq;
      lemma_sym2 = lemma_sym2_lseq;
    }


let lemma_swap_lseq (#a:Type0) [|abelian_group a|] (#len:size_nat) (x:lseq a len) (y:lseq a len) : Lemma (op_lseq #a #g.m x y == op_lseq #a #g.m y x) =
  let op_lseq = op_lseq #a #g.m in
  let customprop (k:nat{k<len}) : Type0 = ((op_lseq x y).[k] == (op_lseq y x).[k]) in
  let customlemma (k:nat{k<len}) : Lemma (customprop k) =
    lemma_swap #a x.[k] y.[k] in
  FStar.Classical.forall_intro customlemma;
  eq_intro (op_lseq x y) (op_lseq y x);
  eq_elim (op_lseq x y) (op_lseq y x)

instance abelian_group_lseq : (#a:Type0) -> (#[FStar.Tactics.Typeclasses.tcresolve ()] ag:abelian_group a) -> (#len:size_nat) -> abelian_group (lseq a len) =
  fun #a #ag #len ->
    {
      g = group_lseq #a #ag.g;
      lemma_swap = lemma_swap_lseq;
    }
