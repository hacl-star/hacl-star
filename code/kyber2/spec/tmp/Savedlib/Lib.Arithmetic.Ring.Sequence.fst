module Lib.Arithmetic.Ring.Sequence

open FStar.Math.Lemmas
open Lib.IntTypes
open FStar.Mul

open Lib.Arithmetic.Ring
open Lib.Sequence

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --print_universes --using_facts_from '* -FStar.Seq'"

let zero_lseq (#a:Type0) [| ring a |] (#len:size_nat) = create len (zero)

let one_lseq (#a:Type0) [| ring a |] (#len:size_nat) = create len (one)

let plus_lseq (#a:Type0) [| ring a |] (#len:size_nat) = Lib.Sequence.map2 #a #a #a #len (plus)  

let minus_lseq (#a:Type0) [| ring a |] (#len:size_nat) = Lib.Sequence.map2 #a #a #a #len (minus)  

let opp_lseq (#a:Type0) [| ring a |] (#len:size_nat) = Lib.Sequence.map #a #a #len (opp)  

let mul_lseq (#a:Type0) [| ring a |] (#len:size_nat) = Lib.Sequence.map2 #a #a #a #len (mul)  

let lemma_plus_assoc_lseq (#a:Type0) (#r:ring a) (#len:size_nat) (x:lseq a len) (y:lseq a len) (z:lseq a len) : Lemma (plus_lseq (plus_lseq x y) z == plus_lseq x (plus_lseq y z)) =
  let customprop (k:nat{k<len}) : Type0 = ((plus_lseq (plus_lseq x y) z).[k] == (plus_lseq x (plus_lseq y z)).[k]) in
  let customlemma (k:nat{k<len}) : Lemma (customprop k) =
    r.lemma_plus_assoc x.[k] y.[k] z.[k] in
  FStar.Classical.forall_intro customlemma;
  eq_intro (plus_lseq (plus_lseq x y) z) (plus_lseq x (plus_lseq y z));
  eq_elim (plus_lseq (plus_lseq x y) z) (plus_lseq x (plus_lseq y z))
  
let lemma_plus_swap_lseq (#a:Type0) (#r:ring a) (#len:size_nat) (x:lseq a len) (y:lseq a len) : Lemma (plus_lseq x y == plus_lseq y x) =
  let customprop (k:nat{k<len}) : Type0 = ((plus_lseq x y).[k] == (plus_lseq y x).[k]) in
  let customlemma (k:nat{k<len}) : Lemma (customprop k) =
    r.lemma_plus_swap x.[k] y.[k] in
  FStar.Classical.forall_intro customlemma;
  eq_intro (plus_lseq x y) (plus_lseq y x);
  eq_elim (plus_lseq x y) (plus_lseq y x)

let lemma_plus_opp1_lseq (#a:Type0) (#r:ring a) (#len:size_nat) (x:lseq a len) : Lemma (plus_lseq x (opp_lseq x) == zero_lseq) =
  let customprop (k:nat{k<len}) : Type0 = ((plus_lseq x (opp_lseq x)).[k] == (zero_lseq #a #r #len).[k]) in
  let customlemma (k:nat{k<len}) : Lemma (customprop k) =
    r.lemma_plus_opp1 x.[k] in
  FStar.Classical.forall_intro customlemma;
  eq_intro (plus_lseq x (opp_lseq x)) zero_lseq;
  eq_elim (plus_lseq x (opp_lseq x)) zero_lseq

let lemma_plus_opp2_lseq (#a:Type0) (#r:ring a) (#len:size_nat) (x:lseq a len) : Lemma (plus_lseq (opp_lseq x) x == zero_lseq) =
  lemma_plus_swap_lseq #a #r (opp_lseq x) x;
  lemma_plus_opp1_lseq #a #r x

let lemma_mul_assoc_lseq (#a:Type0) (#r:ring a) (#len:size_nat) (x:lseq a len) (y:lseq a len) (z:lseq a len) : Lemma (mul_lseq (mul_lseq x y) z == mul_lseq x (mul_lseq y z)) =
  let customprop (k:nat{k<len}) : Type0 = ((mul_lseq (mul_lseq x y) z).[k] == (mul_lseq x (mul_lseq y z)).[k]) in
  let customlemma (k:nat{k<len}) : Lemma (customprop k) =
    r.lemma_mul_assoc x.[k] y.[k] z.[k] in
  FStar.Classical.forall_intro customlemma;
  eq_intro (mul_lseq (mul_lseq x y) z) (mul_lseq x (mul_lseq y z));
  eq_elim (mul_lseq (mul_lseq x y) z) (mul_lseq x (mul_lseq y z))

let lemma_distr_left_lseq (#a:Type0) (#r:ring a) (#len:size_nat) (x:lseq a len) (y:lseq a len) (z:lseq a len) : Lemma (mul_lseq x (plus_lseq y z) == plus_lseq (mul_lseq x y) (mul_lseq x z)) =
  let customprop (k:nat{k<len}) : Type0 = ((mul_lseq x (plus_lseq y z)).[k] == (plus_lseq (mul_lseq x y) (mul_lseq x z)).[k]) in
  let customlemma (k:nat{k<len}) : Lemma (customprop k) =
    r.lemma_distr_left x.[k] y.[k] z.[k] in
  FStar.Classical.forall_intro customlemma;
  eq_intro (mul_lseq x (plus_lseq y z)) (plus_lseq (mul_lseq x y) (mul_lseq x z));
  eq_elim (mul_lseq x (plus_lseq y z)) (plus_lseq (mul_lseq x y) (mul_lseq x z))
  
let lemma_distr_right_lseq (#a:Type0) (#r:ring a) (#len:size_nat) (x:lseq a len) (y:lseq a len) (z:lseq a len) : Lemma (mul_lseq (plus_lseq y z) x == plus_lseq (mul_lseq y x) (mul_lseq z x)) =
  let customprop (k:nat{k<len}) : Type0 = ((mul_lseq (plus_lseq y z) x).[k] == (plus_lseq (mul_lseq y x) (mul_lseq z x)).[k]) in
  let customlemma (k:nat{k<len}) : Lemma (customprop k) =
    r.lemma_distr_right x.[k] y.[k] z.[k] in
  FStar.Classical.forall_intro customlemma;
  eq_intro (mul_lseq (plus_lseq y z) x) (plus_lseq (mul_lseq y x) (mul_lseq z x));
  eq_elim (mul_lseq (plus_lseq y z) x) (plus_lseq (mul_lseq y x) (mul_lseq z x))
  
let lemma_zero1_lseq (#a:Type0) (#r:ring a) (#len:size_nat) (x:lseq a len) : Lemma (plus_lseq zero_lseq x == x) =
  let customprop (k:nat{k<len}) : Type0 = ((plus_lseq zero_lseq x).[k] == x.[k]) in
  let customlemma (k:nat{k<len}) : Lemma (customprop k) =
    r.lemma_zero1 x.[k] in
  FStar.Classical.forall_intro customlemma;
  eq_intro (plus_lseq zero_lseq x) x;
  eq_elim (plus_lseq zero_lseq x) x

let lemma_zero2_lseq (#a:Type0) (#r:ring a) (#len:size_nat) (x:lseq a len) : Lemma (plus_lseq x zero_lseq == x) =
  lemma_plus_swap_lseq #a #r zero_lseq x;
  lemma_zero1_lseq #a #r x
  
let lemma_one1_lseq (#a:Type0) (#r:ring a) (#len:size_nat) (x:lseq a len) : Lemma (mul_lseq one_lseq x == x) =
  let customprop (k:nat{k<len}) : Type0 = ((mul_lseq one_lseq x).[k] == x.[k]) in
  let customlemma (k:nat{k<len}) : Lemma (customprop k) =
    r.lemma_one1 x.[k] in
  FStar.Classical.forall_intro customlemma;
  eq_intro (mul_lseq one_lseq x) x;
  eq_elim (mul_lseq one_lseq x) x

let lemma_one2_lseq (#a:Type0) (#r:ring a) (#len:size_nat) (x:lseq a len) : Lemma (mul_lseq x one_lseq == x) =
  let customprop (k:nat{k<len}) : Type0 = ((mul_lseq x one_lseq).[k] == x.[k]) in
  let customlemma (k:nat{k<len}) : Lemma (customprop k) =
    r.lemma_one2 x.[k] in
  FStar.Classical.forall_intro customlemma;
  eq_intro (mul_lseq x one_lseq) x;
  eq_elim (mul_lseq x one_lseq) x


let lemma_mul_swap_lseq (#a:Type0) (#cr:commutative_ring a) (#len:size_nat) (x:lseq a len) (y:lseq a len) : Lemma (mul_lseq #a #cr.r x y == mul_lseq #a #cr.r y x) =
  let mul_lseq = mul_lseq #a #cr.r in
  let customprop (k:nat{k<len}) : Type0 = ((mul_lseq x y).[k] == (mul_lseq y x).[k]) in
  let customlemma (k:nat{k<len}) : Lemma (customprop k) =
    cr.lemma_mul_swap x.[k] y.[k] in
  FStar.Classical.forall_intro customlemma;
  eq_intro (mul_lseq x y) (mul_lseq y x);
  eq_elim (mul_lseq x y) (mul_lseq y x)

instance ring_lseq: (#a:Type0) -> (#r:ring a) -> (#len:size_nat) -> ring (lseq a len) =
  fun #a #r #len ->
    {
    zero = zero_lseq;
    one = one_lseq;
    plus = plus_lseq;
    minus = minus_lseq;
    mul = mul_lseq;
    opp = opp_lseq;
    lemma_plus_assoc = lemma_plus_assoc_lseq #a #r;
    lemma_plus_swap = lemma_plus_swap_lseq #a #r;
    lemma_plus_opp1 = lemma_plus_opp1_lseq #a #r;
    lemma_plus_opp2 = lemma_plus_opp2_lseq #a #r;
    lemma_mul_assoc = lemma_mul_assoc_lseq #a #r;
    lemma_distr_left = lemma_distr_left_lseq #a #r;
    lemma_distr_right = lemma_distr_right_lseq #a #r;
    lemma_zero1 = lemma_zero1_lseq #a #r;
    lemma_zero2 = lemma_zero2_lseq #a #r;
    lemma_one1 = lemma_one1_lseq #a #r;
    lemma_one2 = lemma_one2_lseq #a #r;
}

instance commutative_ring_lseq: (#a:Type0) -> (#cr:commutative_ring a) -> (#len:size_nat) -> commutative_ring(lseq a len) =
  fun #a #cr #len ->
    {r = ring_lseq #a #cr.r;
    lemma_mul_swap = lemma_mul_swap_lseq #a #cr;
}
