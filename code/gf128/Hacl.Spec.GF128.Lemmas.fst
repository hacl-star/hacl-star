module Hacl.Spec.GF128.Lemmas

open FStar.Mul
open Lib.IntTypes
open Spec.GaloisField

open FStar.Tactics
open FStar.Algebra.CommMonoid
open FStar.Tactics.CanonCommSemiring

friend Lib.IntTypes

let add_identity a =
  FStar.UInt.logxor_commutative #128 (v a) (v #U128 #SEC (zero #S.gf128));
  FStar.UInt.logxor_lemma_1 #128 (v a);
  v_extensionality (zero ^. a) a

let mul_identity a = admit()

let add_associativity a b c =
  FStar.UInt.logxor_associative #128 (v a) (v b) (v c);
  v_extensionality ((a ^. b) ^. c) (a ^. (b ^. c))

let add_commutativity a b =
  FStar.UInt.logxor_commutative #128 (v a) (v b);
  v_extensionality (a ^. b) (b ^. a)

let mul_associativity a b c = admit()

let mul_commutativity a b = admit()


[@canon_attr]
let elem_add_cm : cm elem =
  CM zero ( +% ) add_identity add_associativity add_commutativity

[@canon_attr]
let elem_mul_cm : cm elem =
  CM one ( *% ) mul_identity mul_associativity mul_commutativity

val mul_add_distr: distribute_left_lemma elem elem_add_cm elem_mul_cm
let mul_add_distr a b c = admit()

val mul_zero_l: mult_zero_l_lemma elem elem_add_cm elem_mul_cm
let mul_zero_l a = admit()

[@canon_attr]
let elem_cr : cr elem = admit() //CR elem_add_cm elem_mul_cm mul_add_distr mul_zero_l

let gf128_semiring () : Tac unit = canon_semiring elem_cr


let gf128_update_multi_mul_add_lemma_load_acc_aux a0 b0 b1 b2 b3 r =
  admit();
  add_identity b1;
  add_identity b2;
  add_identity b3;
  assert (
    (a0 +% b0) *% (r *% (r *% (r *% r))) +% b1 *% (r *% (r *% r)) +% b2 *% (r *% r) +% b3 *% r ==
    ((((a0 +% b0) *% r +% b1) *% r +% b2) *% r +% b3) *% r)
  by (gf128_semiring ())


let gf128_update_multi_mul_add_lemma_loop_aux a0 a1 a2 a3 b0 b1 b2 b3 r =
  admit();
  assert (
    (a0 *% (r *% (r *% (r *% r))) +% b0) *% (r *% (r *% (r *% r))) +%
    (a1 *% (r *% (r *% (r *% r))) +% b1) *% (r *% (r *% r)) +%
    (a2 *% (r *% (r *% (r *% r))) +% b2) *% (r *% r) +%
    (a3 *% (r *% (r *% (r *% r))) +% b3) *% r ==
    ((((a0 *% (r *% (r *% (r *% r))) +%
        a1 *% (r *% (r *% r)) +%
	a2 *% (r *% r) +%
	a3 *% r +% b0) *% r +% b1) *% r +% b2) *% r +% b3) *% r)
  by (gf128_semiring ())


module BV = FStar.BitVector

let to_vec128 (x:uint128) : BV.bv_t 128 = UInt.to_vec #128 (v x)
let to_vec64 (x:uint64) : BV.bv_t 64 = UInt.to_vec #64 (v x)

val to_vec128_lemma : x:elem_s -> Lemma
  (to_vec128 (to_elem x) == Seq.append (to_vec64 x.[1]) (to_vec64 x.[0]))
let to_vec128_lemma x =
  UInt.append_lemma (to_vec64 x.[1]) (to_vec64 x.[0])

val logxor_vec_lemma: x:elem_s -> y:elem_s -> Lemma
  (BV.logxor_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y)) ==
   Seq.append (BV.logxor_vec (to_vec64 x.[1]) (to_vec64 y.[1])) (BV.logxor_vec (to_vec64 x.[0]) (to_vec64 y.[0])))
let logxor_vec_lemma x y =
  to_vec128_lemma x;
  to_vec128_lemma y;
  Seq.lemma_eq_intro
    (BV.logxor_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y)))
    (Seq.append (BV.logxor_vec (to_vec64 x.[1]) (to_vec64 y.[1])) (BV.logxor_vec (to_vec64 x.[0]) (to_vec64 y.[0])))

let logxor_s_lemma x y =
  assert (to_vec128 (to_elem x ^. to_elem y) == BV.logxor_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y)));
  logxor_vec_lemma x y;
  assert (to_vec128 (to_elem x ^. to_elem y) == Seq.append (BV.logxor_vec (to_vec64 x.[1]) (to_vec64 y.[1])) (BV.logxor_vec (to_vec64 x.[0]) (to_vec64 y.[0])));
  let lp = logxor_s x y in
  assert (to_vec64 lp.[0] == BV.logxor_vec (to_vec64 x.[0]) (to_vec64 y.[0]));
  assert (to_vec64 lp.[1] == BV.logxor_vec (to_vec64 x.[1]) (to_vec64 y.[1]));
  to_vec128_lemma lp

val logand_vec_lemma: x:elem_s -> y:elem_s -> Lemma
  (BV.logand_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y)) ==
   Seq.append (BV.logand_vec (to_vec64 x.[1]) (to_vec64 y.[1])) (BV.logand_vec (to_vec64 x.[0]) (to_vec64 y.[0])))
let logand_vec_lemma x y =
  to_vec128_lemma x;
  to_vec128_lemma y;
  Seq.lemma_eq_intro
    (BV.logand_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y)))
    (Seq.append (BV.logand_vec (to_vec64 x.[1]) (to_vec64 y.[1])) (BV.logand_vec (to_vec64 x.[0]) (to_vec64 y.[0])))

let logand_s_lemma x y =
  assert (to_vec128 (to_elem x &. to_elem y) == BV.logand_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y)));
  logand_vec_lemma x y;
  assert (to_vec128 (to_elem x &. to_elem y) == Seq.append (BV.logand_vec (to_vec64 x.[1]) (to_vec64 y.[1])) (BV.logand_vec (to_vec64 x.[0]) (to_vec64 y.[0])));
  let lp = logand_s x y in
  assert (to_vec64 lp.[0] == BV.logand_vec (to_vec64 x.[0]) (to_vec64 y.[0]));
  assert (to_vec64 lp.[1] == BV.logand_vec (to_vec64 x.[1]) (to_vec64 y.[1]));
  to_vec128_lemma lp
