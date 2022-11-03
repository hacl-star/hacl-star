module Hacl.Spec.K256.ECSM.Lemmas

open FStar.Mul

module M = Lib.NatMod
module LE = Lib.Exponentiation
module SE = Spec.Exponentiation

module S = Spec.K256
module LS = Spec.K256.Lemmas

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// [a]P in affine coordinates for a >= 0
let aff_point_mul = S.aff_point_mul

// [a]P in affine coordinates for any a
let aff_point_mul_neg (a:int) (p:S.aff_point) : S.aff_point =
  LE.pow_neg S.mk_k256_abelian_group p a


assume
val lemma_order_of_curve_group (p:S.aff_point) :
  Lemma (aff_point_mul S.q p == S.aff_point_at_inf)

(**
   Properties for Elliptic Curve Scalar Multiplication in affine coordinates
*)

// [a + b]P = [a]P + [b]P
val lemma_aff_point_mul_neg_add (a b:int) (p:S.aff_point) :
  Lemma (aff_point_mul_neg (a + b) p ==
    S.aff_point_add (aff_point_mul_neg a p) (aff_point_mul_neg b p))

let lemma_aff_point_mul_neg_add a b p =
  LE.lemma_pow_neg_add S.mk_k256_abelian_group p a b


// [a * b]P = [b]([a]P)
val lemma_aff_point_mul_neg_mul (a b:int) (p:S.aff_point) :
  Lemma (aff_point_mul_neg (a * b) p == aff_point_mul_neg b (aff_point_mul_neg a p))

let lemma_aff_point_mul_neg_mul a b p =
  LE.lemma_pow_neg_mul S.mk_k256_abelian_group p a b


// [a * b + c]P = [b]([a]P) + [c]P
val lemma_aff_point_mul_neg_mul_add (a b c:int) (p:S.aff_point) :
  Lemma (aff_point_mul_neg (a * b + c) p ==
    S.aff_point_add (aff_point_mul_neg b (aff_point_mul_neg a p)) (aff_point_mul_neg c p))

let lemma_aff_point_mul_neg_mul_add a b c p =
  lemma_aff_point_mul_neg_add (a * b) c p;
  lemma_aff_point_mul_neg_mul a b p


// [a]P = [a % S.q]P
val lemma_aff_point_mul_neg_modq (a:int) (p:S.aff_point) :
  Lemma (aff_point_mul_neg a p == aff_point_mul (a % S.q) p)

let lemma_aff_point_mul_neg_modq a p =
  calc (==) {
    aff_point_mul_neg a p;
    (==) { Math.Lemmas.euclidean_division_definition a S.q }
    aff_point_mul_neg (a / S.q * S.q + a % S.q) p;
    (==) { lemma_aff_point_mul_neg_add (a / S.q * S.q) (a % S.q) p }
    S.aff_point_add (aff_point_mul_neg (a / S.q * S.q) p) (aff_point_mul_neg (a % S.q) p);
    (==) { lemma_aff_point_mul_neg_mul (a / S.q) S.q p }
    S.aff_point_add
      (aff_point_mul S.q (aff_point_mul_neg (a / S.q) p))
      (aff_point_mul (a % S.q) p);
    (==) { lemma_order_of_curve_group (aff_point_mul_neg (a / S.q) p) }
    S.aff_point_add S.aff_point_at_inf (aff_point_mul (a % S.q) p);
    (==) { LS.aff_point_add_comm_lemma S.aff_point_at_inf (aff_point_mul (a % S.q) p) }
    S.aff_point_add (aff_point_mul (a % S.q) p) S.aff_point_at_inf;
    (==) { LS.aff_point_at_inf_lemma (aff_point_mul (a % S.q) p) }
    aff_point_mul (a % S.q) p;
  }


// [a]P = [(-a) % q](-P)
val lemma_aff_point_mul_neg: a:S.qelem -> p:S.aff_point ->
  Lemma (aff_point_mul ((- a) % S.q) (S.aff_point_negate p) == aff_point_mul a p)

let lemma_aff_point_mul_neg a p =
  let cm = S.mk_k256_comm_monoid in
  let ag = S.mk_k256_abelian_group in
  let p_neg = S.aff_point_negate p in
  if a > 0 then begin
    calc (==) {
      aff_point_mul ((- a) % S.q) p_neg;
      (==) { lemma_aff_point_mul_neg_modq (- a) p_neg }
      aff_point_mul_neg (- a) p_neg;
      (==) { }
      S.aff_point_negate (aff_point_mul a p_neg);
      (==) { LE.lemma_inverse_pow ag p a }
      S.aff_point_negate (S.aff_point_negate (aff_point_mul a p));
      (==) { LE.lemma_inverse_id ag (aff_point_mul a p) }
      aff_point_mul a p;
    } end
  else begin
    LE.lemma_pow0 cm p;
    LE.lemma_pow0 cm p_neg end

//--------------------------------------------

// [a]([b]P) = [b]([a]P)
val aff_point_mul_mul_lemma: a:nat -> b:nat -> p:S.aff_point ->
  Lemma (aff_point_mul a (aff_point_mul b p) == aff_point_mul b (aff_point_mul a p))

let aff_point_mul_mul_lemma a b p =
  calc (==) {
    aff_point_mul a (aff_point_mul b p);
    (==) { LE.lemma_pow_mul S.mk_k256_comm_monoid p b a }
    aff_point_mul (a * b) p;
    (==) { LE.lemma_pow_mul S.mk_k256_comm_monoid p a b }
    aff_point_mul b (aff_point_mul a p);
  }


// -[a]P = [a](-P)
val aff_point_mul_neg_lemma: a:nat -> p:S.aff_point ->
  Lemma (S.aff_point_negate (aff_point_mul a p) == aff_point_mul a (S.aff_point_negate p))

let aff_point_mul_neg_lemma a p =
  LE.lemma_inverse_pow S.mk_k256_abelian_group p a


// [a](-[b]P) = [b](-[a]P)
val aff_point_mul_mul_neg_lemma: a:nat -> b:nat -> p:S.aff_point ->
  Lemma (aff_point_mul a (S.aff_point_negate (aff_point_mul b p)) ==
    aff_point_mul b (S.aff_point_negate (aff_point_mul a p)))

let aff_point_mul_mul_neg_lemma a b p =
  let p_neg = S.aff_point_negate p in

  calc (==) {
    aff_point_mul a (S.aff_point_negate (aff_point_mul b p));
    (==) { aff_point_mul_neg_lemma b p }
    aff_point_mul a (aff_point_mul b p_neg);
    (==) { aff_point_mul_mul_lemma a b p_neg }
    aff_point_mul b (aff_point_mul a p_neg);
    (==) { aff_point_mul_neg_lemma a p }
    aff_point_mul b (S.aff_point_negate (aff_point_mul a p));
  }
