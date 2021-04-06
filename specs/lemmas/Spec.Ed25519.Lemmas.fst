module Spec.Ed25519.Lemmas

open FStar.Mul

module Fermat = FStar.Math.Fermat
module Euclid = FStar.Math.Euclid

module LE = Lib.Exponentiation
module LM = Lib.NatMod

open Spec.Curve25519
open Spec.Curve25519.Lemmas
open Spec.Ed25519.PointOps

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

//TODO: use the semiring tactic similar to poly1305

assume val prime_lemma: unit -> Lemma (Euclid.is_prime prime)
// see Theorem 3.3. from https://eprint.iacr.org/2007/286.pdf
// precondition: d is not a square in Z/prime
assume val denominator_lemma: p:aff_point -> q:aff_point -> Lemma
  (requires is_on_curve p /\ is_on_curve q)
  (ensures (let x1, y1 = p in let x2, y2 = q in
    1 +% d *% (x1 *% x2) *% (y1 *% y2) <> zero /\
    1 -% d *% (x1 *% x2) *% (y1 *% y2) <> zero))
assume val denominator_lemma1: y:elem -> Lemma (d *% (y *% y) +% one <> zero)

/////////////////////////////////////
//// Properties for finv and fdiv ///
/////////////////////////////////////

val fdiv_lemma: x:elem{x <> zero} -> Lemma (x /% x == one)
let fdiv_lemma x =
  prime_lemma ();
  LM.lemma_div_mod_prime #prime x

val fdiv_one_lemma: x:elem -> Lemma (x /% one == x)
let fdiv_one_lemma x =
  prime_lemma ();
  LM.lemma_div_mod_prime_one #prime x

val fdiv_one_lemma1: x:elem -> z:elem{z <> zero} -> Lemma (x *% (z *% finv z) == x)
let fdiv_one_lemma1 x z =
  fdiv_lemma z;
  LM.lemma_one_mod #prime x

val fdiv_cancel_lemma: x:elem -> y:elem -> z:elem{z <> zero} -> Lemma ((x *% z) /% (z *% y) == x /% y)
let fdiv_cancel_lemma x y z =
  prime_lemma ();
  LM.lemma_div_mod_prime_cancel #prime x y z

val fdiv_to_one_denominator: x1:elem -> x2:elem -> z1:elem{z1 <> zero} -> z2:elem{z2 <> zero} ->
  Lemma (x1 /% z1 *% (x2 /% z2) == x1 *% x2 /% (z1 *% z2))
let fdiv_to_one_denominator x1 x2 z1 z2 =
  prime_lemma ();
  LM.lemma_div_mod_prime_to_one_denominator #prime x1 x2 z1 z2


val fmul_zero_lemma: x:elem -> y:elem -> Lemma (x *% y == 0 <==> (x == 0 \/ y == 0))
let fmul_zero_lemma x y =
  prime_lemma ();
  if x = 0 || y = 0 then ()
  else
    if (x *% y) = 0 then
      Fermat.mod_mult_congr prime x 0 y
    else ()


val fmul_nonzero_lemma: x:elem -> y:elem -> Lemma
  (requires x <> zero /\ y <> zero)
  (ensures  x *% y <> zero)
let fmul_nonzero_lemma x y =
  fmul_zero_lemma x y


val finv2_nonzero_lemma: x:elem -> y:elem -> Lemma
  (requires x <> zero /\ y <> zero)
  (ensures  finv (x *% y) <> zero)
let finv2_nonzero_lemma x y =
  fmul_nonzero_lemma x y;
  fdiv_lemma (x *% y)


////////////////////////////////////////////
//// Addition laws in affine coordinates ///
////////////////////////////////////////////

val lemma_aff_double_aux: x:elem -> y:elem -> Lemma
  (requires 1 +% d *% (x *% x) *% (y *% y) == y *% y -% x *% x)
  (ensures  1 -% d *% (x *% x) *% (y *% y) == 2 -% y *% y +% x *% x)
let lemma_aff_double_aux x y =
  Math.Lemmas.mod_add_both (1 + d *% (x *% x) *% (y *% y)) (y *% y -% x *% x) (-1) prime;
  assert ((d *% (x *% x) *% (y *% y)) % prime == (y *% y -% x *% x - 1) % prime);
  Math.Lemmas.small_mod (d *% (x *% x) *% (y *% y)) prime;
  assert (d *% (x *% x) *% (y *% y) == y *% y -% x *% x -% 1);
  calc (==) {
    1 -% d *% (x *% x) *% (y *% y);
    (==) { }
    1 -% (y *% y -% x *% x -% 1);
    (==) { }
    (1 - (y *% y -% x *% x - 1) % prime) % prime;
    (==) { Math.Lemmas.lemma_mod_sub_distr 1 (y *% y -% x *% x - 1) prime }
    (2 - (y *% y - x *% x) % prime) % prime;
    (==) { Math.Lemmas.lemma_mod_sub_distr 2 (y *% y - x *% x) prime }
    (2 - (y *% y - x *% x)) % prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (2 - y *% y) (x *% x) prime }
    2 -% y *% y +% x *% x;
    }

//see Theorem 3.1. from https://eprint.iacr.org/2007/286.pdf
let aff_point_add_lemma p q = admit()

let aff_point_add_assoc_lemma p q s = admit()

let aff_point_at_infinity_lemma p =
  let x1, y1 = p in
  let x2, y2 = aff_point_at_infinity in
  let k1 = x1 *% y2 +% y1 *% x2 in
  let k2 = 1 +% d *% (x1 *% x2) *% (y1 *% y2) in
  let k3 = y1 *% y2 +% x1 *% x2 in
  let k4 = 1 -% d *% (x1 *% x2) *% (y1 *% y2) in
  assert (aff_point_add p aff_point_at_infinity == (k1 /% k2, k3 /% k4));
  assert (x2 == zero /\ y2 == one);

  calc (==) {
    k1;
    (==) { }
    x1 *% one +% y1 *% zero;
    (==) { Math.Lemmas.small_mod x1 prime }
    x1;
    };

  calc (==) {
    k2;
    (==) { }
    1 +% d *% (x1 *% zero) *% (y1 *% one);
    (==) { }
    1;
    };

  calc (==) {
    k3;
    (==) { }
    y1 *% one +% x1 *% zero;
    (==) { Math.Lemmas.small_mod y1 prime }
    y1;
    };

  calc (==) {
    k4;
    (==) { }
    1 -% d *% (x1 *% zero) *% (y1 *% one);
    (==) { }
    1;
    };

  fdiv_one_lemma k1;
  fdiv_one_lemma k3

let aff_point_add_comm_lemma p q = ()

let aff_point_double_lemma p =
  let x, y = p in
  let k1 = x *% y +% y *% x in
  let k2 = 1 +% d *% (x *% x) *% (y *% y) in
  let k3 = y *% y +% x *% x in
  let k4 = 1 -% d *% (x *% x) *% (y *% y) in

  let k5 = 2 *% x *% y in
  let k6 = y *% y -% x *% x in
  let k7 = y *% y +% x *% x in
  let k8 = 2 -% y *% y +% x *% x in
  assert (aff_point_add p p == (k1 /% k2, k3 /% k4));
  assert (aff_point_double p == (k5 /% k6, k7 /% k8));

  calc (==) {
    k1;
    (==) { }
    x *% y +% y *% x;
    (==) { Math.Lemmas.modulo_distributivity (x * y) (y * x) prime }
    (x * y + y * x) % prime;
    (==) { Math.Lemmas.paren_mul_right 2 x y }
    (2 * x * y) % prime;
    (==) {Math.Lemmas.lemma_mod_mul_distr_l (2 * x) y prime }
    2 *% x *% y;
    (==) { }
    k5;
    };

  calc (==) {
    k2;
    (==) { }
    1 +% d *% (x *% x) *% (y *% y);
    (==) { }
    y *% y -% x *% x;
    (==) { }
    k6;
    };

  calc (==) {
    k4;
    (==) { }
    1 -% d *% (x *% x) *% (y *% y);
    (==) { lemma_aff_double_aux x y }
    2 -% y *% y +% x *% x;
    (==) { }
    k8;
    }

/////////////////////////////////////////////////////////////////////
//// Pseudo-addition laws in Extended Twisted Edwards Coordinates ///
/////////////////////////////////////////////////////////////////////

val ext_dx1x2y1y2: p:ext_point -> q:ext_point -> Lemma
  (requires is_ext p /\ is_ext q)
  (ensures
   (let _X1, _Y1, _Z1, _T1 = p in
    let _X2, _Y2, _Z2, _T2 = q in
    let x1, y1 = to_aff_point p in
    let x2, y2 = to_aff_point q in
    d *% (x1 *% x2) *% (y1 *% y2) ==
    d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2) *% finv (_Z1 *% _Z2)))

let ext_dx1x2y1y2 p q =
  let _X1, _Y1, _Z1, _T1 = p in
  let _X2, _Y2, _Z2, _T2 = q in
  let x1, y1 = to_aff_point p in
  let x2, y2 = to_aff_point q in
  assert (x1 == _X1 /% _Z1 /\ y1 == _Y1 /% _Z1);
  assert (x2 == _X2 /% _Z2 /\ y2 == _Y2 /% _Z2);
  calc (==) {
    d *% (x1 *% x2) *% (y1 *% y2);
    (==) { fdiv_to_one_denominator _X1 _X2 _Z1 _Z2 }
    d *% (_X1 *% _X2 *% finv (_Z1 *% _Z2)) *% (y1 *% y2);
    (==) { fdiv_to_one_denominator _Y1 _Y2 _Z1 _Z2 }
    d *% (_X1 *% _X2 *% finv (_Z1 *% _Z2)) *% (_Y1 *% _Y2 *% finv (_Z1 *% _Z2));
    (==) { LM.lemma_mul_mod_assoc #prime (d *% (_X1 *% _X2 *% finv (_Z1 *% _Z2))) (_Y1 *% _Y2) (finv (_Z1 *% _Z2)) }
    d *% (_X1 *% _X2 *% finv (_Z1 *% _Z2)) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2);
    (==) { LM.lemma_mul_mod_assoc #prime d (_X1 *% _X2) (finv (_Z1 *% _Z2)) }
    d *% (_X1 *% _X2) *% finv (_Z1 *% _Z2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2);
    (==) {
      LM.lemma_mul_mod_assoc #prime (d *% (_X1 *% _X2)) (finv (_Z1 *% _Z2)) (_Y1 *% _Y2);
      LM.lemma_mul_mod_assoc #prime (d *% (_X1 *% _X2)) (_Y1 *% _Y2) (finv (_Z1 *% _Z2)) }
    d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2) *% finv (_Z1 *% _Z2);
    }


val ext_dx1x2y1y2_mulz1z2: p:ext_point -> q:ext_point -> Lemma
  (requires is_ext p /\ is_ext q)
  (ensures
   (let _X1, _Y1, _Z1, _T1 = p in
    let _X2, _Y2, _Z2, _T2 = q in
    let x1, y1 = to_aff_point p in
    let x2, y2 = to_aff_point q in
    _Z1 *% _Z2 *% (d *% (x1 *% x2) *% (y1 *% y2)) ==
    d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2)))

let ext_dx1x2y1y2_mulz1z2 p q =
  let _X1, _Y1, _Z1, _T1 = p in
  let _X2, _Y2, _Z2, _T2 = q in
  let x1, y1 = to_aff_point p in
  let x2, y2 = to_aff_point q in

  calc (==) {
    _Z1 *% _Z2 *% (d *% (x1 *% x2) *% (y1 *% y2));
    (==) { ext_dx1x2y1y2 p q }
    _Z1 *% _Z2 *% (d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2) *% finv (_Z1 *% _Z2));
    (==) { LM.lemma_mul_mod_comm #prime (_Z1 *% _Z2) (d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2) *% finv (_Z1 *% _Z2)) }
    d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2) *% finv (_Z1 *% _Z2) *% (_Z1 *% _Z2);
    (==) { LM.lemma_mul_mod_assoc #prime (d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2)) (finv (_Z1 *% _Z2)) (_Z1 *% _Z2) }
    d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2) *% (finv (_Z1 *% _Z2) *% (_Z1 *% _Z2));
    (==) { fmul_nonzero_lemma _Z1 _Z2; fdiv_one_lemma1 (d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2)) (_Z1 *% _Z2) }
    d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2);
    }


val ext_dt1t2: p:ext_point -> q:ext_point -> Lemma
  (requires is_ext p /\ is_ext q)
  (ensures
   (let _X1, _Y1, _Z1, _T1 = p in
    let _X2, _Y2, _Z2, _T2 = q in
    d *% _T1 *% _T2 == d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2)))

let ext_dt1t2 p q =
  let _X1, _Y1, _Z1, _T1 = p in
  let _X2, _Y2, _Z2, _T2 = q in
  calc (==) {
    d *% _T1 *% _T2;
    (==) { LM.lemma_mul_mod_assoc #prime d _T1 _T2 }
    d *% (_T1 *% _T2);
    (==) { }
    d *% (_X1 *% _Y1 *% finv _Z1 *% (_X2 *% _Y2 *% finv _Z2));
    (==) { LM.lemma_mul_mod_assoc #prime (_X1 *% _Y1) (finv _Z1) (_X2 *% _Y2 *% finv _Z2) }
    d *% (_X1 *% _Y1 *% (finv _Z1 *% (_X2 *% _Y2 *% finv _Z2)));
    (==) { LM.lemma_mul_mod_comm #prime (_X2 *% _Y2) (finv _Z2) }
    d *% (_X1 *% _Y1 *% (finv _Z1 *% (finv _Z2 *% (_X2 *% _Y2))));
    (==) { LM.lemma_mul_mod_assoc #prime (finv _Z1) (finv _Z2) (_X2 *% _Y2) }
    d *% (_X1 *% _Y1 *% (finv _Z1 *% finv _Z2 *% (_X2 *% _Y2)));
    (==) { LM.lemma_mul_mod_comm #prime (finv _Z1 *% finv _Z2) (_X2 *% _Y2) }
    d *% (_X1 *% _Y1 *% (_X2 *% _Y2 *% (finv _Z1 *% finv _Z2)));
    (==) { LM.lemma_mul_mod_assoc #prime (_X1 *% _Y1) (_X2 *% _Y2) (finv _Z1 *% finv _Z2) }
    d *% (_X1 *% _Y1 *% (_X2 *% _Y2) *% (finv _Z1 *% finv _Z2));
    (==) { prime_lemma(); LM.lemma_inv_mod_both #prime _Z1 _Z2 }
    d *% (_X1 *% _Y1 *% (_X2 *% _Y2) *% finv (_Z1 *% _Z2));
    (==) { LM.lemma_mul_mod_assoc #prime (_X1 *% _Y1) _X2 _Y2 }
    d *% (_X1 *% _Y1 *% _X2 *% _Y2 *% finv (_Z1 *% _Z2));
    (==) {
      LM.lemma_mul_mod_assoc #prime _X1 _Y1 _X2;
      LM.lemma_mul_mod_comm #prime _Y1 _X2;
      LM.lemma_mul_mod_assoc #prime _X1 _X2 _Y1 }
    d *% (_X1 *% _X2 *% _Y1 *% _Y2 *% finv (_Z1 *% _Z2));
    (==) { LM.lemma_mul_mod_assoc #prime (_X1 *% _X2) _Y1 _Y2 }
    d *% ((_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2));
    (==) { LM.lemma_mul_mod_assoc #prime d ((_X1 *% _X2) *% (_Y1 *% _Y2)) (finv (_Z1 *% _Z2)) }
    d *% ((_X1 *% _X2) *% (_Y1 *% _Y2)) *% finv (_Z1 *% _Z2);
    (==) { LM.lemma_mul_mod_assoc #prime d (_X1 *% _X2) (_Y1 *% _Y2) }
    d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2);
    }


val ext_x1x2_plus_y1y2: p:ext_point -> q:ext_point -> Lemma
  (requires is_ext p /\ is_ext q)
  (ensures
   (let _X1, _Y1, _Z1, _T1 = p in
    let _X2, _Y2, _Z2, _T2 = q in
    let x1, y1 = to_aff_point p in
    let x2, y2 = to_aff_point q in
    x1 *% x2 +% y1 *% y2 == (_X1 *% _X2 +% _Y1 *% _Y2) *% finv (_Z1 *% _Z2)))

let ext_x1x2_plus_y1y2 p q =
  let _X1, _Y1, _Z1, _T1 = p in
  let _X2, _Y2, _Z2, _T2 = q in
  let x1, y1 = to_aff_point p in
  let x2, y2 = to_aff_point q in
  assert (x1 == _X1 /% _Z1 /\ y1 == _Y1 /% _Z1);
  assert (x2 == _X2 /% _Z2 /\ y2 == _Y2 /% _Z2);

  calc (==) {
    x1 *% x2 +% y1 *% y2;
    (==) { }
    _X1 *% finv _Z1 *% (_X2 *% finv _Z2) +% _Y1 *% finv _Z1 *% (_Y2 *% finv _Z2);
    (==) { fdiv_to_one_denominator _X1 _X2 _Z1 _Z2; fdiv_to_one_denominator _Y1 _Y2 _Z1 _Z2 }
    _X1 *% _X2 *% finv (_Z1 *% _Z2) +% _Y1 *% _Y2 *% finv (_Z1 *% _Z2);
    (==) { LM.lemma_mod_distributivity_add_left #prime (_X1 *% _X2) (_Y1 *% _Y2) (finv (_Z1 *% _Z2)) }
    (_X1 *% _X2 +% _Y1 *% _Y2) *% finv (_Z1 *% _Z2);
    }


val ext_x1y2_plus_y1x2: p:ext_point -> q:ext_point -> Lemma
  (requires is_ext p /\ is_ext q)
  (ensures
   (let _X1, _Y1, _Z1, _T1 = p in
    let _X2, _Y2, _Z2, _T2 = q in
    let x1, y1 = to_aff_point p in
    let x2, y2 = to_aff_point q in
    x1 *% y2 +% y1 *% x2 == (_X1 *% _Y2 +% _Y1 *% _X2) *% finv (_Z1 *% _Z2)))

let ext_x1y2_plus_y1x2 p q =
  let _X1, _Y1, _Z1, _T1 = p in
  let _X2, _Y2, _Z2, _T2 = q in
  let x1, y1 = to_aff_point p in
  let x2, y2 = to_aff_point q in
  assert (x1 == _X1 /% _Z1 /\ y1 == _Y1 /% _Z1);
  assert (x2 == _X2 /% _Z2 /\ y2 == _Y2 /% _Z2);

  calc (==) {
    x1 *% y2 +% y1 *% x2;
    (==) { }
    _X1 *% finv _Z1 *% (_Y2 *% finv _Z2) +% _Y1 *% finv _Z1 *% (_X2 *% finv _Z2);
    (==) { fdiv_to_one_denominator _X1 _Y2 _Z1 _Z2; fdiv_to_one_denominator _Y1 _X2 _Z1 _Z2 }
    _X1 *% _Y2 *% finv (_Z1 *% _Z2) +% _Y1 *% _X2 *% finv (_Z1 *% _Z2);
    (==) { LM.lemma_mod_distributivity_add_left #prime (_X1 *% _Y2) (_Y1 *% _X2) (finv (_Z1 *% _Z2)) }
    (_X1 *% _Y2 +% _Y1 *% _X2) *% finv (_Z1 *% _Z2);
    }


val ext_yy_minus_xx: p:ext_point -> Lemma
  (requires is_ext p)
  (ensures
   (let _X, _Y, _Z, _T = p in
    let x, y = to_aff_point p in
    y *% y -% x *% x = (_Y *% _Y -% _X *% _X) *% finv (_Z *% _Z)))

let ext_yy_minus_xx p =
  let _X, _Y, _Z, _T = p in
  let x, y = to_aff_point p in
  assert (x == _X /% _Z /\ y == _Y /% _Z);

  calc (==) {
    y *% y -% x *% x;
    (==) { }
    _Y *% finv _Z *% (_Y *% finv _Z) -% _X *% finv _Z *% (_X *% finv _Z);
    (==) { fdiv_to_one_denominator _X _X _Z _Z; fdiv_to_one_denominator _Y _Y _Z _Z }
    _Y *% _Y *% finv (_Z *% _Z) -% _X *% _X *% finv (_Z *% _Z);
    (==) { LM.lemma_mod_distributivity_sub_left #prime (_Y *% _Y) (_X *% _X) (finv (_Z *% _Z)) }
    (_Y *% _Y -% _X *% _X) *% finv (_Z *% _Z);
    }


val ext_2_minus_yy_plus_xx: p:ext_point -> Lemma
  (requires is_ext p)
  (ensures
   (let _X, _Y, _Z, _T = p in
    let x, y = to_aff_point p in
    2 -% y *% y +% x *% x == 2 -% (_Y *% _Y -% _X *% _X) *% finv (_Z *% _Z)))

let ext_2_minus_yy_plus_xx p =
  let _X, _Y, _Z, _T = p in
  let x, y = to_aff_point p in
  assert (x == _X /% _Z /\ y == _Y /% _Z);

  calc (==) {
    2 -% y *% y +% x *% x;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (2 - y *% y) (x *% x) prime }
    (2 - y *% y + x *% x) % prime;
    (==) { }
    (2 - (y *% y - x *% x)) % prime;
    (==) { Math.Lemmas.lemma_mod_sub_distr 2 (y *% y - x *% x) prime }
    (2 - (y *% y -% x *% x)) % prime;
    (==) { ext_yy_minus_xx p }
    2 -% (_Y *% _Y -% _X *% _X) *% finv (_Z *% _Z);
    }


val ext_2_minus_yy_plus_xx_mul_zz: p:ext_point -> Lemma
  (requires is_ext p)
  (ensures
   (let _X, _Y, _Z, _T = p in
    let x, y = to_aff_point p in
    (2 -% y *% y +% x *% x) *% (_Z *% _Z) == 2 *% (_Z *% _Z) -% (_Y *% _Y -% _X *% _X)))

let ext_2_minus_yy_plus_xx_mul_zz p =
  let _X, _Y, _Z, _T = p in
  let x, y = to_aff_point p in
  assert (x == _X /% _Z /\ y == _Y /% _Z);

  calc (==) {
    (2 -% y *% y +% x *% x) *% (_Z *% _Z);
    (==) { ext_2_minus_yy_plus_xx p }
    (2 -% (_Y *% _Y -% _X *% _X) *% finv (_Z *% _Z)) *% (_Z *% _Z);
    (==) { LM.lemma_mod_distributivity_sub_left #prime 2 ((_Y *% _Y -% _X *% _X) *% finv (_Z *% _Z)) (_Z *% _Z) }
    2 *% (_Z *% _Z) -% (_Y *% _Y -% _X *% _X) *% finv (_Z *% _Z) *% (_Z *% _Z);
    (==) { LM.lemma_mul_mod_assoc #prime (_Y *% _Y -% _X *% _X) (finv (_Z *% _Z)) (_Z *% _Z) }
    2 *% (_Z *% _Z) -% (_Y *% _Y -% _X *% _X) *% (finv (_Z *% _Z) *% (_Z *% _Z));
    (==) { LM.lemma_mul_mod_comm #prime (finv (_Z *% _Z)) (_Z *% _Z) }
    2 *% (_Z *% _Z) -% (_Y *% _Y -% _X *% _X) *% ((_Z *% _Z) *% finv (_Z *% _Z));
    (==) { fmul_nonzero_lemma _Z _Z; fdiv_one_lemma1 (_Y *% _Y -% _X *% _X) (_Z *% _Z) }
    2 *% (_Z *% _Z) -% (_Y *% _Y -% _X *% _X);
    }


val ext_denominator_lemma1: p:ext_point -> q:ext_point -> Lemma
  (requires
    is_ext p /\ is_ext q /\
    is_on_curve (to_aff_point p) /\ is_on_curve (to_aff_point q))
  (ensures (let _X1, _Y1, _Z1, _T1 = p in let _X2, _Y2, _Z2, _T2 = q in
    _Z1 *% _Z2 +% d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2) <> zero /\
    _Z1 *% _Z2 -% d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2) <> zero))

let ext_denominator_lemma1 p q =
  let _X1, _Y1, _Z1, _T1 = p in
  let _X2, _Y2, _Z2, _T2 = q in
  let x1, y1 = to_aff_point p in
  let x2, y2 = to_aff_point q in

  let p1 = 1 +% d *% (x1 *% x2) *% (y1 *% y2) in
  calc (==) {
    _Z1 *% _Z2 *% p1;
    (==) { LM.lemma_mod_distributivity_add_right #prime (_Z1 *% _Z2) one (d *% (x1 *% x2) *% (y1 *% y2)) }
    _Z1 *% _Z2 *% one +% _Z1 *% _Z2 *% (d *% (x1 *% x2) *% (y1 *% y2));
    (==) { Math.Lemmas.small_mod (_Z1 *% _Z2) prime }
    _Z1 *% _Z2 +% _Z1 *% _Z2 *% (d *% (x1 *% x2) *% (y1 *% y2));
    (==) { ext_dx1x2y1y2_mulz1z2 p q }
    _Z1 *% _Z2 +% d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2);
    };

  let p2 = 1 -% d *% (x1 *% x2) *% (y1 *% y2) in
  calc (==) {
    _Z1 *% _Z2 *% p2;
    (==) { LM.lemma_mod_distributivity_sub_right #prime (_Z1 *% _Z2) one (d *% (x1 *% x2) *% (y1 *% y2)) }
    _Z1 *% _Z2 *% one -% _Z1 *% _Z2 *% (d *% (x1 *% x2) *% (y1 *% y2));
    (==) { Math.Lemmas.small_mod (_Z1 *% _Z2) prime }
    _Z1 *% _Z2 -% _Z1 *% _Z2 *% (d *% (x1 *% x2) *% (y1 *% y2));
    (==) { ext_dx1x2y1y2_mulz1z2 p q }
    _Z1 *% _Z2 -% d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2);
    };

  denominator_lemma (x1, y1) (x2, y2);
  assert (p1 <> zero);
  assert (p2 <> zero);

  fmul_nonzero_lemma _Z1 _Z2;
  fmul_nonzero_lemma (_Z1 *% _Z2) p1;
  fmul_nonzero_lemma (_Z1 *% _Z2) p2


val ext_denominator_lemma2: p:ext_point -> Lemma
  (requires
    is_ext p /\ is_on_curve (to_aff_point p))
  (ensures (let _X, _Y, _Z, _T = p in
    2 *% (_Z *% _Z) -% (_Y *% _Y -% _X *% _X) <> zero /\
    _Y *% _Y -% _X *% _X <> zero))

let ext_denominator_lemma2 p =
  let _X, _Y, _Z, _T = p in
  let x, y = to_aff_point p in

  let p2 = 1 -% d *% (x *% x) *% (y *% y) in
  calc (==) {
    p2 *% (_Z *% _Z);
    (==) { lemma_aff_double_aux x y }
    (2 -% y *% y +% x *% x) *% (_Z *% _Z);
    (==) { ext_2_minus_yy_plus_xx_mul_zz p }
    2 *% (_Z *% _Z) -% (_Y *% _Y -% _X *% _X);
    };

  let p1 = 1 +% d *% (x *% x) *% (y *% y) in
  calc (==) {
    p1 *% (_Z *% _Z);
    (==) { }
    (y *% y -% x *% x) *% (_Z *% _Z);
    (==) { ext_yy_minus_xx p }
    (_Y *% _Y -% _X *% _X) *% finv (_Z *% _Z) *% (_Z *% _Z);
    (==) { LM.lemma_mul_mod_assoc #prime (_Y *% _Y -% _X *% _X) (finv (_Z *% _Z)) (_Z *% _Z) }
    (_Y *% _Y -% _X *% _X) *% (finv (_Z *% _Z) *% (_Z *% _Z));
    (==) { fmul_nonzero_lemma _Z _Z; fdiv_one_lemma1 (_Y *% _Y -% _X *% _X) (_Z *% _Z) }
    (_Y *% _Y -% _X *% _X);
    };

  denominator_lemma (x, y) (x, y);
  assert (p1 <> zero);
  assert (p2 <> zero);

  fmul_nonzero_lemma _Z _Z;
  fmul_nonzero_lemma p2 (_Z *% _Z);
  assert (2 *% (_Z *% _Z) -% (_Y *% _Y -% _X *% _X) <> zero);
  fmul_nonzero_lemma p1 (_Z *% _Z);
  assert (_Y *% _Y -% _X *% _X <> zero)


val lemma_neg_sqr: x:elem -> Lemma ((-x) % prime *% ((-x) % prime) == x *% x)
let lemma_neg_sqr x =
  calc (==) {
    (- x) % prime * ((- x) % prime) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (- x) ((- x) % prime) prime }
    (- x) * ((- x) % prime) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (- x) (- x) prime }
    (- x) * (- x) % prime;
    (==) { Math.Lemmas.neg_mul_left x (- x); Math.Lemmas.neg_mul_right x x }
    (x * x) % prime;
  }


let aff_point_negate_lemma p =
  let (x, y) = p in
  assert (aff_point_negate p == ((-x) % prime, y));
  //assert (y *% y -% x *% x == 1 +% d *% (x *% x) *% (y *% y));
  lemma_neg_sqr x;
  assert (is_on_curve (aff_point_negate p))


let to_aff_point_at_infinity_lemma () =
  let x, y = to_aff_point point_at_infinity in
  assert (point_at_infinity == (zero, one, one, zero));
  assert (aff_point_at_infinity == (zero, one));
  assert (x == zero /% one /\ y == one /% one);
  fdiv_one_lemma zero;
  fdiv_one_lemma one


val point_add_expand_eh_lemma: p:ext_point -> q:ext_point -> Lemma (
  let _X1, _Y1, _Z1, _T1 = p in
  let _X2, _Y2, _Z2, _T2 = q in

  let a = (_Y1 -% _X1) *% (_Y2 -% _X2) in
  let b = (_Y1 +% _X1) *% (_Y2 +% _X2) in
  let e = b -% a in
  let h = b +% a in
  e == 2 *% (_X1 *% _Y2 +% _Y1 *% _X2) /\
  h == 2 *% (_X1 *% _X2 +% _Y1 *% _Y2))

let point_add_expand_eh_lemma p q =
  let _X1, _Y1, _Z1, _T1 = p in
  let _X2, _Y2, _Z2, _T2 = q in

  let a = (_Y1 -% _X1) *% (_Y2 -% _X2) in
  let b = (_Y1 +% _X1) *% (_Y2 +% _X2) in
  let e = b -% a in
  let h = b +% a in

  calc (==) { //a
    (_Y1 -% _X1) *% (_Y2 -% _X2);
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (_Y1 - _X1) (_Y2 -% _X2) prime }
    (_Y1 - _X1) * (_Y2 -% _X2) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (_Y1 - _X1) (_Y2 - _X2) prime }
    (_Y1 - _X1) * (_Y2 - _X2) % prime;
    (==) { Math.Lemmas.distributivity_sub_right (_Y1 - _X1) _Y2 _X2 }
    ((_Y1 - _X1) * _Y2 - (_Y1 - _X1) * _X2) % prime;
    (==) { Math.Lemmas.distributivity_sub_left _Y1 _X1 _Y2 }
    (_Y1 * _Y2 - _X1 * _Y2 - (_Y1 - _X1) * _X2) % prime;
    (==) { Math.Lemmas.distributivity_sub_left _Y1 _X1 _X2 }
    (_Y1 * _Y2 - _X1 * _Y2 - _Y1 * _X2 + _X1 * _X2) % prime;
    };

  calc (==) { //b
    (_Y1 +% _X1) *% (_Y2 +% _X2);
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (_Y1 + _X1) (_Y2 +% _X2) prime }
    (_Y1 + _X1) * (_Y2 +% _X2) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (_Y1 + _X1) (_Y2 + _X2) prime }
    (_Y1 + _X1) * (_Y2 + _X2) % prime;
    (==) { Math.Lemmas.distributivity_add_right (_Y1 + _X1) _Y2 _X2 }
    ((_Y1 + _X1) * _Y2 + (_Y1 + _X1) * _X2) % prime;
    (==) { Math.Lemmas.distributivity_add_left _Y1 _X1 _Y2 }
    (_Y1 * _Y2 + _X1 * _Y2 + (_Y1 + _X1) * _X2) % prime;
    (==) { Math.Lemmas.distributivity_add_left _Y1 _X1 _X2 }
    (_Y1 * _Y2 + _X1 * _Y2 + _Y1 * _X2 + _X1 * _X2) % prime;
    };

  let p1 = _Y1 * _Y2 + _X1 * _Y2 + _Y1 * _X2 + _X1 * _X2 in
  let p2 = _Y1 * _Y2 - _X1 * _Y2 - _Y1 * _X2 + _X1 * _X2 in
  calc (==) { //e = b -% a;
    (_Y1 +% _X1) *% (_Y2 +% _X2) -% (_Y1 -% _X1) *% (_Y2 -% _X2);
    (==) { }
    (p1 % prime - p2 % prime) % prime;
    (==) { Math.Lemmas.lemma_mod_sub_distr (p1 % prime) p2 prime }
    (p1 % prime - p2) % prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l p1 (- p2) prime }
    (p1 - p2) % prime;
    (==) { }
    (_Y1 * _Y2 + _X1 * _Y2 + _Y1 * _X2 + _X1 * _X2 - _Y1 * _Y2 + _X1 * _Y2 + _Y1 * _X2 - _X1 * _X2) % prime;
    (==) { }
    (_X1 * _Y2 + _Y1 * _X2 + _X1 * _Y2 + _Y1 * _X2) % prime;
    (==) { }
    (2 * (_X1 * _Y2) + 2 * (_Y1 * _X2)) % prime;
    (==) { Math.Lemmas.distributivity_add_right 2 (_X1 * _Y2) (_Y1 * _X2) }
    2 * (_X1 * _Y2 + _Y1 * _X2) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r 2 (_X1 * _Y2 + _Y1 * _X2) prime }
    2 * ((_X1 * _Y2 + _Y1 * _X2) % prime) % prime;
    (==) { Math.Lemmas.modulo_distributivity (_X1 * _Y2) (_Y1 * _X2) prime }
    2 *% (_X1 *% _Y2 +% _Y1 *% _X2);
    };

  calc (==) { //h = b +% a;
    (_Y1 +% _X1) *% (_Y2 +% _X2) +% (_Y1 -% _X1) *% (_Y2 -% _X2);
    (==) { }
    (p1 % prime + p2 % prime) % prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r (p1 % prime) p2 prime }
    (p1 % prime + p2) % prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l p1 p2 prime }
    (p1 + p2) % prime;
    (==) { }
    (_Y1 * _Y2 + _X1 * _Y2 + _Y1 * _X2 + _X1 * _X2 + _Y1 * _Y2 - _X1 * _Y2 - _Y1 * _X2 + _X1 * _X2) % prime;
    (==) { }
    (_Y1 * _Y2 + _X1 * _X2 + _Y1 * _Y2 + _X1 * _X2) % prime;
    (==) { }
    (2 * (_Y1 * _Y2) + 2 * (_X1 * _X2)) % prime;
    (==) { Math.Lemmas.distributivity_add_right 2 (_Y1 * _Y2) (_X1 * _X2) }
    2 * (_X1 * _X2 + _Y1 * _Y2) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r 2 (_X1 * _X2 + _Y1 * _Y2) prime }
    2 * ((_X1 * _X2 + _Y1 * _Y2) % prime) % prime;
    (==) { Math.Lemmas.modulo_distributivity (_X1 * _X2) (_Y1 * _Y2) prime }
    2 *% (_X1 *% _X2 +% _Y1 *% _Y2);
    }


val point_add_expand_gf_lemma: p:ext_point{is_ext p} -> q:ext_point{is_ext q} -> Lemma (
  let _X1, _Y1, _Z1, _T1 = p in
  let _X2, _Y2, _Z2, _T2 = q in

  let c =  2 *% d *% _T1 *% _T2 in
  let d1 = 2 *% _Z1 *% _Z2 in
  let f = d1 -% c in
  let g = d1 +% c in
  let k = d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2) in
  f == 2 *% (_Z1 *% _Z2 -% k) /\
  g == 2 *% (_Z1 *% _Z2 +% k))

let point_add_expand_gf_lemma p q =
  let _X1, _Y1, _Z1, _T1 = p in
  let _X2, _Y2, _Z2, _T2 = q in

  let c =  2 *% d *% _T1 *% _T2 in
  let d1 = 2 *% _Z1 *% _Z2 in
  let f = d1 -% c in
  let g = d1 +% c in
  let d2 = 2 *% d in
  let k = d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2) in

  calc (==) { //c
    d2 *% _T1 *% _T2;
    (==) {
      LM.lemma_mul_mod_assoc #prime 2 d _T1;
      LM.lemma_mul_mod_assoc #prime 2 (d *% _T1) _T2 }
    2 *% (d *% _T1 *% _T2);
    (==) { ext_dt1t2 p q }
    2 *% k;
    };

  calc (==) { //f == d1 -% c
    2 *% _Z1 *% _Z2 -% d2 *% _T1 *% _T2;
    (==) { }
    2 *% _Z1 *% _Z2 -% 2 *% k;
    (==) { LM.lemma_mul_mod_assoc #prime 2 _Z1 _Z2 }
    2 *% (_Z1 *% _Z2) -% 2 *% k;
    (==) { LM.lemma_mod_distributivity_sub_right #prime 2 (_Z1 *% _Z2) k }
    2 *% (_Z1 *% _Z2 -% k);
    };

  assert (f == 2 *% (_Z1 *% _Z2 -% k));

  calc (==) { //g == d1 +% c
    2 *% _Z1 *% _Z2 +% d2 *% _T1 *% _T2;
    (==) { }
    2 *% _Z1 *% _Z2 +% 2 *% k;
    (==) { LM.lemma_mul_mod_assoc #prime 2 _Z1 _Z2 }
    2 *% (_Z1 *% _Z2) +% 2 *% k;
    (==) { LM.lemma_mod_distributivity_add_right #prime 2 (_Z1 *% _Z2) k }
    2 *% (_Z1 *% _Z2 +% k);
    };

  assert (g == 2 *% (_Z1 *% _Z2 +% k))


val point_add_expand_gf_lemma_non_zero: p:ext_point -> q:ext_point -> Lemma
  (requires
    is_ext p /\ is_ext q /\
    is_on_curve (to_aff_point p) /\ is_on_curve (to_aff_point q))
  (ensures
    (let _X1, _Y1, _Z1, _T1 = p in
    let _X2, _Y2, _Z2, _T2 = q in
    let c = 2 *% d *% _T1 *% _T2 in
    let d1 = 2 *% _Z1 *% _Z2 in
    let f = d1 -% c in
    let g = d1 +% c in
    f <> zero /\ g <> zero))

let point_add_expand_gf_lemma_non_zero p q =
  let _X1, _Y1, _Z1, _T1 = p in
  let _X2, _Y2, _Z2, _T2 = q in

  let c = (2 *% d *% _T1) *% _T2 in
  let d1 = (2 *% _Z1) *% _Z2 in
  let f = d1 -% c in
  let g = d1 +% c in
  let k = d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2) in
  let p1 = _Z1 *% _Z2 +% k in
  let p2 = _Z1 *% _Z2 -% k in

  point_add_expand_gf_lemma p q;
  assert (g == 2 *% p1);
  assert (f == 2 *% p2);
  ext_denominator_lemma1 p q;
  assert (p1 <> zero);
  assert (p2 <> zero);
  fmul_nonzero_lemma 2 p1;
  fmul_nonzero_lemma 2 p2


val fghe_relation: f:elem -> g:elem -> h:elem -> e:elem -> Lemma
  (requires f <> zero /\ g <> zero)
  (ensures
   (let _X3 = e *% f in
    let _Y3 = g *% h in
    let _T3 = e *% h in
    let _Z3 = f *% g in
    _Z3 <> zero /\ _X3 *% _Y3 /% _Z3 == e *% h /\
    _X3 /% _Z3 == e /% g /\ _Y3 /% _Z3 == h /% f))

let fghe_relation f g h e =
  let _X3 = e *% f in
  let _Y3 = g *% h in
  let _T3 = e *% h in
  let _Z3 = f *% g in

  fmul_nonzero_lemma f g;
  assert (_Z3 <> zero);

  calc (==) {
    _Y3 /% _Z3;
    (==) { }
    g *% h /% (f *% g);
    (==) { LM.lemma_mul_mod_comm #prime g h; LM.lemma_mul_mod_comm #prime f g }
    h *% g *% finv (g *% f);
    (==) { fdiv_cancel_lemma h f g }
    h /% f;
    };

  calc (==) {
    _X3 *% _Y3 /% _Z3;
    (==) { LM.lemma_mul_mod_assoc #prime _X3 _Y3 (finv _Z3) }
    _X3 *% (_Y3 /% _Z3);
    (==) { }
    e *% f *% (h /% f);
    (==) { LM.lemma_mul_mod_comm #prime (finv f) h; LM.lemma_mul_mod_assoc #prime (e *% f) (finv f) h }
    e *% f *% finv f *% h;
    (==) { LM.lemma_mul_mod_assoc #prime e f (finv f); fdiv_one_lemma1 e f }
    e *% h;
    };

  fdiv_cancel_lemma e g f;
  assert (_X3 /% _Z3 == e /% g)


let to_aff_point_add_lemma p q =
  let _X1, _Y1, _Z1, _T1 = p in
  let _X2, _Y2, _Z2, _T2 = q in

  let x1, y1 = to_aff_point p in
  let x2, y2 = to_aff_point q in
  assert (x1 == _X1 /% _Z1 /\ y1 == _Y1 /% _Z1);
  assert (x2 == _X2 /% _Z2 /\ y2 == _Y2 /% _Z2);

  let k1 = x1 *% y2 +% y1 *% x2 in
  let k2 = 1 +% d *% (x1 *% x2) *% (y1 *% y2) in
  let k3 = y1 *% y2 +% x1 *% x2 in
  let k4 = 1 -% d *% (x1 *% x2) *% (y1 *% y2) in
  assert (aff_point_add (x1, y1) (x2, y2) == (k1 /% k2, k3 /% k4));

  let a = (_Y1 -% _X1) *% (_Y2 -% _X2) in
  let b = (_Y1 +% _X1) *% (_Y2 +% _X2) in
  let c = (2 *% d *% _T1) *% _T2 in
  let d1 = (2 *% _Z1) *% _Z2 in
  let e = b -% a in
  let f = d1 -% c in
  let g = d1 +% c in
  let h = b +% a in
  let _X3 = e *% f in
  let _Y3 = g *% h in
  let _T3 = e *% h in
  let _Z3 = f *% g in
  assert ((_X3, _Y3, _Z3, _T3) == point_add p q);

  point_add_expand_gf_lemma_non_zero p q;
  assert (f <> zero /\ g <> zero);
  fghe_relation f g h e;
  assert (_X3 /% _Z3 == e /% g);
  assert (_Y3 /% _Z3 == h /% f);
  assert (is_ext (_X3, _Y3, _Z3, _T3));

  point_add_expand_gf_lemma p q;
  point_add_expand_eh_lemma p q;
  let k = d *% (_X1 *% _X2) *% (_Y1 *% _Y2) *% finv (_Z1 *% _Z2) in

  calc (==) { //_X3 /% _Z3
    e /% g;
    (==) { }
    2 *% (_X1 *% _Y2 +% _Y1 *% _X2) /% (2 *% (_Z1 *% _Z2 +% k));
    (==) { fdiv_cancel_lemma (_X1 *% _Y2 +% _Y1 *% _X2) (_Z1 *% _Z2 +% k) 2 }
    (_X1 *% _Y2 +% _Y1 *% _X2) /% (_Z1 *% _Z2 +% k);
    (==) { finv2_nonzero_lemma _Z1 _Z2; fdiv_cancel_lemma (_X1 *% _Y2 +% _Y1 *% _X2) (_Z1 *% _Z2 +% k) (finv (_Z1 *% _Z2)) }
    (_X1 *% _Y2 +% _Y1 *% _X2) *% finv (_Z1 *% _Z2) /% ((_Z1 *% _Z2 +% k) *% finv (_Z1 *% _Z2));
    (==) { ext_x1y2_plus_y1x2 p q }
    k1 /% ((_Z1 *% _Z2 +% k) *% finv (_Z1 *% _Z2));
    (==) { LM.lemma_mod_distributivity_add_left #prime (_Z1 *% _Z2) k (finv (_Z1 *% _Z2)) }
    k1 /% (_Z1 *% _Z2 *% finv (_Z1 *% _Z2) +% k *% finv (_Z1 *% _Z2));
    (==) { fmul_nonzero_lemma _Z1 _Z2; fdiv_lemma (_Z1 *% _Z2) }
    k1 /% (1 +% k *% finv (_Z1 *% _Z2));
    (==) { ext_dx1x2y1y2 p q }
    k1 /% k2;
    };

  calc (==) { //_Y3 /% _Z3
    h /% f;
    (==) { }
    2 *% (_X1 *% _X2 +% _Y1 *% _Y2) /% (2 *% (_Z1 *% _Z2 -% k));
    (==) { fdiv_cancel_lemma (_X1 *% _X2 +% _Y1 *% _Y2) (_Z1 *% _Z2 -% k) 2 }
    (_X1 *% _X2 +% _Y1 *% _Y2) /% (_Z1 *% _Z2 -% k);
    (==) { finv2_nonzero_lemma _Z1 _Z2; fdiv_cancel_lemma (_X1 *% _X2 +% _Y1 *% _Y2) (_Z1 *% _Z2 -% k) (finv (_Z1 *% _Z2)) }
    (_X1 *% _X2 +% _Y1 *% _Y2) *% finv (_Z1 *% _Z2) /% ((_Z1 *% _Z2 -% k) *% finv (_Z1 *% _Z2));
    (==) { ext_x1x2_plus_y1y2 p q }
    k3 /% ((_Z1 *% _Z2 -% k) *% finv (_Z1 *% _Z2));
    (==) { LM.lemma_mod_distributivity_sub_left #prime (_Z1 *% _Z2) k (finv (_Z1 *% _Z2)) }
    k3 /% (_Z1 *% _Z2 *% finv (_Z1 *% _Z2) -% k *% finv (_Z1 *% _Z2));
    (==) { fmul_nonzero_lemma _Z1 _Z2; fdiv_lemma (_Z1 *% _Z2) }
    k3 /% (1 -% k *% finv (_Z1 *% _Z2));
    (==) { ext_dx1x2y1y2 p q }
    k3 /% k4;
    };
  assert (k1 /% k2 == _X3 /% _Z3 /\ k3 /% k4 == _Y3 /% _Z3);
  aff_point_add_lemma (to_aff_point p) (to_aff_point q)


val point_double_expand_eh_lemma: p:ext_point{is_ext p} -> Lemma (
  let _X, _Y, _Z, _T = p in

  let a = _X *% _X in
  let b = _Y *% _Y in
  let h = a +% b in
  let e = h -% ((_X +% _Y) *% (_X +% _Y)) in
  h == _X *% _X +% _Y *% _Y /\
  e == (- 1) % prime *% (2 *% (_X *% _Y)))

let point_double_expand_eh_lemma p =
  let _X, _Y, _Z, _T = p in

  let a = _X *% _X in
  let b = _Y *% _Y in
  let h = a +% b in
  let e = h -% ((_X +% _Y) *% (_X +% _Y)) in
  assert (h == _X *% _X +% _Y *% _Y);

  calc (==) {
    (_X +% _Y) *% (_X +% _Y);
    (==) { LM.lemma_mod_distributivity_add_right #prime (_X +% _Y) _X _Y }
    (_X +% _Y) *% _X +% (_X +% _Y) *% _Y;
    (==) { LM.lemma_mod_distributivity_add_left #prime _X _Y _X }
    _X *% _X +% _Y *% _X +% (_X +% _Y) *% _Y;
    (==) { LM.lemma_mod_distributivity_add_left #prime _X _Y _Y }
    _X *% _X +% _Y *% _X +% (_X *% _Y +% _Y *% _Y);
    };

  calc (==) {
    h -% ((_X +% _Y) *% (_X +% _Y));
    (==) { }
    (_X *% _X +% _Y *% _Y - (_X *% _X +% _Y *% _X +% (_X *% _Y +% _Y *% _Y))) % prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (_X *% _X + _Y *% _Y) (- (_X *% _X +% _Y *% _X +% (_X *% _Y +% _Y *% _Y))) prime }
    (_X *% _X + _Y *% _Y - (_X *% _X +% _Y *% _X +% (_X *% _Y +% _Y *% _Y))) % prime;
    (==) { Math.Lemmas.modulo_distributivity (_X *% _X + _Y *% _X) (_X *% _Y + _Y *% _Y) prime }
    (_X *% _X + _Y *% _Y - (_X *% _X + _Y *% _X + (_X *% _Y + _Y *% _Y)) % prime) % prime;
    (==) { Math.Lemmas.lemma_mod_sub_distr (_X *% _X + _Y *% _Y) (_X *% _X + _Y *% _X + (_X *% _Y + _Y *% _Y)) prime }
    (_X *% _X + _Y *% _Y - (_X *% _X + _Y *% _X + (_X *% _Y + _Y *% _Y))) % prime;
    (==) { }
    (_X *% _X + _Y *% _Y - _X *% _X - _Y *% _X - _X *% _Y - _Y *% _Y) % prime;
    (==) { }
    (- _Y *% _X - _X *% _Y) % prime;
    (==) { }
    (- 2 * (_X *% _Y)) % prime;
    (==) { }
    ((- 1) * 2 * (_X *% _Y)) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (- 1) (2 * (_X *% _Y)) prime }
    ((- 1) % prime * (2 * (_X *% _Y))) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r ((- 1) % prime) (2 * (_X *% _Y)) prime }
    (- 1) % prime *% (2 *% (_X *% _Y));
    };
  assert (e == (- 1) % prime *% (2 *% (_X *% _Y)))


val point_double_expand_gf_lemma: p:ext_point{is_ext p} -> Lemma (
  let _X, _Y, _Z, _T = p in

  let a = _X *% _X in
  let b = _Y *% _Y in
  let c = 2 *% (_Z *% _Z) in
  let g = a -% b in
  let f = c +% g in
  f == 2 *% (_Z *% _Z) -% (_Y *% _Y -% _X *% _X) /\
  g == (-1) % prime *% (_Y *% _Y -% _X *% _X))

let point_double_expand_gf_lemma p =
  let _X, _Y, _Z, _T = p in

  let a = _X *% _X in
  let b = _Y *% _Y in
  let c = 2 *% (_Z *% _Z) in
  let g = a -% b in
  let f = c +% g in
  assert (g == _X *% _X -% _Y *% _Y);
  assert (f == 2 *% (_Z *% _Z) +% (_X *% _X -% _Y *% _Y));

  calc (==) { //g
    _X *% _X -% _Y *% _Y;
    (==) { }
    (-1) * (_Y *% _Y - _X *% _X) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (- 1) (_Y *% _Y - _X *% _X) prime }
    (-1) % prime * (_Y *% _Y - _X *% _X) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r ((- 1) % prime) (_Y *% _Y - _X *% _X) prime }
    (-1) % prime *% (_Y *% _Y -% _X *% _X);
    };

  calc (==) { //f
    2 *% (_Z *% _Z) +% (_X *% _X -% _Y *% _Y);
    (==) { }
    (2 *% (_Z *% _Z) + (_X *% _X -% _Y *% _Y)) % prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r (2 *% (_Z *% _Z)) (_X *% _X - _Y *% _Y) prime }
    (2 *% (_Z *% _Z) + (_X *% _X - _Y *% _Y)) % prime;
    (==) { }
    (2 *% (_Z *% _Z) - (_Y *% _Y - _X *% _X)) % prime;
    (==) { Math.Lemmas.lemma_mod_sub_distr (2 *% (_Z *% _Z)) (_Y *% _Y - _X *% _X) prime }
    (2 *% (_Z *% _Z) -% (_Y *% _Y -% _X *% _X));
    }


val point_double_expand_gf_lemma_non_zero: p:ext_point -> Lemma
  (requires
    is_ext p /\ is_on_curve (to_aff_point p))
  (ensures
   (let _X, _Y, _Z, _T = p in

    let a = _X *% _X in
    let b = _Y *% _Y in
    let c = 2 *% (_Z *% _Z) in
    let g = a -% b in
    let f = c +% g in
    f <> zero /\ g <> zero))

let point_double_expand_gf_lemma_non_zero p =
  let _X, _Y, _Z, _T = p in

  let a = _X *% _X in
  let b = _Y *% _Y in
  let c = 2 *% (_Z *% _Z) in
  let g = a -% b in
  let f = c +% g in
  point_double_expand_gf_lemma p;
  assert (f == 2 *% (_Z *% _Z) -% (_Y *% _Y -% _X *% _X));
  assert (g == (-1) % prime *% (_Y *% _Y -% _X *% _X));
  ext_denominator_lemma2 p;
  assert (f <> zero);
  assert (_Y *% _Y -% _X *% _X <> zero);
  fmul_zero_lemma ((-1) % prime) (_Y *% _Y -% _X *% _X)


let to_aff_point_double_lemma p =
  let _X, _Y, _Z, _T = p in
  let x, y = to_aff_point p in
  assert (x == _X /% _Z /\ y == _Y /% _Z);

  let k1 = 2 *% x *% y in
  let k2 = y *% y -% x *% x in
  let k3 = y *% y +% x *% x in
  let k4 = 2 -% y *% y +% x *% x in
  assert (aff_point_double (x, y) == (k1 /% k2, k3 /% k4));

  let a = _X *% _X in
  let b = _Y *% _Y in
  let c = 2 *% (_Z *% _Z) in
  let h = a +% b in
  let e = h -% ((_X +% _Y) *% (_X +% _Y)) in
  let g = a -% b in
  let f = c +% g in
  let _X3 = e *% f in
  let _Y3 = g *% h in
  let _T3 = e *% h in
  let _Z3 = f *% g in
  assert ((_X3, _Y3, _Z3, _T3) == point_double p);

  point_double_expand_gf_lemma_non_zero p;
  assert (f <> zero /\ g <> zero);

  fghe_relation f g h e;
  assert (_X3 /% _Z3 == e /% g);
  assert (_Y3 /% _Z3 == h /% f);
  assert (is_ext (_X3, _Y3, _Z3, _T3));

  point_double_expand_eh_lemma p;
  point_double_expand_gf_lemma p;

  calc (==) { //_X3 /% _Z3
    e /% g;
    (==) { }
    (- 1) % prime *% (2 *% (_X *% _Y)) /% ((-1) % prime *% (_Y *% _Y -% _X *% _X));
    (==) { fdiv_cancel_lemma (2 *% (_X *% _Y)) (_Y *% _Y -% _X *% _X) ((- 1) % prime) }
    2 *% (_X *% _Y) /% (_Y *% _Y -% _X *% _X);
    (==) { finv2_nonzero_lemma _Z _Z; fdiv_cancel_lemma (2 *% (_X *% _Y)) (_Y *% _Y -% _X *% _X) (finv (_Z *% _Z)) }
    2 *% (_X *% _Y) *% finv (_Z *% _Z) /% (finv (_Z *% _Z) *% (_Y *% _Y -% _X *% _X));
    (==) { ext_yy_minus_xx p }
    2 *% (_X *% _Y) *% finv (_Z *% _Z) /% k2;
    (==) { LM.lemma_mul_mod_assoc #prime 2 (_X *% _Y) (finv (_Z *% _Z)); fdiv_to_one_denominator _X _Y _Z _Z }
    2 *% (x *% y) /% k2;
    (==) { LM.lemma_mul_mod_assoc #prime 2 x y }
    k1 /% k2;
    };

  calc (==) { //_Y3 /% _Z3
    h /% f;
    (==) { }
    (_X *% _X +% _Y *% _Y) /% (2 *% (_Z *% _Z) -% (_Y *% _Y -% _X *% _X));
    (==) { ext_2_minus_yy_plus_xx_mul_zz p }
    (_X *% _X +% _Y *% _Y) /% (k4 *% (_Z *% _Z));
    (==) { finv2_nonzero_lemma _Z _Z; fdiv_cancel_lemma (_X *% _X +% _Y *% _Y) (k4 *% (_Z *% _Z)) (finv (_Z *% _Z)) }
    (_X *% _X +% _Y *% _Y) *% finv (_Z *% _Z) /% (k4 *% (_Z *% _Z) *% finv (_Z *% _Z));
    (==) { LM.lemma_mul_mod_assoc #prime k4 (_Z *% _Z) (finv (_Z *% _Z)) }
    (_X *% _X +% _Y *% _Y) *% finv (_Z *% _Z) /% (k4 *% ((_Z *% _Z) *% finv (_Z *% _Z)));
    (==) { fmul_nonzero_lemma _Z _Z; fdiv_one_lemma1 k4 (_Z *% _Z) }
    (_X *% _X +% _Y *% _Y) *% finv (_Z *% _Z) /% k4;
    (==) { LM.lemma_mod_distributivity_add_left #prime (_X *% _X) (_Y *% _Y) (finv (_Z *% _Z)) }
    (_X *% _X *% finv (_Z *% _Z) +% _Y *% _Y *% finv (_Z *% _Z)) /% k4;
    (==) { fdiv_to_one_denominator _X _X _Z _Z; fdiv_to_one_denominator _Y _Y _Z _Z }
    k3 /% k4;
    };
  assert (k1 /% k2 == _X3 /% _Z3 /\ k3 /% k4 == _Y3 /% _Z3);
  aff_point_double_lemma (to_aff_point p);
  aff_point_add_lemma (to_aff_point p) (to_aff_point p)


let to_aff_point_negate p =
  let (_X, _Y, _Z, _T) = p in
  let p' = point_negate p in
  assert (point_negate p == ((-_X) % prime, _Y, _Z, (-_T) % prime));
  assert (is_ext p /\ is_on_curve (to_aff_point p));
  assert (_T == _X *% _Y /% _Z);
  let x = _X /% _Z in
  let y = _Y /% _Z in
  assert (y *% y -% x *% x == 1 +% d *% (x *% x) *% (y *% y));
  calc (==) {
    (-_X) % prime * finv _Z % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (-_X) (finv _Z) prime }
    (-_X) * finv _Z % prime;
    (==) { Math.Lemmas.neg_mul_left _X (finv _Z) }
    (- (_X * finv _Z)) % prime;
    (==) { Math.Lemmas.lemma_mod_sub_distr 0 (_X * finv _Z) prime }
    (- (_X *% finv _Z)) % prime;
    };
  lemma_neg_sqr (_X *% finv _Z);
  assert (is_on_curve (to_aff_point p'));

  calc (==) {
    ((-_X) % prime * _Y) % prime * finv _Z % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (-_X) _Y prime }
    ((-_X) * _Y) % prime * finv _Z % prime;
    (==) { Math.Lemmas.neg_mul_left _X _Y }
    (-(_X * _Y)) % prime * finv _Z % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (-(_X * _Y)) (finv _Z) prime }
    (-(_X * _Y)) * finv _Z % prime;
    (==) { Math.Lemmas.neg_mul_left (_X * _Y) (finv _Z) }
    (-(_X * _Y * finv _Z)) % prime;
    (==) { Math.Lemmas.lemma_mod_sub_distr 0 (_X * _Y * finv _Z) prime }
    (-(_X * _Y * finv _Z % prime)) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (_X * _Y) (finv _Z) prime }
    (-(_X *% _Y *% finv _Z)) % prime;
    (==) { }
    (-_T) % prime;
    };
  assert (is_ext p');
  aff_point_negate_lemma (to_aff_point p)


val fmul_both_lemma: a:elem -> b:elem -> c:elem -> Lemma
  (requires a == b)
  (ensures  a *% c == b *% c)
let fmul_both_lemma a b c =
  calc (==) {
    (a * c) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l a c prime }
    ((a % prime) * c) % prime;
    (==) {  }
    ((b % prime) * c) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l b c prime }
    (b * c) % prime;
  }

val fmul_both_lemma_neq: a:elem -> b:elem -> c:elem{c <> 0} -> Lemma
  (a <> b <==> (a *% c <> b *% c))
let fmul_both_lemma_neq a b c =
  prime_lemma ();
  if a *% c = b *% c then
    Fermat.mod_mult_congr prime a b c
  else ()


val lemma_fmul_assoc1: a:elem -> b:elem -> c:elem ->
  Lemma (a *% b *% c == a *% c *% b)
let lemma_fmul_assoc1 a b c =
  LM.lemma_mul_mod_assoc #prime a b c;
  LM.lemma_mul_mod_comm #prime b c;
  LM.lemma_mul_mod_assoc #prime a c b


val fdiv_lemma1: a:elem -> b:elem{b <> 0} -> c:elem -> d:elem{d <> 0} -> Lemma
  (requires a /% b == c /% d)
  (ensures  a *% d == c *% b)
let fdiv_lemma1 a b c d =
  fmul_both_lemma (a /% b) (c /% d) (b *% d);
  assert (a *% finv b *% (b *% d) == c *% finv d *% (b *% d));
  calc (==) {
    a *% finv b *% (b *% d);
    (==) { lemma_fmul_assoc1 a (finv b) (b *% d) }
    a *% (b *% d) *% finv b;
    (==) {
      LM.lemma_mul_mod_comm #prime b d;
      LM.lemma_mul_mod_assoc #prime a (d *% b) (finv b) }
    a *% ((d *% b) *% finv b);
    (==) { LM.lemma_mul_mod_assoc #prime d b (finv b) }
    a *% (d *% (b *% finv b));
    (==) { fdiv_one_lemma1 d b }
    a *% d;
    };

  calc (==) {
    c *% finv d *% (b *% d);
    (==) { lemma_fmul_assoc1 c (finv d) (b *% d) }
    c *% (b *% d) *% finv d;
    (==) { LM.lemma_mul_mod_assoc #prime c (b *% d) (finv d) }
    c *% ((b *% d) *% finv d);
    (==) { LM.lemma_mul_mod_assoc #prime b d (finv d) }
    c *% (b *% (d *% finv d));
    (==) { fdiv_one_lemma1 b d }
    c *% b;
    }


val point_equal_lemma_aux1: a:elem -> b:elem{b <> 0} -> c:elem -> d:elem{d <> 0} -> e:elem -> f:elem{f <> 0} -> Lemma
  (requires a *% b <> c *% d /\ a /% d == e /% f)
  (ensures  e *% b <> c *% f)
let point_equal_lemma_aux1 a b c d e f =
  fmul_both_lemma_neq (a *% b) (c *% d) f;
  assert (a *% b *% f <> c *% d *% f);
  calc (==) {
    a *% b *% f;
    (==) { lemma_fmul_assoc1 a b f }
    a *% f *% b;
    (==) { fdiv_lemma1 a d e f }
    e *% d *% b;
    (==) { lemma_fmul_assoc1 e d b }
    e *% b *% d;
    };
  lemma_fmul_assoc1 c d f;
  assert (e *% b *% d <> c *% f *% d);
  fmul_both_lemma_neq (e *% b) (c *% f) d


val point_equal_lemma_aux2: a:elem -> b:elem{b <> 0} -> c:elem -> d:elem{d <> 0} -> e:elem -> f:elem{f <> 0} -> Lemma
  (requires a *% b == c *% d /\ a /% d == e /% f)
  (ensures  e *% b == c *% f)
let point_equal_lemma_aux2 a b c d e f =
  fmul_both_lemma (a *% b) (c *% d) f;
  assert (a *% b *% f == c *% d *% f);
  calc (==) {
    a *% b *% f;
    (==) { lemma_fmul_assoc1 a b f }
    a *% f *% b;
    (==) { fdiv_lemma1 a d e f }
    e *% d *% b;
    (==) { lemma_fmul_assoc1 e d b }
    e *% b *% d;
    };
  lemma_fmul_assoc1 c d f;
  assert (e *% b *% d == c *% f *% d);
  prime_lemma ();
  Fermat.mod_mult_congr prime (e *% b) (c *% f) d;
  Math.Lemmas.small_mod (e *% b) prime;
  Math.Lemmas.small_mod (c *% f) prime;
  assert (e *% b == c *% f)


let point_equal_lemma p q s =
  let px, py, pz, pt = p in
  let qx, qy, qz, qt = q in
  let sx, sy, sz, st = s in
  assert (px /% pz == qx /% qz);
  assert (py /% pz == qy /% qz);

  if ((px *% sz) <> (sx *% pz)) then
    point_equal_lemma_aux1 px sz sx pz qx qz
  else if ((py *% sz) <> (sy *% pz)) then
    point_equal_lemma_aux1 py sz sy pz qy qz
    else begin
      point_equal_lemma_aux2 px sz sx pz qx qz;
      point_equal_lemma_aux2 py sz sy pz qy qz end


let aff_g_is_on_curve () =
  assert_norm (is_on_curve (g_x, g_y))


let g_is_on_curve () =
  assert (to_aff_point g == (g_x /% one, g_y /% one));
  fdiv_one_lemma g_x;
  fdiv_one_lemma g_y;
  assert (to_aff_point g == (g_x, g_y));
  assert_norm (is_on_curve (g_x, g_y));
  fdiv_one_lemma (g_x *% g_y)


val recover_x_lemma_aux: y:elem ->
  Lemma (let y2 = y *% y in
    let x2 = (y2 -% one) *% finv (d *% y2 +% one) in
    y2 -% x2 == one +% d *% x2 *% y2)

let recover_x_lemma_aux y =
  let y2 = y *% y in
  let p = finv (d *% y2 +% one) in
  let x2 = (y2 -% one) *% finv (d *% y2 +% one) in
  calc (==) {
    x2 *% (d *% y2 +% one);
    (==) { }
    (y2 -% one) *% p *% (d *% y2 +% one);
    (==) { Lib.NatMod.lemma_mul_mod_assoc #prime (y2 -% one) p (d *% y2 +% one) }
    (y2 -% one) *% (p *% (d *% y2 +% one));
    (==) { denominator_lemma1 y; fdiv_one_lemma1 (y2 -% one) (d *% y2 +% one) }
    y2 -% one;
    };
  assert (x2 *% (d *% y2 +% one) == y2 -% one);
  calc (==) {
    x2 *% (d *% y2 +% one);
    (==) { LM.lemma_mod_distributivity_add_right #prime x2 (d *% y2) one }
    x2 *% (d *% y2) +% x2 *% one;
    (==) {
      Lib.NatMod.lemma_mul_mod_assoc #prime d y2 x2;
      Lib.NatMod.lemma_mul_mod_comm #prime y2 x2;
      Lib.NatMod.lemma_mul_mod_assoc #prime d x2 y2 }
    d *% x2 *% y2 +% x2 *% one;
    (==) { Math.Lemmas.small_mod x2 prime }
    d *% x2 *% y2 +% x2;
    };

  assert (d *% x2 *% y2 +% x2 == y2 -% one);
  Math.Lemmas.mod_add_both (d *% x2 *% y2 + x2) (y2 - one) (one - x2) prime;
  assert ((d *% x2 *% y2 + x2 + one - x2) % prime == (y2 - one + one - x2) % prime);
  assert (d *% x2 *% y2 +% one == y2 -% x2)


val recover_x_lemma: y:nat -> sign:bool -> Lemma (let x = recover_x y sign in
  Some? x ==> (y < prime /\ is_on_curve (Some?.v x, y)))
let recover_x_lemma y sign =
  if y >= prime then ()
  else begin
    let y2 = y *% y in
    let x2 = (y2 -% one) *% finv (d *% y2 +% one) in
    recover_x_lemma_aux y;
    assert (y2 -% x2 == one +% d *% x2 *% y2);
    if x2 = zero then ()
    else begin
      let x = x2 **% ((prime + 3) / 8) in
      let x = if ((x *% x) -% x2) <> zero then x *% modp_sqrt_m1 else x in
      if ((x *% x) -% x2) <> zero then ()
      else begin
        assert (x *% x -% x2 = zero);
        Math.Lemmas.mod_add_both (x *% x - x2) zero x2 prime;
	assert ((x *% x - x2 + x2) % prime = (zero + x2) % prime);
	Math.Lemmas.small_mod (x *% x) prime;
	Math.Lemmas.small_mod x2 prime;
	assert (x *% x == x2);
	if (x % 2 = 1) <> sign then begin
	  let x1 = (prime - x) % prime in
	  calc (==) {
	    x1 *% x1;
	    (==) { }
	    (prime - x) % prime * ((prime - x) % prime) % prime;
	    (==) { Math.Lemmas.modulo_addition_lemma (-x) prime 1 }
	    (- x) % prime * ((- x) % prime) % prime;
	    (==) { lemma_neg_sqr x }
	    (x * x) % prime;
	    };
	  assert (x1 *% x1 = x2);
	  () end
	else ()
      end
    end
  end

module BSeq = Lib.ByteSequence

let point_decompress_lemma s =
  let p = point_decompress s in
  let y = BSeq.nat_from_bytes_le s in
  let sign = (y / pow2 255) % 2 = 1 in
  let y = y % pow2 255 in
  let x = recover_x y sign in

  recover_x_lemma y sign;
  if (Some? x) then begin
    let x = Some?.v x in
    let p = (x, y, one, x *% y) in
    assert (is_on_curve (x, y));
    fdiv_one_lemma x;
    fdiv_one_lemma y;
    assert (is_on_curve (to_aff_point p));
    fdiv_one_lemma (x *% y);
    assert (is_ext p) end


#push-options "--fuel 2"
val lemma_fpow1: a:elem -> Lemma (fpow a 1 == a)
let lemma_fpow1 a = ()

val lemma_fpow_unfold0: a:elem -> b:pos{b % 2 = 0} -> Lemma
  (fpow a b == fpow (a *% a) (b / 2))
let lemma_fpow_unfold0 a b = ()

val lemma_fpow_unfold1: a:elem -> b:pos{1 < b /\ b % 2 = 1} -> Lemma
  (fpow a b == a *% (fpow (a *% a) (b / 2)))
let lemma_fpow_unfold1 a b = ()
#pop-options

val fpow_is_pow: a:elem -> b:pos ->
  Lemma (ensures (fpow a b == LM.pow a b % prime))
  (decreases b)

let rec fpow_is_pow a b =
  if b = 1 then begin
    lemma_fpow1 a;
    LM.lemma_pow1 a end
  else begin
    if b % 2 = 0 then begin
      calc (==) {
	fpow a b;
	(==) { lemma_fpow_unfold0 a b }
	fpow (a *% a) (b / 2);
	(==) { fpow_is_pow (a *% a) (b / 2) }
	LM.pow (a *% a) (b / 2) % prime;
	(==) { LM.lemma_pow_mod_base (a * a) (b / 2) prime }
	LM.pow (a * a) (b / 2) % prime;
	(==) { LM.lemma_pow_double a (b / 2) }
	LM.pow a b % prime;
      };
      assert (fpow a b == LM.pow a b % prime) end
    else begin
      calc (==) {
	fpow a b;
	(==) { lemma_fpow_unfold1 a b }
	a *% (fpow (a *% a) (b / 2));
	(==) { fpow_is_pow (a *% a) (b / 2) }
	a *% (LM.pow (a *% a) (b / 2) % prime);
	(==) { LM.lemma_pow_mod_base (a * a) (b / 2) prime }
	a *% (LM.pow (a * a) (b / 2) % prime);
	(==) { LM.lemma_pow_double a (b / 2) }
	a *% (LM.pow a (b / 2 * 2) % prime);
	(==) { Math.Lemmas.lemma_mod_mul_distr_r a (LM.pow a (b / 2 * 2)) prime }
	a * LM.pow a (b / 2 * 2) % prime;
	(==) { LM.lemma_pow1 a }
	LM.pow a 1 * LM.pow a (b / 2 * 2) % prime;
	(==) { LM.lemma_pow_add a 1 (b / 2 * 2) }
	LM.pow a (b / 2 * 2 + 1) % prime;
	(==) { Math.Lemmas.euclidean_division_definition b 2 }
	LM.pow a b % prime;
	};
      assert (fpow a b == LM.pow a b % prime) end
    end


let fpow_is_pow_mod a b =
  LM.lemma_pow_mod #prime a b;
  fpow_is_pow a b
