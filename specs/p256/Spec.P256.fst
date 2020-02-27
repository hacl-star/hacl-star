module Spec.P256

open FStar.Mul
open Spec.P256.Field

#set-options "--fuel 0 --ifuel 0 --z3rlimit 40"

///
/// NIST P-256 Weirstrass curve y^2 = x^3 + ax + b over the prime field F_p with
///
/// p = 2^256 - 2^224 + 2^192 + 2^96 - 1
/// a = -3
/// b = 41058363725152142129326129780047268409114441015993725554835256314039467401291
///
/// See D.1.2.3 in https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.186-4.pdf
///

let a: elem = ~%3

let b: elem =
  let b = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b in
  assert_norm (b < prime);
  b

val on_curve: elem -> elem -> bool
let on_curve x y = y**2 = x**3 +% a *% x +% b


/// The points P x y on the curve together with the point at infinity O
/// form an Abelian group
type point =
  | P: x:elem -> y:elem{on_curve x y} -> point
  | O: point


/// Base point (group generator)
let base: point =
  let x = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296 in
  let y = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5 in
  assert_norm (x < prime /\ y < prime /\ on_curve x y);
  P x y


/// Order of the base point.
/// i.e. minimum k such that k `scalar_multiplication` base == O
let order: n:pos{n < pow2 256} =
  let n = pow2 256 - pow2 224 + pow2 192 - 89188191075325690597107910205041859247 in
  assert_norm (0 < n /\ n < pow2 256);
  n

#push-options "--ifuel 1" // Or use `allow_inversion point`

(** TODO: prove that the result is on the curve when xp <> xq *)
val add_neq: p:point -> q:point{p <> q /\ p <> O /\ q <> O} -> point
let add_neq p q =
  let P xp yp = p in
  let P xq yq = q in
  if xp = xq then O
  else
    begin
    sub_neq xq xp;
    let lambda = (yq -% yp) /% (xq -% xp) in
    let xr = lambda *% lambda -% xp -% xq in
    let yr = lambda *% (xp -% xr) -% yp in
    assume (on_curve xr yr);
    P xr yr
    end


val double_on_curve: p:point{p <> O /\ (let P _ yp = p in yp <> 0)} ->
  Lemma (
    let P xp yp = p in
    let lambda = (3 *% xp *% xp +% a) /% (2 *% yp) in
    let xr = lambda *% lambda -% 2 *% xp in
    let yr = lambda *% (xp -% xr) -% yp in
    on_curve xr yr)
let double_on_curve p =
  let P xp yp = p in
  mult_eq_zero 2 yp;
  let lambda = (3 *% xp *% xp +% a) /% (2 *% yp) in
  let xr = lambda *% lambda -% 2 *% xp in
  let yr = lambda *% (xp -% xr) -% yp in

  calc (==) {
    (xr**3 +% a *% xr +% b) *% (2 *% yp)**6;
    == { assert ((xr**3 +% a *% xr +% b) *% (2 *% yp)**6 ==
          (((2 *% yp) *% inverse (2 *% yp))**2 *% (a +% 3 *% xp**2)**2 -% 8 *% xp *% yp**2)**3 +%
          ((2 *% yp) *% inverse (2 *% yp))**2 *% 16 *% yp**4 *% a *% (a +% 3 *% xp**2)**2 -%
          128 *% a *% xp *% yp**6 +%
          64 *% yp**6 *% b)
        by (p256_field ())
       }
    (((2 *% yp) *% inverse (2 *% yp))**2 *% (a +% 3 *% xp**2)**2 -% 8 *% xp *% yp**2)**3 +%
    ((2 *% yp) *% inverse (2 *% yp))**2 *% 16 *% yp**4 *% a *% (a +% 3 *% xp**2)**2 -%
    128 *% a *% xp *% yp**6 +%
    64 *% yp**6 *% b;
    == { mul_inverse (2 *% yp) }
    (1**2 *% (a +% 3 *% xp**2)**2 -% 8 *% xp *% yp**2)**3 +%
    1**2 *% 16 *% yp**4 *% a *% (a +% 3 *% xp**2)**2 -%
    128 *% a *% xp *% yp**6 +%
    64 *% yp**6 *% b;
    == { _ by (p256_field ()) }
    ((a +% 3 *% xp**2)**2 -% 8 *% xp *% yp**2)**3 +%
    16 *% (yp**2)**2 *% a *% (a +% 3 *% xp**2)**2 -%
    128 *% a *% xp *% (yp**2)**3 +%
    64 *% (yp**2)**3 *% b;
    == { }
    ((a +% 3 *% xp**2)**2 -% 8 *% xp *% (xp**3 +% a *% xp +% b))**3 +%
    16 *% (yp**2)**2 *% a *% (a +% 3 *% xp**2)**2 -%
    128 *% a *% xp *% (xp**3 +% a *% xp +% b)**3 +%
    64 *% (xp**3 +% a *% xp +% b)**3 *% b;
  };

  calc (==) {
    (yr**2) *% (2 *% yp)**6;
    == { assert(
          (yr**2) *% (2 *% yp)**6 ==
          (8 *% yp**4 -% ((2 *% yp) *% inverse (2 *% yp)) *% (12 *% xp *% yp**2 -% ((2 *% yp) *% inverse (2 *% yp))**2 *% (3 *% xp**2 +% a)**2) *% (3 *% xp**2 +% a))**2)
         by (p256_field ())
       }
    (8 *% yp**4 -% ((2 *% yp) *% inverse (2 *% yp)) *% (12 *% xp *% yp**2 -% ((2 *% yp) *% inverse (2 *% yp))**2 *% (3 *% xp**2 +% a)**2) *% (3 *% xp**2 +% a))**2;
    == { mul_inverse (2 *% yp) }
    (8 *% yp**4 -% 1 *% (12 *% xp *% yp**2 -% 1**2 *% (3 *% xp**2 +% a)**2) *% (3 *% xp**2 +% a))**2;
    == { _ by (p256_field ()) }
    (8 *% (yp**2)**2 -% (12 *% xp *% yp**2 -% (3 *% xp**2 +% a)**2) *% (3 *% xp**2 +% a))**2;
    == { }
    (8 *% (xp**3 +% a *% xp +% b)**2 -%
     (12 *% xp *% (xp**3 +% a *% xp +% b) -%
     (3 *% xp**2 +% a)**2) *% (3 *% xp**2 +% a))**2;
    == { _ by (p256_field ()) }
    ((a +% 3 *% xp**2)**2 -% 8 *% xp *% (xp**3 +% a *% xp +% b))**3 +%
    16 *% (xp**3 +% a *% xp +% b)**2 *% a *% (a +% 3 *% xp**2)**2 -%
    128 *% a *% xp *% (xp**3 +% a *% xp +% b)**3 +%
    64 *% (xp**3 +% a *% xp +% b)**3 *% b;
  };

  pow_eq_zero (2 *% yp) 6;
  mod_mult_congr (yr**2) (xr**3 +% a *% xr +% b) ((2 *% yp)**6)

val double: p:point{p <> O} -> point
let double p =
  let P xp yp = p in
  if yp = 0 then O
  else
    begin
    mult_eq_zero 2 yp;
    let lambda = (3 *% xp *% xp +% a) /% (2 *% yp) in
    let xr = lambda *% lambda -% 2 *% xp in
    let yr = lambda *% (xp -% xr) -% yp in
    double_on_curve p;
    P xr yr
    end

val add: point -> point -> point
let add p q =
  if p = O then q
  else if q = O then p
  else if p = q then double p
  else add_neq p q

val neg: point -> point
let neg = function
  | O -> O
  | P x y ->
    assert_norm (y**2 == y *% y /\ (~%y)**2 == (~%y) *% (~%y));
    mul_opp_cancel y y;
    P x (~%y)

val scalar_multiplication: pos -> point -> point
let rec scalar_multiplication k p =
  if k = 1 then p
  else scalar_multiplication (k-1) p `add` p

(*
///
/// Rough test (needs the strictness atribute on Field.inverse to be removed)
///
let test_add =
  assert (
    let xq = 0x87f8f2b218f49845f6f10eec3877136269f5c1a54736dbdf69f89940cad41555 in
    let yq = 0xe15f369036f49842fac7a86c8a2b0557609776814448b8f5e84aa9f4395205e9 in
    xq < prime /\ yq < prime /\
    on_curve xq yq /\
    base `add` (P xq yq) `add` base == (P xq yq) `add` (base `add` base))
*)

val add_O_l (p:point) : Lemma (O `add` p == p)
let add_O_l p = ()

val add_O_r (p:point) : Lemma (p `add` O == p)
let add_O_r p = ()

val add_neg (p:point) : Lemma (p `add` neg p == O)
let add_neg p =
  match p, neg p with
  | O, _ -> ()
  | _, O -> ()
  | P x y, P x' y' ->
    if y = 0 then ()
    else if (y % prime = (-y) % prime) then mod_neg_eq y

///
/// TODO: This proof involves lengthy formulas and is tedious without a
/// proper `field` tactic
///
val add_associative (p q r:point) : Lemma
  ((p `add` q) `add` r == p `add` (q `add` r))
let add_associative p q r =
  if p = O || q = O || r = O then ()
  else admit()

val sub_eq (a b:elem) : Lemma (requires a <> b) (ensures (a -% b) <> 0)
let sub_eq a b = ()

val add_slope_eq (xp yp xq yq:elem) : Lemma
  (requires xp <> xq)
  (ensures  (yq -% yp) /% (xq -% xp) == (yp -% yq) /% (xp -% xq))
let add_slope_eq xp yp xq yq =
  calc (==) {
    (yq -% yp) /% (xq -% xp);
    == { opp_sub xp xq; opp_sub yp yq }
    ~%(yp -% yq) /% (~%(xp -% xq));
    == { inverse_opp (xp -% xq) }
    ~%(yp -% yq) *% ~%(inverse (xp -% xq));
    == { mul_opp_cancel (yp -% yq) (inverse (xp -% xq)) }
    (yp -% yq) *% inverse (xp -% xq);
    == { }
    (yp -% yq) /% (xp -% xq);
  }

val add_comm_aux (x xp yp xq yq:elem) : Lemma
  (requires xq <> xp)
  (ensures
   (let l = (yp -% yq) /% (xp -% xq) in
    (l *% xp +% x -% yp == l *% xq +% x -% yq)))
let add_comm_aux x xp yp xq yq =
  sub_neq xp xq;
  let l = (yp -% yq) /% (xp -% xq) in
  calc (<==>) {
    l *% xp +% x -% yp == l *% xq +% x -% yq;
    <==> { add_sub_congr (l *% xp +% x) (~%yp) (l *% xq +% x) (~%yq) }
    l *% xp +% x +% ~%(l *% xq +% x) == ~%yq -% ~%yp;
    <==> { opp_add (l *% xq) x }
    l *% xp +% x +% (~%(l *% xq) +% ~%x) == ~%yq -% ~%yp;
    <==> { opp_opp yq}
    l *% xp +% x +% (~%(l *% xq) +% ~%x) == ~%yq +% ~%(~%yp);
    <==> { opp_add yq (~%yp); opp_sub yq yp }
    l *% xp +% x +% (~%(l *% xq) +% ~%x) == yp -% yq;
    <==> { assert (l *% xp +% x +% (~%(l *% xq) +% ~%x) ==
                 (x +% ~%x) +% (l *% xp -% (l *% xq)))
          by (p256_field ())}
    (x +% ~%x) +% (l *% xp -% l *% xq) == yp -% yq;
    <==> { add_opp x; add_identity (l *% xp -% l *% xq) }
    l *% xp +% ~%(l *% xq) == yp -% yq;
    <==> { mul_add_distr l xp (~%xq); mul_neg_r l xq }
    l *% (xp -% xq) == yp -% yq;
    <==> { mul_associative (yp -% yq) (inverse (xp -% xq)) (xp -% xq) }
    (yp -% yq) *% (inverse (xp -% xq) *% (xp -% xq)) == yp -% yq;
    <==> { mul_commutative (inverse (xp -% xq)) (xp -% xq); mul_inverse (xp -% xq) }
    (yp -% yq) *% one == yp -% yq;
    <==> { mul_identity (yp -% yq) }
    yp -% yq == yp -% yq;
  }

val add_comm (p q:point) : Lemma (p `add` q == q `add` p)
let add_comm p q =
  if p = O || q = O || p = q then ()
  else
    begin
    let P xp yp = p in
    let P xq yq = q in
    if xp = xq then () else
      begin
      sub_neq xq xp;
      sub_neq xp xq;
      let lambda1 = (yq -% yp) /% (xq -% xp) in
      let lambda2 = (yp -% yq) /% (xp -% xq) in
      let x1 = lambda1 *% lambda1 -% xp -% xq in
      let y1 = lambda1 *% (xp -% x1) -% yp in
      let x2 = lambda2 *% lambda2 -% xq -% xp in
      let y2 = lambda2 *% (xq -% x2) -% yq in
      calc (==) {
        x1;
        == { }
        lambda1 *% lambda1 -% xp -% xq;
        == { _ by (p256_field ()) }
        lambda1 *% lambda1 -% xq -% xp;
        == { add_slope_eq xp yp xq yq }
        lambda2 *% lambda2 -% xq -% xp;
        == { }
        x2;
      };
      calc (==) {
        y1;
        == { }
        lambda1 *% (xp -% x1) -% yp;
        == { _ by (p256_field ()) }
        lambda1 *% xp +% lambda1 *% ~%x1 -% yp;
        == { add_comm_aux (lambda1 *% ~%x1) xq yq xp yp }
        lambda1 *% xq +% lambda1 *% ~%x1 +% ~% yq;
        == { _ by (p256_field ()) }
        lambda1 *% (xq -% x1) -% yq;
        == { add_slope_eq xp yp xq yq }
        y2;
      }
      end
    end
