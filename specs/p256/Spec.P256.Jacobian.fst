module Spec.P256.Jacobian

open FStar.Mul
open Spec.P256.Field
open Spec.P256

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

///
/// NIST P-256 operations on Jacobian coordinates
///
/// See e.g. https://www.iacr.org/archive/ches2010/62250075/62250075.pdf
///

/// A point in Jacobian coordinates has multiple representations
///
///  (X : Y : Z) == (lambda^2 X : lambda^3 Y : lambda Z), lambda <> zero
///
/// TODO: should probably refine this to points that are on the curve group
/// when converted to affine coordinates.
type pointJ = elem & elem & elem


val isPointAtInfinity: pointJ -> bool
let isPointAtInfinity (_, _, z) = z = 0


val doubleJ: pointJ -> pointJ
let doubleJ (x, y, z) =
  let a = 4 *% x *% y *% y in
  let b = 8 *% y *% y *% y *% y in
  let c = 3 *% (x -% z *% z) *% (x +% z *% z) in
  let d = c *% c -% 2 *% a in
  let xr = d in
  let yr = c *% (a -% d) -% b in
  let zr = 2 *% y *% z in
  xr, yr, zr


val addJ: p:pointJ -> q:pointJ{let _,_,z = q in z = 1} -> pointJ
let addJ (xp, yp, zp) (xq, yq, _) =
  let a = xq *% (zp *% zp) in
  let b = yq *% (zp *% zp *% zp) in
  let c = a -% xp in
  let d = b -% yp in
  let xr = d *% d -% (c *% c *% c +% 2 *% xp *% c *% c) in
  let yr = d *% (xp *% c *% c -% xr) -% yp *% c *% c *% c in
  let zr = zp *% c in
  xr, yr, zr


val normJ: pointJ -> q:pointJ{let _,_,z = q in z = 0 \/ z = 1}
let normJ (x, y, z) =
  if z = 0 then (0, 0, 0)
  else
    begin
    mult_eq_zero z z;
    mult_eq_zero (z *% z) z;
    (x /% (z *% z), y /% (z *% z *% z), 1)
    end

val negJ: pointJ -> pointJ
let negJ (x, y, z) =
  x, ~%y, z


val toJacobian: point -> pointJ
let toJacobian p =
  allow_inversion point;
  match p with
  | O -> (0, 0, 0)
  | P x y -> (x, y, 1)


val fromJacobian: p:pointJ -> Pure point
  (requires (let x, y, z = normJ p in z = 0 \/ on_curve x y))
  (ensures  fun _ -> True)
let fromJacobian p =
  let x, y, z = normJ p in
  if z = 0 then O
  else P x y


val negJ_correct (p:point) : Lemma
  (toJacobian (neg p) == negJ (toJacobian p))
let negJ_correct p =
  allow_inversion point


val addJ_correct (p:point) (q:point{p <> q /\ p <> O /\ q <> O}) : Lemma
  (toJacobian (add_neq p q) == normJ (addJ (toJacobian p) (toJacobian q)))
let addJ_correct p q =
  allow_inversion point;
  let P xp yp = p in
  let P xq yq = q in
  if xp = xq then
    begin
    mul_identity 1;
    mul_one_r xq;
    add_opp xq;
    mul_identity (xq -% xp)
    end
  else
    begin
    sub_neq xq xp;
    let lambda = (yq -% yp) /% (xq -% xp) in
    let xr = lambda *% lambda -% xp -% xq in
    let yr = lambda *% (xp -% xr) -% yp in
    assert (toJacobian (add_neq p q) == (xr, yr, 1));

    let c = xq -% xp in
    let d = yq -% yp in
    let xr' = d *% d -% (c *% c *% c +% 2 *% xp *% c *% c) in
    let yr' = d *% (xp *% c *% c -% xr') -% yp *% c *% c *% c in
    let zr' = xq -% xp in
    mul_identity 1;
    mul_one_r xq;
    mul_one_r yq;
    mul_identity (xq -% xp);
    assert (addJ (toJacobian p) (toJacobian q) == (xr', yr', zr'));

    mult_eq_zero zr' zr';
    mult_eq_zero (zr' *% zr') zr';
    let xr'' = xr' /% (zr' *% zr') in
    let yr'' = yr' /% (zr' *% zr' *% zr') in
    assert (normJ (addJ (toJacobian p) (toJacobian q)) == (xr'', yr'', 1));

    calc (==) {
      xr;
      == { assert (xr == (yq *% yq -% 2 *% yp *% yq +% yp *% yp) *%
                  (inverse zr' *% inverse zr') -% (xp +% xq))
           by (p256_field ())
         }
      (yq *% yq -% 2 *% yp *% yq +% yp *% yp) *% (inverse zr' *% inverse zr') -%
      (xp +% xq);
      == { inverse_mul zr' zr' }
      (yq *% yq -% 2 *% yp *% yq +% yp *% yp) /% (zr' *% zr') -% (xp +% xq);
      == { div_plus_l (yq *% yq -% 2 *% yp *% yq +% yp *% yp)
                      (zr' *% zr') ~%(xp +% xq) }
      (yq *% yq -% 2 *% yp *% yq +% yp *% yp +% (zr' *% zr') *% ~%(xp +% xq)) /%
      (zr' *% zr');
      == { assert (xr' ==
             yq *% yq -% 2 *% yp *% yq +% yp *% yp +% (zr' *% zr') *% ~%(xp +% xq))
           by (p256_field ())
         }
      xr' /% (zr' *% zr');
      == { }
      xr'';
    };

    calc (==) {
      yr;
      == { }
      (d /% c) *% (xp -% xr) -% yp;
      == { mul_associative d (inverse c) (xp -% xr);
           mul_commutative (inverse c) (xp -% xr);
           mul_associative d (xp -% xr) (inverse c) }
      (d *% (xp -% xr)) /% c -% yp;
      == { div_plus_l (d *% (xp -% xr)) c ~%yp }
      (d *% (xp -% xr) +% c *% ~%yp) /% c;
      == { }
      (d *% (xp -% xr' /% (c *% c)) +% c *% ~%yp) /% c;
      == { div_mul_eq_l (d *% (xp -% xr' /% (c *% c)) +% c *% ~%yp) c (c *% c) }
      (c *% c *% (d *% (xp -% xr' /% (c *% c)) +% c *% ~%yp)) /% (c *% c *% c);
      == {
         calc (==) {
           c *% c *% (d *% (xp -% xr' /% (c *% c)) +% c *% ~%yp);
           == { assert (
                  c *% c *% (d *% (xp -% xr' /% (c *% c)) +% c *% ~%yp) ==
                  d *% (xp *% c *% c -% ((c *% c) /% (c *% c)) *% xr') -%
                  yp *% c *% c *% c)
                by (p256_field ())
              }
           d *% (xp *% c *% c -% ((c *% c) /% (c *% c)) *% xr') -%
           yp *% c *% c *% c;
           == { mul_inverse (c *% c); mul_one_r xr' }
           d *% (xp *% c *% c -% xr') -% yp *% c *% c *% c;
           == { }
           yr';
         }
         }
      yr' /% (c *% c *% c);
      == { }
      yr'';
    }
    end


val doubleJ_correct (p:point{p <> O}) : Lemma
  (toJacobian (double p) == normJ (doubleJ (toJacobian p)))
let doubleJ_correct p =
  allow_inversion point;
  let P x y = p in
  if y = 0 then
    begin
    calc (==) {
      toJacobian (double p);
      == { }
      (0, 0, 0);
      == { assert_norm (2 *% 0 *% 1 == 0) }
      normJ (doubleJ (toJacobian p));
    }
    end
  else
    begin
    mult_eq_zero 2 y;
    let lambda = (3 *% x *% x -% 3) /% (2 *% y) in
    let xr = lambda *% lambda -% 2 *% x in
    let yr = lambda *% (x -% xr) -% y in
    assert (toJacobian (double p) == (xr, yr, 1));

    let a = 4 *% x *% y *% y in
    let b = 8 *% y *% y *% y *% y in
    let c = 3 *% (x -% 1) *% (x +% 1) in
    let d = c *% c -% 2 *% a in

    let xr' = d in
    let yr' = c *% (a -% d) -% b in
    let zr' = 2 *% y in
    mul_identity zr';
    mul_identity 1;
    assert (doubleJ (toJacobian p) == (xr', yr', zr'));

    mult_eq_zero zr' zr';
    mult_eq_zero (zr' *% zr') zr';
    let xr'' = xr' /% (zr' *% zr') in
    let yr'' = yr' /% (zr' *% zr' *% zr') in
    assert (normJ (doubleJ (toJacobian p)) == (xr'', yr'', 1));

    calc (==) {
      xr;
      == { assert (xr == (9 *% x *% x *% x *% x -% 18 *% x *% x +% 9) *%
                         (inverse zr' *% inverse zr') -% 2 *% x)
           by (p256_field ())
         }
      (9 *% x *% x *% x *% x -% 18 *% x *% x +% 9) *%
      (inverse zr' *% inverse zr') -% 2 *% x;
      == { inverse_mul zr' zr' }
      (9 *% x *% x *% x *% x -% 18 *% x *% x +% 9) /% (zr' *% zr') -% 2 *% x;
      == { div_plus_l (9 *% x *% x *% x *% x -% 18 *% x *% x +% 9)
                      (zr' *% zr') ~%(2 *% x) }
      (9 *% x *% x *% x *% x -% 18 *% x *% x +% 9 +% (zr' *% zr') *% ~%(2 *% x)) /%
      (zr' *% zr');
      == { assert (xr' ==
             (9 *% x *% x *% x *% x -% 18 *% x *% x +% 9 +% (zr' *% zr') *% ~%(2 *% x)))
           by (p256_field ())
         }
      xr' /% (zr' *% zr');
      == { }
      xr'';
    };

    calc (==) {
      yr;
      == { }
      ((3 *% x *% x -% 3) /% zr') *% (x -% xr) -% y;
      == { mul_associative (3 *% x *% x -% 3) (inverse zr') (x -% xr);
           mul_commutative (inverse zr') (x -% xr);
           mul_associative (3 *% x *% x -% 3) (x -% xr) (inverse zr') }
      ((3 *% x *% x -% 3) *% (x -% xr)) /% zr' -% y;
      == { div_plus_l ((3 *% x *% x -% 3) *% (x -% xr)) zr' ~%y }
      ((3 *% x *% x -% 3) *% (x -% xr) +% zr' *% ~%y) /% zr';
      == { }
      ((3 *% x *% x -% 3) *% (x -% d /% (zr' *% zr')) +% zr' *% ~%y) /% zr';
      == { div_mul_eq_l
            ((3 *% x *% x -% 3) *% (x -% d /% (zr' *% zr')) +% zr' *% ~%y)
            zr' (zr' *% zr')
         }
      (zr' *% zr' *% ((3 *% x *% x -% 3) *% (x -% d /% (zr' *% zr')) +% zr' *% ~%y)) /%
      (zr' *% zr' *% zr');
      == {
         calc (==) {
           zr' *% zr' *% ((3 *% x *% x -% 3) *% (x -% d /% (zr' *% zr')) +% zr' *% ~%y);
           == {
             assert (
               zr' *% zr' *%
               ((3 *% x *% x -% 3) *% (x -% d /% (zr' *% zr')) +% zr' *% ~%y) ==
               c *% (a -% d *% ((zr' *% zr') /% (zr' *% zr'))) -% b)
             by (p256_field ())
           }
           c *% (a -% d *% ((zr' *% zr') /% (zr' *% zr'))) -% b;
           == { mul_inverse (zr' *% zr'); mul_one_r d }
           c *% (a -% d) -% b;
           == { }
           yr';
         }
         }
      yr' /% (zr' *% zr' *% zr');
      == { }
      yr'';
    }
    end
