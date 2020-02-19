module Spec.P256.Jacobian

open FStar.Mul
open Spec.P256.Field
open Spec.P256

#set-options "--fuel 0 --ifuel 0 --z3rlimit 60"

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
let addJ (xp, yp, zp) (xq, yq, zq) =
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
  allow_inversion point;
  match p with
  | O -> ()
  | P x y -> ()


assume
val addJ_correct (p:point) (q:point{p <> q /\ p <> O /\ q <> O}) : Lemma
  (toJacobian (add_neq p q) == normJ (addJ (toJacobian p) (toJacobian q)))


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
      normJ (doubleJ (x, y, 1));
      == { }
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

    mul_identity (2 *% y);
    mul_identity 1;
    let a = 4 *% x *% y *% y in
    let b = 8 *% y *% y *% y *% y in
    let c = 3 *% (x -% 1) *% (x +% 1) in
    let d = c *% c -% 2 *% a in
    let xr' = d in
    let yr' = c *% (a -% d) -% b in
    let zr' = 2 *% y in
    assert (doubleJ (toJacobian p) == (xr', yr', zr'));

    mult_eq_zero zr' zr';
    mult_eq_zero (zr' *% zr') zr';
    let xr'' = xr' /% (zr' *% zr') in
    let yr'' = yr' /% (zr' *% zr' *% zr') in   
    assert (normJ (doubleJ (toJacobian p)) == (xr'', yr'', 1));
    
    assert (zr' *% zr' == 4 *% y *% y) 
      by (p256_field ());
    assert (c == 3 *% x *% x -% 3) 
      by (p256_field ());
    assert (c *% c == 9 *% x *% x *% x *% x +% ~%18 *% x *% x +% 9)
      by (p256_field ());
    assert (d == 9 *% x *% x *% x *% x +% ~%18 *% x *% x +% 9 +% ~%8 *% x *% y *% y)
      by (p256_field ());

    calc (==) {
      xr;
      == { assert (xr ==
             (9 *% x *% x *% x *% x +% (6 *% ~%3) *% x *% x +% ~%3 *% ~%3) *%
             (inverse (2 *% y) *% inverse (2 *% y)) -% 2 *% x)
           by (p256_field ()); 
           assert_norm (6 *% ~%3 == ~%18 /\ ~%3 *% ~%3 == 9) 
         }
      (9 *% x *% x *% x *% x +% ~%18 *% x *% x +% 9) *%
      (inverse (2 *% y) *% inverse (2 *% y)) -% 2 *% x;
      == { inverse_mul (2 *% y) (2 *% y) }
      (9 *% x *% x *% x *% x +% ~%18 *% x *% x +% 9) /% (4 *% y *% y) 
      -% 2 *% x;
      == { div_plus_l (9 *% x *% x *% x *% x +% ~%18 *% x *% x +% 9)
                      (4 *% y *% y) (~%(2 *% x)) }
      (9 *% x *% x *% x *% x +% ~%18 *% x *% x +% 9 +%
      (4 *% y *% y) *% ~%(2 *% x)) /%
      (4 *% y *% y);
      == { assert ((4 *% y *% y) *% (~%2 *% x) == (4 *% ~%2) *% x *% y *% y)
           by (p256_field ());
           mul_neg_r x 2;
           assert_norm (4 *% ~%2 == ~% 8)
         }
      (9 *% x *% x *% x *% x +% ~%18 *% x *% x +% 9 +% ~%8 *% x *% y *% y) /%
      (4 *% y *% y);
      == { }
      d /% (4 *% y *% y);
      == { }
      d /% (zr' *% zr');
      == { }
      xr'';
    };
    
    assume (yr == yr'')
    end
