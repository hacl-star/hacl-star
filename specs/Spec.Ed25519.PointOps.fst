module Spec.Ed25519.PointOps

open FStar.Mul
open Spec.Curve25519

module BSeq = Lib.ByteSequence

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"


type aff_point = elem & elem               // Affine point
type ext_point = elem & elem & elem & elem // Homogeneous extended coordinates

let modp_sqrt_m1 : elem = 2 **% ((prime - 1) / 4)

let fexp (x:elem) (b:pos) : elem = Lib.NatMod.pow_mod #prime x b
let finv (x:elem) : elem = fexp x (prime - 2)
let ( /% ) (x:elem) (y:elem) = x *% finv y

let d : elem =
  let x = 37095705934669439343138083508754565189542113879843219016388785533085940283555 in
  assert_norm(x < prime);
  x

let g_x : elem = 15112221349535400772501151409588531511454012693041857206046113283949847762202
let g_y : elem = 46316835694926478169428394003475163141307993866256225615783033603165251855960

let aff_g : aff_point = (g_x, g_y)
let g: ext_point = (g_x, g_y, 1, g_x *% g_y)


let is_on_curve (p:aff_point) =
  let (x, y) = p in
  y *% y -% x *% x == 1 +% d *% (x *% x) *% (y *% y)

let to_aff_point (p:ext_point) : aff_point =
  let _X, _Y, _Z, _T = p in
  _X /% _Z, _Y /% _Z

let is_ext (p:ext_point) =
  let _X, _Y, _Z, _T = p in
  _T == _X *% _Y /% _Z /\ _Z <> zero

let point_inv (p:ext_point) =
  is_ext p /\ is_on_curve (to_aff_point p)

// let is_on_curve_ext (p:ext_point) =
//   let _X, _Y, _Z, _T = p in
//   _Y *% _Y -% X *% X == _Z *% _Z +% d *% _T *% _T

// let to_ext_point (p:aff_point) : ext_point =
//   let x, y = p in
//   (x, y, one, x *% y)

///  Point addition and doubling in affine coordinates

let aff_point_add (p:aff_point) (q:aff_point) : aff_point =
  let x1, y1 = p in
  let x2, y2 = q in
  let x3 = (x1 *% y2 +% y1 *% x2) /% (1 +% d *% (x1 *% x2) *% (y1 *% y2)) in
  let y3 = (y1 *% y2 +% x1 *% x2) /% (1 -% d *% (x1 *% x2) *% (y1 *% y2)) in
  x3, y3

let aff_point_double (p:aff_point) : aff_point =
  let x, y = p in
  let x3 = (2 *% x *% y) /% (y *% y -% x *% x) in
  let y3 = (y *% y +% x *% x) /% (2 -% y *% y +% x *% x) in
  x3, y3

let aff_point_at_infinity : aff_point = (zero, one)

let aff_point_negate (p:aff_point) : aff_point =
  let x, y = p in
  ((-x) % prime, y)


///  Point addition and doubling in Extended Twisted Edwards Coordinates

let point_add (p:ext_point) (q:ext_point) : Tot ext_point =
  let _X1, _Y1, _Z1, _T1 = p in
  let _X2, _Y2, _Z2, _T2 = q in
  let a = (_Y1 -% _X1) *% (_Y2 -% _X2) in
  let b = (_Y1 +% _X1) *% (_Y2 +% _X2) in
  let c = (2 *% d *% _T1) *% _T2 in
  let d = (2 *% _Z1) *% _Z2 in
  let e = b -% a in
  let f = d -% c in
  let g = d +% c in
  let h = b +% a in
  let _X3 = e *% f in
  let _Y3 = g *% h in
  let _T3 = e *% h in
  let _Z3 = f *% g in
  (_X3, _Y3, _Z3, _T3)

let point_double (p:ext_point) : Tot ext_point =
  let _X1, _Y1, _Z1, _T1 = p in
  let a = _X1 *% _X1 in
  let b = _Y1 *% _Y1 in
  let c = 2 *% (_Z1 *% _Z1) in
  let h = a +% b in
  let e = h -% ((_X1 +% _Y1) *% (_X1 +% _Y1)) in
  let g = a -% b in
  let f = c +% g in
  let _X3 = e *% f in
  let _Y3 = g *% h in
  let _T3 = e *% h in
  let _Z3 = f *% g in
  (_X3, _Y3, _Z3, _T3)

let point_at_infinity: ext_point = (zero, one, one, zero)

let point_negate (p:ext_point) : ext_point =
  let _X, _Y, _Z, _T = p in
  ((-_X) % prime, _Y, _Z, (-_T) % prime)


let point_compress (p:ext_point) : Tot (BSeq.lbytes 32) =
  let px, py, pz, pt = p in
  let zinv = finv pz in
  let x = px *% zinv in
  let y = py *% zinv in
  BSeq.nat_to_bytes_le 32 (pow2 255 * (x % 2) + y)

let recover_x (y:nat) (sign:bool) : Tot (option elem) =
  if y >= prime then None
  else (
    let y2 = y *% y in
    let x2 = (y2 -% one) *% (finv ((d *% y2) +% one)) in
    if x2 = zero then (
      if sign then None
      else Some zero)
    else (
      let x = x2 **% ((prime + 3) / 8) in
      let x = if ((x *% x) -% x2) <> zero then x *% modp_sqrt_m1 else x in
      if ((x *% x) -% x2) <> zero then None
      else (
        let x = if (x % 2 = 1) <> sign then (prime - x) % prime else x in
        Some x)))

let point_decompress (s:BSeq.lbytes 32) : Tot (option ext_point) =
  let y = BSeq.nat_from_bytes_le s in
  let sign = (y / pow2 255) % 2 = 1 in
  let y = y % pow2 255 in
  let x = recover_x y sign in
  match x with
  | Some x -> Some (x, y, one, x *% y)
  | _ -> None

let point_equal (p:ext_point) (q:ext_point) =
  let px, py, pz, pt = p in
  let qx, qy, qz, qt = q in
  if ((px *% qz) <> (qx *% pz)) then false
  else if ((py *% qz) <> (qy *% pz)) then false
  else true
