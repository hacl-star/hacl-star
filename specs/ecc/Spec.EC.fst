module Spec.EC

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

module M = Lib.NatMod
module BSeq = Lib.ByteSequence

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let tuple2_lt_n (n:pos) =
  p:tuple2 nat nat{let (px, py) = p in px < n /\ py < n}

let tuple2_on_curve (n:pos) (a b:M.nat_mod n) (g:tuple2_lt_n n) =
  let ( +% ) = M.add_mod #n in
  let ( *% ) = M.mul_mod #n in
  let (x, y) = g in y *% y = x *% x *% x +% a *% x +% b


// cofactor = 1
inline_for_extraction
class curve = {
  prime: x:nat{24 < x /\ x % 2 = 1};
  coeff_a: M.nat_mod prime;
  coeff_b: x:M.nat_mod prime{0 < x}; // (0, 0) is not on the curve

  order: x:pos{1 < x};
  base_point: x:tuple2_lt_n prime{tuple2_on_curve prime coeff_a coeff_b x};

  prime_len_bytes: x:nat{prime < pow2 (8 * x) /\ 2 * x <= max_size_t};
  order_len_bytes: x:nat{order < pow2 (8 * x) /\ 2 * x <= max_size_t};

  weierstrass_curve: unit ->
    Lemma ((4 * coeff_a * coeff_a * coeff_a + 27 * coeff_b * coeff_b) % prime <> 0);
  prime_lemma: unit -> Lemma (FStar.Math.Euclid.is_prime prime);
  order_lemma: unit -> Lemma (FStar.Math.Euclid.is_prime order);
}


///  Base Field Arithmetic

let felem (k:curve) = x:nat{x < k.prime}
let zero (k:curve) : felem k = 0
let one (k:curve) : felem k = 1

let fadd (k:curve) (x y:felem k) : felem k = (x + y) % k.prime
let fsub (k:curve) (x y:felem k) : felem k = (x - y) % k.prime
let fmul (k:curve) (x y:felem k) : felem k = (x * y) % k.prime
let finv (k:curve) (a:felem k) : felem k = M.pow_mod #k.prime a (k.prime - 2)


///  Scalar Field Arithmetic

let qelem (k:curve) = x:nat{x < k.order}
let qadd (k:curve) (x y:qelem k) : qelem k = (x + y) % k.order
let qmul (k:curve) (x y:qelem k) : qelem k = (x * y) % k.order
let qinv (k:curve) (x:qelem k) : qelem k = M.pow_mod #k.order x (k.order - 2)


///  Elliptic Curve Arithmetic in affine coordinates

let aff_point (k:curve) = tuple2_lt_n k.prime

// y * y =?= x * x * x + a * x + b
let is_on_curve (k:curve) (p:aff_point k) : bool =
  tuple2_on_curve k.prime k.coeff_a k.coeff_b p

let aff_point_at_inf (k:curve) : aff_point k = (zero k, zero k) // not on the curve!

let is_aff_point_at_inf (k:curve) (p:aff_point k) : bool =
  let (x, y) = p in x = zero k && y = zero k


let aff_point_inv (k:curve) (p:aff_point k) =
  is_on_curve k p || is_aff_point_at_inf k p

let aff_point_c (k:curve) = p:aff_point k{aff_point_inv k p}


///  Point addition in affine coordinates

let aff_point_double (k:curve) (p:aff_point k) : aff_point k =
  let ( +% ) = fadd k in
  let ( -% ) = fsub k in
  let ( *% ) = fmul k in
  let ( /% ) (x y:felem k) = x *% finv k y in

  let (px, py) = p in
  if is_aff_point_at_inf k p then p
  else begin
    if py = 0 then aff_point_at_inf k
    else begin
      let lambda = (3 *% px *% px +% k.coeff_a) /% (2 *% py) in
      let rx = lambda *% lambda -% px -% px in
      let ry = lambda *% (px -% rx) -% py in
      (rx, ry) end
  end


let aff_point_add (k:curve) (p:aff_point k) (q:aff_point k) : aff_point k =
  let ( +% ) = fadd k in
  let ( -% ) = fsub k in
  let ( *% ) = fmul k in
  let ( /% ) (x y:felem k) = x *% finv k y in

  let (px, py) = p in let (qx, qy) = q in
  if is_aff_point_at_inf k p then q
  else begin
    if is_aff_point_at_inf k q then p
    else begin
      if p = q then aff_point_double k p
      else begin
        if qx = px then aff_point_at_inf k
        else begin
          let lambda = (qy -% py) /% (qx -% px) in
          let rx = lambda *% lambda -% px -% qx in
          let ry = lambda *% (px -% rx) -% py in
          (rx, ry)
        end
      end
    end
  end


let aff_point_negate (k:curve) (p:aff_point k) : aff_point k =
  let x, y = p in x, (-y) % prime


///  Point conversion between affine and bytes representation

let aff_point_load (k:curve) (b:BSeq.lbytes (2 * k.prime_len_bytes)) : option (aff_point_c k) =
  let len = k.prime_len_bytes in
  let pk_x = BSeq.nat_from_bytes_be (sub b 0 len) in
  let pk_y = BSeq.nat_from_bytes_be (sub b len len) in
  let is_x_valid = pk_x < k.prime in
  let is_y_valid = pk_y < k.prime in
  let is_xy_on_curve =
    if is_x_valid && is_y_valid then is_on_curve k (pk_x, pk_y) else false in
  if is_xy_on_curve then Some (pk_x, pk_y) else None


let aff_point_store (k:curve) (p:aff_point k) : BSeq.lbytes (2 * k.prime_len_bytes) =
  let (px, py) = p in
  let len = k.prime_len_bytes in
  let pxb = BSeq.nat_to_bytes_be len px in
  let pxy = BSeq.nat_to_bytes_be len py in
  concat #uint8 #len #len pxb pxy
