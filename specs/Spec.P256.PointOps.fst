module Spec.P256.PointOps

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

module M = Lib.NatMod
module BSeq = Lib.ByteSequence

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Curve Parameters

let is_fodd (x:nat) : bool = x % 2 = 1

class curve_params = {
  bits: pos;
  bytes: x:pos{bits <= 8 * x /\ 3 * x < pow2 32}; 
    // length restriction to allow for serializing affine and projective points
  prime: x:pos{x > 3 /\ x < pow2 bits /\ is_fodd x};
  order: x:pos{x > 1 /\ x < pow2 bits /\ is_fodd x};
  basepoint_x: x:nat{x < prime};
  basepoint_y: x:nat{x < prime};
  a_coeff: x:nat{x < prime};
  b_coeff: x:nat{x < prime};
  mont_mu: x:uint64{(1 + prime * v x) % pow2 64 == 0};
  mont_q_mu: x:uint64{(1 + order * v x) % pow2 64 == 0};
  bn_limbs: x:size_t{v x == (bytes + 7) / 8 /\ v x * 8 >= bytes}
  // also add co-factor?
}

///  Base Field Arithmetic

let felem {| curve_params |} = x:nat{x < prime}
let zero  {| curve_params |} : felem = 0
let one   {| curve_params |} : felem = 1

let fadd {| curve_params |} (x y:felem) : felem = (x + y) % prime
let fsub {| curve_params |} (x y:felem) : felem = (x - y) % prime
let fmul {| curve_params |} (x y:felem) : felem = (x * y) % prime
let finv {| curve_params |} (a:felem) : felem = M.pow_mod #prime a (prime - 2)
let fsqrt {| curve_params |} (a:felem) : felem = M.pow_mod #prime a ((prime + 1) / 4)

let ( +% ) {| curve_params |} = fadd
let ( -% ) {| curve_params |} = fsub
let ( *% ) {| curve_params |} = fmul
let ( /% ) {| curve_params |} (x y:felem) = x *% finv y

///  Scalar Field Arithmetic

let qelem {| c:curve_params |} = x:nat{x < c.order}
let qadd {| c:curve_params |} (x y:qelem) : qelem = (x + y) % c.order
let qmul {| c:curve_params |} (x y:qelem) : qelem = (x * y) % c.order
let qinv {| c:curve_params |} (x:qelem) : qelem = M.pow_mod #c.order x (c.order - 2)

let ( +^ ) {| c:curve_params |} = qadd
let ( *^ ) {| c:curve_params |} = qmul 

///  Elliptic curve `y^2 = x^3 + a * x + b`

//let aff_point (c:curve_params) = p:tuple2 nat nat{let (px, py) = p in px < c.prime /\ py < c.prime}
//let proj_point (c:curve_params) = p:tuple3 nat nat nat{let (px, py, pz) = p in px < c.prime /\ py < c.prime /\ pz < c.prime}
let aff_point {| curve_params |} = felem & felem
let proj_point {| curve_params |} = felem & felem & felem

let base_point {| curve_params |} : proj_point = (basepoint_x, basepoint_y, one)

let is_on_curve {| curve_params |} (p:aff_point) : bool =
  let (x, y) = p in y *% y = x *% x *% x +% a_coeff *% x +% b_coeff

let aff_point_at_inf {| curve_params |} : aff_point = (zero, zero) // not on the curve!
let point_at_inf {| curve_params |} : proj_point = (zero, one, zero)

let is_aff_point_at_inf {| curve_params |} (p:aff_point) : bool =
  let (x, y) = p in x = zero && y = zero

let is_point_at_inf {| curve_params |} (p:proj_point) =
  let (_, _, z) = p in z = 0


let to_proj_point {| curve_params |} (p:aff_point) : proj_point =
  let (x, y) = p in (x, y, one)

let to_aff_point {| curve_params |} (p:proj_point) : aff_point =
  // if is_proj_point_at_inf p then aff_point_at_inf
  let (px, py, pz) = p in
  let zinv = finv pz in
  let x = px *% zinv in
  let y = py *% zinv in
  (x, y)


///  Point addition in affine coordinates

let aff_point_double {| curve_params |} (p:aff_point) : aff_point =
  let (px, py) = p in
  if is_aff_point_at_inf p then p
  else begin
    if py = 0 then aff_point_at_inf
    else begin
      let lambda = (3 *% px *% px +% a_coeff) /% (2 *% py) in
      let rx = lambda *% lambda -% px -% px in
      let ry = lambda *% (px -% rx) -% py in
      (rx, ry) end
  end

let aff_point_add {| curve_params |} (p:aff_point) (q:aff_point) : aff_point =
  let (px, py) = p in let (qx, qy) = q in
  if is_aff_point_at_inf p then q
  else begin
    if is_aff_point_at_inf q then p
    else begin
      if p = q then aff_point_double p
      else begin
        if qx = px then aff_point_at_inf
        else begin
          let lambda = (qy -% py) /% (qx -% px) in
          let rx = lambda *% lambda -% px -% qx in
          let ry = lambda *% (px -% rx) -% py in
          (rx, ry)
        end
      end
    end
  end


///  Point addition and doubling in projective coordinates

// Alg 4 from https://eprint.iacr.org/2015/1060.pdf
let point_add {| curve_params |} (p q:proj_point) : proj_point =
  let x1, y1, z1 = p in
  let x2, y2, z2 = q in
  let t0 = x1 *% x2 in
  let t1 = y1 *% y2 in
  let t2 = z1 *% z2 in
  let t3 = x1 +% y1 in
  let t4 = x2 +% y2 in
  let t3 = t3 *% t4 in
  let t4 = t0 +% t1 in
  let t3 = t3 -% t4 in
  let t4 = y1 +% z1 in
  let t5 = y2 +% z2 in
  let t4 = t4 *% t5 in
  let t5 = t1 +% t2 in
  let t4 = t4 -% t5 in
  let x3 = x1 +% z1 in
  let y3 = x2 +% z2 in
  let x3 = x3 *% y3 in
  let y3 = t0 +% t2 in
  let y3 = x3 -% y3 in
  let z3 = b_coeff *% t2 in
  let x3 = y3 -% z3 in
  let z3 = x3 +% x3 in
  let x3 = x3 +% z3 in
  let z3 = t1 -% x3 in
  let x3 = t1 +% x3 in
  let y3 = b_coeff *% y3 in
  let t1 = t2 +% t2 in
  let t2 = t1 +% t2 in
  let y3 = y3 -% t2 in
  let y3 = y3 -% t0 in
  let t1 = y3 +% y3 in
  let y3 = t1 +% y3 in
  let t1 = t0 +% t0 in
  let t0 = t1 +% t0 in
  let t0 = t0 -% t2 in
  let t1 = t4 *% y3 in
  let t2 = t0 *% y3 in
  let y3 = x3 *% z3 in
  let y3 = y3 +% t2 in
  let x3 = t3 *% x3 in
  let x3 = x3 -% t1 in
  let z3 = t4 *% z3 in
  let t1 = t3 *% t0 in
  let z3 = z3 +% t1 in
  (x3, y3, z3)


// Alg 6 from https://eprint.iacr.org/2015/1060.pdf
let point_double {| curve_params |} (p:proj_point) : proj_point =
  let (x, y, z) = p in
  let t0 = x *% x in
  let t1 = y *% y in
  let t2 = z *% z in
  let t3 = x *% y in
  let t3 = t3 +% t3 in
  let t4 = y *% z in
  let z3 = x *% z in
  let z3 = z3 +% z3 in
  let y3 = b_coeff *% t2 in
  let y3 = y3 -% z3 in
  let x3 = y3 +% y3 in
  let y3 = x3 +% y3 in
  let x3 = t1 -% y3 in
  let y3 = t1 +% y3 in
  let y3 = x3 *% y3 in
  let x3 = x3 *% t3 in
  let t3 = t2 +% t2 in
  let t2 = t2 +% t3 in
  let z3 = b_coeff *% z3 in
  let z3 = z3 -% t2 in
  let z3 = z3 -% t0 in
  let t3 = z3 +% z3 in
  let z3 = z3 +% t3 in
  let t3 = t0 +% t0 in
  let t0 = t3 +% t0 in
  let t0 = t0 -% t2 in
  let t0 = t0 *% z3 in
  let y3 = y3 +% t0 in
  let t0 = t4 +% t4 in
  let z3 = t0 *% z3 in
  let x3 = x3 -% z3 in
  let z3 = t0 *% t1 in
  let z3 = z3 +% z3 in
  let z3 = z3 +% z3 in
  (x3, y3, z3)


///  Point conversion between affine, projective and bytes representation

let aff_point_load {| c:curve_params |} (b:BSeq.lbytes (2*c.bytes)) : option (aff_point) =
  let pk_x = BSeq.nat_from_bytes_be (sub b 0 c.bytes) in
  let pk_y = BSeq.nat_from_bytes_be (sub b c.bytes c.bytes) in
  let is_x_valid = pk_x < c.prime in
  let is_y_valid = pk_y < c.prime in
  let is_xy_on_curve =
    if is_x_valid && is_y_valid then is_on_curve #c (pk_x, pk_y) else false in
  if is_xy_on_curve then Some (pk_x, pk_y) else None


let load_point {| c:curve_params |} (b:BSeq.lbytes (2*c.bytes)) : option (proj_point) =
  match (aff_point_load b) with
  | Some p -> Some (to_proj_point p)
  | None -> None


let aff_point_store {| c:curve_params |} (p:aff_point) : BSeq.lbytes (2*c.bytes) =
  let (px, py) = p in
  FStar.Math.Lemmas.pow2_le_compat (8*c.bytes) c.bits;
  let pxb = BSeq.nat_to_bytes_be c.bytes px in
  let pxy = BSeq.nat_to_bytes_be c.bytes py in
  concat #uint8 #c.bytes #c.bytes pxb pxy


let point_store {| c:curve_params |} (p:proj_point) : BSeq.lbytes (2*c.bytes) =
  aff_point_store (to_aff_point p)


let recover_y {| curve_params |} (x:felem) (is_odd:bool) : option (felem) =
  let y2 = x *% x *% x +% a_coeff *% x +% b_coeff in
  let y = fsqrt y2 in
  if y *% y <> y2 then None
  else begin
    let y = if is_fodd y <> is_odd then (prime - y) % prime else y in
    Some y end

let aff_point_decompress {| c:curve_params |} (s:BSeq.lbytes (c.bytes+1)) : option (aff_point) =
  let s0 = Lib.RawIntTypes.u8_to_UInt8 s.[0] in
  if not (s0 = 0x02uy || s0 = 0x03uy) then None
  else begin
    let x = BSeq.nat_from_bytes_be (sub s 1 c.bytes) in
    let is_x_valid = x < c.prime in
    let is_y_odd = s0 = 0x03uy in

    if not is_x_valid then None
    else
      match (recover_y x is_y_odd) with
      | Some y -> Some (x, y)
      | None -> None end

