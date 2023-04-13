module Spec.P256.PointOps

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

module M = Lib.NatMod
module BSeq = Lib.ByteSequence

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Base field

// 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
let prime: (a:pos{a = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff /\ a < pow2 256}) =
  let p = pow2 256 - pow2 224 + pow2 192 + pow2 96 - 1 in
  assert_norm (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff = p);
  assert_norm (p < pow2 256); p

let felem = x:nat{x < prime}
let zero : felem = 0
let one  : felem = 1

let fadd (x y:felem) : felem = (x + y) % prime
let fsub (x y:felem) : felem = (x - y) % prime
let fmul (x y:felem) : felem = (x * y) % prime
let finv (a:felem) : felem = M.pow_mod #prime a (prime - 2)
let fsqrt (a:felem) : felem = M.pow_mod #prime a ((prime + 1) / 4)
let is_fodd (x:nat) : bool = x % 2 = 1

let ( +% ) = fadd
let ( -% ) = fsub
let ( *% ) = fmul
let ( /% ) (x y:felem) = x *% finv y

///  Scalar field

// Group order
let order: (a:pos{a < pow2 256}) =
  let o = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551 in
  assert_norm (o < pow2 256); o

let qelem = x:nat{x < order}
let qadd (x y:qelem) : qelem = (x + y) % order
let qmul (x y:qelem) : qelem = (x * y) % order
let qinv (x:qelem) : qelem = M.pow_mod #order x (order - 2)

let ( +^ ) = qadd
let ( *^ ) = qmul


///  Elliptic curve `y^2 = x^3 + a * x + b`

let aff_point = p:tuple2 nat nat{let (px, py) = p in px < prime /\ py < prime}
let proj_point = p:tuple3 nat nat nat{let (px, py, pz) = p in px < prime /\ py < prime /\ pz < prime}

// let aff_point = felem & felem           // Affine point
// let proj_point = felem & felem & felem  // Projective coordinates

let a_coeff : felem = (-3) % prime
let b_coeff : felem =
  let b = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b in
  assert_norm (b < prime); b


// Base point
let g_x : felem =
  let x = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296 in
  assert_norm (x < prime); x
let g_y : felem =
  let y = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5 in
  assert_norm (y < prime); y

let base_point : proj_point = (g_x, g_y, one)


let is_on_curve (p:aff_point) : bool =
  let (x, y) = p in y *% y = x *% x *% x +% a_coeff *% x +% b_coeff


let aff_point_at_inf : aff_point = (zero, zero) // not on the curve!
let point_at_inf : proj_point = (zero, one, zero)

let is_aff_point_at_inf (p:aff_point) : bool =
  let (x, y) = p in x = zero && y = zero

let is_point_at_inf (p:proj_point) =
  let (_, _, z) = p in z = 0


let to_proj_point (p:aff_point) : proj_point =
  let (x, y) = p in (x, y, one)

let to_aff_point (p:proj_point) : aff_point =
  // if is_proj_point_at_inf p then aff_point_at_inf
  let (px, py, pz) = p in
  let zinv = finv pz in
  let x = px *% zinv in
  let y = py *% zinv in
  (x, y)


///  Point addition in affine coordinates

let aff_point_double (p:aff_point) : aff_point =
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

let aff_point_add (p:aff_point) (q:aff_point) : aff_point =
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
let point_add (p q:proj_point) : proj_point =
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
let point_double (p:proj_point) : proj_point =
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

let aff_point_load (b:BSeq.lbytes 64) : option aff_point =
  let pk_x = BSeq.nat_from_bytes_be (sub b 0 32) in
  let pk_y = BSeq.nat_from_bytes_be (sub b 32 32) in
  let is_x_valid = pk_x < prime in
  let is_y_valid = pk_y < prime in
  let is_xy_on_curve =
    if is_x_valid && is_y_valid then is_on_curve (pk_x, pk_y) else false in
  if is_xy_on_curve then Some (pk_x, pk_y) else None


let load_point (b:BSeq.lbytes 64) : option proj_point =
  match (aff_point_load b) with
  | Some p -> Some (to_proj_point p)
  | None -> None


let aff_point_store (p:aff_point) : BSeq.lbytes 64 =
  let (px, py) = p in
  let pxb = BSeq.nat_to_bytes_be 32 px in
  let pxy = BSeq.nat_to_bytes_be 32 py in
  concat #uint8 #32 #32 pxb pxy


let point_store (p:proj_point) : BSeq.lbytes 64 =
  aff_point_store (to_aff_point p)


let recover_y (x:felem) (is_odd:bool) : option felem =
  let y2 = x *% x *% x +% a_coeff *% x +% b_coeff in
  let y = fsqrt y2 in
  if y *% y <> y2 then None
  else begin
    let y = if is_fodd y <> is_odd then (prime - y) % prime else y in
    Some y end


let aff_point_decompress (s:BSeq.lbytes 33) : option aff_point =
  let s0 = Lib.RawIntTypes.u8_to_UInt8 s.[0] in
  if not (s0 = 0x02uy || s0 = 0x03uy) then None
  else begin
    let x = BSeq.nat_from_bytes_be (sub s 1 32) in
    let is_x_valid = x < prime in
    let is_y_odd = s0 = 0x03uy in

    if not is_x_valid then None
    else
      match (recover_y x is_y_odd) with
      | Some y -> Some (x, y)
      | None -> None end
