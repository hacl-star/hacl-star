module Spec.P256.PointOps

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

module M = Lib.NatMod
module BSeq = Lib.ByteSequence

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Base field

// 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
let prime: (a:pos{8 < a && a < pow2 256}) =
  let p = pow2 256 - pow2 224 + pow2 192 + pow2 96 - 1 in
  assert_norm (8 < p); assert_norm (p < pow2 256); p

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
let jacob_point = p:tuple3 nat nat nat{let (px, py, pz) = p in px < prime /\ py < prime /\ pz < prime}

// let aff_point = felem & felem           // Affine point
// let jacob_point = felem & felem & felem // Jacobian coordinates

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

let base_point : jacob_point = (g_x, g_y, one)

let is_point_on_curve (p:aff_point) : bool =
  let (x, y) = p in y *% y = x *% x *% x +% a_coeff *% x +% b_coeff

let point_at_inf : jacob_point = (zero, zero, zero)

let is_point_at_inf (p:jacob_point) =
  let (_, _, z) = p in z = 0

let to_jacob_point (p:aff_point) : jacob_point =
  let (x, y) = p in (x, y, one)


// TODO: avoid computing finv twice
let norm_jacob_point (p:jacob_point) : jacob_point =
  let (x, y, z) = p in
  let z2 = z *% z in
  let z3 = z2 *% z in
  let z2i = finv z2 in
  let z3i = finv z3 in
  let x3 = z2i *% x in
  let y3 = z3i *% y in
  let z3 = if is_point_at_inf (x, y, z) then zero else one in
  (x3, y3, z3)


///  Point addition and doubling in jacobian coordinates
// TODO: use complete formulas

let point_double (p:jacob_point) : jacob_point =
  let x, y, z = p in
  let delta = z *% z in
  let gamma = y *% y in
  let beta = x *% gamma in
  let alpha = 3 *% (x -% delta) *% (x +% delta) in
  let x3 = alpha *% alpha -% 8 *% beta in
  let y3 = alpha *% (4 *% beta -% x3) -% 8 *% gamma *% gamma in
  let z3 = (y +% z) *% (y +% z) -% delta -% gamma in
  (x3, y3, z3)


let point_add_no_point_at_inf (p:jacob_point) (q:jacob_point) : jacob_point =
  let (x1, y1, z1) = p in
  let (x2, y2, z2) = q in

  let z2z2 = z2 *% z2 in
  let z1z1 = z1 *% z1 in

  let u1 = x1 *% z2z2 in
  let u2 = x2 *% z1z1 in

  let s1 = y1 *% z2 *% z2z2 in
  let s2 = y2 *% z1 *% z1z1 in

  let h = u2 -% u1 in
  let r = s2 -% s1 in

  let rr = r *% r in
  let hh = h *% h in
  let hhh = hh *% h in

  let x3 = rr -% hhh -% 2 *% (u1 *% hh) in
  let y3 = r *% (u1 *% hh -% x3) -% s1 *% hhh in
  let z3 = h *% z1 *% z2 in
  (x3, y3, z3)

let point_add (p:jacob_point) (q:jacob_point) : jacob_point =
  let r = point_add_no_point_at_inf p q in
  if is_point_at_inf q then p
  else
    if is_point_at_inf p then q
    else r


///  Point conversion between affine, jacobian and bytes representation

let load_point (b:BSeq.lbytes 64) : option jacob_point =
  let pk_x = BSeq.nat_from_bytes_be (sub b 0 32) in
  let pk_y = BSeq.nat_from_bytes_be (sub b 32 32) in
  let is_x_valid = pk_x < prime in
  let is_y_valid = pk_y < prime in
  let is_xy_on_curve =
    if is_x_valid && is_y_valid then is_point_on_curve (pk_x, pk_y) else false in
  if is_xy_on_curve then Some (to_jacob_point (pk_x, pk_y)) else None


let aff_point_store (p:aff_point) : BSeq.lbytes 64 =
  let (px, py) = p in
  let pxb = BSeq.nat_to_bytes_be 32 px in
  let pxy = BSeq.nat_to_bytes_be 32 py in
  concat #uint8 #32 #32 pxb pxy


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
