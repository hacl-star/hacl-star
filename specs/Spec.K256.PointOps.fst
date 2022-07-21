module Spec.K256.PointOps

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

module M = Lib.NatMod
module BSeq = Lib.ByteSequence

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

///  Finite field

let prime : (p:pos{p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F}) =
  assert_norm (24 < pow2 256 - 0x1000003D1);
  assert_norm (pow2 256 - 0x1000003D1 = pow2 256 - pow2 32 - pow2 9 - pow2 8 - pow2 7 - pow2 6 - pow2 4 - 1);
  assert_norm (pow2 256 - 0x1000003D1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F);
  pow2 256 - 0x1000003D1

let felem = x:nat{x < prime}
let zero : felem = 0
let one  : felem = 1

let fadd (x y:felem) : felem = (x + y) % prime
let fsub (x y:felem) : felem = (x - y) % prime
let fmul (x y:felem) : felem = (x * y) % prime

let ( +% ) = fadd
let ( -% ) = fsub
let ( *% ) = fmul

let finv (x:felem) : felem = M.pow_mod #prime x (prime - 2)
let ( /% ) (x y:felem) = x *% finv y

// for parsing and serializing public keys
let fsqrt (x:felem) : felem = M.pow_mod #prime x ((prime + 1) / 4)
let is_fodd (x:nat) : bool = x % 2 = 1


///  Scalar field

// Group order
let q : q:pos{q < pow2 256} =
  assert_norm (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 < pow2 256);
  0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

let qelem = x:nat{x < q}
let qadd (x y:qelem) : qelem = (x + y) % q
let qmul (x y:qelem) : qelem = (x * y) % q
let qinv (x:qelem) : qelem = M.pow_mod #q x (q - 2)

let ( +^ ) = qadd
let ( *^ ) = qmul

///  Elliptic curve

let aff_point = felem & felem        // Affine point
let proj_point = felem & felem & felem // Projective coordinates

// y * y = x * x * x + b
let b : felem = 7

let is_on_curve (p:aff_point) =
  let x, y = p in y *% y = x *% x *% x +% b

let aff_point_at_inf : aff_point = (zero, zero) // not on the curve!
let point_at_inf : proj_point = (zero, one, zero)

let is_proj_point_at_inf (p:proj_point) : bool =
  let (_, _, z) = p in z = zero

let to_aff_point (p:proj_point) : aff_point =
  let (px, py, pz) = p in
  let zinv = finv pz in
  let x = px *% zinv in
  let y = py *% zinv in
  (x, y)

let to_proj_point (p:aff_point) : proj_point =
  let (x, y) = p in (x, y, one)

// Base point
let g_x : felem = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
let g_y : felem = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
let g : proj_point = (g_x, g_y, one)

///  Point addition in affine coordinates

assume
val aff_point_add (p:aff_point) (y:aff_point) : aff_point

///  Point addition and doubling in projective coordinates

let point_add (p:proj_point) (q:proj_point) : proj_point =
  let x1, y1, z1 = p in
  let x2, y2, z2 = q in
  let xx = x1 *% x2 in
  let yy = y1 *% y2 in
  let zz = z1 *% z2 in
  let xy_pairs = (x1 +% y1) *% (x2 +% y2) -% (xx +% yy) in
  let yz_pairs = (y1 +% z1) *% (y2 +% z2) -% (yy +% zz) in
  let xz_pairs = (x1 +% z1) *% (x2 +% z2) -% (xx +% zz) in
  let bzz3 = 3 *% b *% zz in
  let yy_m_bzz3 = yy -% bzz3 in
  let yy_p_bzz3 = yy +% bzz3 in
  let byz3 = 3 *% b *% yz_pairs in
  let xx3 = 3 *% xx in
  let bxx9 = 3 *% b *% xx3 in
  let x3 = xy_pairs *% yy_m_bzz3 -% byz3 *% xz_pairs in
  let y3 = yy_p_bzz3 *% yy_m_bzz3 +% bxx9 *% xz_pairs in
  let z3 = yz_pairs *% yy_p_bzz3 +% xx3 *% xy_pairs in
  x3, y3, z3

let point_double (p:proj_point) : proj_point =
  let x, y, z = p in
  let yy = y *% y in
  let zz = z *% z in
  let xy2 = 2 *% x *% y in
  let bzz3 = 3 *% b *% zz in
  let bzz9 = 3 *% bzz3 in
  let yy_m_bzz9 = yy -% bzz9 in
  let yy_p_bzz3 = yy +% bzz3 in
  let yy_zz = yy *% zz in
  let t = 24 *% b *% yy_zz in
  let x3 = xy2 *% yy_m_bzz9 in
  let y3 = yy_m_bzz9 *% yy_p_bzz3 +% t in
  let z3 = yy *% y *% z *% 8 in
  x3, y3, z3

let point_negate (p:proj_point) : proj_point =
  let x, y, z = p in
  x, (-y) % prime, z


let recover_y (x:felem{0 < x}) (is_odd:bool) : option felem =
  let y2 = x *% x *% x +% b in
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
    let is_x_valid = 0 < x && x < prime in
    let is_y_odd = s0 = 0x03uy in

    if not is_x_valid then None
    else
      match (recover_y x is_y_odd) with
      | Some y -> Some (x, y)
      | None -> None end


let aff_point_compress (p:aff_point) : BSeq.lbytes 33 =
  let (x, y) = p in
  let is_y_odd = y % 2 = 1 in
  let s0 = if is_y_odd then u8 0x03 else u8 0x02 in
  concat #_ #1 #32 (create 1 s0) (BSeq.nat_to_bytes_be 32 x)


let point_decompress (s:BSeq.lbytes 33) : option proj_point =
  match (aff_point_decompress s) with
  | Some p -> Some (to_proj_point p)
  | None -> None


let point_compress (p:proj_point) : BSeq.lbytes 33 =
  aff_point_compress (to_aff_point p)


let point_equal (p:proj_point) (q:proj_point) : bool =
  let px, py, pz = p in // x_p = px / pz /\ y_p = py / pz
  let qx, qy, qz = q in // x_q = qx / qz /\ y_q = qy / qz
  // p == q <==> x_p == x_q /\ y_p == y_q <==> px * qz == qx * pz /\ py * qz == qy * pz
  if ((px *% qz) <> (qx *% pz)) then false
  else ((py *% qz) = (qy *% pz))
