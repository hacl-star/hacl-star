module Spec.K256

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module M = Lib.NatMod
module LE = Lib.Exponentiation
module SE = Spec.Exponentiation


#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

(**
 K256: https://en.bitcoin.it/wiki/Secp256k1
 ECDSA: https://en.bitcoin.it/wiki/Elliptic_Curve_Digital_Signature_Algorithm
 https://www.hyperelliptic.org/EFD/g1p/auto-shortw.html
*)

///  Finite field

let prime : (p:pos{p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F}) =
  assert_norm (24 < pow2 256 - 0x1000003D1);
  assert_norm (pow2 256 - 0x1000003D1 = pow2 256 - pow2 32 - pow2 9 - pow2 8 - pow2 7 - pow2 6 - pow2 4 - 1);
  assert_norm (pow2 256 - 0x1000003D1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F);
  pow2 256 - 0x1000003D1

let elem = x:nat{x < prime}
let zero : elem = 0
let one  : elem = 1

let fadd (x y:elem) : elem = (x + y) % prime
let fsub (x y:elem) : elem = (x - y) % prime
let fmul (x y:elem) : elem = (x * y) % prime

let ( +% ) = fadd
let ( -% ) = fsub
let ( *% ) = fmul

let finv (x:elem) : elem = M.pow_mod #prime x (prime - 2)
let ( /% ) (x y:elem) = x *% finv y


///  Elliptic curve

let aff_point = elem & elem        // Affine point
let proj_point = elem & elem & elem // Projective coordinates

// y * y = x * x * x + b
let b : elem = 7

// Base point
let g_x : elem = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
let g_y : elem = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
let g : proj_point = (g_x, g_y, one)

// Group order
let q : pos =
  0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

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


let is_proj_point_at_inf (p:proj_point) : bool =
  let (_, _, z) = p in z = zero

// TODO: add `is_point_on_curve`
let aff_point_at_inf : aff_point = (zero, zero) // not on the curve!
let point_at_inf : proj_point = (zero, one, zero)


let to_aff_point (p:proj_point) : aff_point =
  let (x, y, z) = p in
  (x /% z, y /% z)

let to_proj_point (p:aff_point) : proj_point =
  let (x, y) = p in (x, y, one)

assume
val aff_point_add (p:aff_point) (y:aff_point) : aff_point

assume
val aff_point_at_inf_lemma : p:aff_point ->
  Lemma (aff_point_add p aff_point_at_inf  = p)

assume
val aff_point_add_assoc_lemma : p:aff_point -> q:aff_point -> s:aff_point ->
  Lemma (aff_point_add (aff_point_add p q) s == aff_point_add p (aff_point_add q s))

assume
val aff_point_add_comm_lemma : p:aff_point -> q:aff_point ->
  Lemma (aff_point_add p q = aff_point_add q p)


let mk_k256_cm : LE.comm_monoid aff_point = {
  LE.one = aff_point_at_inf;
  LE.mul = aff_point_add;
  LE.lemma_one = aff_point_at_inf_lemma;
  LE.lemma_mul_assoc = aff_point_add_assoc_lemma;
  LE.lemma_mul_comm = aff_point_add_comm_lemma;
}

let mk_to_k256_cm : SE.to_comm_monoid proj_point = {
  SE.a_spec = aff_point;
  SE.comm_monoid = mk_k256_cm;
  SE.refl = to_aff_point;
}

val point_at_inf_c: SE.one_st proj_point mk_to_k256_cm
let point_at_inf_c _ =
  assume (to_aff_point point_at_inf = aff_point_at_inf);
  point_at_inf

val point_add_c : SE.mul_st proj_point mk_to_k256_cm
let point_add_c p q =
  assume (to_aff_point (point_add p q) == aff_point_add (to_aff_point p) (to_aff_point q));
  point_add p q

val point_double_c : SE.sqr_st proj_point mk_to_k256_cm
let point_double_c p =
  assume (to_aff_point (point_double p) == aff_point_add (to_aff_point p) (to_aff_point p));
  point_double p


let mk_k256_concrete_ops : SE.concrete_ops proj_point = {
  SE.to = mk_to_k256_cm;
  SE.one = point_at_inf_c;
  SE.mul = point_add_c;
  SE.sqr = point_double_c;
}


// [a]G
let point_mul_g (a:lbytes 32) : proj_point =
  SE.exp_fw mk_k256_concrete_ops g 256 (nat_from_bytes_be a) 4

// [a1]G + [a2]P
let point_mul_double_g (a1:lbytes 32) (a2:lbytes 32) (p:proj_point) : proj_point =
  SE.exp_double_fw mk_k256_concrete_ops g 256 (nat_from_bytes_be a1) p (nat_from_bytes_be a2) 4

///  ECDSA

let scalar_t = s:lbytes 32{nat_from_bytes_be s < q}

// TODO: add `secret_to_public`?

// TODO: check that 0 < `private_key` < q?
val ecdsa_sign_hashed_msg:
     m:lbytes 32
  -> private_key:lbytes 32
  -> k:lbytes 32{0 < nat_from_bytes_be k /\ nat_from_bytes_be k < q} ->
  tuple3 scalar_t scalar_t bool

let ecdsa_sign_hashed_msg m private_key k =
  let z = nat_from_bytes_be m % q in
  let d_a = nat_from_bytes_be private_key in

  let (_X, _Y, _Z) = point_mul_g k in
  let x = _X /% _Z in (* or (x, y) = to_aff_point (_X, _Y, _Z) *)

  let r = x % q in
  let kinv = M.pow_mod #q (nat_from_bytes_be k) (q - 2) in
  let s = kinv * (z + r * d_a) % q in

  let rb = nat_to_bytes_be 32 r in
  let sb = nat_to_bytes_be 32 s in

  if r = 0 || s = 0 then
    rb, sb, false
  else
    rb, sb, true


// TODO: check that `public_key` is a point on the curve
val ecdsa_verify_hashed_msg:
     m:lbytes 32
  -> public_key:aff_point
  -> rb:lbytes 32 -> sb:lbytes 32 ->
  bool

let ecdsa_verify_hashed_msg m public_key rb sb =
  let r = nat_from_bytes_be rb in
  let s = nat_from_bytes_be sb in
  let z = nat_from_bytes_be m % q in

  assert_norm (q < pow2 256);

  if not (0 < r && r < q) then false
  else begin
    if not (0 < s && s < q) then false
    else begin
      let sinv = M.pow_mod #q s (q - 2) in
      let u1 = z * sinv % q in
      let u2 = r * sinv % q in
      let (_X, _Y, _Z) =
	point_mul_double_g (nat_to_bytes_be 32 u1) (nat_to_bytes_be 32 u2) (to_proj_point public_key) in

      if (is_proj_point_at_inf (_X, _Y, _Z)) then false
      else begin
	let x = _X /% _Z in (* TODO: optimize, as we don't need to compute a field inverse *)
	if x % q = r then true else false end
    end
  end



let _:_:unit{Spec.Hash.Definitions.max_input_length Spec.Hash.Definitions.SHA2_256 > pow2 32} =
 assert_norm (Spec.Hash.Definitions.max_input_length Spec.Hash.Definitions.SHA2_256 > pow2 32)


val ecdsa_sign_sha256:
    msgLen:size_nat
  -> msg:lbytes msgLen
  -> private_key:lbytes 32
  -> k:lbytes 32{0 < nat_from_bytes_be k /\ nat_from_bytes_be k < q} ->
  tuple3 scalar_t scalar_t bool

let ecdsa_sign_sha256 msgLen msg private_key k =
  let m = Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_256 msg in
  ecdsa_sign_hashed_msg m private_key k


val ecdsa_verify_sha256:
    msg_len:size_nat
  -> msg:lbytes msg_len
  -> public_key:aff_point
  -> r:lbytes 32 -> s:lbytes 32 ->
  bool

let ecdsa_verify_sha256 msg_len msg public_key r s =
  let m = Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_256 msg in
  ecdsa_verify_hashed_msg m public_key r s
