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

let scalar_t = s:lbytes 32{nat_from_bytes_be s < q}

///  Elliptic curve

let aff_point = felem & felem        // Affine point
let proj_point = felem & felem & felem // Projective coordinates

// y * y = x * x * x + b
let b : felem = 7

// Base point
let g_x : felem = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
let g_y : felem = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
let g : proj_point = (g_x, g_y, one)

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


let is_on_curve (p:aff_point) =
  let x, y = p in y *% y = x *% x *% x +% b

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
val aff_point_at_inf_lemma (p:aff_point) :
  Lemma (aff_point_add p aff_point_at_inf = p)

assume
val aff_point_add_assoc_lemma (p q s:aff_point) :
  Lemma (aff_point_add (aff_point_add p q) s == aff_point_add p (aff_point_add q s))

assume
val aff_point_add_comm_lemma (p q:aff_point) :
  Lemma (aff_point_add p q = aff_point_add q p)

assume
val to_aff_point_at_infinity_lemma: unit ->
  Lemma (to_aff_point point_at_inf == aff_point_at_inf)

assume
val to_aff_point_add_lemma (p q:proj_point) :
  Lemma (to_aff_point (point_add p q) == aff_point_add (to_aff_point p) (to_aff_point q))

assume
val to_aff_point_double_lemma (p:proj_point) :
  Lemma (to_aff_point (point_double p) == aff_point_add (to_aff_point p) (to_aff_point p))


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
  to_aff_point_at_infinity_lemma ();
  point_at_inf

val point_add_c : SE.mul_st proj_point mk_to_k256_cm
let point_add_c p q =
  to_aff_point_add_lemma p q;
  point_add p q

val point_double_c : SE.sqr_st proj_point mk_to_k256_cm
let point_double_c p =
  to_aff_point_double_lemma p;
  point_double p

let mk_k256_concrete_ops : SE.concrete_ops proj_point = {
  SE.to = mk_to_k256_cm;
  SE.one = point_at_inf_c;
  SE.mul = point_add_c;
  SE.sqr = point_double_c;
}


// [a]P
let point_mul (a:qelem) (p:proj_point) : proj_point =
  let out = SE.exp_fw mk_k256_concrete_ops p 256 a 4 in
  assert (to_aff_point out == LE.exp_fw #aff_point mk_k256_cm (to_aff_point p) 256 a 4);
  out

// [a1]P1 + [a2]P2
let point_mul_double (a1:qelem) (p1:proj_point) (a2:qelem) (p2:proj_point) : proj_point =
  SE.exp_double_fw mk_k256_concrete_ops p1 256 a1 p2 a2 4

// [a]G
let point_mul_g (a:qelem) : proj_point = point_mul a g

// [a1]G + [a2]P
let point_mul_double_g (a1:qelem) (a2:qelem) (p:proj_point) : proj_point =
  point_mul_double a1 g a2 p

///  ECDSA with a prehashed message

// TODO: add `secret_to_public`?

val ecdsa_sign_hashed_msg:
     m:lbytes 32
  -> private_key:scalar_t{0 < nat_from_bytes_be private_key}
  -> k:scalar_t{0 < nat_from_bytes_be k} ->
  tuple3 scalar_t scalar_t bool

let ecdsa_sign_hashed_msg m private_key k =
  let k_q = nat_from_bytes_be k in
  let d_a = nat_from_bytes_be private_key in
  let z = nat_from_bytes_be m % q in

  let _X, _Y, _Z = point_mul_g k_q in
  let x = _X /% _Z in (* or (x, y) = to_aff_point (_X, _Y, _Z) *)
  let r = x % q in

  let kinv = qinv k_q in
  let s = kinv *^ (z +^ r *^ d_a) in

  let rb = nat_to_bytes_be 32 r in
  let sb = nat_to_bytes_be 32 s in

  if r = 0 || s = 0 then
    rb, sb, false
  else
    rb, sb, true


val is_public_key_valid (pk_x pk_y:lbytes 32) : tuple3 nat nat bool
let is_public_key_valid pk_x pk_y =
  let pk_x = nat_from_bytes_be pk_x in
  let pk_y = nat_from_bytes_be pk_y in
  let is_x_valid = 0 < pk_x && pk_x < prime in
  let is_y_valid = 0 < pk_y && pk_y < prime in
  let is_xy_on_curve =
    if is_x_valid && is_y_valid then is_on_curve (pk_x, pk_y) else false in
  pk_x, pk_y, is_xy_on_curve


val ecdsa_verify_hashed_msg (m public_key_x public_key_y r s:lbytes 32) : bool
let ecdsa_verify_hashed_msg m public_key_x public_key_y r s =
  let pk_x, pk_y, is_xy_on_curve = is_public_key_valid public_key_x public_key_y in
  let r = nat_from_bytes_be r in
  let s = nat_from_bytes_be s in
  let z = nat_from_bytes_be m % q in

  let is_r_valid = 0 < r && r < q in
  let is_s_valid = 0 < s && s < q in

  if not (is_xy_on_curve && is_r_valid && is_s_valid) then false
  else begin
    assert_norm (q < pow2 256);
    let sinv = qinv s in
    let u1 = z *^ sinv in
    let u2 = r *^ sinv in
    let _X, _Y, _Z = point_mul_double_g u1 u2 (pk_x, pk_y, one) in
    let x = _X /% _Z in (* TODO: optimize, as we don't need to compute a field inverse *)
    x % q = r
  end


(*  if _Z = 0 then x = 0 and r <> 0, i.e., we return `false` anyway

    if (is_proj_point_at_inf (_X, _Y, _Z)) then false
    else begin
      let x = _X /% _Z in
      x % q = r
    end
*)

///  ECDSA

let _:_:unit{Spec.Hash.Definitions.max_input_length Spec.Hash.Definitions.SHA2_256 > pow2 32} =
 assert_norm (Spec.Hash.Definitions.max_input_length Spec.Hash.Definitions.SHA2_256 > pow2 32)


val ecdsa_sign_sha256:
    msg_len:size_nat
  -> msg:lbytes msg_len
  -> private_key:scalar_t{0 < nat_from_bytes_be private_key}
  -> k:scalar_t{0 < nat_from_bytes_be k} ->
  tuple3 scalar_t scalar_t bool

let ecdsa_sign_sha256 msg_len msg private_key k =
  let m = Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_256 msg in
  ecdsa_sign_hashed_msg m private_key k


val ecdsa_verify_sha256
  (msg_len:size_nat) (msg:lbytes msg_len)
  (public_key_x public_key_y r s:lbytes 32) : bool

let ecdsa_verify_sha256 msg_len msg public_key_x public_key_y r s =
  let m = Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_256 msg in
  ecdsa_verify_hashed_msg m public_key_x public_key_y r s
