module Hacl.Spec.K256.ECSM.Lemmas

open FStar.Mul

module M = Lib.NatMod
module LE = Lib.Exponentiation
module SE = Spec.Exponentiation

module S = Spec.K256
module LS = Spec.K256.Lemmas

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// [a]P in affine coordinates
let aff_point_mul = S.aff_point_mul

// [a]P in affine coordinates
let aff_point_mul_neg (a:int) (p:S.aff_point) : S.aff_point =
  LE.pow_neg S.mk_k256_abelian_group p a


assume
val lemma_order_of_curve_group (p:S.aff_point) :
  Lemma (aff_point_mul S.q p == S.aff_point_at_inf)


val lemma_proj_aff_id (p:S.aff_point) :
  Lemma (S.(to_aff_point (to_proj_point p)) == p)

let lemma_proj_aff_id p =
  let (px, py) = p in
  let (pX, pY, pZ) = S.to_proj_point p in
  assert (pX = px /\ pY = pY /\ pZ = S.one);
  let (rx, ry) = S.to_aff_point (pX, pY, pZ) in
  assert (rx = S.(pX /% pZ) /\ ry = S.(pY /% pZ));
  M.lemma_div_mod_prime_one #S.prime pX;
  M.lemma_div_mod_prime_one #S.prime pY;
  assert (rx = pX /\ ry = pY)


// // TODO: what about point_at_infinity?
// val lemma_point_mul (a:S.qelem) (p:S.proj_point) : Lemma
//   (S.(to_aff_point (point_mul a p)) == aff_point_mul a (S.to_aff_point p))

// let lemma_point_mul a p =
//   SE.exp_fw_lemma S.mk_k256_concrete_ops p 256 a 4;
//   LE.exp_fw_lemma S.mk_k256_comm_monoid (S.to_aff_point p) 256 a 4


// val lemma_aff_point_mul_via_proj (a:S.qelem) (p:S.aff_point) : Lemma
//   (S.(to_aff_point (point_mul a (to_proj_point p))) == aff_point_mul a p)

// let lemma_aff_point_mul_via_proj a p =
//   lemma_point_mul a (S.to_proj_point p);
//   lemma_proj_aff_id p


(**
   Properties for Elliptic Curve Scalar Multiplication in affine coordinates
*)

val lemma_aff_point_mul_neg_add (a b:int) (p:S.aff_point) :
  Lemma (aff_point_mul_neg (a + b) p ==
    S.aff_point_add (aff_point_mul_neg a p) (aff_point_mul_neg b p))

let lemma_aff_point_mul_neg_add a b p =
  LE.lemma_pow_neg_add S.mk_k256_abelian_group p a b


val lemma_aff_point_mul_neg_mul (a b:int) (p:S.aff_point) :
  Lemma (aff_point_mul_neg (a * b) p == aff_point_mul_neg b (aff_point_mul_neg a p))

let lemma_aff_point_mul_neg_mul a b p =
  LE.lemma_pow_neg_mul S.mk_k256_abelian_group p a b


val lemma_aff_point_mul_neg_mul_add (a b c:int) (p:S.aff_point) :
  Lemma (aff_point_mul_neg (a * b + c) p ==
    S.aff_point_add (aff_point_mul_neg b (aff_point_mul_neg a p)) (aff_point_mul_neg c p))

let lemma_aff_point_mul_neg_mul_add a b c p =
  lemma_aff_point_mul_neg_add (a * b) c p;
  lemma_aff_point_mul_neg_mul a b p


val lemma_aff_point_mul_neg_modq (a:int) (p:S.aff_point) :
  Lemma (aff_point_mul_neg a p == aff_point_mul (a % S.q) p)

let lemma_aff_point_mul_neg_modq a p =
  calc (==) {
    aff_point_mul_neg a p;
    (==) { Math.Lemmas.euclidean_division_definition a S.q }
    aff_point_mul_neg (a / S.q * S.q + a % S.q) p;
    (==) { lemma_aff_point_mul_neg_add (a / S.q * S.q) (a % S.q) p }
    S.aff_point_add (aff_point_mul_neg (a / S.q * S.q) p) (aff_point_mul_neg (a % S.q) p);
    (==) { lemma_aff_point_mul_neg_mul (a / S.q) S.q p }
    S.aff_point_add
      (aff_point_mul S.q (aff_point_mul_neg (a / S.q) p))
      (aff_point_mul (a % S.q) p);
    (==) { lemma_order_of_curve_group (aff_point_mul_neg (a / S.q) p) }
    S.aff_point_add S.aff_point_at_inf (aff_point_mul (a % S.q) p);
    (==) { LS.aff_point_add_comm_lemma S.aff_point_at_inf (aff_point_mul (a % S.q) p) }
    S.aff_point_add (aff_point_mul (a % S.q) p) S.aff_point_at_inf;
    (==) { LS.aff_point_at_inf_lemma (aff_point_mul (a % S.q) p) }
    aff_point_mul (a % S.q) p;
  }

//-----------------------------------

(**
  ECDSA-verify using ECSM in affine coordinates
*)

open Lib.Sequence
open Lib.ByteSequence

let aff_ecdsa_verify_hashed_msg (msgHash:lbytes 32) (public_key signature:lbytes 64) : bool =
  let open Spec.K256 in
  let pk_x, pk_y, is_xy_on_curve = load_public_key public_key in
  let r = nat_from_bytes_be (sub signature 0 32) in
  let s = nat_from_bytes_be (sub signature 32 32) in
  let z = nat_from_bytes_be msgHash % q in

  let is_r_valid = 0 < r && r < q in
  let is_s_valid = 0 < s && s < q in

  if not (is_xy_on_curve && is_r_valid && is_s_valid) then false
  else begin
    assert_norm (q < pow2 256);
    let sinv = qinv s in
    let u1 = z *^ sinv in
    let u2 = r *^ sinv in
    let x, y = aff_point_mul_double u1 (g_x, g_y) u2 (pk_x, pk_y) in
    if is_aff_point_at_inf (x,y) then false
    else x % q = r
  end


val ecdsa_verify_hashed_msg_is_aff (msgHash:lbytes 32) (public_key signature:lbytes 64) :
  Lemma (S.ecdsa_verify_hashed_msg msgHash public_key signature ==
    aff_ecdsa_verify_hashed_msg msgHash public_key signature)

let ecdsa_verify_hashed_msg_is_aff msgHash public_key signature =
  let open Spec.K256 in
  let pk_x, pk_y, is_xy_on_curve = load_public_key public_key in
  let r = nat_from_bytes_be (sub signature 0 32) in
  let s = nat_from_bytes_be (sub signature 32 32) in
  let z = nat_from_bytes_be msgHash % q in

  let is_r_valid = 0 < r && r < q in
  let is_s_valid = 0 < s && s < q in

  if not (is_xy_on_curve && is_r_valid && is_s_valid) then ()
  else begin
    assert_norm (q < pow2 256);
    let sinv = qinv s in
    let u1 = z *^ sinv in
    let u2 = r *^ sinv in

    let pk = (pk_x, pk_y) in
    let pk_proj = to_proj_point pk in
    let base = (g_x, g_y) in
    let base_proj = g in

    let x, y = aff_point_mul_double u1 base u2 pk in
    let _X, _Y, _Z = point_mul_double_g u1 u2 pk_proj in

    lemma_proj_aff_id base;
    lemma_proj_aff_id pk;
    assert (to_aff_point base_proj == base);
    assert (to_aff_point pk_proj == pk);
    SE.exp_double_fw_lemma mk_k256_concrete_ops base_proj 256 u1 pk_proj u2 4;
    LE.exp_double_fw_lemma mk_k256_comm_monoid
      (to_aff_point base_proj) 256 u1 (to_aff_point pk_proj) u2 4;
    assert (to_aff_point (_X, _Y, _Z) == (x, y));
    () end
