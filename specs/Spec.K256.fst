module Spec.K256

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module M = Lib.NatMod
module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module KL = Spec.K256.Lemmas

include Spec.K256.PointOps

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

(**
 K256: https://en.bitcoin.it/wiki/Secp256k1
 ECDSA: https://en.bitcoin.it/wiki/Elliptic_Curve_Digital_Signature_Algorithm
 https://www.hyperelliptic.org/EFD/g1p/auto-shortw.html
*)

let mk_k256_cm : LE.comm_monoid aff_point = {
  LE.one = aff_point_at_inf;
  LE.mul = aff_point_add;
  LE.lemma_one = KL.aff_point_at_inf_lemma;
  LE.lemma_mul_assoc = KL.aff_point_add_assoc_lemma;
  LE.lemma_mul_comm = KL.aff_point_add_comm_lemma;
}

let mk_to_k256_cm : SE.to_cm proj_point = {
  SE.a_spec = aff_point;
  SE.cm = mk_k256_cm;
  SE.refl = to_aff_point;
}

val point_at_inf_c: SE.one_st proj_point mk_to_k256_cm
let point_at_inf_c _ =
  KL.to_aff_point_at_infinity_lemma ();
  point_at_inf

val point_add_c : SE.mul_st proj_point mk_to_k256_cm
let point_add_c p q =
  KL.to_aff_point_add_lemma p q;
  point_add p q

val point_double_c : SE.sqr_st proj_point mk_to_k256_cm
let point_double_c p =
  KL.to_aff_point_double_lemma p;
  point_double p

let mk_k256_concrete_ops : SE.concrete_ops proj_point = {
  SE.to = mk_to_k256_cm;
  SE.one = point_at_inf_c;
  SE.mul = point_add_c;
  SE.sqr = point_double_c;
}


// [a]P
let point_mul (a:qelem) (p:proj_point) : proj_point =
  SE.exp_fw mk_k256_concrete_ops p 256 a 4

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

let scalar_t = s:lbytes 32{nat_from_bytes_be s < q}


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


val is_public_key_valid (pk:lbytes 64) : tuple3 nat nat bool
let is_public_key_valid pk =
  let pk_x = nat_from_bytes_be (sub pk 0 32) in
  let pk_y = nat_from_bytes_be (sub pk 32 32) in
  let is_x_valid = 0 < pk_x && pk_x < prime in
  let is_y_valid = 0 < pk_y && pk_y < prime in
  let is_xy_on_curve =
    if is_x_valid && is_y_valid then is_on_curve (pk_x, pk_y) else false in
  pk_x, pk_y, is_xy_on_curve


val ecdsa_verify_hashed_msg (m:lbytes 32) (public_key:lbytes 64) (r s:lbytes 32) : bool
let ecdsa_verify_hashed_msg m public_key r s =
  let pk_x, pk_y, is_xy_on_curve = is_public_key_valid public_key in
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

    if is_proj_point_at_inf (_X, _Y, _Z) then false
    else begin
      let x = _X /% _Z in
      x % q = r end
  end

(*
   _Z <> 0
   q < prime < 2 * q
   let x = _X /% _Z in x % q = r <==>
   1. x = r <==> _X = r *% _Z
   2. x - q = r <==> _X = (r + q) *% _Z
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
  (public_key:lbytes 64) (r s:lbytes 32) : bool

let ecdsa_verify_sha256 msg_len msg public_key r s =
  let m = Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_256 msg in
  ecdsa_verify_hashed_msg m public_key r s


///  Parsing and Serializing public keys

// raw          = [ x; y ], 64 bytes
// uncompressed = [ 0x04; x; y ], 65 bytes
// compressed   = [ 0x02 for even `y` and 0x03 for odd `y`; x ], 33 bytes

let pk_uncompressed_to_raw (pk:lbytes 65) : option (lbytes 64) =
  if Lib.RawIntTypes.u8_to_UInt8 pk.[0] <> 0x04uy then None else Some (sub pk 1 64)

let pk_uncompressed_from_raw (pk:lbytes 64) : lbytes 65 =
  concat (create 1 (u8 0x04)) pk

let pk_compressed_to_raw (pk:lbytes 33) : option (lbytes 64) =
  let pk0 = Lib.RawIntTypes.u8_to_UInt8 pk.[0] in
  if not (pk0 = 0x02uy || pk0 = 0x03uy) then None
  else begin
    let pk_xb = sub pk 1 32 in
    let is_pk_y_odd = pk0 = 0x03uy in
    let pk_yb = recover_y_bytes pk_xb is_pk_y_odd in
    match pk_yb with
    | Some pk_yb -> Some (concat #_ #32 #32 pk_xb pk_yb)
    | None -> None end

let pk_compressed_from_raw (pk:lbytes 64) : lbytes 33 =
  let pk_x = sub pk 0 32 in
  let pk_y = sub pk 32 32 in
  let is_pk_y_odd = nat_from_bytes_be pk_y % 2 = 1 in // <==> pk_y % 2 = 1
  let pk0 = if is_pk_y_odd then u8 0x03 else u8 0x02 in
  concat (create 1 pk0) pk_x
