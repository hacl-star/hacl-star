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

let mk_k256_comm_monoid : LE.comm_monoid aff_point = {
  LE.one = aff_point_at_inf;
  LE.mul = aff_point_add;
  LE.lemma_one = KL.aff_point_at_inf_lemma;
  LE.lemma_mul_assoc = KL.aff_point_add_assoc_lemma;
  LE.lemma_mul_comm = KL.aff_point_add_comm_lemma;
}

let mk_to_k256_comm_monoid : SE.to_comm_monoid proj_point = {
  SE.a_spec = aff_point;
  SE.comm_monoid = mk_k256_comm_monoid;
  SE.refl = to_aff_point;
}

val point_at_inf_c: SE.one_st proj_point mk_to_k256_comm_monoid
let point_at_inf_c _ =
  KL.to_aff_point_at_infinity_lemma ();
  point_at_inf

val point_add_c : SE.mul_st proj_point mk_to_k256_comm_monoid
let point_add_c p q =
  KL.to_aff_point_add_lemma p q;
  point_add p q

val point_double_c : SE.sqr_st proj_point mk_to_k256_comm_monoid
let point_double_c p =
  KL.to_aff_point_double_lemma p;
  point_double p

let mk_k256_concrete_ops : SE.concrete_ops proj_point = {
  SE.to = mk_to_k256_comm_monoid;
  SE.one = point_at_inf_c;
  SE.mul = point_add_c;
  SE.sqr = point_double_c;
}

// [a]P in affine coordinates
let aff_point_mul (a:nat) (p:aff_point) : aff_point =
  LE.pow mk_k256_comm_monoid p a

// [a1]P1 + [a2]P2
let aff_point_mul_double (a1:qelem) (p1:aff_point) (a2:qelem) (p2:aff_point) : aff_point =
  aff_point_add (aff_point_mul a1 p1) (aff_point_mul a2 p2)

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

let ecdsa_sign_hashed_msg (msgHash private_key nonce:lbytes 32) : option (lbytes 64) =
  let k_q = nat_from_bytes_be nonce in
  let d_a = nat_from_bytes_be private_key in
  let z = nat_from_bytes_be msgHash % q in

  let is_privkey_valid = 0 < d_a && d_a < q in
  let is_nonce_valid = 0 < k_q && k_q < q in

  if not (is_privkey_valid && is_nonce_valid) then None
  else begin
    let _X, _Y, _Z = point_mul_g k_q in
    let x = _X /% _Z in
    let r = x % q in

    let kinv = qinv k_q in
    let s = kinv *^ (z +^ r *^ d_a) in

    let rb = nat_to_bytes_be 32 r in
    let sb = nat_to_bytes_be 32 s in

    if r = 0 || s = 0 then None else Some (concat #_ #32 #32 rb sb) end


let load_public_key (pk:lbytes 64) : tuple3 nat nat bool =
  let pk_x = nat_from_bytes_be (sub pk 0 32) in
  let pk_y = nat_from_bytes_be (sub pk 32 32) in
  let is_x_valid = 0 < pk_x && pk_x < prime in
  let is_y_valid = 0 < pk_y && pk_y < prime in
  let is_xy_on_curve =
    if is_x_valid && is_y_valid then is_on_curve (pk_x, pk_y) else false in
  pk_x, pk_y, is_xy_on_curve


let ecdsa_verify_hashed_msg (msgHash:lbytes 32) (public_key signature:lbytes 64) : bool =
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
    let _X, _Y, _Z = point_mul_double_g u1 u2 (to_proj_point (pk_x, pk_y)) in

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

let _: squash(Spec.Hash.Definitions.max_input_length Spec.Hash.Definitions.SHA2_256 > pow2 32) =
 assert_norm (Spec.Hash.Definitions.max_input_length Spec.Hash.Definitions.SHA2_256 > pow2 32)


let ecdsa_sign_sha256 (msg_len:size_nat) (msg:lbytes msg_len) (private_key nonce:lbytes 32) : option (lbytes 64) =
  let msgHash = Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_256 msg in
  ecdsa_sign_hashed_msg msgHash private_key nonce


let ecdsa_verify_sha256 (msg_len:size_nat) (msg:lbytes msg_len) (public_key signature:lbytes 64) : bool =
  let msgHash = Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_256 msg in
  ecdsa_verify_hashed_msg msgHash public_key signature


///  Parsing and Serializing public keys

// raw          = [ x; y ], 64 bytes
// uncompressed = [ 0x04; x; y ], 65 bytes
// compressed   = [ 0x02 for even `y` and 0x03 for odd `y`; x ], 33 bytes

let pk_uncompressed_to_raw (pk:lbytes 65) : option (lbytes 64) =
  if Lib.RawIntTypes.u8_to_UInt8 pk.[0] <> 0x04uy then None else Some (sub pk 1 64)

let pk_uncompressed_from_raw (pk:lbytes 64) : lbytes 65 =
  concat (create 1 (u8 0x04)) pk

let pk_compressed_to_raw (pk:lbytes 33) : option (lbytes 64) =
  let pk_x = sub pk 1 32 in
  match (aff_point_decompress pk) with
  | Some (x, y) -> Some (concat #_ #32 #32 pk_x (nat_to_bytes_be 32 y))
  | None -> None


let pk_compressed_from_raw (pk:lbytes 64) : lbytes 33 =
  let pk_x = sub pk 0 32 in
  let pk_y = sub pk 32 32 in
  let is_pk_y_odd = nat_from_bytes_be pk_y % 2 = 1 in // <==> pk_y % 2 = 1
  let pk0 = if is_pk_y_odd then u8 0x03 else u8 0x02 in
  concat (create 1 pk0) pk_x


///  Low-S normalization

(**
   https://en.bitcoin.it/wiki/BIP_0062
   https://yondon.blog/2019/01/01/how-not-to-use-ecdsa/
   https://eklitzke.org/bitcoin-transaction-malleability
*)

// The value S in signatures must be between 0x1 and q / 2 (inclusive).
// If S is too high, simply replace it by S' = q - S.
let secp256k1_ecdsa_signature_normalize (signature:lbytes 64) : option (lbytes 64) =
  let sn = nat_from_bytes_be (sub signature 32 32) in
  let is_sn_valid = 0 < sn && sn < q in

  if is_sn_valid then begin
    let sn = if sn <= q / 2 then sn else (q - sn) % q in
    let sgnt = update_sub signature 32 32 (nat_to_bytes_be 32 sn) in
    Some sgnt end
  else None


let secp256k1_ecdsa_is_signature_normalized (signature:lbytes 64) : bool =
  let sn = nat_from_bytes_be (sub signature 32 32) in
  0 < sn && sn <= q / 2


let secp256k1_ecdsa_sign_hashed_msg (msgHash private_key nonce:lbytes 32) : option (lbytes 64) =
  let signature = ecdsa_sign_hashed_msg msgHash private_key nonce in
  match signature with
  | Some x -> secp256k1_ecdsa_signature_normalize x
  | None -> None


let secp256k1_ecdsa_sign_sha256 (msg_len:size_nat) (msg:lbytes msg_len) (private_key nonce:lbytes 32) : option (lbytes 64) =
  let msgHash = Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_256 msg in
  secp256k1_ecdsa_sign_hashed_msg msgHash private_key nonce


let secp256k1_ecdsa_verify_hashed_msg (msgHash:lbytes 32) (public_key signature:lbytes 64) : bool =
  if not (secp256k1_ecdsa_is_signature_normalized signature) then false
  else ecdsa_verify_hashed_msg msgHash public_key signature


let secp256k1_ecdsa_verify_sha256 (msg_len:size_nat) (msg:lbytes msg_len) (public_key signature:lbytes 64) : bool =
  let msgHash = Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_256 msg in
  secp256k1_ecdsa_verify_hashed_msg msgHash public_key signature
