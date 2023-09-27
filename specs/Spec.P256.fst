module Spec.P256

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Hash.Definitions
module M = Lib.NatMod
module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module PL = Spec.P256.Lemmas

include Spec.P256.PointOps

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let mk_p256_comm_monoid {| curve_params |} : LE.comm_monoid (aff_point) = {
  LE.one = aff_point_at_inf;
  LE.mul = aff_point_add;
  LE.lemma_one = PL.aff_point_at_inf_lemma;
  LE.lemma_mul_assoc = PL.aff_point_add_assoc_lemma;
  LE.lemma_mul_comm = PL.aff_point_add_comm_lemma;
}

let mk_to_p256_comm_monoid {| curve_params |} : SE.to_comm_monoid (proj_point) = {
  SE.a_spec = aff_point;
  SE.comm_monoid = mk_p256_comm_monoid;
  SE.refl = to_aff_point;
}

val point_at_inf_c {| curve_params |} : SE.one_st proj_point mk_to_p256_comm_monoid
let point_at_inf_c  #c _ =
  PL.to_aff_point_at_infinity_lemma #c;
  point_at_inf

val point_add_c {| curve_params |} : SE.mul_st proj_point mk_to_p256_comm_monoid
let point_add_c p q =
  PL.to_aff_point_add_lemma p q;
  point_add p q

val point_double_c {| curve_params |} : SE.sqr_st proj_point mk_to_p256_comm_monoid
let point_double_c p =
  PL.to_aff_point_double_lemma p;
  point_double p

let mk_p256_concrete_ops {| curve_params |} : SE.concrete_ops proj_point = {
  SE.to = mk_to_p256_comm_monoid;
  SE.one = point_at_inf_c;
  SE.mul = point_add_c;
  SE.sqr = point_double_c;
}

// [a]P
let point_mul {| c:curve_params |} (a:qelem) (p:proj_point) : proj_point =
  SE.exp_fw mk_p256_concrete_ops p c.bits a 4

// [a]G
let point_mul_g {| c:curve_params |} (a:qelem) : proj_point = point_mul a base_point

// [a1]G + [a2]P
let point_mul_double_g {| c:curve_params |} (a1 a2:qelem) (p:proj_point) : proj_point =
  SE.exp_double_fw mk_p256_concrete_ops base_point c.bits a1 p a2 5


///  ECDSA over the P256 elliptic curve

type hash_alg_ecdsa =
  | NoHash
  | Hash of (a:hash_alg{a == SHA2_256 \/ a == SHA2_384 \/ a == SHA2_512})

let _: squash (inversion hash_alg_ecdsa) = allow_inversion hash_alg_ecdsa

let _: squash (pow2 32 < pow2 61 /\ pow2 32 < pow2 125) =
  Math.Lemmas.pow2_lt_compat 61 32;
  Math.Lemmas.pow2_lt_compat 125 32

let min_input_length {| c:curve_params |} (a:hash_alg_ecdsa) (msg_len:size_nat) =
  match a with | NoHash -> msg_len >= c.bytes | Hash a -> hash_length a >= c.bytes
val hash_ecdsa:
    {| c:curve_params |}
  -> a:hash_alg_ecdsa
  -> msg_len:size_nat{min_input_length a msg_len}
  -> msg:lseq uint8 msg_len ->
  Tot (r:lbytes
    (if Hash? a then hash_length (match a with Hash a -> a) else msg_len){length r >= c.bytes})

let hash_ecdsa {| c:curve_params |} a msg_len msg =
  match a with | NoHash -> msg | Hash a -> Spec.Agile.Hash.hash a msg


let ecdsa_sign_msg_as_qelem {| c:curve_params |} (m:qelem) (private_key nonce:lbytes (c.bytes)) : option (lbytes (2*c.bytes)) =
  let k_q = nat_from_bytes_be nonce in
  let d_a = nat_from_bytes_be private_key in
  let is_privkey_valid = 0 < d_a && d_a < order in
  let is_nonce_valid = 0 < k_q && k_q < order in

  if not (is_privkey_valid && is_nonce_valid) then None
  else begin
    let _X, _Y, _Z = point_mul_g k_q in
    let x = _X /% _Z in
    let r = x % order in

    let kinv = qinv k_q in
    let s = kinv *^ (m +^ r *^ d_a) in
    
    FStar.Math.Lemmas.pow2_le_compat (8*c.bytes) c.bits;
    let rb = nat_to_bytes_be c.bytes r in
    let sb = nat_to_bytes_be c.bytes s in
    if r = 0 || s = 0 then None else Some (concat #_ #c.bytes #c.bytes rb sb) end


let ecdsa_verify_msg_as_qelem {| c:curve_params |} (m:qelem) (public_key:lbytes (2*c.bytes)) (sign_r sign_s:lbytes c.bytes) : bool =
  let pk = load_point public_key in
  let r = nat_from_bytes_be sign_r in
  let s = nat_from_bytes_be sign_s in
  let is_r_valid = 0 < r && r < order in
  let is_s_valid = 0 < s && s < order in

  if not (Some? pk && is_r_valid && is_s_valid) then false
  else begin
    let sinv = qinv s in
    let u1 = sinv *^ m in
    let u2 = sinv *^ r in
    let _X, _Y, _Z = point_mul_double_g u1 u2 (Some?.v pk) in
    if is_point_at_inf (_X, _Y, _Z) then false
    else begin
      let x = _X /% _Z in
      x % order = r end
  end

(*
   _Z <> 0
   q < prime < 2 * q
   let x = _X /% _Z in x % q = r <==>
   1. x = r <==> _X = r *% _Z
   2. x - q = r <==> _X = (r + q) *% _Z
*)


val ecdsa_signature_agile:
  {| c:curve_params |}
  -> alg:hash_alg_ecdsa
  -> msg_len:size_nat{min_input_length alg msg_len}
  -> msg:lbytes msg_len
  -> private_key:lbytes c.bytes
  -> nonce:lbytes c.bytes ->
  option (lbytes (2*c.bytes))

let ecdsa_signature_agile {| c:curve_params |} alg msg_len msg private_key nonce =
  let hashM = hash_ecdsa alg msg_len msg in
  let m_q = nat_from_bytes_be (sub hashM 0 c.bytes) % order in
  ecdsa_sign_msg_as_qelem m_q private_key nonce


val ecdsa_verification_agile:
  {| c:curve_params |}
  -> alg:hash_alg_ecdsa
  -> msg_len:size_nat{min_input_length alg msg_len}
  -> msg:lbytes msg_len
  -> public_key:lbytes (2*c.bytes)
  -> signature_r:lbytes c.bytes
  -> signature_s:lbytes c.bytes ->
  bool

let ecdsa_verification_agile #c alg msg_len msg public_key signature_r signature_s =
  let hashM = hash_ecdsa alg msg_len msg in
  let m_q = nat_from_bytes_be (sub hashM 0 c.bytes) % order in
  ecdsa_verify_msg_as_qelem m_q public_key signature_r signature_s


///  ECDH over the P256 elliptic curve

let secret_to_public {| c:curve_params |} (private_key:lbytes c.bytes) : option (lbytes (2*c.bytes)) =
  let sk = nat_from_bytes_be private_key in
  let is_sk_valid = 0 < sk && sk < order in
  if is_sk_valid then
    let pk = point_mul_g sk in
    Some (point_store pk)
  else None


let ecdh {| c:curve_params |} (their_public_key:lbytes (2*c.bytes)) (private_key:lbytes c.bytes) : option (lbytes (2*c.bytes)) =
  let pk = load_point their_public_key in
  let sk = nat_from_bytes_be private_key in
  let is_sk_valid = 0 < sk && sk < order in
  if Some? pk && is_sk_valid then
    let ss = point_mul sk (Some?.v pk) in
    Some (point_store ss)
  else None


///  Parsing and Serializing public keys

// raw          = [ x; y ], 64 bytes
// uncompressed = [ 0x04; x; y ], 65 bytes
// compressed   = [ 0x02 for even `y` and 0x03 for odd `y`; x ], 33 bytes

let validate_public_key {| c:curve_params |} (pk:lbytes (2*c.bytes)) : bool =
  Some? (load_point pk)

let pk_uncompressed_to_raw {| c:curve_params |} (pk:lbytes (2*c.bytes+1)) : option (lbytes (2*c.bytes)) =
  if Lib.RawIntTypes.u8_to_UInt8 pk.[0] <> 0x04uy then None else Some (sub pk 1 (2*c.bytes))

let pk_uncompressed_from_raw {| c:curve_params |} (pk:lbytes (2*c.bytes)) : lbytes (2*c.bytes+1) =
  concat (create 1 (u8 0x04)) pk

let pk_compressed_to_raw {| c:curve_params |} (pk:lbytes (c.bytes+1)) : option (lbytes (2*c.bytes)) =
  let pk_x = sub pk 1 c.bytes in
  FStar.Math.Lemmas.pow2_le_compat (8*c.bytes) c.bits;
  match (aff_point_decompress pk) with
  | Some (x, y) -> Some (concat #_ #c.bytes #c.bytes pk_x (nat_to_bytes_be c.bytes y))
  | None -> None

let pk_compressed_from_raw {| c:curve_params |} (pk:lbytes (2*c.bytes)) : lbytes (c.bytes+1) =
  let pk_x = sub pk 0 c.bytes in
  let pk_y = sub pk c.bytes c.bytes in
  let is_pk_y_odd = nat_from_bytes_be pk_y % 2 = 1 in // <==> pk_y % 2 = 1
  let pk0 = if is_pk_y_odd then u8 0x03 else u8 0x02 in
  concat (create 1 pk0) pk_x

///  P-256 Curve Parameters

let p256_bits = 256

let p256_bytes : (x:nat{8 * x >= p256_bits}) = 32

let p256_prime: (a:pos{a = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff /\ a < pow2 256}) =
  let p = pow2 256 - pow2 224 + pow2 192 + pow2 96 - 1 in
  assert_norm (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff = p);
  assert_norm (p < pow2 256); p

let p256_order: (a:pos{a < pow2 256}) =
  let o = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551 in
  assert_norm (o < pow2 256); o

let p256_a_coeff : (x:pos{x < p256_prime}) = (-3) % p256_prime
let p256_b_coeff : (x:pos{x < p256_prime}) =
  let b = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b in
  assert_norm (b < p256_prime); b

let p256_basepoint_x : (x:pos{x < p256_prime}) =
  let x = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296 in
  assert_norm (x < p256_prime); x
let p256_basepoint_y : (x:pos{x < p256_prime}) =
  let y = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5 in
  assert_norm (y < p256_prime); y

let p256_mont_mu: (x:uint64{(1 + p256_prime * v x) % pow2 64 == 0}) =
  assert_norm((1 + p256_prime) % pow2 64 == 0);
  u64 1

let p256_mont_q_mu: (x:uint64{(1 + p256_order * v x) % pow2 64 == 0}) =
  assert_norm((1 + p256_order * 0xccd1c8aaee00bc4f) % pow2 64 == 0);
  u64 0xccd1c8aaee00bc4f

let p256_bn_limbs: (x:size_t{v x = (p256_bytes + 7) / 8}) =
  assert_norm(4 == (p256_bytes + 7) / 8);
  size 4
  
(*
instance p256_params : curve_params = {
  bits = p256_bits;
  bytes = p256_bytes;
  prime = p256_prime;
  order = p256_order;
  basepoint_x = p256_basepoint_x;
  basepoint_y = p256_basepoint_y;
  a_coeff = p256_a_coeff;
  b_coeff = p256_b_coeff;
  mont_mu = p256_mont_mu;
  mont_q_mu = p256_mont_mu;
  bn_limbs = p256_bn_limbs
}
*)
