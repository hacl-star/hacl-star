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
module EC = Spec.ECC

include Spec.P256.PointOps

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** https://eprint.iacr.org/2013/816.pdf *)

///  Elliptic curve scalar multiplication

let mk_to_p256_comm_monoid : SE.to_comm_monoid proj_point = {
  SE.a_spec = EC.aff_point p256;
  SE.comm_monoid = EC.mk_ec_comm_monoid p256;
  SE.refl = to_aff_point;
}

val point_at_inf_c: SE.one_st proj_point mk_to_p256_comm_monoid
let point_at_inf_c _ =
  PL.to_aff_point_at_infinity_lemma ();
  point_at_inf

val point_add_c : SE.mul_st proj_point mk_to_p256_comm_monoid
let point_add_c p q =
  PL.to_aff_point_add_lemma p q;
  point_add p q

val point_double_c : SE.sqr_st proj_point mk_to_p256_comm_monoid
let point_double_c p =
  PL.to_aff_point_double_lemma p;
  point_double p

let mk_p256_concrete_ops : SE.concrete_ops proj_point = {
  SE.to = mk_to_p256_comm_monoid;
  SE.one = point_at_inf_c;
  SE.mul = point_add_c;
  SE.sqr = point_double_c;
}

// [a]P
let point_mul (a:qelem) (p:proj_point)
  : res:proj_point{to_aff_point res == EC.aff_point_mul p256 a (to_aff_point p) }
 =
  SE.exp_fw_lemma mk_p256_concrete_ops p 256 a 4;
  LE.exp_fw_lemma (EC.mk_ec_comm_monoid p256) (to_aff_point p) 256 a 4;
  SE.exp_fw mk_p256_concrete_ops p 256 a 4


// [a1]G + [a2]P
let point_mul_double_g (a1 a2:qelem) (p:proj_point)
  : res:proj_point{to_aff_point res ==
      EC.aff_point_add p256
        (EC.aff_point_mul p256 a1 p256.base_point)
        (EC.aff_point_mul p256 a2 (to_aff_point p)) }
 =
  PL.lemma_proj_aff_id (g_x, g_y);
  SE.exp_double_fw_lemma mk_p256_concrete_ops (g_x, g_y, 1) 256 a1 p a2 5;
  LE.exp_double_fw_lemma (EC.mk_ec_comm_monoid p256) (g_x, g_y) 256 a1 (to_aff_point p) a2 5;
  SE.exp_double_fw mk_p256_concrete_ops (g_x, g_y, 1) 256 a1 p a2 5


let is_point_at_inf_c (p:proj_point)
  : res:bool{res ==> EC.is_aff_point_at_inf p256 (to_aff_point p)}
 =
  PL.lemma_aff_is_point_at_inf p;
  is_point_at_inf p


let p256_concrete_ops : EC.ec_concrete_ops = {
  EC.ec = p256;
  EC.t = proj_point;
  EC.to_point_t = to_proj_point;
  EC.to_aff_point = to_aff_point;
  EC.lemma_to_from_aff_point = PL.lemma_proj_aff_id;
  EC.is_point_at_inf = is_point_at_inf_c;
  EC.point_mul = point_mul;
  EC.point_mul_double_g = point_mul_double_g;
}


///  ECDSA over the P256 elliptic curve

type hash_alg_ecdsa =
  | NoHash
  | Hash of (a:hash_alg{a == SHA2_256 \/ a == SHA2_384 \/ a == SHA2_512})

let _: squash (inversion hash_alg_ecdsa) = allow_inversion hash_alg_ecdsa

let _: squash (pow2 32 < pow2 61 /\ pow2 32 < pow2 125) =
  Math.Lemmas.pow2_lt_compat 61 32;
  Math.Lemmas.pow2_lt_compat 125 32


let min_input_length (a:hash_alg_ecdsa) : nat =
  match a with | NoHash -> 32 | Hash a -> 0


val hash_ecdsa:
    a:hash_alg_ecdsa
  -> msg_len:size_nat{msg_len >= min_input_length a}
  -> msg:lseq uint8 msg_len ->
  Tot (r:lbytes
    (if Hash? a then hash_length (match a with Hash a -> a) else msg_len){length r >= 32})

let hash_ecdsa a msg_len msg =
  match a with | NoHash -> msg | Hash a -> Spec.Agile.Hash.hash a msg


val ecdsa_signature_agile:
    alg:hash_alg_ecdsa
  -> msg_len:size_nat{msg_len >= min_input_length alg}
  -> msg:lbytes msg_len
  -> private_key:lbytes 32
  -> nonce:lbytes 32 ->
  option (lbytes 64)

let ecdsa_signature_agile alg msg_len msg private_key nonce =
  let hashM = hash_ecdsa alg msg_len msg in
  let m_q = nat_from_bytes_be (sub hashM 0 32) % order in
  EC.ecdsa_sign_msg_as_qelem p256_concrete_ops m_q private_key nonce


val ecdsa_verification_agile:
    alg:hash_alg_ecdsa
  -> msg_len:size_nat{msg_len >= min_input_length alg}
  -> msg:lbytes msg_len
  -> public_key:lbytes 64
  -> signature_r:lbytes 32
  -> signature_s:lbytes 32 ->
  bool

let ecdsa_verification_agile alg msg_len msg public_key signature_r signature_s =
  let hashM = hash_ecdsa alg msg_len msg in
  let m_q = nat_from_bytes_be (sub hashM 0 32) % order in
  EC.ecdsa_verify_msg_as_qelem p256_concrete_ops m_q public_key signature_r signature_s

(** The following functions can be removed *)

///  ECDH over the P256 elliptic curve

let secret_to_public (private_key:lbytes 32) : option (lbytes 64) =
  EC.secret_to_public p256_concrete_ops private_key

let ecdh (their_public_key:lbytes 64) (private_key:lbytes 32) : option (lbytes 64) =
  EC.ecdh p256_concrete_ops their_public_key private_key


///  Parsing and Serializing public keys

// raw          = [ x; y ], 64 bytes
// uncompressed = [ 0x04; x; y ], 65 bytes
// compressed   = [ 0x02 for even `y` and 0x03 for odd `y`; x ], 33 bytes

let validate_public_key (pk:lbytes 64) : bool =
  EC.validate_public_key p256_concrete_ops pk

let pk_uncompressed_to_raw (pk:lbytes 65) : option (lbytes 64) =
  EC.pk_uncompressed_to_raw p256_concrete_ops pk

let pk_uncompressed_from_raw (pk:lbytes 64) : lbytes 65 =
  EC.pk_uncompressed_from_raw p256_concrete_ops pk

let pk_compressed_to_raw (pk:lbytes 33) : option (lbytes 64) =
  EC.pk_compressed_to_raw p256_concrete_ops pk

let pk_compressed_from_raw (pk:lbytes 64) : lbytes 33 =
  EC.pk_compressed_from_raw p256_concrete_ops pk
