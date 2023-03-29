module Spec.P256

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Hash.Definitions
module M = Lib.NatMod

include Spec.P256.PointOps

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** https://eprint.iacr.org/2013/816.pdf *)

///  Elliptic curve scalar multiplication
// TODO: use Lib.Exponentiation

let scalar = lbytes 32

let ith_bit (k:scalar) (i:nat{i < 256}) : uint64 =
  let q = 31 - i / 8 in let r = size (i % 8) in
  to_u64 ((index k q >>. r) &. u8 1)


val _ml_step0: p:proj_point -> q:proj_point -> tuple2 proj_point proj_point
let _ml_step0 r0 r1 =
  let r0 = point_add r1 r0 in
  let r1 = point_double r1 in
  (r0, r1)


val _ml_step1: p: proj_point -> q:proj_point -> tuple2 proj_point proj_point
let _ml_step1 r0 r1 =
  let r1 = point_add r0 r1 in
  let r0 = point_double r0 in
  (r0, r1)


val _ml_step: k:scalar -> i:nat{i < 256} -> tuple2 proj_point proj_point -> tuple2 proj_point proj_point
let _ml_step k i (p, q) =
  let bit = 255 - i in
  let bit = ith_bit k bit in
  let open Lib.RawIntTypes in
  if uint_to_nat bit = 0 then
    _ml_step1 p q
  else
    _ml_step0 p q


val montgomery_ladder_spec: k:scalar -> tuple2 proj_point proj_point -> tuple2 proj_point proj_point
let montgomery_ladder_spec k pq =
  Lib.LoopCombinators.repeati 256 (_ml_step k) pq

//---------------------------

// TODO: some functions don't check for `a < order`
let lbytes_as_nat = x:nat{x < pow2 256}

// [a]P
let point_mul (a:lbytes_as_nat) (p:proj_point) : proj_point =
  let a = nat_to_bytes_be 32 a in
  let q, f = montgomery_ladder_spec a (point_at_inf, p) in
  q

// [a]G
let point_mul_g (a:lbytes_as_nat) : proj_point = point_mul a base_point


// [a1]G + [a2]P
let point_mul_double_g (a1 a2:lbytes_as_nat) (p:proj_point) : proj_point =
  point_add (point_mul_g a1) (point_mul a2 p)


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


let ecdsa_sign_msg_as_qelem (m:qelem) (private_key nonce:lbytes 32) : option (lbytes 64) =
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
    let rb = nat_to_bytes_be 32 r in
    let sb = nat_to_bytes_be 32 s in
    if r = 0 || s = 0 then None else Some (concat #_ #32 #32 rb sb) end


let ecdsa_verify_msg_as_qelem (m:qelem) (public_key:lbytes 64) (sign_r sign_s:lbytes 32) : bool =
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
    alg:hash_alg_ecdsa
  -> msg_len:size_nat{msg_len >= min_input_length alg}
  -> msg:lbytes msg_len
  -> private_key:lbytes 32
  -> nonce:lbytes 32 ->
  option (lbytes 64)

let ecdsa_signature_agile alg msg_len msg private_key nonce =
  let hashM = hash_ecdsa alg msg_len msg in
  let m_q = nat_from_bytes_be (sub hashM 0 32) % order in
  ecdsa_sign_msg_as_qelem m_q private_key nonce


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
  ecdsa_verify_msg_as_qelem m_q public_key signature_r signature_s


///  ECDH over the P256 elliptic curve

// Initiator
let ecp256_dh_i (private_key:lbytes 32) : tuple2 (lbytes 64) bool =
  let sk = nat_from_bytes_be private_key in
  let pk = point_mul_g sk in
  point_store pk, not (is_point_at_inf pk)


// Responder
let ecp256_dh_r (their_public_key:lbytes 64) (private_key:lbytes 32) : tuple2 (lbytes 64) bool =
  let pk = load_point their_public_key in
  let sk = nat_from_bytes_be private_key in
  if Some? pk then
    let ss = point_mul sk (Some?.v pk) in
    point_store ss, not (is_point_at_inf ss)
  else
    aff_point_store aff_point_at_inf, false


///  Parsing and Serializing public keys

// raw          = [ x; y ], 64 bytes
// uncompressed = [ 0x04; x; y ], 65 bytes
// compressed   = [ 0x02 for even `y` and 0x03 for odd `y`; x ], 33 bytes

let validate_public_key (pk:lbytes 64) : bool =
  Some? (load_point pk)

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
