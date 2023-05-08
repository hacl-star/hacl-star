module Spec.K256

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module EC = Spec.ECC
module EP = Spec.ECC.Projective

include Spec.K256.PointOps

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

(**
 K256: https://en.bitcoin.it/wiki/Secp256k1
 ECDSA: https://en.bitcoin.it/wiki/Elliptic_Curve_Digital_Signature_Algorithm
 https://www.hyperelliptic.org/EFD/g1p/auto-shortw.html
*)

let k256_concrete_ops : EC.ec_concrete_ops =
  EP.ec_concrete_ops_proj k256

///  ECDSA with a prehashed message

let ecdsa_sign_hashed_msg (msgHash private_key nonce:lbytes 32) : option (lbytes 64) =
  let z = nat_from_bytes_be msgHash % q in
  EC.ecdsa_sign_msg_as_qelem k256_concrete_ops z private_key nonce


let ecdsa_verify_hashed_msg (msgHash:lbytes 32) (public_key signature:lbytes 64) : bool =
  let z = nat_from_bytes_be msgHash % q in
  let signature_r = sub signature 0 32 in
  let signature_s = sub signature 32 32 in
  EC.ecdsa_verify_msg_as_qelem k256_concrete_ops z public_key signature_r signature_s


///  ECDSA using SHA2-256

let _: squash(Some?.v (Spec.Hash.Definitions.max_input_length Spec.Hash.Definitions.SHA2_256) > pow2 32) =
 assert_norm (Some?.v (Spec.Hash.Definitions.max_input_length Spec.Hash.Definitions.SHA2_256) > pow2 32)


let ecdsa_sign_sha256 (msg_len:size_nat) (msg:lbytes msg_len) (private_key nonce:lbytes 32) : option (lbytes 64) =
  let msgHash = Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_256 msg in
  ecdsa_sign_hashed_msg msgHash private_key nonce


let ecdsa_verify_sha256 (msg_len:size_nat) (msg:lbytes msg_len) (public_key signature:lbytes 64) : bool =
  let msgHash = Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_256 msg in
  ecdsa_verify_hashed_msg msgHash public_key signature


///  ECDH over the secp256k1 elliptic curve

let secret_to_public (private_key:lbytes 32) : option (lbytes 64) =
  EC.secret_to_public k256_concrete_ops private_key

let ecdh (their_public_key:lbytes 64) (private_key:lbytes 32) : option (lbytes 64) =
  EC.ecdh k256_concrete_ops their_public_key private_key

///  Parsing and Serializing public keys

// raw          = [ x; y ], 64 bytes
// uncompressed = [ 0x04; x; y ], 65 bytes
// compressed   = [ 0x02 for even `y` and 0x03 for odd `y`; x ], 33 bytes

let validate_public_key (pk:lbytes 64) : bool =
  EC.validate_public_key k256_concrete_ops pk

let pk_uncompressed_to_raw (pk:lbytes 65) : option (lbytes 64) =
  EC.pk_uncompressed_to_raw k256_concrete_ops pk

let pk_uncompressed_from_raw (pk:lbytes 64) : lbytes 65 =
  EC.pk_uncompressed_from_raw k256_concrete_ops pk

let pk_compressed_to_raw (pk:lbytes 33) : option (lbytes 64) =
  EC.pk_compressed_to_raw k256_concrete_ops pk

let pk_compressed_from_raw (pk:lbytes 64) : lbytes 33 =
  EC.pk_compressed_from_raw k256_concrete_ops pk


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
