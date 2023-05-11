module Spec.K256

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module EC = Spec.ECC
module EP = Spec.ECC.Projective

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

(**
 K256: https://en.bitcoin.it/wiki/Secp256k1
 ECDSA: https://en.bitcoin.it/wiki/Elliptic_Curve_Digital_Signature_Algorithm
 https://www.hyperelliptic.org/EFD/g1p/auto-shortw.html
*)

let prime : (p:pos{p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F}) =
  assert_norm (24 < pow2 256 - 0x1000003D1);
  assert_norm (pow2 256 - 0x1000003D1 = pow2 256 - pow2 32 - pow2 9 - pow2 8 - pow2 7 - pow2 6 - pow2 4 - 1);
  assert_norm (pow2 256 - 0x1000003D1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F);
  pow2 256 - 0x1000003D1

// Group order
let q : q:pos{q < pow2 256} =
  assert_norm (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 < pow2 256);
  0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141


let felem = x:nat{x < prime}
let a : felem = 0
let b : felem = 7

// Base point
let g_x : felem = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
let g_y : felem = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8

let base_point : x:EC.tuple2_lt_n prime{EC.tuple2_on_curve prime a b x} =
  let ( +% ) = Lib.NatMod.add_mod #prime in
  let ( *% ) = Lib.NatMod.mul_mod #prime in
  assert_norm (g_y *% g_y = g_x *% g_x *% g_x +% a *% g_x +% b);
  (g_x, g_y)


assume
val prime_lemma: unit -> Lemma (FStar.Math.Euclid.is_prime prime)

assume
val order_lemma: unit -> Lemma (FStar.Math.Euclid.is_prime q)

val weierstrass_curve: unit ->
  Lemma ((4 * a * a * a + 27 * b * b) % prime <> 0)

let weierstrass_curve () =
  assert_norm ((4 * a * a * a + 27 * b * b) % prime <> 0)


let k256: EC.curve = {
  EC.prime;
  EC.coeff_a = a;
  EC.coeff_b = b;

  EC.order = q;
  EC.base_point;

  EC.prime_len_bytes = 32;
  EC.order_len_bytes = 32;

  EC.weierstrass_curve;
  EC.prime_lemma;
  EC.order_lemma;
}

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
