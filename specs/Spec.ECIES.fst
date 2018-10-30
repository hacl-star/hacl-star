module Spec.ECIES

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence


module Hash = Spec.Hash



(* BB. TODO: Relocate this function *)
assume val crypto_random: len:size_nat -> Tot (lbytes len)

(* BB. TODO: Relocate this constant *)
let empty : lbytes 0 = create 0 (u8 0)



(** Constants for ECIES labels *)
let const_label_iv : lbytes 8 =
  [@inline_let]
  let l = [u8 0x65; u8 0x63; u8 0x69; u8 0x65; u8 0x73; u8 0x20; u8 0x69; u8 0x76] in
  assert_norm(List.Tot.length l == 8);
  createL l

let const_label_key : lbytes 9 =
  [@inline_let]
  let l = [u8 0x65; u8 0x63; u8 0x69; u8 0x65; u8 0x73; u8 0x20; u8 0x6b; u8 0x65; u8 0x79] in
  assert_norm(List.Tot.length l == 9);
  createL l


(** Definition of a ECIES IV *)
inline_for_extraction let vsize_iv: size_nat = 12 (* AES_GCM with TLS length IV *)


(** Definition of a ECIES keys *)
inline_for_extraction let vsize_key_symmetric: size_nat = 16
inline_for_extraction let vsize_key_asymmetric: size_nat = 32
type ecies_key_public_s = lbytes vsize_key_asymmetric
type ecies_key_private_s = lbytes vsize_key_asymmetric
type ecies_key_s = lbytes vsize_key_asymmetric


(** Definition of a ECIES keypair *)
type ecies_keypair_r = (ecies_key_public_s * option ecies_key_private_s)


(** Generation of an EC public private keypair for Curve25519 *)
val ecies_secret_to_public: ecies_key_private_s -> Tot ecies_key_public_s
let ecies_secret_to_public kpriv =
  let basepoint_zeros = create vsize_key_asymmetric (u8 0) in
  let basepoint = upd basepoint_zeros (vsize_key_asymmetric - 1) (u8 0x09) in
  Spec.Curve25519.scalarmult kpriv basepoint


(** Generation of an EC public private keypair for Curve25519 *)
val ecies_generate: unit -> Tot ecies_keypair_r
let ecies_generate () =
  let basepoint_zeros = create vsize_key_asymmetric (u8 0) in
  let basepoint = upd basepoint_zeros (vsize_key_asymmetric - 1) (u8 0x09) in
  let kpriv = crypto_random vsize_key_asymmetric in
  let kpub = ecies_secret_to_public kpriv in
  kpub, Some kpriv


(** ECIES Encryption *)
val encrypt:
    #olen: size_nat
  -> a: Hash.algorithm
  -> receiver: ecies_key_public_s
  -> sender: ecies_key_private_s
  -> input: bytes ->
  Tot (lbytes olen)

let encrypt #olen a receiver sender input =
  let len = length input in
  let ek: lbytes vsize_key_asymmetric = Spec.Curve25519.scalarmult receiver sender in
  let unsafe = for_all (fun a -> uint_to_nat #U8 a = 0) ek in
  let kdf_iv_zeros = create vsize_key_asymmetric (u8 0) in
  let extracted = Spec.HKDF.hkdf_extract a kdf_iv_zeros ek in
  let iv = Spec.HKDF.hkdf_expand a extracted const_ecies_label_iv vsize_iv in
  let key = Spec.HKDF.hkdf_expand a extracted const_ecies_label_key vsize_key_symmetric in
  let out = Spec.AESGCM.aead_encrypt key vsize_iv iv len input 0 empty in
  let zeros = create (len + vsize_iv) (u8 0) in
  if unsafe then zeros else out


(** ECIES Decryption *)
val decrypt:
    #olen: size_nat
  -> a: Hash.algorithm
  -> sender: ecies_key_public_s
  -> receiver: ecies_key_private_s
  -> input: bytes ->
  Tot (lbytes olen)

let decrypt #olen a sender receiver input =
  let len = length input in
  let ek: lbytes vsize_key_asymmetric = Spec.Curve25519.scalarmult receiver sender in
  let unsafe = for_all (fun a -> uint_to_nat #U8 a = 0) ek in
  let kdf_iv_zeros = create vsize_key_asymmetric (u8 0) in
  let extracted = Spec.HKDF.hkdf_extract a kdf_iv_zeros ek in
  let iv = Spec.HKDF.hkdf_expand a extracted const_ecies_label_iv vsize_iv in
  let key = Spec.HKDF.hkdf_expand a extracted const_ecies_label_key vsize_key_symmetric in
  let out = Spec.AESGCM.aead_decrypt key 12 iv len input 0 empty in
  let zeros = create (len + vsize_iv) (u8 0) in
  if unsafe then zeros else out


///
/// Alternative Design
/// ------------------
/// WIP: The motivation behind this alternative design is that
/// generating a nonce for each encryption is costly. I beleive
/// the call to HKDF can be used to derive an fresh nonce without
/// risking entropy exhaustion by seeding the HKDF call with a
/// counter. As for a nonce, the counter MUST not be reused.
/// My expectation is that construction is INT-CTXT IND-CPA secure
/// which remains to be proven correct.
///

(** ECIES Encryption *)
assume val encrypt_counter:
    #olen: size_nat
  -> i: size_nat
  -> receiver: ecies_key_public_s
  -> sender: ecies_key_private_s
  -> len: size_nat
  -> plaintext: lbytes len ->
  Tot (lbytes olen)

(** ECIES Decryption *)
assume val decrypt_counter:
    #olen: size_nat
  -> i: size_nat
  -> sender: ecies_key_public_s
  -> receiver: ecies_key_private_s
  -> len: size_nat
  -> ciphertext: lbytes len ->
  Tot (lbytes olen)
