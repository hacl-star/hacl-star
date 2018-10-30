module Spec.ECIES

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence


module Hash = Spec.Hash



(* BB. TODO: Relocate this function *)
assume val crypto_random: len:size_nat -> Tot (lbytes len)


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
type key_public_s = lbytes vsize_key_asymmetric
type key_private_s = lbytes vsize_key_asymmetric
type key_s = lbytes vsize_key_asymmetric


(** Definition of a ECIES keypair *)
type keypair_r = (key_public_s & option key_private_s)


(** Generation of an EC public private keypair for Curve25519 *)
val secret_to_public: key_private_s -> Tot key_public_s
let secret_to_public kpriv =
  let basepoint_zeros = create vsize_key_asymmetric (u8 0) in
  let basepoint = upd basepoint_zeros (vsize_key_asymmetric - 1) (u8 0x09) in
  Spec.Curve25519.scalarmult kpriv basepoint


(** Generation of an EC public private keypair for Curve25519 *)
val generate: unit -> Tot keypair_r
let generate () =
  let basepoint_zeros = create vsize_key_asymmetric (u8 0) in
  let basepoint = upd basepoint_zeros (vsize_key_asymmetric - 1) (u8 0x09) in
  let kpriv = crypto_random vsize_key_asymmetric in
  let kpub = secret_to_public kpriv in
  kpub, Some kpriv



#set-options "--z3rlimit 25"

(** ECIES Encryption *)
val encrypt:
    a: Hash.algorithm
  -> receiver: key_public_s
  -> sender: key_private_s
  -> input: bytes{length input <= max_size_t /\ length input + Hash.size_block a <= max_size_t /\ length input + Spec.AES128_GCM.padlen (length input) <= max_size_t} ->
  Tot (lbytes (length input + Spec.AES128_GCM.size_block))

let encrypt a receiver sender input =
  let len = length input in
  let olen = length input + Spec.AES128_GCM.size_block in
  let ek: lbytes vsize_key_asymmetric = Spec.Curve25519.scalarmult receiver sender in
  let unsafe : bool = for_all (fun a -> uint_to_nat #U8 a = 0) ek in
  let kdf_iv_zeros = create vsize_key_asymmetric (u8 0) in
  // assert(vsize_key_asymmetric <= pow2 32 * pow2 3);
  assert_norm(pow2 32 * pow2 3 <= pow2 61 - 1);
  assert_norm(pow2 32 * pow2 3 <= pow2 125 - 1);
  // assert(vsize_key_asymmetric <= Hash.max_input a);
  let extracted = Spec.HKDF.hkdf_extract a kdf_iv_zeros ek in
  let iv = Spec.HKDF.hkdf_expand a extracted const_label_iv vsize_iv in
  let key = Spec.HKDF.hkdf_expand a extracted const_label_key vsize_key_symmetric in
  let out = Spec.AES128_GCM.aead_encrypt key iv input lbytes_empty in
  let zeros = create olen (u8 0) in
  if unsafe then zeros else out


(** ECIES Decryption *)
val decrypt:
    a: Hash.algorithm
  -> sender: key_public_s
  -> receiver: key_private_s
  -> input: bytes{Spec.AES128_GCM.size_block < length input /\ length input <= max_size_t} ->
  Tot (lbytes (length input - Spec.AES128_GCM.size_block))

let decrypt a sender receiver input =
  let len = length input in
  let olen = length input - Spec.AES128_GCM.size_block in
  let ek: lbytes vsize_key_asymmetric = Spec.Curve25519.scalarmult receiver sender in
  let unsafe = for_all (fun a -> uint_to_nat #U8 a = 0) ek in
  let kdf_iv_zeros = create vsize_key_asymmetric (u8 0) in
  let extracted = Spec.HKDF.hkdf_extract a kdf_iv_zeros ek in
  let iv = Spec.HKDF.hkdf_expand a extracted const_label_iv vsize_iv in
  let key = Spec.HKDF.hkdf_expand a extracted const_label_key vsize_key_symmetric in
  let out = Spec.AES128_GCM.aead_decrypt key iv input lbytes_empty in
  let zeros = create olen (u8 0) in
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
  -> receiver: key_public_s
  -> sender: key_private_s
  -> len: size_nat
  -> plaintext: lbytes len ->
  Tot (lbytes olen)

(** ECIES Decryption *)
assume val decrypt_counter:
    #olen: size_nat
  -> i: size_nat
  -> sender: key_public_s
  -> receiver: key_private_s
  -> len: size_nat
  -> ciphertext: lbytes len ->
  Tot (lbytes olen)
