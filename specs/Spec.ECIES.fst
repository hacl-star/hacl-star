module Spec.ECIES

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence


assume val crypto_random: len:size_nat -> Tot (lbytes len)


(** Definition of a ECKEM IV *)
inline_for_extraction
let vsize_eckem_iv: size_nat = 12
type eckem_iv_s = lbytes vsize_eckem_iv

(** Definition of a ECKEM counter *)
type eckem_counter_t = uint32

(** Definition of a ECKEM keys *)
inline_for_extraction let vsize_eckem_key_asymmetric: size_nat = 32
type eckem_key_public_s = lbytes vsize_eckem_key_asymmetric
type eckem_key_private_s = lbytes vsize_eckem_key_asymmetric


(** Definition of a ECKEM keypair *)
type eckem_keypair_r = (eckem_key_public_s * option eckem_key_private_s)


(** Generation of an EC public private keypair for Curve25519 *)
val eckem_secret_to_public: eckem_key_private_s -> Tot eckem_key_public_s
let eckem_secret_to_public kpriv =
  let basepoint_zeros = create 32 (u8 0) in
  let basepoint = upd basepoint_zeros 31 (u8 0x09) in
  Spec.Curve25519.scalarmult kpriv basepoint


(** Generation of an EC public private keypair for Curve25519 *)
val eckem_generate: unit -> Tot eckem_keypair_r
let eckem_generate () =
  let basepoint_zeros = create 32 (u8 0) in
  let basepoint = upd basepoint_zeros 31 (u8 0x09) in
  let kpriv = crypto_random vsize_eckem_key_asymmetric in
  let kpub = eckem_secret_to_public kpriv in
  kpub, Some kpriv


(** ECKEM Encryption *)
val encrypt:
    #olen: size_nat
  -> receiver: eckem_key_public_s
  -> sender: eckem_key_private_s
  -> len: size_nat
  -> input: lbytes len ->
  Tot (lbytes olen)

let encrypt #olen receiver sender len input =
  let kdf_iv = crypto_random vsize_eckem_iv in
  let ek: lbytes 32 = Spec.Curve25519.scalarmult receiver sender in
  let safe = for_all (fun a -> uint_to_nat #U8 a = 0) ek in
  let stream = Spec.HKDF.hkdf_extract Spec.Hash.SHA2_256 vsize_eckem_iv kdf_iv 32 ek in
  let key = sub stream 0 Spec.AESGCM.keylen in
  let iv = sub stream Spec.AESGCM.keylen 12 in
  let c = Spec.AESGCM.aead_encrypt key 12 iv len input 0 empty in
  let zeros = create (len + vsize_eckem_iv) (u8 0) in
  let out = create (len + vsize_eckem_iv) (u8 0) in
  let out = update_sub out 0 vsize_eckem_iv iv in
  let out = update_sub out vsize_eckem_iv len c in
  if safe then out else zeros


(** ECKEM Decryption *)
val decrypt:
    #olen: size_nat
  -> sender: eckem_key_public_s
  -> receiver: eckem_key_private_s
  -> len: size_nat
  -> input: lbytes len ->
  Tot (lbytes olen)

let decrypt #olen sender receiver len input =
  let kdf_iv = sub input 0 vsize_eckem_iv in
  let ek: lbytes 32 = Spec.Curve25519.scalarmult sender receiver in
  let safe = for_all (fun a -> uint_to_nat #U8 a = 0) ek in
  let stream = Spec.HKDF.hkdf_extract Spec.Hash.SHA2_256 vsize_eckem_iv kdf_iv 32 ek in
  let key = sub stream 0 Spec.AESGCM.keylen in
  let iv = sub stream Spec.AESGCM.keylen 12 in
  let ciphertext = sub input vsize_eckem_iv (len - vsize_eckem_iv) in
  let out = Spec.AESGCM.aead_decrypt key 12 iv len ciphertext 0 empty in
  let zeros = create (len + vsize_eckem_iv) (u8 0) in
  if safe then out else zeros


///
/// Alternative API
///


(** ECKEM Encryption *)
val encrypt_explicit_iv:
    #olen: size_nat
  -> iv: eckem_iv_s
  -> receiver: eckem_key_public_s
  -> sender: eckem_key_private_s
  -> len: size_nat
  -> input: lbytes len ->
  Tot (lbytes olen)

let encrypt_explicit_iv #olen kdf_iv receiver sender len input =
  let ek: lbytes 32 = Spec.Curve25519.scalarmult receiver sender in
  let safe = for_all (fun a -> uint_to_nat #U8 a = 0) ek in
  let stream = Spec.HKDF.hkdf_extract Spec.Hash.SHA2_256 vsize_eckem_iv kdf_iv 32 ek in
  let key = sub stream 0 Spec.AESGCM.keylen in
  let iv = sub stream Spec.AESGCM.keylen 12 in
  let c = Spec.AESGCM.aead_encrypt key 12 iv len input 0 empty in
  let zeros = create (len + vsize_eckem_iv) (u8 0) in
  let out = create (len + vsize_eckem_iv) (u8 0) in
  let out = update_sub out 0 vsize_eckem_iv iv in
  let out = update_sub out vsize_eckem_iv len c in
  if safe then out else zeros


(** ECKEM Decryption *)
val decrypt_explicit_iv:
    #olen: size_nat
  -> iv: eckem_iv_s
  -> sender: eckem_key_public_s
  -> receiver: eckem_key_private_s
  -> len: size_nat
  -> input: lbytes len ->
  Tot (lbytes olen)

let decrypt_explicit_iv #olen iv sender receiver len input =
  let kdf_iv = sub input 0 vsize_eckem_iv in
  let ek: lbytes 32 = Spec.Curve25519.scalarmult sender receiver in
  let safe = for_all (fun a -> uint_to_nat #U8 a = 0) ek in
  let stream = Spec.HKDF.hkdf_extract Spec.Hash.SHA2_256 vsize_eckem_iv kdf_iv 32 ek in
  let key = sub stream 0 Spec.AESGCM.keylen in
  let iv = sub stream Spec.AESGCM.keylen 12 in
  let encrypted_plaintext = sub input vsize_eckem_iv (len - vsize_eckem_iv) in
  let out = Spec.AESGCM.aead_decrypt key 12 iv len input 0 empty in
  let zeros = create (len + vsize_eckem_iv) (u8 0) in
  if safe then out else zeros


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

(** ECKEM Encryption *)
assume val encrypt_counter:
    #olen: size_nat
  -> i: eckem_counter_t
  -> receiver: eckem_key_public_s
  -> sender: eckem_key_private_s
  -> len: size_nat
  -> plaintext: lbytes len ->
  Tot (lbytes olen)

(** ECKEM Decryption *)
assume val decrypt_counter:
    #olen: size_nat
  -> i: eckem_counter_t
  -> sender: eckem_key_public_s
  -> receiver: eckem_key_private_s
  -> len: size_nat
  -> ciphertext: lbytes len ->
  Tot (lbytes olen)
