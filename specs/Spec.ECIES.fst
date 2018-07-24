module Spec.ECIES

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


assume val crypto_random: len:size_nat -> Tot (lbytes len)


(** Definition of a ECKEM IV *)
inline_for_extraction
let vsize_eckem_iv: size_nat = 12
type eckem_iv_s = lbytes vsize_eckem_iv


(** Definition of a ECKEM keys *)
inline_for_extraction let vsize_eckem_key_asymmetric: size_nat = 32
type eckem_key_public_s = lbytes vsize_eckem_key_asymmetric
type eckem_key_private_s = lbytes vsize_eckem_key_asymmetric


(** Definition of a ECKEM keypair *)
type eckem_keypair_r = (eckem_key_public_s * option eckem_key_private_s)


(** Definition of a ECKEM Ciphertext *)
noeq type eckem_ciphertext_r (len:size_nat) = {
  eckem_ciphertext: lbytes len;
  eckem_key_public: lbytes 32;
  eckem_iv: eckem_iv_s;
}

(** Generation of an EC public private keypair for Curve25519 *)
val eckem_generate: unit -> Tot eckem_keypair_r
let eckem_generate () =
  let basepoint_zeros = create 32 (u8 0) in
  let basepoint = upd basepoint_zeros 31 (u8 0x09) in
  let kpriv = crypto_random vsize_eckem_key_asymmetric in
  let kpub = Spec.Curve25519.scalarmult kpriv basepoint in
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
  let iv = crypto_random vsize_eckem_iv in
  let ek: lbytes 32 = Spec.Curve25519.scalarmult receiver sender in
  let key = Spec.HKDF.hkdf_extract Spec.Hash.SHA2_256 vsize_eckem_iv iv 32 ek in
  let key = sub ek 0 Spec.AESGCM.keylen in
  let c = Spec.AESGCM.aead_encrypt key 12 iv len input 0 empty in
  let out = create (len + vsize_eckem_iv) (u8 0) in
  let out = update_sub out 0 vsize_eckem_iv iv in
  let out = update_sub out vsize_eckem_iv len c in
  out


(** ECKEM Decryption *)
val decrypt:
    #olen: size_nat
  -> sender: eckem_key_public_s
  -> receiver: eckem_key_private_s
  -> len: size_nat
  -> input: lbytes len ->
  Tot (lbytes olen)

let decrypt #olen sender receiver len input =
  let iv = sub input 0 vsize_eckem_iv in
  let ek: lbytes 32 = Spec.Curve25519.scalarmult sender receiver in
  let key = Spec.HKDF.hkdf_extract Spec.Hash.SHA2_256 vsize_eckem_iv iv 32 ek in
  let key = sub ek 0 Spec.AESGCM.keylen in
  let ciphertext = sub input vsize_eckem_iv (len - vsize_eckem_iv) in
  let p = Spec.AESGCM.aead_decrypt key 12 iv len ciphertext 0 empty in
  p


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
  -> plaintext: lbytes len ->
  Tot (lbytes olen)

let encrypt_explicit_iv #olen iv receiver sender len plaintext =
  let ek: lbytes 32 = Spec.Curve25519.scalarmult receiver sender in
  let key = Spec.HKDF.hkdf_extract Spec.Hash.SHA2_256 vsize_eckem_iv iv 32 ek in
  let key = sub ek 0 Spec.AESGCM.keylen in
  let c = Spec.AESGCM.aead_encrypt key 12 iv len plaintext 0 empty in
  c


(** ECKEM Decryption *)
val decrypt_explicit_iv:
    #olen: size_nat
  -> iv: eckem_iv_s
  -> sender: eckem_key_public_s
  -> receiver: eckem_key_private_s
  -> len: size_nat
  -> ciphertext: lbytes len ->
  Tot (lbytes olen)

let decrypt_explicit_iv #olen iv sender receiver len ciphertext =
  let ek: lbytes 32 = Spec.Curve25519.scalarmult sender receiver in
  let key = Spec.HKDF.hkdf_extract Spec.Hash.SHA2_256 vsize_eckem_iv iv 32 ek in
  let key = sub ek 0 Spec.AESGCM.keylen in
  let p = Spec.AESGCM.aead_decrypt key 12 iv len ciphertext 0 empty in
  p
