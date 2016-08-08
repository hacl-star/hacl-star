module Hacl.Constants

open Platform.Bytes



(* Type for plaintext data and ciphertext *)
new type plaintext
new type ciphertext

(* Define hash algorithms *)
type hash_alg = 
  | SHA1 
  | SHA224 
  | SHA256 
  | SHA384 
  | SHA512

(* Define block cipher algorithms *)
type block_cipher = 
  | AES_128_CTR 
  | AES_256_CTR

(* Define AEAD cipher algorithms *)
type aead_cipher = 
  | AES_128_GCM 
  | AES_256_GCM
  | XSALSA20_POLY1305
  | SALSA20_POLY1305
  | CHACHA20_POLY1305

(* Define elliptic curves algorithms *)
type ec_curve =
  | ECC_P256
  | ECC_Curve25519
  | ECC_Ed448

(* Define elliptic cureve parameters *)
type ec_params = {
  curve: ec_curve;
  point_compression: bool;
}

(* Define an elliptic curve point *)
type ec_point = {
  ecx : bytes;
  ecy : bytes;
}

(* Define a SKE key *)
type key

(* Define a PKE key *)
type ec_key = {
  ec_params : ec_params;
  ec_point : ec_point;
  ec_priv : option bytes;
}

(* Functions returning key,iv and tag sizes for AEAD ciphers *)
let aeadKeySize = function
  | AES_128_GCM -> 16
  | AES_256_GCM -> 32

let aeadRealIVSize = function
  | AES_128_GCM -> 12
  | AES_256_GCM -> 12

let aeadTagSize = function
  | AES_128_GCM -> 16
  | AES_256_GCM -> 16
 
(* Function returning the length in bytes of a hash result *)
val hashSize: hash_alg -> Tot nat
let hashSize = function
  | SHA1 -> 20
  | SHA224 -> 28
  | SHA256 -> 32
  | SHA384 -> 48
  | SHA512 -> 64


(* Serializing and parsing functions for ec_point and ec_key *)
assume val serialize_ec_point: ec_point -> Tot bytes
assume val serialize_ec_key: ec_key -> Tot bytes
assume val parsing_ec_point: bytes -> Tot ec_point
assume val parsing_ec_key: bytes -> Tot ec_key
assume val ec_point_is_on_curve: ec_curve -> ec_point -> Tot bool
assume val ec_point_is_pkey_of_skey: ec_curve -> ec_key -> ec_point -> Tot bool
