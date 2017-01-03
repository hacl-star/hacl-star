module Hacl.Constants

(* Type abbreviations *)
type u8  = FStar.UInt8.t
type u32 = FStar.UInt32.t
type u64 = FStar.UInt64.t

type h8  = Hacl.UInt8.t
type h32  = Hacl.UInt32.t
type h64  = Hacl.UInt64.t

type uint8_p = FStar.Buffer.buffer h8

(* Size constants (for specifications) *)
let crypto_box_NONCEBYTES     = 24
let crypto_box_PUBLICKEYBYTES = 32
let crypto_box_SECRETKEYBYTES = 32
let crypto_box_MACBYTES       = 16

let crypto_secretbox_NONCEBYTES = 24
let crypto_secretbox_KEYBYTES   = 32
let crypto_secretbox_MACBYTES   = 16

(* (\* Define hash algorithms *\) *)
(* type hash_alg =  *)
(*   | SHA1  *)
(*   | SHA224  *)
(*   | SHA256  *)
(*   | SHA384  *)
(*   | SHA512 *)

(* (\* Define block cipher algorithms *\) *)
(* type block_cipher =  *)
(*   | AES_128_CTR  *)
(*   | AES_256_CTR *)

(* (\* Define AEAD cipher algorithms *\) *)
(* type aead_cipher =  *)
(*   | AES_128_GCM  *)
(*   | AES_256_GCM *)
(*   | XSALSA20_POLY1305 *)
(*   | SALSA20_POLY1305 *)
(*   | CHACHA20_POLY1305 *)

(* (\* Define elliptic curves algorithms *\) *)
(* type ec_curve = *)
(*   | ECC_P256 *)
(*   | ECC_Curve25519 *)
(*   | ECC_Ed448 *)

(* (\* Define elliptic cureve parameters *\) *)
(* type ec_params = { *)
(*   curve: ec_curve; *)
(*   point_compression: bool; *)
(* } *)

(* (\* Define an elliptic curve point *\) *)
(* noeq type ec_point = { *)
(*   ecx : uint8_p; *)
(*   ecy : uint8_p; *)
(* } *)

(* (\* Define a SKE key *\) *)
(* type key *)

(* (\* Define a PKE key *\) *)
(* type ec_key = { *)
(*   ec_params : ec_params; *)
(*   ec_point : ec_point; *)
(*   ec_priv : option uint8_p; *)
(* } *)

(* (\* Functions returning key,iv and tag sizes for AEAD ciphers *\) *)
(* let aeadKeySize = function *)
(*   | AES_128_GCM -> 16ul *)
(*   | AES_256_GCM -> 32ul *)

(* let aeadRealIVSize = function *)
(*   | AES_128_GCM -> 12ul *)
(*   | AES_256_GCM -> 12ul *)

(* let aeadTagSize = function *)
(*   | AES_128_GCM -> 16ul *)
(*   | AES_256_GCM -> 16ul *)
 
(* (\* Function returning the length in bytes of a hash result *\) *)
(* val hashSize: hash_alg -> Tot FStar.UInt32.t *)
(* let hashSize = function *)
(*   | SHA1 -> 20ul *)
(*   | SHA224 -> 28ul *)
(*   | SHA256 -> 32ul *)
(*   | SHA384 -> 48ul *)
(*   | SHA512 -> 64ul *)


(* (\* Serializing and parsing functions for ec_point and ec_key *\) *)
(* assume val serialize_ec_point: ec_point -> Tot uint8_p *)
(* assume val serialize_ec_key: ec_key -> Tot uint8_p *)
(* assume val parsing_ec_point: uint8_p -> Tot ec_point *)
(* assume val parsing_ec_key: uint8_p -> Tot ec_key *)
(* assume val ec_point_is_on_curve: ec_curve -> ec_point -> Tot bool *)
(* assume val ec_point_is_pkey_of_skey: ec_curve -> ec_key -> ec_point -> Tot bool *)
