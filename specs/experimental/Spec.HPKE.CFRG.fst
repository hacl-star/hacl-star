module Spec.HPKE.CFRG

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.RandomSequence

module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD.Hacl
module Hash = Spec.Agile.Hash
module HKDF = Spec.Agile.HKDF
module KDF = Spec.Agile.KDF


let pow2_61 : _:unit{pow2 61 == 2305843009213693952} = assert_norm(pow2 61 == 2305843009213693952)
let pow2_35_less_than_pow2_61 : _:unit{pow2 32 * pow2 3 <= pow2 61 - 1} = assert_norm(pow2 32 * pow2 3 <= pow2 61 - 1)
let pow2_35_less_than_pow2_125 : _:unit{pow2 32 * pow2 3 <= pow2 125 - 1} = assert_norm(pow2 32 * pow2 3 <= pow2 125 - 1)

#set-options "--z3rlimit 200"

/// Types

let is_ciphersuite = function
  | DH.DH_Curve25519, AEAD.AEAD_AES128_GCM,        Hash.SHA2_256
  | DH.DH_Curve25519, AEAD.AEAD_Chacha20_Poly1305, Hash.SHA2_256
  | DH.DH_Curve448,   AEAD.AEAD_AES256_GCM,        Hash.SHA2_512
  | DH.DH_Curve448,   AEAD.AEAD_Chacha20_Poly1305, Hash.SHA2_512
  | DH.DH_P256,       AEAD.AEAD_AES128_GCM,        Hash.SHA2_256
  | DH.DH_P256,       AEAD.AEAD_Chacha20_Poly1305, Hash.SHA2_256 -> true
  | _,_,_ -> false

type ciphersuite = cs:(DH.algorithm & AEAD.algorithm & Hash.algorithm){is_ciphersuite cs}


inline_for_extraction
let size_cs_identifier: size_nat = 1


val id_of_cs: cs:ciphersuite -> Tot (lbytes size_cs_identifier)
let id_of_cs cs =
  match cs with
  | DH.DH_Curve25519, AEAD.AEAD_AES128_GCM,        Hash.SHA2_256 -> create 1 (u8 1)
  | DH.DH_Curve25519, AEAD.AEAD_Chacha20_Poly1305, Hash.SHA2_256 -> create 1 (u8 2)
  | DH.DH_Curve448,   AEAD.AEAD_AES256_GCM,        Hash.SHA2_512 -> create 1 (u8 3)
  | DH.DH_Curve448,   AEAD.AEAD_Chacha20_Poly1305, Hash.SHA2_512 -> create 1 (u8 4)
  | DH.DH_P256,       AEAD.AEAD_AES128_GCM,        Hash.SHA2_256 -> create 1 (u8 5)
  | DH.DH_P256,       AEAD.AEAD_Chacha20_Poly1305, Hash.SHA2_256 -> create 1 (u8 6)


let curve_of_cs (cs:ciphersuite) : DH.algorithm =
  let (c,a,h) = cs in c

let aead_of_cs (cs:ciphersuite) : AEAD.algorithm =
  let (c,a,h) = cs in a

let hash_of_cs (cs:ciphersuite) : Hash.algorithm =
  let (c,a,h) = cs in h


/// Constants

inline_for_extraction
let size_label_nonce: size_nat = 10

inline_for_extraction
let size_label_key: size_nat = 8

(** Constants for HPKE labels *)
let label_nonce_list : l:list uint8{List.Tot.length l == size_label_nonce} =
  [@inline_let]
  let l = [u8 0x68; u8 0x70; u8 0x6b; u8 0x65; u8 0x20; u8 0x6e; u8 0x6f; u8 0x6e; u8 0x63; u8 0x65] in
  assert_norm(List.Tot.length l == size_label_nonce);
  l

let label_key_list : l:list uint8{List.Tot.length l == size_label_key} =
  [@inline_let]
  let l = [u8 0x68; u8 0x70; u8 0x6b; u8 0x65; u8 0x20; u8 0x6b; u8 0x65; u8 0x79] in
  assert_norm(List.Tot.length l == size_label_key);
  l


let label_nonce : lbytes size_label_nonce = createL label_nonce_list
let label_key : lbytes size_label_key = createL label_key_list



/// Constants sizes

inline_for_extraction
let size_aead_nonce (cs:ciphersuite): size_nat = AEAD.size_nonce (aead_of_cs cs)

inline_for_extraction
let size_aead_key (cs:ciphersuite): size_nat = AEAD.size_key (aead_of_cs cs)

inline_for_extraction
let size_dh_key (cs:ciphersuite): size_nat = DH.size_key (curve_of_cs cs)

inline_for_extraction
let size_dh_public (cs:ciphersuite): size_nat = DH.size_public (curve_of_cs cs)

inline_for_extraction
let size_einfo: size_nat = 32

inline_for_extraction
let size_context (cs:ciphersuite): size_nat =
  size_cs_identifier + 2 * size_dh_public cs + size_einfo

/// Types

type key_dh_public_s (cs:ciphersuite) = lbytes (size_dh_public cs)
type key_dh_secret_s (cs:ciphersuite) = lbytes (size_dh_key cs)
type key_aead_s (cs:ciphersuite) = lbytes (size_aead_key cs)
type nonce_aead_s (cs:ciphersuite) = lbytes (size_aead_nonce cs)



val build_context:
    cs:ciphersuite
  -> key_dh_public_s cs
  -> key_dh_public_s cs
  -> lbytes (size_einfo) ->
  Tot (lbytes (size_context cs))

let build_context cs pkE pkR einfo =
  let idcs: lbytes 1 = id_of_cs cs in
  idcs @| pkE @| pkR @| einfo


/// SetupI()
///
/// Input: ciphersuite, pkR, info
///
///    1. (skE, pkE) = GenerateKeyPair()
///    2. zz = DH(skE, pkR)
///    3. secret = Extract(0^Nh, zz)
///    4. context = ciphersuite || Marshal(pkE) || Marshal(pkR) || info
///    6. keyIR = Expand(secret, "hpke key" || context, Nk)
///    8. nonceIR = Expand(secret, "hpke nonce" || context, Nn)
///
/// Output: pkE, keyIR, nonceIR

val encap:
    cs: ciphersuite
  -> skE: key_dh_secret_s cs
  -> pkR: key_dh_public_s cs
  -> einfo: lbytes size_einfo ->
  Tot (key_dh_public_s cs & key_aead_s cs & nonce_aead_s cs)

let encap cs skE pkR einfo =
  let pkE = DH.secret_to_public (curve_of_cs cs) skE in
  let zz = DH.scalarmult (curve_of_cs cs) skE pkR in
  let nh0 = create (size_dh_key cs) (u8 0) in
  let secret = HKDF.extract (hash_of_cs cs) nh0 zz in
  let context: lbytes (size_context cs) = build_context cs pkE pkR einfo in
  let info_key: lbytes (size_context cs + size_label_key) = label_key @| context in
  let info_nonce: lbytes (size_context cs + size_label_nonce) = label_nonce @| context in
  let keyIR = HKDF.expand (hash_of_cs cs) secret info_key (size_aead_key cs) in
  let nonceIR = HKDF.expand (hash_of_cs cs) secret info_nonce (size_aead_nonce cs) in
  pkE, keyIR, nonceIR


/// SetupR()
///
/// Input: ciphersuite, pkE, skR, info
///
///    1. zz = DH(skR, pkE)
///    2. secret = Extract(0^Nh, zz)
///    3. context = ciphersuite || Marshal(pkE) || Marshal(pkR) || info
///    4. keyIR = Expand(secret, "hpke key" || context, Nk)
///    5. nonceIR = Expand(secret, "hpke nonce" || context, Nn)
///
/// Output: keyIR, nonceIR

val decap:
    cs: ciphersuite
  -> pkE: key_dh_public_s cs
  -> skR: key_dh_secret_s cs
  -> einfo: lbytes size_einfo ->
  Tot (key_aead_s cs & nonce_aead_s cs)

let decap cs pkE skR einfo =
  let pkR = DH.secret_to_public (curve_of_cs cs) skR in
  let zz = DH.scalarmult (curve_of_cs cs) skR pkE in
  let nh0 = create (size_dh_key cs) (u8 0) in
  let secret = HKDF.extract (hash_of_cs cs) nh0 zz in
  let context: lbytes (size_context cs) = build_context cs pkE pkR einfo in
  let info_key: lbytes (size_context cs + size_label_key) = label_key @| context in
  let info_nonce: lbytes (size_context cs + size_label_nonce) = label_nonce @| context in
  let keyIR = HKDF.expand (hash_of_cs cs) secret info_key (size_aead_key cs) in
  let nonceIR = HKDF.expand (hash_of_cs cs) secret info_nonce (size_aead_nonce cs) in
  keyIR, nonceIR


/// Encrypt()
///
/// Input: ciphersuite, pkR, info, ad, pt
///
///    1. pkE, keyIR, nonceIR = SetupI(ciphersuite, pkR, info)
///    2. ct = Seal(keyIR, nonceIR, ad, pt)
///
/// Output: ct, pkE

val encrypt:
    cs: ciphersuite
  -> skE: key_dh_secret_s cs
  -> pkR: key_dh_public_s cs
  -> info: lbytes size_einfo
  -> aad: bytes {length aad + AEAD.padlen (aead_of_cs cs) (length aad) <= max_size_t}
  -> pt: bytes {length pt <= max_size_t
           /\ length pt + AEAD.size_block (aead_of_cs cs) <= max_size_t
           /\ length pt + AEAD.padlen (aead_of_cs cs) (length pt) <= max_size_t} ->
  Tot (bytes & key_dh_public_s cs)

let encrypt cs skE pkR info aad pt =
  let pkE, keyIR, nonceIR = encap cs skE pkR info in
  let ct = AEAD.aead_encrypt (aead_of_cs cs) keyIR nonceIR pt aad in
  ct, pkE


/// Decrypt()
///
/// Input: ciphersuite, skR, pkE, info, ad, ct
///
///    1. keyIR, nonceIR = Decap(ciphersuite, pkE, pkR, info)
///    2. pt = Open(keyIR, nonceIR, ad, ct)
///
/// Output: pt

val decrypt:
    cs: ciphersuite
  -> skR: key_dh_secret_s cs
  -> pkE: key_dh_public_s cs
  -> info: lbytes size_einfo
  -> aad: bytes{length aad + AEAD.padlen (aead_of_cs cs) (length aad) <= max_size_t}
  -> ct: bytes{AEAD.size_tag (aead_of_cs cs) <= length ct
             /\ (length ct + length aad) / 64 <= max_size_t
             /\ length ct + AEAD.size_block (aead_of_cs cs) <= max_size_t}
  -> mac: AEAD.tag (aead_of_cs cs) ->
  Tot (option (lbytes (length ct)))

let decrypt cs skR pkE info aad ct mac =
  let keyIR, nonceIR = decap cs pkE skR info in
  AEAD.aead_decrypt (aead_of_cs cs) keyIR nonceIR ct mac aad
