module Spec.HPKE.CFRG

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.RandomSequence

module DH = Spec.DH
module AEAD = Spec.AEAD
module Hash = Spec.Hash
module HKDF = Spec.HKDF


let pow2_61 : _:unit{pow2 61 == 2305843009213693952} = assert_norm(pow2 61 == 2305843009213693952)
let pow2_35_less_than_pow2_61 : _:unit{pow2 32 * pow2 3 <= pow2 61 - 1} = assert_norm(pow2 32 * pow2 3 <= pow2 61 - 1)
let pow2_35_less_than_pow2_125 : _:unit{pow2 32 * pow2 3 <= pow2 125 - 1} = assert_norm(pow2 32 * pow2 3 <= pow2 125 - 1)

#set-options "--z3rlimit 25 --max_fuel 0"

/// Types

type ciphersuite = DH.algorithm & AEAD.algorithm & a:Hash.algorithm{a == Hash.SHA2_256 \/ a == Hash.SHA2_512}

inline_for_extraction
let size_cs_identifier: size_nat = 1

val id_of_cs: cs:ciphersuite -> Tot (lbytes size_cs_identifier)
let id_of_cs cs =
  match cs with
  | DH.DH_Curve25519, AEAD.AEAD_AES128_GCM,        Hash.SHA2_256 -> create 1 (u8 0x01)
  | DH.DH_Curve25519, AEAD.AEAD_Chacha20_Poly1305, Hash.SHA2_256 -> create 1 (u8 0x02)
  | DH.DH_Curve448,   AEAD.AEAD_Chacha20_Poly1305, Hash.SHA2_512 -> create 1 (u8 0x04)
  | _ -> magic()

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
let size_nonce (cs:ciphersuite): size_nat = AEAD.size_nonce (aead_of_cs cs)

inline_for_extraction
let size_key (cs:ciphersuite): size_nat = AEAD.size_key (aead_of_cs cs)

inline_for_extraction
let size_key_dh (cs:ciphersuite): size_nat = DH.size_key (curve_of_cs cs)

/// Types

type key_public_s (cs:ciphersuite) = lbytes (size_key_dh cs)
type key_secret_s (cs:ciphersuite) = lbytes (size_key_dh cs)
type key_s (cs:ciphersuite) = lbytes (size_key cs)
type nonce_s (cs:ciphersuite) = lbytes (size_nonce cs)


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
  -> e: entropy
  -> pkR: key_public_s cs
  -> info: lbytes 32 ->
  Tot (entropy & key_public_s cs & key_s cs & nonce_s cs)

let encap cs e pkR info =
  let e', skE = crypto_random e (size_key_dh cs) in
  let pkE = DH.secret_to_public (curve_of_cs cs) skE in
  let zz = DH.scalarmult (curve_of_cs cs) skE pkR in
  let nh0 = create (Spec.Hash.size_hash (hash_of_cs cs)) (u8 0) in
  let secret = HKDF.hkdf_extract (hash_of_cs cs) nh0 zz in
  let context = (id_of_cs cs) @| pkE @| pkR in
  let context = concat #uint8 #(length context) #(length info) context info in
  let keyIR = HKDF.hkdf_expand (hash_of_cs cs) secret (label_key @| context) (size_key cs) in
  let nonceIR = HKDF.hkdf_expand (hash_of_cs cs) secret (label_nonce @| context) (size_nonce cs) in
  e', pkE, keyIR, nonceIR


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
  -> pkE: key_public_s cs
  -> skR: key_secret_s cs
  -> info: lbytes 32 ->
  Tot (key_s cs & nonce_s cs)

let decap cs pkE skR info =
  let zz = DH.scalarmult (curve_of_cs cs) skR pkE in
  let nh0 = create (Spec.Hash.size_hash (hash_of_cs cs)) (u8 0) in
  let secret = HKDF.hkdf_extract (hash_of_cs cs) nh0 zz in
  let pkR = DH.secret_to_public (curve_of_cs cs) skR in
  let context = (id_of_cs cs) @| pkE @| pkR in
  let context = concat #uint8 #_ #(length info) context info in
  let keyIR = HKDF.hkdf_expand (hash_of_cs cs) secret (label_key @| context) (size_key cs) in
  let nonceIR = HKDF.hkdf_expand (hash_of_cs cs) secret (label_nonce @| context) (size_nonce cs) in
  keyIR, nonceIR

/// Input: ciphersuite, pkR, info, ad, pt
///
///    1. pkE, keyIR, nonceIR = SetupI(ciphersuite, pkR, info)
///    2. ct = Seal(keyIR, nonceIR, ad, pt)
///
/// Output: ct, pkE

val encrypt:
    cs: ciphersuite
  -> e: entropy
  -> pkR: key_public_s cs
  -> info: lbytes 32
  -> aad: bytes {length aad <= max_size_t /\ length aad + AEAD.padlen (aead_of_cs cs) (length aad) <= max_size_t}
  -> pt: bytes{length pt <= max_size_t
           /\ length pt + AEAD.size_block (aead_of_cs cs) <= max_size_t
           /\ length pt + AEAD.padlen (aead_of_cs cs) (length pt) <= max_size_t} ->
  Tot (bytes & key_public_s cs)

let encrypt cs e pkR info aad pt =
  let e, pkE, keyIR, nonceIR = encap cs e pkR info in
  let ct = AEAD.aead_encrypt (aead_of_cs cs) keyIR nonceIR pt aad in
  ct, pkE

/// Input: ciphersuite, skR, pkE, info, ad, ct
///
///    1. keyIR, nonceIR = Decap(ciphersuite, pkE, pkR, info)
///    2. pt = Open(keyIR, nonceIR, ad, ct)
///
/// Output: pt

#set-options "--z3rlimit 50 --max_fuel 1"

val decrypt:
    cs: ciphersuite
  -> skR: key_secret_s cs
  -> pkE: key_public_s cs
  -> info: lbytes 32
  -> aad: bytes{length aad <= max_size_t
             /\ length aad + AEAD.padlen (aead_of_cs cs) (length aad) <= max_size_t}
  -> ct: bytes{AEAD.size_tag (aead_of_cs cs) <= length ct /\ (length ct + length aad) / 64 <= max_size_t /\ length ct <= max_size_t} ->
  Tot (option (lbytes (length ct - AEAD.size_tag (aead_of_cs cs))))

let decrypt cs skR pkE info aad ct =
  let keyIR, nonceIR = decap cs pkE skR info in
  Spec.AEAD.aead_decrypt (aead_of_cs cs) keyIR nonceIR ct aad
