module Spec.ECIES

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

#set-options "--z3rlimit 100"

/// Types

type ciphersuite = DH.algorithm & AEAD.algorithm & a:Hash.algorithm{a == Hash.SHA2_256 \/ a == Hash.SHA2_512}

val id_of_cs: cs:ciphersuite -> Tot (lbytes 1)
let id_of_cs cs =
  match cs with
  | DH.DH_Curve25519, AEAD.AEAD_AES128_GCM,        Hash.SHA2_256 -> create 1 (u8 0)
  | DH.DH_Curve25519, AEAD.AEAD_AES128_GCM,        Hash.SHA2_512 -> create 1 (u8 1)
  | DH.DH_Curve25519, AEAD.AEAD_Chacha20_Poly1305, Hash.SHA2_256 -> create 1 (u8 2)
  | DH.DH_Curve25519, AEAD.AEAD_Chacha20_Poly1305, Hash.SHA2_512 -> create 1 (u8 3)
  | DH.DH_Curve448,   AEAD.AEAD_AES128_GCM,        Hash.SHA2_256 -> create 1 (u8 4)
  | DH.DH_Curve448,   AEAD.AEAD_AES128_GCM,        Hash.SHA2_512 -> create 1 (u8 5)
  | DH.DH_Curve448,   AEAD.AEAD_Chacha20_Poly1305, Hash.SHA2_256 -> create 1 (u8 6)
  | DH.DH_Curve448,   AEAD.AEAD_Chacha20_Poly1305, Hash.SHA2_512 -> create 1 (u8 7)

let curve_of_cs (cs:ciphersuite) : DH.algorithm =
  let (c,a,h) = cs in c

let aead_of_cs (cs:ciphersuite) : AEAD.algorithm =
  let (c,a,h) = cs in a

let hash_of_cs (cs:ciphersuite) : Hash.algorithm =
  let (c,a,h) = cs in h


/// Constants

(** Constants for ECIES labels *)
let const_label_nonce : lbytes 11 =
  [@inline_let]
  let l = [u8 0x65; u8 0x63; u8 0x69; u8 0x65; u8 0x73; u8 0x20; u8 0x6e; u8 0x6f; u8 0x6e; u8 0x63; u8 0x65] in
  assert_norm(List.Tot.length l == 11);
  createL l

let const_label_key : lbytes 9 =
  [@inline_let]
  let l = [u8 0x65; u8 0x63; u8 0x69; u8 0x65; u8 0x73; u8 0x20; u8 0x6b; u8 0x65; u8 0x79] in
  assert_norm(List.Tot.length l == 9);
  createL l


/// Constants sizes

inline_for_extraction
let size_nonce (cs:ciphersuite): size_nat = AEAD.size_nonce (aead_of_cs cs)

inline_for_extraction
let size_key (cs:ciphersuite): size_nat = AEAD.size_key (aead_of_cs cs) + size_nonce cs - numbytes U32

inline_for_extraction
let size_key_dh (cs:ciphersuite): size_nat = DH.size_key (curve_of_cs cs)

/// Types

type key_public_s (cs:ciphersuite) = lbytes (size_key_dh cs)
type key_private_s (cs:ciphersuite) = lbytes (size_key_dh cs)
type key_s (cs:ciphersuite) = lbytes (size_key cs)


/// Cryptographic Primitives

val encap:
    cs: ciphersuite
  -> e: entropy
  -> pk: key_public_s cs
  -> context: lbytes 32 ->
  Tot (entropy & (option (key_s cs & key_public_s cs)))

let encap cs e pk context =
  let e', esk = crypto_random e (size_key_dh cs) in
  let epk = DH.secret_to_public (curve_of_cs cs) esk in
  match DH.dh (curve_of_cs cs) esk pk with
  | None -> e', None
  | Some secret ->
    let salt = epk @| pk in
    let extracted = HKDF.hkdf_extract (hash_of_cs cs) salt secret in
    let info = (id_of_cs cs) @| const_label_key @| context in
    let key = HKDF.hkdf_expand (hash_of_cs cs) extracted info (size_key cs) in
    e', Some (key, epk)


val decap:
    cs: ciphersuite
  -> sk: key_private_s cs
  -> epk: key_public_s cs
  -> context: lbytes 32 ->
  Tot (option (key_s cs))

let decap cs sk epk context =
  let pk = DH.secret_to_public (curve_of_cs cs) sk in
  match DH.dh (curve_of_cs cs) sk epk with
  | None -> None
  | Some secret ->
    let salt = epk @| pk in
    let extracted = HKDF.hkdf_extract (hash_of_cs cs) salt secret in
    let info = (id_of_cs cs) @| const_label_key @| context in
    let key = HKDF.hkdf_expand (hash_of_cs cs) extracted info (size_key cs) in
    Some key


val encrypt:
    cs: ciphersuite
  -> sk: key_s cs
  -> input: bytes{length input <= max_size_t
           /\ length input + AEAD.size_block (aead_of_cs cs) <= max_size_t
           /\ length input + AEAD.padlen (aead_of_cs cs) (length input) <= max_size_t}
  -> aad: bytes {length aad <= max_size_t /\ length aad + AEAD.padlen (aead_of_cs cs) (length aad) <= max_size_t}
  -> counter: uint32 ->
  Tot bytes

let encrypt cs sk input aad counter =
  let klen = AEAD.size_key (aead_of_cs cs) in
  let key = sub sk 0 klen in
  let nonce = sub sk klen (size_nonce cs - numbytes U32) in
  let ctr = uint_to_bytes_le counter in
  AEAD.aead_encrypt (aead_of_cs cs) key (nonce @| ctr) input aad


val decrypt:
    cs: ciphersuite
  -> sk: key_s cs
  -> c: bytes{AEAD.size_tag (aead_of_cs cs) <= length c /\ length c <= max_size_t}
  -> aad: bytes{length aad <= max_size_t
             /\ (length c + length aad) / 64 <= max_size_t
             /\ length aad + AEAD.padlen (aead_of_cs cs) (length aad) <= max_size_t}
  -> counter:uint32 ->
  Tot (option (lbytes (length c - AEAD.size_tag (aead_of_cs cs))))

let decrypt cs sk input aad counter =
  let klen = AEAD.size_key (aead_of_cs cs) in
  let key = sub sk 0 klen in
  let nonce = sub sk klen (size_nonce cs - numbytes U32) in
  let ctr = uint_to_bytes_le counter in
  AEAD.aead_decrypt (aead_of_cs cs) key (nonce @| ctr) input aad

///
/// One time KEM API
///

(** KEM Encrypt a payload to a specific Group or Participant *)
val encrypt_single:
    cs: ciphersuite
  -> e: entropy
  -> pk: key_public_s cs
  -> input: bytes{length input <= max_size_t
           /\ length input + size_key_dh cs + AEAD.size_block (aead_of_cs cs) <= max_size_t
           /\ length input + size_key_dh cs + AEAD.padlen (aead_of_cs cs) (length input) <= max_size_t}
  -> context: lbytes 32 ->
  Tot (entropy & (option (lbytes (size_key_dh cs + length input + AEAD.size_tag (aead_of_cs cs)))))

let encrypt_single cs e pk input context =
  match encap cs e pk context with
  | e', None -> e', None
  | e', Some (key, epk) ->
    let ciphertext = encrypt cs key input lbytes_empty (u32 0) in
    e', Some (concat #uint8 #(size_key_dh cs) #(length input + AEAD.size_tag (aead_of_cs cs)) epk ciphertext)


(** KEM Decrypt a payload that was generated using KEM Encrypt *)
val decrypt_single:
    cs: ciphersuite
  -> sk: key_private_s cs
  -> input: bytes {size_key_dh cs + AEAD.size_tag (aead_of_cs cs) <= length input /\ length input <= max_size_t}
  -> context: lbytes 32 ->
  Tot (option (lbytes (length input - (size_key_dh cs) - AEAD.size_tag ((aead_of_cs cs)))))

let decrypt_single cs sk input context =
  let epk = sub #uint8 #(length input) input 0 (size_key_dh cs) in
  let ciphertext = sub #uint8 #(length input) input (size_key_dh cs) ((length input) - size_key_dh cs) in
  match decap cs sk epk context with
  | None -> None
  | Some key -> decrypt cs key ciphertext lbytes_empty (u32 0)
