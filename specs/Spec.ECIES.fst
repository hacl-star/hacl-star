module Spec.ECIES

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence


module DH = Spec.DH
module AEAD = Spec.AEAD
module Hash = Spec.Hash


(* BB. TODO: Relocate this function *)
assume val crypto_random: len:size_nat -> Tot (option (lbytes len))

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

inline_for_extraction let vsize_nonce (cs:ciphersuite): size_nat = AEAD.size_nonce (aead_of_cs cs)
inline_for_extraction let vsize_key (cs:ciphersuite): size_nat = AEAD.size_key (aead_of_cs cs) + 8
inline_for_extraction let vsize_key_dh (cs:ciphersuite): size_nat = DH.size_key (curve_of_cs cs)

/// Types

type key_public_s (cs:ciphersuite) = lbytes (vsize_key_dh cs)
type key_private_s (cs:ciphersuite) = lbytes (vsize_key_dh cs)
type key_s (cs:ciphersuite) = lbytes (vsize_key cs)


/// Cryptographic Primitives

val encap:
    cs: ciphersuite
  -> kpub: key_public_s cs ->
  Tot (option (key_s cs & key_public_s cs))

let encap cs kpub =
  match crypto_random (vsize_key_dh cs) with
  | None -> None
  | Some eph_kpriv ->
    let eph_kpub = DH.secret_to_public (curve_of_cs cs) eph_kpriv in
    match DH.dh (curve_of_cs cs) eph_kpriv kpub with
    | None -> None
    | Some secret ->
      let salt = (id_of_cs cs) @| eph_kpub @| kpub in
      let extracted = Spec.HKDF.hkdf_extract (hash_of_cs cs) salt secret in
      let key = Spec.HKDF.hkdf_expand (hash_of_cs cs) extracted const_label_key (vsize_key cs) in
      Some (key, eph_kpub)


val decap:
    cs: ciphersuite
  -> kpriv: key_private_s cs
  -> eph_kpub: key_public_s cs ->
  Tot (option (key_s cs))

let decap cs kpriv eph_kpub =
  let kpub = DH.secret_to_public (curve_of_cs cs) kpriv in
  match DH.dh (curve_of_cs cs) kpriv eph_kpub with
  | None -> None
  | Some secret ->
    let salt = (id_of_cs cs) @| eph_kpub @| kpub in
    let extracted = Spec.HKDF.hkdf_extract (hash_of_cs cs) salt secret in
    let key = Spec.HKDF.hkdf_expand (hash_of_cs cs) extracted const_label_key (vsize_key cs) in
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
  let nonce = sub sk klen 8 in
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
  let nonce = sub sk klen 8 in
  let ctr = uint_to_bytes_le counter in
  AEAD.aead_decrypt (aead_of_cs cs) key (nonce @| ctr) input aad
