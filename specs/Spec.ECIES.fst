module Spec.ECIES

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence


module Hash = Spec.Hash


(* BB. TODO: Relocate this function *)
assume val crypto_random: len:size_nat -> Tot (option (lbytes len))

let pow2_61 : _:unit{pow2 61 == 2305843009213693952} = assert_norm(pow2 61 == 2305843009213693952)
let pow2_35_less_than_pow2_61 : _:unit{pow2 32 * pow2 3 <= pow2 61 - 1} = assert_norm(pow2 32 * pow2 3 <= pow2 61 - 1)
let pow2_35_less_than_pow2_125 : _:unit{pow2 32 * pow2 3 <= pow2 125 - 1} = assert_norm(pow2 32 * pow2 3 <= pow2 125 - 1)

#set-options "--z3rlimit 100"

type ciphersuite =
  | Curve25519_AES128_GCM_SHA2_256
  | Curve25519_AES128_GCM_SHA2_512
  | Curve448_AES128_GCM_SHA2_256
  | Curve448_AES128_GCM_SHA2_512

(** Ciphersuite identifiers *)
val id_of_cs: cs:ciphersuite -> Tot (lbytes 1)
let id_of_cs cs =
  match cs with
  | Curve25519_AES128_GCM_SHA2_256 -> create 1 (u8 0)
  | Curve25519_AES128_GCM_SHA2_512 -> create 1 (u8 1)
  | Curve448_AES128_GCM_SHA2_256 -> create 1 (u8 2)
  | Curve448_AES128_GCM_SHA2_512 -> create 1 (u8 3)

let hash_of_cs (cs:ciphersuite) : Spec.Hash.algorithm =
  match cs with
  | Curve25519_AES128_GCM_SHA2_256 -> Hash.SHA2_256
  | Curve25519_AES128_GCM_SHA2_512 -> Hash.SHA2_512
  | Curve448_AES128_GCM_SHA2_256 -> Hash.SHA2_256
  | Curve448_AES128_GCM_SHA2_512 -> Hash.SHA2_512


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

inline_for_extraction let vsize_nonce: size_nat = 12 (* AES_GCM with TLS length IV *)
inline_for_extraction let vsize_key_symmetric (cs:ciphersuite): size_nat = 16 + 8
inline_for_extraction let vsize_key_asymmetric (cs:ciphersuite): size_nat =
  match cs with
  | Curve25519_AES128_GCM_SHA2_256 -> 32
  | Curve25519_AES128_GCM_SHA2_512 -> 32
  | Curve448_AES128_GCM_SHA2_256 -> 56
  | Curve448_AES128_GCM_SHA2_512 -> 56


/// Types

type key_public_s (cs:ciphersuite) = lbytes (vsize_key_asymmetric cs)
type key_private_s (cs:ciphersuite) = lbytes (vsize_key_asymmetric cs)
type key_s (cs:ciphersuite) = lbytes (vsize_key_symmetric cs)


/// Cryptographic Primitives

val dh: cs:ciphersuite -> key_private_s cs -> key_public_s cs -> Tot (option (lbytes (vsize_key_asymmetric cs)))
let dh cs kpriv kpub =
  let secret =
    match cs with
    | Curve25519_AES128_GCM_SHA2_256
    | Curve25519_AES128_GCM_SHA2_512 -> Curve25519.scalarmult kpriv kpub
    | Curve448_AES128_GCM_SHA2_256
    | Curve448_AES128_GCM_SHA2_512 -> Curve448.scalarmult kpriv kpub
  in
  let unsafe : bool = for_all (fun a -> uint_to_nat #U8 a = 0) secret in
  if unsafe then None else Some secret


val secret_to_public: cs:ciphersuite -> key_private_s cs -> Tot (option (key_public_s cs))
let secret_to_public cs kpriv =
  let basepoint_zeros = create (vsize_key_asymmetric cs) (u8 0) in
  let basepoint = upd basepoint_zeros ((vsize_key_asymmetric cs) - 1) (u8 0x09) in
  dh cs kpriv basepoint


val encap: cs:ciphersuite -> kpub:key_public_s cs -> Tot (option (key_s cs & key_public_s cs))
let encap cs kpub =
  match crypto_random (vsize_key_asymmetric cs) with
  | None -> None
  | Some eph_kpriv ->
  match secret_to_public cs eph_kpriv with
  | None -> None
  | Some eph_kpub ->
  match dh cs eph_kpriv kpub with
  | None -> None
  | Some secret ->
    let salt = (id_of_cs cs) @| eph_kpub @| kpub in
    let extracted = Spec.HKDF.hkdf_extract (hash_of_cs cs) salt secret in
    let key = Spec.HKDF.hkdf_expand (hash_of_cs cs) extracted const_label_key (vsize_key_symmetric cs) in
    Some (key, eph_kpub)


val decap: cs:ciphersuite -> key_private_s cs -> eph_kpub:key_public_s cs -> Tot (option (key_s cs))
let decap cs kpriv eph_kpub =
  match secret_to_public cs kpriv with
  | None -> None
  | Some kpub ->
  match dh cs kpriv eph_kpub with
  | None -> None
  | Some secret ->
    let salt = (id_of_cs cs) @| eph_kpub @| kpub in
    let extracted = Spec.HKDF.hkdf_extract (hash_of_cs cs) salt secret in
    let key = Spec.HKDF.hkdf_expand (hash_of_cs cs) extracted const_label_key (vsize_key_symmetric cs) in
    Some key


val encrypt:
    cs: ciphersuite
  -> sk: key_s cs
  -> input: bytes{length input + 16 <= max_size_t}
  -> aad: bytes{length aad + 16 <= max_size_t}
  -> counter: uint32 ->
  Tot bytes

let encrypt cs sk input aad counter =
  let key = sub sk 0 16 in
  let nonce = sub sk 16 8 in
  let ctr = uint_to_bytes_le counter in
  Spec.AES128_GCM.aead_encrypt key (nonce @| ctr) input aad


val decrypt:
    cs: ciphersuite
  -> sk: key_s cs
  -> input:bytes{16 <= length input /\ length input <= max_size_t}
  -> aad:bytes{length aad + 16 <= max_size_t}
  -> counter:uint32 ->
  Tot bytes

let decrypt cs sk input aad counter =
  let key = sub sk 0 16 in
  let nonce = sub sk 16 8 in
  let ctr = uint_to_bytes_le counter in
  Spec.AES128_GCM.aead_decrypt key (nonce @| ctr) input aad

