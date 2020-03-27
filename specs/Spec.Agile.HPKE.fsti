module Spec.Agile.HPKE

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash
module HKDF = Spec.Agile.HKDF

#set-options "--z3rlimit 20 --fuel 0 --ifuel 1"

let is_ciphersuite = function
  | DH.DH_Curve25519, AEAD.AES128_GCM,        Hash.SHA2_256
  | DH.DH_Curve25519, AEAD.CHACHA20_POLY1305, Hash.SHA2_256
  | DH.DH_P256,       AEAD.AES128_GCM,        Hash.SHA2_256
  | DH.DH_P256,       AEAD.CHACHA20_POLY1305, Hash.SHA2_256 -> true
  | DH.DH_Curve25519, AEAD.CHACHA20_POLY1305, Hash.SHA2_512 -> true
  | _,_,_ -> false

let ciphersuite = cs:(DH.algorithm & AEAD.alg & Hash.algorithm){is_ciphersuite cs}

let curve_of_cs (cs:ciphersuite) : DH.algorithm =
  let (c,a,h) = cs in c

let aead_of_cs (cs:ciphersuite) : AEAD.alg =
  let (c,a,h) = cs in a

let hash_of_cs (cs:ciphersuite) : Hash.algorithm =
  let (c,a,h) = cs in h

/// Constants sizes

inline_for_extraction
let size_aead_nonce (cs:ciphersuite): (n:size_nat{AEAD.iv_length (aead_of_cs cs) n}) =
  assert_norm (8 * 12 <= pow2 64 - 1);
  12

inline_for_extraction
let size_aead_key (cs:ciphersuite): size_nat = AEAD.key_length (aead_of_cs cs)

inline_for_extraction
let size_aead_tag (cs:ciphersuite): size_nat = AEAD.tag_length (aead_of_cs cs)

inline_for_extraction
let size_dh_key (cs:ciphersuite): size_nat = DH.size_key (curve_of_cs cs)

inline_for_extraction
let size_dh_public (cs:ciphersuite): size_nat = match curve_of_cs cs with
  | DH.DH_Curve25519 -> DH.size_public DH.DH_Curve25519
  | DH.DH_P256 -> DH.size_public DH.DH_P256 + 1 // Need the additional byte for representation

inline_for_extraction
let size_kdf (cs:ciphersuite): size_nat = Hash.size_hash (hash_of_cs cs)

inline_for_extraction
let size_psk (cs:ciphersuite): size_nat = size_kdf cs

inline_for_extraction
let max_length (cs:ciphersuite) : size_nat = AEAD.max_length (aead_of_cs cs)

inline_for_extraction
let max_pskID: size_nat = pow2 16 - 1

inline_for_extraction
let max_info: size_nat = pow2 16 - 1


/// Types

type key_dh_public_s (cs:ciphersuite) = lbytes (size_dh_public cs)
type key_dh_secret_s (cs:ciphersuite) = lbytes (size_dh_key cs)
type key_aead_s (cs:ciphersuite) = lbytes (size_aead_key cs)
type nonce_aead_s (cs:ciphersuite) = lbytes (size_aead_nonce cs)
type psk_s (cs:ciphersuite) = lbytes (size_psk cs)

val setupBaseI:
    cs:ciphersuite
  -> skE: key_dh_secret_s cs
  -> pkR:key_dh_public_s cs
  -> info:bytes{Seq.length info <= max_info} ->
  Tot (option (key_dh_public_s cs & key_aead_s cs & nonce_aead_s cs))

val setupBaseR:
    cs:ciphersuite
  -> pkE: key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:bytes{Seq.length info <= max_info} ->
  Tot (option (key_aead_s cs & nonce_aead_s cs))

val sealBase:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:key_dh_public_s cs
  -> m:bytes{Seq.length m <= max_length cs}
  -> info:bytes{Seq.length info <= max_info} ->
  Tot (option bytes)

val openBase:
    cs:ciphersuite
  -> skR:key_dh_secret_s cs
  -> input:bytes{size_dh_public cs + size_aead_tag cs <= Seq.length input /\ Seq.length input <= max_size_t}
  -> info:bytes{Seq.length info <= max_info} ->
  Tot (option bytes)
