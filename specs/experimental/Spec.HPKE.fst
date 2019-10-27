module Spec.HPKE

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD.Hacl
module Hash = Spec.Agile.Hash
module HKDF = Spec.Agile.HKDF


let pow2_61 : _:unit{pow2 61 == 2305843009213693952} = assert_norm(pow2 61 == 2305843009213693952)
let pow2_35_less_than_pow2_61 : _:unit{pow2 32 * pow2 3 <= pow2 61 - 1} = assert_norm(pow2 32 * pow2 3 <= pow2 61 - 1)
let pow2_35_less_than_pow2_125 : _:unit{pow2 32 * pow2 3 <= pow2 125 - 1} = assert_norm(pow2 32 * pow2 3 <= pow2 125 - 1)

#set-options "--z3rlimit 200"


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


/// Types

inline_for_extraction
let size_cs_identifier: size_nat = 2

inline_for_extraction
let size_mode_identifier: size_nat = 1


let is_ciphersuite = function
  | DH.DH_Curve25519, AEAD.AEAD_AES128_GCM,        Hash.SHA2_256
  | DH.DH_Curve25519, AEAD.AEAD_Chacha20_Poly1305, Hash.SHA2_256
  | DH.DH_Curve448,   AEAD.AEAD_AES256_GCM,        Hash.SHA2_512
  | DH.DH_Curve448,   AEAD.AEAD_Chacha20_Poly1305, Hash.SHA2_512
  | DH.DH_P256,       AEAD.AEAD_AES128_GCM,        Hash.SHA2_256
  | DH.DH_P256,       AEAD.AEAD_Chacha20_Poly1305, Hash.SHA2_256 -> true
  | _,_,_ -> false

type ciphersuite = cs:(DH.algorithm & AEAD.algorithm & Hash.algorithm){is_ciphersuite cs}


val id_of_cs: cs:ciphersuite -> Tot (lbytes size_cs_identifier)
let id_of_cs cs =
  match cs with
  | DH.DH_Curve25519, AEAD.AEAD_AES128_GCM,        Hash.SHA2_256 -> create 2 (u8 1)
  | DH.DH_Curve25519, AEAD.AEAD_Chacha20_Poly1305, Hash.SHA2_256 -> create 2 (u8 2)
  | DH.DH_Curve448,   AEAD.AEAD_AES256_GCM,        Hash.SHA2_512 -> create 2 (u8 3)
  | DH.DH_Curve448,   AEAD.AEAD_Chacha20_Poly1305, Hash.SHA2_512 -> create 2 (u8 4)
  | DH.DH_P256,       AEAD.AEAD_AES128_GCM,        Hash.SHA2_256 -> create 2 (u8 5)
  | DH.DH_P256,       AEAD.AEAD_Chacha20_Poly1305, Hash.SHA2_256 -> create 2 (u8 6)


let curve_of_cs (cs:ciphersuite) : DH.algorithm =
  let (c,a,h) = cs in c

let aead_of_cs (cs:ciphersuite) : AEAD.algorithm =
  let (c,a,h) = cs in a

let hash_of_cs (cs:ciphersuite) : Hash.algorithm =
  let (c,a,h) = cs in h


type mode =
  | Base
  | PSK
  | Auth
  | PSKAuth

val id_of_mode: m:mode -> Tot (lbytes size_mode_identifier)
let id_of_mode m =
  match m with
  | Base -> create 1 (u8 0)
  | PSK -> create 1 (u8 1)
  | Auth -> create 1 (u8 2)
  | PSKAuth -> create 1 (u8 3)

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
let size_kdf (cs:ciphersuite): size_nat = Hash.size_hash (hash_of_cs cs)

inline_for_extraction
let size_psk (cs:ciphersuite): size_nat = size_kdf cs


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


/// def Encap(pkR):
///     skE, pkE = GenerateKeyPair()
///     zz = DH(skE, pkR)
///     enc = Marshal(pkE)
///     return zz, enc

val encap:
    cs: ciphersuite
  -> skE: key_dh_secret_s cs
  -> pkR: key_dh_public_s cs ->
  Tot (key_dh_public_s cs & key_dh_public_s cs)

let encap cs skE pkR =
  let pkE = DH.secret_to_public (curve_of_cs cs) skE in
  let zz = DH.scalarmult (curve_of_cs cs) skE pkR in
  zz, pkE


/// def Decap(enc, skR):
///      pkE = Unmarshal(enc)
///      return DH(skR, pkE)

val decap:
    cs: ciphersuite
  -> pkE: key_dh_public_s cs
  -> skR: key_dh_secret_s cs ->
  Tot (key_dh_public_s cs)

let decap cs pkE skR = DH.scalarmult (curve_of_cs cs) skR pkE


/// def AuthEncap(pkR, skI):
///      skE, pkE = GenerateKeyPair()
///      zz = concat(DH(skE, pkR), DH(skI, pkR))
///      enc = Marshal(pkE)
///      return zz, enc

val auth_encap:
    cs: ciphersuite
  -> skE: key_dh_secret_s cs
  -> skI: key_dh_secret_s cs
  -> pkR: key_dh_public_s cs ->
  Tot (lbytes (2 * size_dh_public cs) & key_dh_public_s cs)

let auth_encap cs skE skI pkR =
  let pkE = DH.secret_to_public (curve_of_cs cs) skE in
  let er = DH.scalarmult (curve_of_cs cs) skE pkR in
  let ir = DH.scalarmult (curve_of_cs cs) skI pkR in
  let zz = concat er ir in
  zz, pkE


/// def AuthDecap(enc, skR, pkI):
///      pkE = Unmarshal(enc)
///      return concat(DH(skR, pkE), DH(skR, pkI))

val auth_decap:
    cs: ciphersuite
  -> pkE: key_dh_public_s cs
  -> pkI: key_dh_public_s cs
  -> skR: key_dh_secret_s cs ->
  Tot (lbytes (2 * size_dh_public cs))

let auth_decap cs pkE pkI skR =
  let re = DH.scalarmult (curve_of_cs cs) skR pkE in
  let ri = DH.scalarmult (curve_of_cs cs) skR pkI in
  concat re ri

/// default_pkIm = zero(Npk)
/// default_psk = zero(Nh)
/// default_pskId = zero(0)

let default_pkI (cs:ciphersuite):bytes = create (size_dh_public cs) (u8 0)
let default_psk (cs:ciphersuite): bytes = create (size_psk cs) (u8 0)
let default_pskId: b:bytes{Seq.length b = 0} = lbytes_empty


/// def VerifyMode(mode, psk, pskID, pkIm):
///     got_psk = (psk != default_psk and pskID != default_pskID)
///     no_psk = (psk == default_psk and pskID == default_pskID)
///     got_pkIm = (pkIm != default_pkIm)
///     no_pkIm = (pkIm == default_pkIm)
///
///     if mode == mode_base and (got_psk or got_pkIm):
///       raise Exception("Invalid configuration for mode_base")
///     if mode == mode_psk and (no_psk or got_pkIm):
///       raise Exception("Invalid configuration for mode_psk")
///     if mode == mode_auth and (got_psk or no_pkIm):
///       raise Exception("Invalid configuration for mode_auth")
///     if mode == mode_psk_auth and (no_psk or no_pkIm):
///       raise Exception("Invalid configuration for mode_psk_auth")
///
///
/// BB. Implementing this function should not be necessary for us.
///     We are filtering those using our option type in `ks_derive`.

val build_context:
    cs:ciphersuite
  -> m:mode
  -> pkE:key_dh_public_s cs
  -> pkR:key_dh_public_s cs
  -> pkI:key_dh_public_s cs
  -> pskID:bytes{Seq.length pskID <= max_pskID}
  -> info:bytes{Seq.length info <= max_pskID} ->
  Tot bytes

let build_context cs m pkE pkR pkI pskID info =
  let pskID_len: lbytes 2 = nat_to_bytes_be 2 (Seq.length pskID) in
  let info_len: lbytes 2 = nat_to_bytes_be 2 (Seq.length info) in
  let context = (id_of_mode m) @| (id_of_cs cs) @| pkE @| pkR @| pkI in
  let context = Seq.append context pskID_len in
  let context = Seq.append context pskID in
  let context = Seq.append context info_len in
  let context = Seq.append context info in
  context


val ks_derive:
    cs:ciphersuite
  -> m:mode
  -> pkR:key_dh_public_s cs
  -> zz:bytes{Seq.length zz = size_dh_public cs \/ Seq.length zz = 2 * size_dh_public cs}
  -> pkE:key_dh_public_s cs
  -> info:bytes{Seq.length info <= max_info}
  -> opsk:option (psk_s cs & id:bytes{Seq.length id <= max_pskID})
  -> opkI:option (key_dh_public_s cs) ->
  Tot (key_aead_s cs & nonce_aead_s cs)

let ks_derive cs m pkR zz pkE info opsk opkI =
  let (psk, pskID) =
    match opsk with
    | None -> (default_psk cs, default_pskId)
    | Some (psk, pskID) -> (psk, pskID) in
  let pkI =
    match opkI with
    | None -> default_pkI cs
    | Some pki -> pki in
  let context = build_context cs m pkE pkR pkI pskID info in
  let secret = HKDF.extract (hash_of_cs cs) psk zz in
  let info_key = Seq.append label_key context in
  let info_nonce = Seq.append label_nonce context in
  let keyIR = HKDF.expand (hash_of_cs cs) secret info_key (size_aead_key cs) in
  let nonceIR = HKDF.expand (hash_of_cs cs) secret info_nonce (size_aead_nonce cs) in
  keyIR, nonceIR


/// def SetupBaseI(pkR, info):
///     zz, enc = Encap(pkR)
///     return enc, KeySchedule(mode_base, pkR, zz, enc, info,
///                             default_psk, default_pskID, default_pkIm)

val setupBaseI:
    cs:ciphersuite
  -> skE: key_dh_secret_s cs
  -> pkR:key_dh_public_s cs
  -> info:bytes{Seq.length info <= max_info} ->
  Tot (key_dh_public_s cs & key_aead_s cs & nonce_aead_s cs)

let setupBaseI cs skE pkR info =
  let zz, pkE = encap cs skE pkR in
  let k,n = ks_derive cs Base pkR zz pkE info None None in
  pkE, k, n


/// def SetupBaseR(enc, skR, info):
///     zz = Decap(enc, skR)
///     return KeySchedule(mode_base, pk(skR), zz, enc, info,
///                        default_psk, default_pskID, default_pkIm)

val setupBaseR:
    cs:ciphersuite
  -> pkE: key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:bytes{Seq.length info <= max_info} ->
  Tot (key_aead_s cs & nonce_aead_s cs)

let setupBaseR cs pkE skR info =
  let pkR = DH.secret_to_public (curve_of_cs cs) skR in
  let zz = decap cs pkE skR in
  ks_derive cs Base pkR zz pkE info None None


/// def SetupAuthI(pkR, skI, info):
///     zz, enc = AuthEncap(pkR, skI)
///     pkIm = Marshal(pk(skI))
///     return enc, KeySchedule(pkR, zz, enc, info,
///                             default_psk, default_pskID, pkIm)

val setupAuthI:
    cs:ciphersuite
  -> skE: key_dh_secret_s cs
  -> skI: key_dh_secret_s cs
  -> pkR:key_dh_public_s cs
  -> info:bytes{Seq.length info <= max_info} ->
  Tot (key_dh_public_s cs & key_aead_s cs & nonce_aead_s cs)

let setupAuthI cs skE skI pkR info =
  let pkI = DH.secret_to_public (curve_of_cs cs) skI in
  let zz, pkE = auth_encap cs skE skI pkR in
  let k, n = ks_derive cs Auth pkR zz pkE info None (Some pkI) in
  pkE, k, n


/// def SetupAuthR(enc, skR, pkI, info):
///     zz = AuthDecap(enc, skR, pkI)
///     pkIm = Marshal(pkI)
///     return KeySchedule(pk(skR), zz, enc, info,
///                        default_psk, default_pskID, pkIm)

val setupAuthR:
    cs:ciphersuite
  -> pkE: key_dh_public_s cs
  -> pkI: key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:bytes{Seq.length info <= max_info} ->
  Tot (key_aead_s cs & nonce_aead_s cs)

let setupAuthR cs pkE pkI skR info =
  let pkR = DH.secret_to_public (curve_of_cs cs) skR in
  let zz = auth_decap cs pkE pkI skR in
  ks_derive cs Auth pkR zz pkE info None (Some pkI)


/// def SetupAuthI(pkR, psk, pskID, skI, info):
///     zz, enc = AuthEncap(pkR, skI)
///     pkIm = Marshal(pk(skI))
///     return enc, KeySchedule(pkR, zz, enc, info, psk, pskID, pkIm)

val setupPSKAuthI:
    cs:ciphersuite
  -> skE: key_dh_secret_s cs
  -> skI: key_dh_secret_s cs
  -> pkR: key_dh_public_s cs
  -> psk: psk_s cs
  -> pskID: bytes{Seq.length pskID <= max_pskID}
  -> info:bytes{Seq.length info <= max_info} ->
  Tot (key_dh_public_s cs & key_aead_s cs & nonce_aead_s cs)

let setupPSKAuthI cs skE skI pkR psk pskID info =
  let pkI = DH.secret_to_public (curve_of_cs cs) skI in
  let zz, pkE = auth_encap cs skE skI pkR in
  let k, n = ks_derive cs PSKAuth pkR zz pkE info (Some (psk, pskID)) (Some pkI) in
  pkE, k, n


/// def SetupAuthR(enc, skR, psk, pskID, pkI, info):
///     zz = AuthDecap(enc, skR, pkI)
///     pkIm = Marshal(pkI)
///     return KeySchedule(pk(skR), zz, enc, info, psk, pskID, pkIm)

val setupPSKAuthR:
    cs:ciphersuite
  -> pkE: key_dh_public_s cs
  -> pkI: key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> psk: psk_s cs
  -> pskID: bytes{Seq.length pskID <= max_pskID}
  -> info:bytes{Seq.length info <= max_info} ->
  Tot (key_aead_s cs & nonce_aead_s cs)

let setupPSKAuthR cs pkE pkI skR psk pskID info =
  let pkR = DH.secret_to_public (curve_of_cs cs) skR in
  let zz = auth_decap cs pkE pkI skR in
  ks_derive cs PSKAuth pkR zz pkE info (Some (psk, pskID)) (Some pkI)


/// Encrypt() and Decrypt using the derived AEAD key and nonce
/// are implemented by calling AEAD.encrypt and AEAD.Decrypt

val encryptBase:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:key_dh_public_s cs
  -> m:bytes
  -> info:bytes{Seq.length info <= max_info} ->
  Tot (option bytes)

let encryptBase cs skE pkR m info =
  let zz, pkR = encap cs skE pkR in
  let pkE,k,n = setupBaseI cs skE pkR info in
  match Spec.Defensive.AEAD.encrypt (aead_of_cs cs) k n m info with
  | None -> None
  | Some c -> Some (Seq.append pkE c)


val decryptBase:
    cs:ciphersuite
  -> pkE:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> input:bytes{size_dh_public cs <= Seq.length input /\ Seq.length input <= max_size_t}
  -> info:bytes{Seq.length info <= max_info} ->
  Tot (option bytes)

let decryptBase cs pkE skR input info =
  let pkE = sub #uint8 #(Seq.length input) input 0 (size_dh_key cs) in
  let c = sub #uint8 #(Seq.length input) input (size_dh_public cs) (length input - (size_dh_public cs)) in
  let zz = decap cs pkE skR in
  let k,n = setupBaseR cs pkE skR info in
  Spec.Defensive.AEAD.decrypt (aead_of_cs cs) k n c info
