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


let pow2_61 : _:unit{pow2 61 == 2305843009213693952} = assert_norm(pow2 61 == 2305843009213693952)
let pow2_35_less_than_pow2_61 : _:unit{pow2 32 * pow2 3 <= pow2 61 - 1} = assert_norm(pow2 32 * pow2 3 <= pow2 61 - 1)
let pow2_35_less_than_pow2_125 : _:unit{pow2 32 * pow2 3 <= pow2 125 - 1} = assert_norm(pow2 32 * pow2 3 <= pow2 125 - 1)

#set-options "--z3rlimit 20 --fuel 0 --ifuel 1"


/// Constants

(** Constants for HPKE labels *)
inline_for_extraction
let size_rfcXXXX: size_nat = 10 // TODO use the actual value // TODO Do I need an empty line after inline_for_extraction?
let rfcXXXX_list : l:list uint8{List.Tot.length l == size_rfcXXXX} =
  [@inline_let]
  let l = [u8 0x68; u8 0x70; u8 0x6b; u8 0x65; u8 0x20; u8 0x6e; u8 0x6f; u8 0x6e; u8 0x63; u8 0x65] in
  assert_norm(List.Tot.length l == size_rfcXXXX);
  l
let rfcXXXX : lbytes size_rfcXXXX = createL rfcXXXX_list

inline_for_extraction
let size_label_dh: size_nat = 10
let label_dh_list : l:list uint8{List.Tot.length l == size_label_dh} =
  [@inline_let]
  let l = [u8 0x68; u8 0x70; u8 0x6b; u8 0x65; u8 0x20; u8 0x6e; u8 0x6f; u8 0x6e; u8 0x63; u8 0x65] in
  assert_norm(List.Tot.length l == size_label_dh);
  l
let label_dh : lbytes size_label_dh = createL label_dh_list

inline_for_extraction
let size_label_prk: size_nat = 10
let label_prk_list : l:list uint8{List.Tot.length l == size_label_prk} =
  [@inline_let]
  let l = [u8 0x68; u8 0x70; u8 0x6b; u8 0x65; u8 0x20; u8 0x6e; u8 0x6f; u8 0x6e; u8 0x63; u8 0x65] in
  assert_norm(List.Tot.length l == size_label_prk);
  l
let label_prk : lbytes size_label_prk = createL label_prk_list

inline_for_extraction
let size_label_nonce: size_nat = 10
let label_nonce_list : l:list uint8{List.Tot.length l == size_label_nonce} =
  [@inline_let]
  let l = [u8 0x68; u8 0x70; u8 0x6b; u8 0x65; u8 0x20; u8 0x6e; u8 0x6f; u8 0x6e; u8 0x63; u8 0x65] in
  assert_norm(List.Tot.length l == size_label_nonce);
  l
let label_nonce : lbytes size_label_nonce = createL label_nonce_list

inline_for_extraction
let size_label_key: size_nat = 8
let label_key_list : l:list uint8{List.Tot.length l == size_label_key} =
  [@inline_let]
  let l = [u8 0x68; u8 0x70; u8 0x6b; u8 0x65; u8 0x20; u8 0x6b; u8 0x65; u8 0x79] in
  assert_norm(List.Tot.length l == size_label_key);
  l
let label_key : lbytes size_label_key = createL label_key_list


/// Types

inline_for_extraction
let size_cs_identifier: size_nat = 6

inline_for_extraction
let size_mode_identifier: size_nat = 1

// TODO This must match the first two and set the id accordingly
val id_kem: cs:ciphersuite -> Tot (lbytes 2)
let id_kem cs = let dh, _, _, _ = cs in
  match dh with
  | DH.DH_P256 -> create 1 (u8 0) @| create 1 (u8 1)
  | DH.DH_Curve25519 -> create 1 (u8 0) @| create 1 (u8 2)

val id_kdf: cs:ciphersuite -> Tot (lbytes 2)
let id_kdf cs = let _, _, _, h = cs in
  match h with
  | Hash.SHA2_256 -> create 1 (u8 0) @| create 1 (u8 1)
  | Hash.SHA2_512 -> create 1 (u8 0) @| create 1 (u8 2)

val id_aead: cs:ciphersuite -> Tot (lbytes 2)
let id_aead cs = let _, _, a, _ = cs in
  match a with
  | AEAD.AES128_GCM -> create 1 (u8 0) @| create 1 (u8 1)
  | AEAD.AES256_GCM -> create 1 (u8 0) @| create 1 (u8 2)
  | AEAD.CHACHA20_POLY1305 -> create 1 (u8 0) @| create 1 (u8 3)


val id_of_cs: cs:ciphersuite -> Tot (lbytes size_cs_identifier)
let id_of_cs cs = id_kem cs @| id_kdf cs @| id_aead cs

// TODO rename to AuthPSK
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

val unmarshal:
    cs:ciphersuite
  -> pk:key_dh_public_s cs ->
  Tot (DH.serialized_point (curve_of_cs cs))

let unmarshal cs pk = match curve_of_cs cs with
  | DH.DH_Curve25519 -> pk
  // Extract the point coordinates by removing the first representation byte
  | DH.DH_P256 -> sub pk 1 64

val marshal:
    cs:ciphersuite
  -> pk:DH.serialized_point (curve_of_cs cs) ->
  Tot (key_dh_public_s cs)

let marshal cs pk = match curve_of_cs cs with
  | DH.DH_Curve25519 -> pk
  // Add the first representation byte to the point coordinates
  | DH.DH_P256 -> create 1 (u8 4) @| pk

//[@"opaque_to_smt"]
//let labeled_extract_pred_ikm (a:Hash.algorithm) (label:bytes) (ikm:bytes) (consts:nat) =
//   Seq.length rfcXXXX + Seq.length label + Seq.length ikm + Spec.Hash.Definitions.block_length a + consts <= Spec.Hash.Definitions.max_input_length a

//let labeled_extract_pred_ikm_elim (a:Hash.algorithm) (label:bytes) (ikm:bytes) (consts:nat) :Lemma
//  (requires labeled_extract_pred_ikm a label ikm consts)
//  (ensures Seq.length rfcXXXX + Seq.length label + Seq.length ikm + Spec.Hash.Definitions.block_length a + consts <= Spec.Hash.Definitions.max_input_length a)
//= ()
////  assert (Seq.length rfcXXXX + Seq.length label + Seq.length ikm + Spec.Hash.Definitions.block_length a + consts <= Spec.Hash.Definitions.max_input_length a) by (FStar.Tactics.fail "foobar")

let labeled_extract_ikm_length_pred (a:Hash.algorithm) (ikm_length:nat) =
  HKDF.extract_ikm_length_pred a (Seq.length rfcXXXX + ikm_length)

val labeled_extract:
    a:Hash.algorithm
  -> salt:bytes
  -> label:bytes
  -> ikm:bytes ->
  Pure (lbytes (Spec.Hash.Definitions.hash_length a))
    (requires
      Spec.Agile.HMAC.keysized a (Seq.length salt) /\
      labeled_extract_ikm_length_pred a (Seq.length label + Seq.length ikm))
    (ensures fun _ -> True)

let labeled_extract a salt label ikm =
//  labeled_extract_pred_ikm_elim a label ikm 0;
  let labeledIKM = Seq.append rfcXXXX label in
  let labeledIKM = Seq.append labeledIKM ikm in
  HKDF.extract a salt labeledIKM

let labeled_expand_info_length_pred (a:Hash.algorithm) (info_length:nat) =
  HKDF.expand_info_length_pred a (2 + Seq.length rfcXXXX + info_length)

val labeled_expand:
    a:Hash.algorithm
  -> prk:bytes
  -> label:bytes
  -> info:bytes
  -> l:size_nat ->
  Pure (lbytes l)
    (requires
      Spec.Hash.Definitions.hash_length a <= Seq.length prk /\
      Spec.Agile.HMAC.keysized a (Seq.length prk) /\
      labeled_expand_info_length_pred a (Seq.length label + Seq.length info) /\
      HKDF.expand_output_length_pred a l)
    (ensures fun _ -> True)

let labeled_expand a prk label info l =
  let labeledInfo = nat_to_bytes_be 2 l in
  let labeledInfo = Seq.append labeledInfo rfcXXXX in
  let labeledInfo = Seq.append labeledInfo label in
  let labeledInfo = Seq.append labeledInfo info in
  HKDF.expand a prk labeledInfo l

let extract_and_expand_dh_pred (cs:ciphersuite) (dh_length:nat) =
  labeled_extract_ikm_length_pred (kem_hash_of_cs cs) (Seq.length label_dh + dh_length)

let extract_and_expand_ctx_pred (cs:ciphersuite) (ctx_length:nat) =
  labeled_expand_info_length_pred (kem_hash_of_cs cs) (Seq.length label_prk + ctx_length)

val extract_and_expand:
    cs:ciphersuite
  -> dh:bytes
  -> kemContext:bytes ->
  Pure (key_kem_s cs)
    (requires
      extract_and_expand_dh_pred cs (Seq.length dh) /\
      extract_and_expand_ctx_pred cs (Seq.length kemContext))
    (ensures fun _ -> True)

let extract_and_expand cs dh kemContext =
  let prk = labeled_extract (kem_hash_of_cs cs) lbytes_empty label_dh dh in
  labeled_expand (kem_hash_of_cs cs) prk label_prk kemContext (size_kem_key cs)

/// def Encap(pkR):
///   skE, pkE = GenerateKeyPair()
///   dh = DH(skE, pkR)
///   enc = Marshal(pkE)
///
///   pkRm = Marshal(pkR)
///   kemContext = concat(enc, pkRm)
///
///  zz = ExtractAndExpand(dh, kemContext)
///  return zz, enc

val encap:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkRm:key_dh_public_s cs -> // TODO the spec has an unmarshaled pkR in the parameters
  Tot (option (key_kem_s cs & key_dh_public_s cs))

#set-options "--z3rlimit 75 --fuel 0 --ifuel 1"
let encap cs skE pkRm =
  match DH.secret_to_public (curve_of_cs cs) skE with
  | None -> None
  | Some pkE ->
    let enc = marshal cs pkE in // TODO rename to marshal and unmarshal
    let pkR = unmarshal cs pkRm in
    match DH.dh (curve_of_cs cs) skE pkR with
    | None -> None
    | Some dh ->
      let kemContext:lbytes (2*size_dh_public cs) = concat enc pkRm in
      let dhm = marshal cs dh in
      assert (Seq.length enc + Seq.length pkRm = Seq.length kemContext);
      assert (extract_and_expand_ctx_pred cs (Seq.length enc + Seq.length pkRm));
      let zz:key_kem_s cs = extract_and_expand cs dhm kemContext in
      Some (zz, enc)

/// def Decap(enc, skR):
///   pkE = Unmarshal(enc)
///   dh = DH(skR, pkE)
/// 
///   pkRm = Marshal(pk(skR))
///   kemContext = concat(enc, pkRm)
/// 
///   zz = ExtractAndExpand(dh, kemContext)
///   return zz

val decap:
    cs: ciphersuite
  -> enc: key_dh_public_s cs
  -> skR: key_dh_secret_s cs ->
  Tot (option (key_kem_s cs))

let decap cs enc skR =
  let pkE = unmarshal cs enc in
  match DH.dh (curve_of_cs cs) skR pkE with
  | None -> None
  | Some dh ->
    match DH.secret_to_public (curve_of_cs cs) skR with
    | None -> None
    | Some pkR ->
      let pkRm = marshal cs pkR in
      let kemContext:lbytes (2*size_dh_public cs) = concat enc pkRm in
      let dhm = marshal cs dh in
      assert (Seq.length enc + Seq.length pkRm = Seq.length kemContext);
      assert (extract_and_expand_ctx_pred cs (Seq.length kemContext));
      let zz = extract_and_expand cs dhm kemContext in
      Some (zz)

// TODO Correctness lemma for encap/decap?

/// def AuthEncap(pkR, skS):
///   skE, pkE = GenerateKeyPair()
///   dh = concat(DH(skE, pkR), DH(skS, pkR))
///   enc = Marshal(pkE)
///
///   pkRm = Marshal(pkR)
///   pkSm = Marshal(pk(skS))
///   kemContext = concat(enc, pkRm, pkSm)
///
///   zz = ExtractAndExpand(dh, kemContext)
///   return zz, enc

val auth_encap:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkRm:key_dh_public_s cs
  -> skS:key_dh_secret_s cs ->
  Tot (option (key_kem_s cs & key_dh_public_s cs))

#set-options "--z3rlimit 75 --fuel 0 --ifuel 2"
let auth_encap cs skE pkRm skS =
  match DH.secret_to_public (curve_of_cs cs) skE with
  | None -> None
  | Some pkE ->
    let pkR = unmarshal cs pkRm in
    match DH.dh (curve_of_cs cs) skE pkR with
    | None -> None
    | Some es ->
      match DH.dh (curve_of_cs cs) skS pkR with
      | None -> None
      | Some ss ->
        let esm = marshal cs es in
        let ssm = marshal cs ss in
        let dh = concat esm ssm in
        let enc = marshal cs pkE in
        match DH.secret_to_public (curve_of_cs cs) skE with
        | None -> None
        | Some pkS ->
          let pkSm = marshal cs pkS in
          let kemContext:lbytes (3*size_dh_public cs) = concat enc (concat pkRm pkSm) in
          assert (Seq.length enc + Seq.length pkRm + Seq.length pkSm = Seq.length kemContext);
          assert (extract_and_expand_ctx_pred cs (Seq.length kemContext));
          assert (Seq.length dh = 2*size_dh_public cs);
          assert (extract_and_expand_dh_pred cs (Seq.length dh));
          let zz = extract_and_expand cs dh kemContext in
          Some (zz, enc)

/// def AuthDecap(enc, skR, pkS):
///   pkE = Unmarshal(enc)
///   dh = concat(DH(skR, pkE), DH(skR, pkS))
///
///   pkRm = Marshal(pk(skR))
///   pkSm = Marshal(pkS)
///   kemContext = concat(enc, pkRm, pkSm)
///
///   zz = ExtractAndExpand(dh, kemContext)
///   return zz

val auth_decap:
    cs: ciphersuite
  -> enc: key_dh_public_s cs
  -> skR: key_dh_secret_s cs
  -> pkSm: key_dh_public_s cs ->
  Tot (option (key_kem_s cs))

#set-options "--z3rlimit 75 --fuel 0 --ifuel 2"
let auth_decap cs enc skR pkSm = // TODO the function should take an unmarshaled key
  let pkE = unmarshal cs enc in
  match DH.dh (curve_of_cs cs) skR pkE with
  | None -> None
  | Some es ->
    let pkS = unmarshal cs pkSm in
    match DH.dh (curve_of_cs cs) skR pkS with
    | None -> None
    | Some ss ->
      let esm = marshal cs es in
      let ssm = marshal cs ss in
      let dh = concat esm ssm in
      let enc = marshal cs pkE in
      match DH.secret_to_public (curve_of_cs cs) skR with
      | None -> None
      | Some pkR ->
        let pkRm = marshal cs pkR in
        let kemContext:lbytes (3*size_dh_public cs) = concat enc (concat pkRm pkSm) in
        assert (Seq.length enc + Seq.length pkRm + Seq.length pkSm = Seq.length kemContext);
        assert (extract_and_expand_ctx_pred cs (Seq.length kemContext));
        assert (Seq.length dh = 2*size_dh_public cs);
        assert (extract_and_expand_dh_pred cs (Seq.length dh));
        let zz = extract_and_expand cs dh kemContext in
        Some (zz)

/// default_pkIm = zero(Npk)
/// default_psk = zero(Nh)
/// default_pskId = zero(0)

let default_pkSm (cs:ciphersuite):bytes = create (size_dh_public cs) (u8 0)
let default_psk (cs:ciphersuite):bytes = create (size_psk cs) (u8 0)
let default_pskID: b:bytes{Seq.length b = 0} = lbytes_empty


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
    m:mode
  -> cs:ciphersuite
  -> pkE:key_dh_public_s cs
  -> pkR:key_dh_public_s cs
  -> pkI:key_dh_public_s cs
  -> pskID_hash:bytes{Seq.length pskID_hash = Hash.size_hash (hash_of_cs cs)}
  -> info_hash:bytes{Seq.length info_hash = Hash.size_hash (hash_of_cs cs)} ->
  Tot (b:bytes{Seq.length b == 7 + 3 * size_dh_public cs + 2 * Hash.size_hash (hash_of_cs cs) })

let build_context m cs pkE pkR pkI pskID_hash info_hash =
  let pskID_len: lbytes 1 = nat_to_bytes_be 1 (Hash.size_hash (hash_of_cs cs)) in
  let info_len: lbytes 1 = nat_to_bytes_be 1 (Hash.size_hash (hash_of_cs cs)) in
  let context = (id_of_mode m) @| (id_of_cs cs) @| pkE @| pkR @| pkI in
  let context = Seq.append context pskID_hash in
  let context = Seq.append context info_hash in
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

#push-options "--z3rlimit 50"
let ks_derive cs m pkR zz pkE info opsk opkI =
  let (psk, pskID) =
    match opsk with
    | None -> (default_psk cs, default_pskId)
    | Some (psk, pskID) -> (psk, pskID) in
  let pkI =
    match opkI with
    | None -> default_pkI cs
    | Some pki -> pki in
  let pskID_hash = Hash.hash (hash_of_cs cs) pskID in
  let info_hash = Hash.hash (hash_of_cs cs) info in
  let context = build_context m cs pkE pkR pkI pskID_hash info_hash in
  let secret = HKDF.extract (hash_of_cs cs) psk zz in
  let info_key = Seq.append label_key context in
  let info_nonce = Seq.append label_nonce context in
  let keyIR = HKDF.expand (hash_of_cs cs) secret info_key (size_aead_key cs) in
  let nonceIR = HKDF.expand (hash_of_cs cs) secret info_nonce (size_aead_nonce cs) in
  keyIR, nonceIR
#pop-options

/// def SetupBaseI(pkR, info):
///     zz, enc = Encap(pkR)
///     return enc, KeySchedule(mode_base, pkR, zz, enc, info,
///                             default_psk, default_pskID, default_pkIm)

let setupBaseS cs skE pkR info =
  let res = encap cs skE pkR in
  match res with
  | Some (zz, pkE) ->
    let k,n = ks_derive cs Base pkR zz pkE info None None in
    Some (pkE, k, n)
  | None -> None


/// def SetupBaseR(enc, skR, info):
///     zz = Decap(enc, skR)
///     return KeySchedule(mode_base, pk(skR), zz, enc, info,
///                        default_psk, default_pskID, default_pkIm)

let setupBaseR cs pkE skR info =
  let pkR = DH.secret_to_public (curve_of_cs cs) skR in
  let zz = decap cs pkE skR in
  match pkR, zz with
  | Some pkR, Some zz ->
    Some (ks_derive cs Base (marshal cs pkR) zz pkE info None None)
  | _ -> None


/// def SetupAuthI(pkR, skI, info):
///     zz, enc = AuthEncap(pkR, skI)
///     pkIm = Marshal(pk(skI))
///     return enc, KeySchedule(pkR, zz, enc, info,
///                             default_psk, default_pskID, pkIm)

val setupAuthS:
    cs:ciphersuite
  -> skE: key_dh_secret_s cs
  -> skI: key_dh_secret_s cs
  -> pkR:key_dh_public_s cs
  -> info:bytes{Seq.length info <= max_info} ->
  Tot (option (key_dh_public_s cs & key_aead_s cs & nonce_aead_s cs))

let setupAuthS cs skE skI pkR info =
  let pkI = DH.secret_to_public (curve_of_cs cs) skI in
  let res = auth_encap cs skE skI pkR in
  match pkI, res with
  | Some pkI, Some (zz, pkE) ->
    let k, n = ks_derive cs Auth pkR zz pkE info None (Some (marshal cs pkI)) in
    Some (pkE, k, n)
  | _ -> None


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
  Tot (option (key_aead_s cs & nonce_aead_s cs))

let setupAuthR cs pkE pkI skR info =
  let pkR = DH.secret_to_public (curve_of_cs cs) skR in
  let zz = auth_decap cs pkE pkI skR in
  match pkR, zz with
  | Some pkR, Some zz ->
    Some (ks_derive cs Auth (marshal cs pkR) zz pkE info None (Some pkI))
  | _ -> None

/// def SetupAuthPSKI(pkR, info, psk, pskID, skI):
///     zz, enc = AuthEncap(pkR, skI)
///     pkIm = Marshal(pk(skI))
///     return enc, KeySchedule(mode_psk_auth, pkR, zz, enc, info, psk, pskID, pkIm)

val setupAuthPSKS:
    cs:ciphersuite
  -> skE: key_dh_secret_s cs
  -> skI: key_dh_secret_s cs
  -> pkR: key_dh_public_s cs
  -> psk: psk_s cs
  -> pskID: bytes{Seq.length pskID <= max_pskID}
  -> info:bytes{Seq.length info <= max_info} ->
  Tot (option (key_dh_public_s cs & key_aead_s cs & nonce_aead_s cs))

let setupAuthPSKS cs skE skI pkR psk pskID info =
  let pkI = DH.secret_to_public (curve_of_cs cs) skI in
  let res = auth_encap cs skE skI pkR in
  match pkI, res with
  | Some pkI, Some (zz, pkE) ->
    let k, n = ks_derive cs PSKAuth pkR zz pkE info (Some (psk, pskID)) (Some (marshal cs pkI)) in
    Some (pkE, k, n)
  | _ -> None


/// def SetupAuthPSKR(enc, skR, info, psk, pskID, pkI):
///     zz = AuthDecap(enc, skR, pkI)
///     pkIm = Marshal(pkI)
///     return KeySchedule(mode_psk_auth, pk(skR), zz, enc, info, psk, pskID, pkIm)

val setupAuthPSKR:
    cs:ciphersuite
  -> pkE: key_dh_public_s cs
  -> pkI: key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> psk: psk_s cs
  -> pskID: bytes{Seq.length pskID <= max_pskID}
  -> info:bytes{Seq.length info <= max_info} ->
  Tot (option (key_aead_s cs & nonce_aead_s cs))

let setupAuthPSKR cs pkE pkI skR psk pskID info =
  let pkR = DH.secret_to_public (curve_of_cs cs) skR in
  let zz = auth_decap cs pkE pkI skR in
  match pkR, zz with
  | Some pkR, Some zz ->
    Some (ks_derive cs PSKAuth (marshal cs pkR) zz pkE info (Some (psk, pskID)) (Some pkI))
  | _ -> None


/// Encrypt() and Decrypt using the derived AEAD key and nonce
/// are implemented by calling AEAD.encrypt and AEAD.Decrypt

#set-options "--z3rlimit 50"

let sealBase cs skE pkR m info =
  match setupBaseS cs skE pkR info with
  | Some (pkE,k,n) ->
    Some (Seq.append pkE (AEAD.encrypt #(aead_of_cs cs) k n info m))
  | None -> None

let openBase cs skR input info =
  let pkE = sub #uint8 #(Seq.length input) input 0 (size_dh_public cs) in
  let c = sub #uint8 #(Seq.length input) input (size_dh_public cs) (length input - (size_dh_public cs)) in
  match setupBaseR cs pkE skR info with
  | Some (k,n) -> begin
    match AEAD.decrypt #(aead_of_cs cs) k n info c with
    | None -> None
    | Some v -> Some v
    end
  | None -> None
