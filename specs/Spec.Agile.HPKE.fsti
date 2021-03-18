module Spec.Agile.HPKE

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

module DH = Spec.Agile.DH
//module DHKEM = Spec.Agile.DHKEM
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash
module HKDF = Spec.Agile.HKDF

#set-options "--z3rlimit 20 --fuel 0 --ifuel 1"

let is_valid_kem = function
  | DH.DH_Curve25519, Hash.SHA2_256
  | DH.DH_P256,       Hash.SHA2_256 -> true
  | _,_ -> false

noeq type aead =
  | Seal: alg:AEAD.alg -> aead
  | ExportOnly

let is_valid_aead = function
  | Seal AEAD.AES128_GCM
  | Seal AEAD.AES256_GCM
  | Seal AEAD.CHACHA20_POLY1305
  | ExportOnly -> true
  | _ -> false

let is_valid_hash = function
  | Hash.SHA2_256
  | Hash.SHA2_384
  | Hash.SHA2_512 -> true
  | _ -> false

let hash_algorithm = a:Hash.algorithm{is_valid_hash a}
// TODO define the following two. KEM should be separated
//let aead_algorithm = a:AEAD.alg{is_valid_aead a}
//let dh_algorithm = a:DH.algorithm{is_valid_dh a}

let is_valid_ciphersuite (cs:DH.algorithm & hash_algorithm & aead & Hash.algorithm) : bool =
  let kem_dh, kem_hash, aead, hash = cs in
  (is_valid_kem (kem_dh, kem_hash)) && (is_valid_aead aead) && (is_valid_hash hash)

let ciphersuite = cs:(DH.algorithm & hash_algorithm & aead & Hash.algorithm){is_valid_ciphersuite cs}

// TODO rename to dh_of_cs or kemdh or dhkem
let curve_of_cs (cs:ciphersuite) : DH.algorithm =
  let (c,_,_,_) = cs in c

let kem_hash_of_cs (cs:ciphersuite) : hash_algorithm =
  let (_,h,_,_) = cs in h

let aead_of_cs (cs:ciphersuite) : aead =
  let (_,_,a,_) = cs in a

let hash_of_cs (cs:ciphersuite) : hash_algorithm =
  let (_,_,_,h) = cs in h

// TODO rename to AuthPSK
type mode =
  | Base
  | PSK
  | Auth
  | AuthPSK
/// Constants

(** Constants for HPKE labels *)

// generated: "HPKE-v1"
inline_for_extraction
let size_label_version: size_nat = 7
let label_version_list : l:list uint8{List.Tot.length l == size_label_version} =
  [@inline_let]
  let l = [u8 0x48; u8 0x50; u8 0x4b; u8 0x45; u8 0x2d; u8 0x76; u8 0x31] in
  assert_norm(List.Tot.length l == size_label_version);
  l
let label_version : lbytes size_label_version = createL label_version_list


// generated: "eae_prk"
inline_for_extraction
let size_label_eae_prk: size_nat = 7
let label_eae_prk_list : l:list uint8{List.Tot.length l == size_label_eae_prk} =
  [@inline_let]
  let l = [u8 0x65; u8 0x61; u8 0x65; u8 0x5f; u8 0x70; u8 0x72; u8 0x6b] in
  assert_norm(List.Tot.length l == size_label_eae_prk);
  l
let label_eae_prk : lbytes size_label_eae_prk = createL label_eae_prk_list


// generated: "KEM"
inline_for_extraction
let size_label_KEM: size_nat = 3
let label_KEM_list : l:list uint8{List.Tot.length l == size_label_KEM} =
  [@inline_let]
  let l = [u8 0x4b; u8 0x45; u8 0x4d] in
  assert_norm(List.Tot.length l == size_label_KEM);
  l
let label_KEM : lbytes size_label_KEM = createL label_KEM_list


// generated: "HPKE"
inline_for_extraction
let size_label_HPKE: size_nat = 4
let label_HPKE_list : l:list uint8{List.Tot.length l == size_label_HPKE} =
  [@inline_let]
  let l = [u8 0x48; u8 0x50; u8 0x4b; u8 0x45] in
  assert_norm(List.Tot.length l == size_label_HPKE);
  l
let label_HPKE : lbytes size_label_HPKE = createL label_HPKE_list


// generated: "shared_secret"
inline_for_extraction
let size_label_shared_secret: size_nat = 13
let label_shared_secret_list : l:list uint8{List.Tot.length l == size_label_shared_secret} =
  [@inline_let]
  let l = [u8 0x73; u8 0x68; u8 0x61; u8 0x72; u8 0x65; u8 0x64; u8 0x5f; u8 0x73; u8 0x65; u8 0x63; u8 0x72; u8 0x65; u8 0x74] in
  assert_norm(List.Tot.length l == size_label_shared_secret);
  l
let label_shared_secret : lbytes size_label_shared_secret = createL label_shared_secret_list


// generated: "psk_id_hash"
inline_for_extraction
let size_label_psk_id_hash: size_nat = 11
let label_psk_id_hash_list : l:list uint8{List.Tot.length l == size_label_psk_id_hash} =
  [@inline_let]
  let l = [u8 0x70; u8 0x73; u8 0x6b; u8 0x5f; u8 0x69; u8 0x64; u8 0x5f; u8 0x68; u8 0x61; u8 0x73; u8 0x68] in
  assert_norm(List.Tot.length l == size_label_psk_id_hash);
  l
let label_psk_id_hash : lbytes size_label_psk_id_hash = createL label_psk_id_hash_list


// generated: "info_hash"
inline_for_extraction
let size_label_info_hash: size_nat = 9
let label_info_hash_list : l:list uint8{List.Tot.length l == size_label_info_hash} =
  [@inline_let]
  let l = [u8 0x69; u8 0x6e; u8 0x66; u8 0x6f; u8 0x5f; u8 0x68; u8 0x61; u8 0x73; u8 0x68] in
  assert_norm(List.Tot.length l == size_label_info_hash);
  l
let label_info_hash : lbytes size_label_info_hash = createL label_info_hash_list


// generated: "secret"
inline_for_extraction
let size_label_secret: size_nat = 6
let label_secret_list : l:list uint8{List.Tot.length l == size_label_secret} =
  [@inline_let]
  let l = [u8 0x73; u8 0x65; u8 0x63; u8 0x72; u8 0x65; u8 0x74] in
  assert_norm(List.Tot.length l == size_label_secret);
  l
let label_secret : lbytes size_label_secret = createL label_secret_list


// generated: "key"
inline_for_extraction
let size_label_key: size_nat = 3
let label_key_list : l:list uint8{List.Tot.length l == size_label_key} =
  [@inline_let]
  let l = [u8 0x6b; u8 0x65; u8 0x79] in
  assert_norm(List.Tot.length l == size_label_key);
  l
let label_key : lbytes size_label_key = createL label_key_list


// generated: "base_nonce"
inline_for_extraction
let size_label_base_nonce: size_nat = 10
let label_base_nonce_list : l:list uint8{List.Tot.length l == size_label_base_nonce} =
  [@inline_let]
  let l = [u8 0x62; u8 0x61; u8 0x73; u8 0x65; u8 0x5f; u8 0x6e; u8 0x6f; u8 0x6e; u8 0x63; u8 0x65] in
  assert_norm(List.Tot.length l == size_label_base_nonce);
  l
let label_base_nonce : lbytes size_label_base_nonce = createL label_base_nonce_list


// generated: "exp"
inline_for_extraction
let size_label_exp: size_nat = 3
let label_exp_list : l:list uint8{List.Tot.length l == size_label_exp} =
  [@inline_let]
  let l = [u8 0x65; u8 0x78; u8 0x70] in
  assert_norm(List.Tot.length l == size_label_exp);
  l
let label_exp : lbytes size_label_exp = createL label_exp_list


// generated: "sec"
inline_for_extraction
let size_label_sec: size_nat = 3
let label_sec_list : l:list uint8{List.Tot.length l == size_label_sec} =
  [@inline_let]
  let l = [u8 0x73; u8 0x65; u8 0x63] in
  assert_norm(List.Tot.length l == size_label_sec);
  l
let label_sec : lbytes size_label_sec = createL label_sec_list


// generated: "dkp_prk"
inline_for_extraction
let size_label_dkp_prk: size_nat = 7
let label_dkp_prk_list : l:list uint8{List.Tot.length l == size_label_dkp_prk} =
  [@inline_let]
  let l = [u8 0x64; u8 0x6b; u8 0x70; u8 0x5f; u8 0x70; u8 0x72; u8 0x6b] in
  assert_norm(List.Tot.length l == size_label_dkp_prk);
  l
let label_dkp_prk : lbytes size_label_dkp_prk = createL label_dkp_prk_list


// generated: "candidate"
inline_for_extraction
let size_label_candidate: size_nat = 9
let label_candidate_list : l:list uint8{List.Tot.length l == size_label_candidate} =
  [@inline_let]
  let l = [u8 0x63; u8 0x61; u8 0x6e; u8 0x64; u8 0x69; u8 0x64; u8 0x61; u8 0x74; u8 0x65] in
  assert_norm(List.Tot.length l == size_label_candidate);
  l
let label_candidate : lbytes size_label_candidate = createL label_candidate_list


// generated: "sk"
inline_for_extraction
let size_label_sk: size_nat = 2
let label_sk_list : l:list uint8{List.Tot.length l == size_label_sk} =
  [@inline_let]
  let l = [u8 0x73; u8 0x6b] in
  assert_norm(List.Tot.length l == size_label_sk);
  l
let label_sk : lbytes size_label_sk = createL label_sk_list



let is_valid_not_export_only_ciphersuite (cs:ciphersuite) : bool =
  match aead_of_cs cs with
  | ExportOnly -> false
  | Seal _ -> true

let ciphersuite_not_export_only = cs:ciphersuite{is_valid_not_export_only_ciphersuite cs}

let aead_alg_of (cs:ciphersuite_not_export_only) = match aead_of_cs cs with
  | Seal alg -> alg


///
/// Constants sizes
///

inline_for_extraction
let size_aead_nonce (cs:ciphersuite): size_nat =
  assert_norm (8 * 12 <= pow2 64 - 1);
  match aead_of_cs cs with
  | ExportOnly -> 0
  | Seal _ -> 12

inline_for_extraction
let size_aead_key (cs:ciphersuite): size_nat =
  match aead_of_cs cs with
  | ExportOnly -> 0
  | Seal _ -> AEAD.key_length (aead_alg_of cs)

inline_for_extraction
let size_aead_tag (cs:ciphersuite): size_nat =
  match aead_of_cs cs with
  | ExportOnly -> 0
  | Seal _ -> AEAD.tag_length (aead_alg_of cs)

inline_for_extraction
let size_dh_key (cs:ciphersuite): size_nat = DH.size_key (curve_of_cs cs)

inline_for_extraction
let size_dh_public (cs:ciphersuite): size_nat = match curve_of_cs cs with
  | DH.DH_Curve25519 -> DH.size_public DH.DH_Curve25519
  | DH.DH_P256 -> DH.size_public DH.DH_P256 + 1 // Need the additional byte for representation
// TODO shouldn't the extra byte be handled inside the P256 module?

inline_for_extraction
let size_kem_kdf (cs:ciphersuite): size_nat = Hash.size_hash (kem_hash_of_cs cs)
// TODO size_...

inline_for_extraction
let size_kem_key (cs:ciphersuite): size_nat = Hash.size_hash (kem_hash_of_cs cs)

inline_for_extraction
let size_kdf (cs:ciphersuite): size_nat = Hash.size_hash (hash_of_cs cs)

let max_seq (cs:ciphersuite): nat =
  match aead_of_cs cs with
  | ExportOnly -> 0
  | Seal _ -> pow2 (8*(size_aead_nonce cs)) - 1

inline_for_extraction
let size_suite_id_kem: size_nat = size_label_KEM + 2

inline_for_extraction
let size_suite_id_hpke: size_nat = size_label_HPKE + 6

inline_for_extraction
let size_mode_identifier: size_nat = 1

let size_ks_ctx (cs:ciphersuite): size_nat = size_mode_identifier + 2*(size_kdf cs)

// TODO
(* let keysized (a:hash_alg) (l:nat) = *)
(*   l <= max_input_length a /\ *)
(*   l + block_length a < pow2 32 *)

let labeled_extract_ikm_length_pred (a:hash_algorithm) (ikm_length:nat) =
  HKDF.extract_ikm_length_pred a (size_label_version + ikm_length)

// TODO this should not be exposed
val labeled_extract:
    a:hash_algorithm
  -> suite_id:bytes
  -> salt:bytes
  -> label:bytes
  -> ikm:bytes ->
  Pure (lbytes (Spec.Hash.Definitions.hash_length a))
    (requires
      Spec.Agile.HMAC.keysized a (Seq.length salt) /\
      labeled_extract_ikm_length_pred a (Seq.length suite_id + Seq.length label + Seq.length ikm))
    (ensures fun _ -> True)

let labeled_expand_info_length_pred (a:hash_algorithm) (info_length:nat) =
  HKDF.expand_info_length_pred a (2 + size_label_version + info_length)

// TODO this should not be exposed
val labeled_expand:
    a:hash_algorithm
  -> suite_id:bytes
  -> prk:bytes
  -> label:bytes
  -> info:bytes
  -> l:size_nat ->
  Pure (lbytes l)
    (requires
      Spec.Hash.Definitions.hash_length a <= Seq.length prk /\
      Spec.Agile.HMAC.keysized a (Seq.length prk) /\
      labeled_expand_info_length_pred a (Seq.length suite_id + Seq.length label + Seq.length info) /\
      HKDF.expand_output_length_pred a l)
    (ensures fun _ -> True)

let pow2_61_1 : _:unit{pow2 61 - 1 == 2305843009213693951} = assert_norm(pow2 61 - 1 == 2305843009213693951)
let pow2_125_1 : _:unit{pow2 125 - 1 == 42535295865117307932921825928971026431} = assert_norm(pow2 125 - 1 == 42535295865117307932921825928971026431)

// TODO maybe functional equivalence should be proven with Spec.Hash.Definitions.max_input_length
// TODO this could be restricted to hash_algorithms valid in HPKE
let hash_max_input_length (a:hash_algorithm) =
  match a with
  | Hash.MD5 | Hash.SHA1
  | Hash.SHA2_224 | Hash.SHA2_256 -> 2305843009213693951 // pow2 61 - 1
  | Hash.SHA2_384 | Hash.SHA2_512 -> 42535295865117307932921825928971026431 // pow2 125 - 1

let labeled_extract_max_length_ikm (a:hash_algorithm) (size_suite_id:size_nat) (size_local_label:size_nat) =
  hash_max_input_length a - size_label_version - size_suite_id - size_local_label - Spec.Hash.Definitions.block_length a

let labeled_expand_max_length_info (a:hash_algorithm) (size_suite_id:size_nat) (size_local_label:size_nat) =
  hash_max_input_length a - Spec.Hash.Definitions.hash_length a - 2 - size_label_version - size_suite_id - size_local_label - 1 - Spec.Hash.Definitions.block_length a

let max_length_psk (a:hash_algorithm) = labeled_extract_max_length_ikm a size_suite_id_hpke size_label_secret
let max_length_psk_id (a:hash_algorithm) = labeled_extract_max_length_ikm a size_suite_id_hpke size_label_psk_id_hash
let max_length_info (a:hash_algorithm) = labeled_extract_max_length_ikm a size_suite_id_hpke size_label_info_hash
let max_length_exp_ctx (a:hash_algorithm) = labeled_expand_max_length_info a size_suite_id_hpke size_label_sec
let max_length_dkp_ikm (a:hash_algorithm) = labeled_extract_max_length_ikm a size_suite_id_kem size_label_dkp_prk

/// Types

type key_dh_public_s (cs:ciphersuite) = lbytes (size_dh_public cs)
type key_dh_secret_s (cs:ciphersuite) = lbytes (size_dh_key cs)
type key_kem_s (cs:ciphersuite) = lbytes (size_kem_key cs) // TODO This is true for the current DHKEM. It would be nice to have it modular depending on the KEM.
type key_aead_s (cs:ciphersuite) = lbytes (size_aead_key cs)
type nonce_aead_s (cs:ciphersuite) = lbytes (size_aead_nonce cs)
type seq_aead_s (cs:ciphersuite) = n:nat{n <= max_seq cs}
type exporter_secret_s (cs:ciphersuite) = lbytes (size_kdf cs)
(* let max_length_psk: size_nat = 65535 *)
(* let max_length_psk_id: size_nat = 65535 *)
(* let max_length_info: size_nat = 65535 *)
(* let max_length_exp_ctx: size_nat = 65535 *)
// could we use normalization or smth else to compute the maximum bounds for each cs?
(* type psk_s (cs:ciphersuite) = b:bytes{labeled_extract_ikm_length_pred (hash_of_cs cs) (size_label_psk_hash + Seq.length b)} *)
(* type psk_id_s (cs:ciphersuite) = b:bytes{labeled_extract_ikm_length_pred (hash_of_cs cs) (size_label_psk_id_hash + Seq.length b)} *)
(* type info_s (cs:ciphersuite) = b:bytes{labeled_extract_ikm_length_pred (hash_of_cs cs) (size_label_info_hash + Seq.length b)} *)
(* type exp_ctx_s (cs:ciphersuite) = b:bytes{labeled_expand_info_length_pred (hash_of_cs cs) (size_label_sec + Seq.length b)} *)
type psk_s (cs:ciphersuite) =     b:bytes{Seq.length b >= 32 /\ Seq.length b <= max_length_psk (hash_of_cs cs)}
type psk_id_s (cs:ciphersuite) =   b:bytes{Seq.length b >= 1 /\ Seq.length b <= max_length_psk_id (hash_of_cs cs)}
type info_s (cs:ciphersuite) =    b:bytes{Seq.length b <= max_length_info (hash_of_cs cs)}
type exp_ctx_s (cs:ciphersuite) = b:bytes{Seq.length b <= max_length_exp_ctx (hash_of_cs cs)}
type dkp_ikm_s (cs:ciphersuite) = b:bytes{Seq.length b <= max_length_dkp_ikm (kem_hash_of_cs cs) /\ Seq.length b >= size_dh_key cs}
(* type psk_s (cs:ciphersuite) = b:bytes{Seq.length b <= max_length_psk} *)
(* type psk_id_s (cs:ciphersuite) = b:bytes{Seq.length b <= max_length_psk_id} *)
(* type info_s (cs:ciphersuite) = b:bytes{Seq.length b <= max_length_info} *)
(* type exp_ctx_s (cs:ciphersuite) = b:bytes{Seq.length b <= max_length_exp_ctx} *)

// TODO public keys should be more abstract to prepare for other KEMs
// TODO This looks weird: _de_serialize function returns a _serialized_ point.
//      Well, ok, understood: HPKE has _another_ format (the stupid extra byte).
val deserialize_public_key:
    cs:ciphersuite // TODO could this be an implicit parameter?
  -> pk:key_dh_public_s cs ->
  Tot (DH.serialized_point (curve_of_cs cs))

val serialize_public_key:
    cs:ciphersuite
  -> pk:DH.serialized_point (curve_of_cs cs) ->
  Tot (key_dh_public_s cs)

val derive_key_pair:
    cs:ciphersuite
  -> ikm:dkp_ikm_s cs ->
  Tot (option (key_dh_secret_s cs & key_dh_public_s cs))
// TODO annotate this saying it does not return None for Curve25519.


(* noeq type encryption_context_export_only (cs:ciphersuite_export_only) =
  | ExportOnlyContext: exp:exporter_secret_s cs -> encryption_context_export_only cs *)

// TODO can we hide the contents of encryption_context, i.e. not
//      expose them in this fsti, to avoid usage which is not
//      conform with the spec?
//      -> just declare a Type0 and only detail it in the fst, as a constructed type.
// TODO encode in a refinement that key and nonce will be zero-length if AEAD is Export-Only
// TODO maybe rename to _state (because it is not a context that gets hashed into smth)
// TODO This name is bad because it is also used for context_export
let encryption_context (cs:ciphersuite) = key_aead_s cs & nonce_aead_s cs & seq_aead_s cs & exporter_secret_s cs


let exp_len (cs:ciphersuite) = l:size_nat{HKDF.expand_output_length_pred (hash_of_cs cs) l}

val context_export:
    cs:ciphersuite
  -> ctx:encryption_context cs
  -> exp_ctx:exp_ctx_s cs // TODO replace this by a pre-condition that uses labeled_expand predicates
  -> l:exp_len cs ->
  Tot (lbytes l)

val context_compute_nonce:
    cs:ciphersuite_not_export_only
  -> ctx:encryption_context cs
  -> seq:seq_aead_s cs ->
  Tot (nonce_aead_s cs)

val context_increment_seq:
    cs:ciphersuite_not_export_only
  -> ctx:encryption_context cs ->
  Tot (option (encryption_context cs))

val context_seal:
    cs:ciphersuite_not_export_only
  -> ctx:encryption_context cs
  -> aad:AEAD.ad (aead_alg_of cs)
  -> pt:AEAD.plain (aead_alg_of cs) ->
  Tot (option (encryption_context cs & AEAD.cipher (aead_alg_of cs)))

val context_open:
    cs:ciphersuite_not_export_only
  -> ctx:encryption_context cs
  -> aad:AEAD.ad (aead_alg_of cs)
  -> ct:AEAD.cipher (aead_alg_of cs) ->
  Tot (option (encryption_context cs & AEAD.plain (aead_alg_of cs)))

val setupBaseS:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (curve_of_cs cs)
  -> info:info_s cs ->
  Tot (option (key_dh_public_s cs & encryption_context cs))

val setupBaseR:
    cs:ciphersuite
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs ->
  Tot (option (encryption_context cs))

val sealBase:
    cs:ciphersuite_not_export_only
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (curve_of_cs cs)
  -> info:info_s cs
  -> aad:AEAD.ad (aead_alg_of cs)
  -> pt:AEAD.plain (aead_alg_of cs) ->
  Tot (option (key_dh_public_s cs & AEAD.encrypted #(aead_alg_of cs) pt))

val openBase:
    cs:ciphersuite_not_export_only
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> aad:AEAD.ad (aead_alg_of cs)
  -> ct:AEAD.cipher (aead_alg_of cs) ->
  Tot (option (AEAD.decrypted #(aead_alg_of cs) ct))

val sendExportBase:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (curve_of_cs cs)
  -> info:info_s cs
  -> exp_ctx:exp_ctx_s cs
  -> l:exp_len cs ->
  Tot (option (key_dh_public_s cs & lbytes l))

val receiveExportBase:
    cs:ciphersuite
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> exp_ctx:exp_ctx_s cs
  -> l:exp_len cs ->
  Tot (option (lbytes l))

val setupPSKS:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (curve_of_cs cs)
  -> info:info_s cs
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs ->
  Tot (option (key_dh_public_s cs & encryption_context cs))

val setupPSKR:
    cs:ciphersuite
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs ->
  Tot (option (encryption_context cs))

val sealPSK:
    cs:ciphersuite_not_export_only
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (curve_of_cs cs)
  -> info:info_s cs
  -> aad:AEAD.ad (aead_alg_of cs)
  -> pt:AEAD.plain (aead_alg_of cs)
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs ->
  Tot (option (key_dh_public_s cs & AEAD.encrypted #(aead_alg_of cs) pt))

val openPSK:
    cs:ciphersuite_not_export_only
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> aad:AEAD.ad (aead_alg_of cs)
  -> ct:AEAD.cipher (aead_alg_of cs)
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs ->
  Tot (option (AEAD.decrypted #(aead_alg_of cs) ct))

val sendExportPSK:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (curve_of_cs cs)
  -> info:info_s cs
  -> exp_ctx:exp_ctx_s cs
  -> l:exp_len cs
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs ->
  Tot (option (key_dh_public_s cs & lbytes l))

val receiveExportPSK:
    cs:ciphersuite
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> exp_ctx:exp_ctx_s cs
  -> l:exp_len cs
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs ->
  Tot (option (lbytes l))

val setupAuthS:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (curve_of_cs cs)
  -> info:info_s cs
  -> skS:key_dh_secret_s cs ->
  Tot (option (key_dh_public_s cs & encryption_context cs))

val setupAuthR:
    cs:ciphersuite
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> pkS:DH.serialized_point (curve_of_cs cs) ->
  Tot (option (encryption_context cs))

val sealAuth:
    cs:ciphersuite_not_export_only
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (curve_of_cs cs)
  -> info:info_s cs
  -> aad:AEAD.ad (aead_alg_of cs)
  -> pt:AEAD.plain (aead_alg_of cs)
  -> skS:key_dh_secret_s cs ->
  Tot (option (key_dh_public_s cs & AEAD.encrypted #(aead_alg_of cs) pt))

val openAuth:
    cs:ciphersuite_not_export_only
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> aad:AEAD.ad (aead_alg_of cs)
  -> ct:AEAD.cipher (aead_alg_of cs)
  -> pkS:DH.serialized_point (curve_of_cs cs) ->
  Tot (option (AEAD.decrypted #(aead_alg_of cs) ct))

val sendExportAuth:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (curve_of_cs cs)
  -> info:info_s cs
  -> exp_ctx:exp_ctx_s cs
  -> l:exp_len cs
  -> skS:key_dh_secret_s cs ->
  Tot (option (key_dh_public_s cs & lbytes l))

val receiveExportAuth:
    cs:ciphersuite
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> exp_ctx:exp_ctx_s cs
  -> l:exp_len cs
  -> pkS:DH.serialized_point (curve_of_cs cs) ->
  Tot (option (lbytes l))

val setupAuthPSKS:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (curve_of_cs cs)
  -> info:info_s cs
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs
  -> skS:key_dh_secret_s cs ->
  Tot (option (key_dh_public_s cs & encryption_context cs))

val setupAuthPSKR:
    cs:ciphersuite
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs
  -> pkS:DH.serialized_point (curve_of_cs cs) ->
  Tot (option (encryption_context cs))

val sealAuthPSK:
    cs:ciphersuite_not_export_only
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (curve_of_cs cs)
  -> info:info_s cs
  -> aad:AEAD.ad (aead_alg_of cs)
  -> pt:AEAD.plain (aead_alg_of cs)
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs
  -> skS:key_dh_secret_s cs ->
  Tot (option (key_dh_public_s cs & AEAD.encrypted #(aead_alg_of cs) pt))

val openAuthPSK:
    cs:ciphersuite_not_export_only
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> aad:AEAD.ad (aead_alg_of cs)
  -> ct:AEAD.cipher (aead_alg_of cs)
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs
  -> pkS:DH.serialized_point (curve_of_cs cs) ->
  Tot (option (AEAD.decrypted #(aead_alg_of cs) ct))

val sendExportAuthPSK:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (curve_of_cs cs)
  -> info:info_s cs
  -> exp_ctx:exp_ctx_s cs
  -> l:exp_len cs
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs
  -> skS:key_dh_secret_s cs ->
  Tot (option (key_dh_public_s cs & lbytes l))

val receiveExportAuthPSK:
    cs:ciphersuite
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> exp_ctx:exp_ctx_s cs
  -> l:exp_len cs
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs
  -> pkS:DH.serialized_point (curve_of_cs cs) ->
  Tot (option (lbytes l))

