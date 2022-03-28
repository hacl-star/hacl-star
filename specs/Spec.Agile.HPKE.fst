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




/// Types

val id_kem: cs:ciphersuite -> Tot (lbytes 2)
let id_kem cs = let kem_dh, kem_hash, _, _ = cs in
  match kem_dh, kem_hash with
  | DH.DH_P256, Hash.SHA2_256 -> create 1 (u8 0) @| create 1 (u8 16)
  | DH.DH_Curve25519, Hash.SHA2_256 -> create 1 (u8 0) @| create 1 (u8 32)

val id_kdf: cs:ciphersuite -> Tot (lbytes 2)
let id_kdf cs = let _, _, _, h = cs in
  match h with
  | Hash.SHA2_256 -> create 1 (u8 0) @| create 1 (u8 1)
  | Hash.SHA2_384 -> create 1 (u8 0) @| create 1 (u8 2)
  | Hash.SHA2_512 -> create 1 (u8 0) @| create 1 (u8 3)

val id_aead: cs:ciphersuite -> Tot (lbytes 2)
let id_aead cs = let _, _, a, _ = cs in
  match a with
  | Seal AEAD.AES128_GCM -> create 1 (u8 0) @| create 1 (u8 1)
  | Seal AEAD.AES256_GCM -> create 1 (u8 0) @| create 1 (u8 2)
  | Seal AEAD.CHACHA20_POLY1305 -> create 1 (u8 0) @| create 1 (u8 3)
  | ExportOnly -> create 1 (u8 255) @| create 1 (u8 255)

val suite_id_kem: cs:ciphersuite -> Tot (lbytes size_suite_id_kem)
let suite_id_kem cs =
  Seq.append label_KEM (id_kem cs)

val suite_id_hpke: cs:ciphersuite -> Tot (lbytes size_suite_id_hpke)
let suite_id_hpke cs =
  Seq.append label_HPKE (id_kem cs @| id_kdf cs @| id_aead cs)

val id_of_mode: m:mode -> Tot (lbytes size_mode_identifier)
let id_of_mode m =
  match m with
  | Base -> create 1 (u8 0)
  | PSK -> create 1 (u8 1)
  | Auth -> create 1 (u8 2)
  | AuthPSK -> create 1 (u8 3)

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




let labeled_extract a suite_id salt label ikm =
  let labeled_ikm1 = Seq.append label_version suite_id in
  let labeled_ikm2 = Seq.append labeled_ikm1 label in
  let labeled_ikm3 = Seq.append labeled_ikm2 ikm in
  HKDF.extract a salt labeled_ikm3

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


let labeled_expand a suite_id prk label info l =
  let labeled_info1 = nat_to_bytes_be 2 l in
  let labeled_info2 = Seq.append labeled_info1 label_version in
  let labeled_info3 = Seq.append labeled_info2 suite_id in
  let labeled_info4 = Seq.append labeled_info3 label in
  let labeled_info5 = Seq.append labeled_info4 info in
  HKDF.expand a prk labeled_info5 l

let extract_and_expand_dh_pred (cs:ciphersuite) (dh_length:nat) =
  labeled_extract_ikm_length_pred (kem_hash_of_cs cs) (size_suite_id_kem + size_label_eae_prk + dh_length)

let extract_and_expand_ctx_pred (cs:ciphersuite) (ctx_length:nat) =
  labeled_expand_info_length_pred (kem_hash_of_cs cs) (size_suite_id_kem + size_label_shared_secret + ctx_length)

val extract_and_expand:
    cs:ciphersuite
  -> dh:bytes
  -> kem_context:bytes ->
  Pure (key_kem_s cs)
    (requires
      extract_and_expand_dh_pred cs (Seq.length dh) /\
      extract_and_expand_ctx_pred cs (Seq.length kem_context))
    (ensures fun _ -> True)

let extract_and_expand cs dh kem_context =
  let eae_prk = labeled_extract (kem_hash_of_cs cs) (suite_id_kem cs) lbytes_empty label_eae_prk dh in
  labeled_expand (kem_hash_of_cs cs) (suite_id_kem cs) eae_prk label_shared_secret kem_context (size_kem_key cs)

let deserialize_public_key cs pk = match kem_dh_of_cs cs with
  | DH.DH_Curve25519 -> pk
  // Extract the point coordinates by removing the first representation byte
  | DH.DH_P256 -> sub pk 1 64


let serialize_public_key cs pk = match kem_dh_of_cs cs with
  | DH.DH_Curve25519 -> pk
  // Add the first representation byte to the point coordinates
  | DH.DH_P256 -> create 1 (u8 4) @| pk


val dkp_nist_p: cs:ciphersuite -> lbytes (size_kem_kdf cs) -> counter:uint8 -> Tot (option (key_dh_secret_s cs & key_dh_public_s cs)) (decreases 255 - v counter)
let rec dkp_nist_p cs dkp_prk counter =
  let counterbyte = nat_to_intseq_be #U8 #SEC 1 (v counter) in
  let bytes = labeled_expand (kem_hash_of_cs cs) (suite_id_kem cs) dkp_prk label_candidate counterbyte (size_dh_key cs) in
  let bytes = Lib.Sequence.map2 (logand #U8 #SEC) bytes (Seq.create (size_dh_key cs) (u8 255)) in
  let sk = nat_from_intseq_be #U8 #SEC bytes in
  if sk = 0 || sk >= Spec.P256.prime then
    if (v counter) = 255 then None
    else dkp_nist_p cs dkp_prk (counter +! (u8 1))
  else
    match DH.secret_to_public (kem_dh_of_cs cs) bytes with
    | Some pk -> Some (bytes, serialize_public_key cs pk)
    | None ->
      if (v counter) = 255 then None
      else dkp_nist_p cs dkp_prk (counter +! (u8 1))



let derive_key_pair cs ikm =
  match kem_dh_of_cs cs with
  | DH.DH_Curve25519 -> begin
    let dkp_prk = labeled_extract (kem_hash_of_cs cs) (suite_id_kem cs) lbytes_empty label_dkp_prk ikm in
    let sk = labeled_expand (kem_hash_of_cs cs) (suite_id_kem cs) dkp_prk label_sk lbytes_empty (size_dh_key cs) in
    match DH.secret_to_public (kem_dh_of_cs cs) sk with
    | Some pk -> Some (sk, serialize_public_key cs pk)
    end
  | DH.DH_P256 ->
    let dkp_prk = labeled_extract (kem_hash_of_cs cs) (suite_id_kem cs) lbytes_empty label_dkp_prk ikm in
    dkp_nist_p cs dkp_prk (u8 0)

val prepare_dh: cs:ciphersuite -> DH.serialized_point (kem_dh_of_cs cs) -> Tot (lbytes 32)
let prepare_dh cs dh = match (kem_dh_of_cs cs) with
  | DH.DH_Curve25519 -> serialize_public_key cs dh
  | DH.DH_P256 -> sub dh 0 32


val encap:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (kem_dh_of_cs cs) ->
  Tot (option (key_kem_s cs & key_dh_public_s cs))

#set-options "--z3rlimit 300 --fuel 0 --ifuel 2"
let encap cs skE pkR =
  match DH.secret_to_public (kem_dh_of_cs cs) skE with
  | None -> None
  | Some pkE ->
    let enc = serialize_public_key cs pkE in
    match DH.dh (kem_dh_of_cs cs) skE pkR with
    | None -> None
    | Some dh ->
      let pkRm = serialize_public_key cs pkR in
      let kem_context = concat enc pkRm in
      let dhm = prepare_dh cs dh in
      assert (Seq.length kem_context = 2*size_dh_public cs);
      assert (extract_and_expand_ctx_pred cs (Seq.length kem_context));
      let shared_secret:key_kem_s cs = extract_and_expand cs dhm kem_context in
      Some (shared_secret, enc)


val decap:
    cs: ciphersuite
  -> enc: key_dh_public_s cs
  -> skR: key_dh_secret_s cs ->
  Tot (option (key_kem_s cs))

#set-options "--z3rlimit 300 --fuel 0 --ifuel 2"
let decap cs enc skR =
  let pkE = deserialize_public_key cs enc in
  match DH.dh (kem_dh_of_cs cs) skR pkE with
  | None -> None
  | Some dh ->
    match DH.secret_to_public (kem_dh_of_cs cs) skR with
    | None -> None
    | Some pkR ->
      let pkRm = serialize_public_key cs pkR in
      let kem_context = concat enc pkRm in
      let dhm = prepare_dh cs dh in
      assert (Seq.length kem_context = 2*size_dh_public cs);
      assert (extract_and_expand_ctx_pred cs (Seq.length kem_context));
      let shared_secret = extract_and_expand cs dhm kem_context in
      Some (shared_secret)

val auth_encap:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (kem_dh_of_cs cs)
  -> skS:key_dh_secret_s cs ->
  Tot (option (key_kem_s cs & key_dh_public_s cs))

#set-options "--z3rlimit 1000 --fuel 0 --ifuel 2"
let auth_encap cs skE pkR skS =
  match DH.secret_to_public (kem_dh_of_cs cs) skE with
  | None -> None
  | Some pkE ->
    match DH.dh (kem_dh_of_cs cs) skE pkR with
    | None -> None
    | Some es ->
      match DH.dh (kem_dh_of_cs cs) skS pkR with
      | None -> None
      | Some ss ->
        let esm = prepare_dh cs es in
        let ssm = prepare_dh cs ss in
        // TODO Do not put 32 literally
        let dh = concat #uint8 #32 #32 esm ssm in
        let enc = serialize_public_key cs pkE in
        match DH.secret_to_public (kem_dh_of_cs cs) skS with
        | None -> None
        | Some pkS ->
          let pkSm = serialize_public_key cs pkS in
          let pkRm = serialize_public_key cs pkR in
          let kem_context = concat enc (concat pkRm pkSm) in
          assert (Seq.length kem_context = 3*size_dh_public cs);
          assert (labeled_expand_info_length_pred (kem_hash_of_cs cs) (size_suite_id_kem + size_label_shared_secret + Seq.length kem_context));
          assert (extract_and_expand_ctx_pred cs (Seq.length kem_context));
          // TODO Do not put 64 literally
          assert (Seq.length dh = 64);
          assert (labeled_extract_ikm_length_pred (kem_hash_of_cs cs) (size_suite_id_kem + size_label_eae_prk + Seq.length dh));
          assert (extract_and_expand_dh_pred cs (Seq.length dh));
          let shared_secret = extract_and_expand cs dh kem_context in
          Some (shared_secret, enc)
#reset-options

val auth_decap:
    cs: ciphersuite
  -> enc: key_dh_public_s cs
  -> skR: key_dh_secret_s cs
  -> pkS: DH.serialized_point (kem_dh_of_cs cs) ->
  Tot (option (key_kem_s cs))

#set-options "--z3rlimit 1000 --fuel 0 --ifuel 4"
let auth_decap cs enc skR pkS =
  let pkE = deserialize_public_key cs enc in
  match DH.dh (kem_dh_of_cs cs) skR pkE with
  | None -> None
  | Some es ->
    match DH.dh (kem_dh_of_cs cs) skR pkS with
    | None -> None
    | Some ss ->
      let esm = prepare_dh cs es in
      let ssm = prepare_dh cs ss in
      let dh = concat #uint8 #32 #32 esm ssm in
      match DH.secret_to_public (kem_dh_of_cs cs) skR with
      | None -> None
      | Some pkR ->
        let pkRm = serialize_public_key cs pkR in
        let pkSm = serialize_public_key cs pkS in
        let kem_context = concat enc (concat pkRm pkSm) in
        assert (Seq.length kem_context = 3*size_dh_public cs);
        assert (labeled_expand_info_length_pred (kem_hash_of_cs cs) (size_suite_id_kem + size_label_shared_secret + Seq.length kem_context));
        assert (extract_and_expand_ctx_pred cs (Seq.length kem_context));
        assert (Seq.length dh = 64);
        assert (labeled_extract_ikm_length_pred (kem_hash_of_cs cs) (size_suite_id_kem + size_label_eae_prk + Seq.length dh));
        assert (extract_and_expand_dh_pred cs (Seq.length dh));
        let shared_secret = extract_and_expand cs dh kem_context in
        Some (shared_secret)
#reset-options


let default_psk = lbytes_empty
let default_psk_id = lbytes_empty

val build_context:
    cs:ciphersuite
  -> m:mode
  -> psk_id_hash:lbytes (size_kdf cs)
  -> info_hash:lbytes (size_kdf cs) ->
  Tot (lbytes (size_ks_ctx cs))

let build_context cs m psk_id_hash info_hash =
  let context = id_of_mode m in
  let context = Seq.append context psk_id_hash in
  let context = Seq.append context info_hash in
  context

let verify_psk_inputs (cs:ciphersuite) (m:mode) (opsk:option(psk_s cs & psk_id_s cs)) : bool =
  match (m, opsk) with
  | Base, None -> true
  | PSK, Some _ -> true
  | Auth, None -> true
  | AuthPSK, Some _ -> true
  | _, _ -> false

// key and nonce are zero-length if AEAD is Export-Only
let encryption_context (cs:ciphersuite) = key_aead_s cs & nonce_aead_s cs & seq_aead_s cs & exporter_secret_s cs

val key_schedule:
    cs:ciphersuite
  -> m:mode
  -> shared_secret:key_kem_s cs
  -> info:info_s cs
  -> opsk:option (psk_s cs & psk_id_s cs) ->
  Pure (encryption_context cs)
    (requires verify_psk_inputs cs m opsk)
    (ensures fun _ -> True)

#set-options "--z3rlimit 500 --fuel 0 --ifuel 2"
let key_schedule_core
  (cs:ciphersuite)
  (m:mode)
  (shared_secret:key_kem_s cs)
  (info:info_s cs)
  (opsk:option (psk_s cs & psk_id_s cs))
  : (lbytes (size_ks_ctx cs) & exporter_secret_s cs & (lbytes (Spec.Hash.Definitions.hash_length (hash_of_cs cs)))) =
  let (psk, psk_id) =
    match opsk with
    | None -> (default_psk, default_psk_id)
    | Some (psk, psk_id) -> (psk, psk_id)
  in
  let psk_id_hash = labeled_extract (hash_of_cs cs) (suite_id_hpke cs) lbytes_empty label_psk_id_hash psk_id in
  let info_hash = labeled_extract (hash_of_cs cs) (suite_id_hpke cs) lbytes_empty label_info_hash info in
  let context = build_context cs m psk_id_hash info_hash in
  let secret = labeled_extract (hash_of_cs cs) (suite_id_hpke cs) shared_secret label_secret psk in

  let exporter_secret = labeled_expand (hash_of_cs cs) (suite_id_hpke cs) secret label_exp context (size_kdf cs) in
  context, exporter_secret, secret

let key_schedule_end
  (cs:ciphersuite)
  (m:mode)
  (context:lbytes (size_ks_ctx cs))
  (exporter_secret:exporter_secret_s cs)
  (secret:(lbytes (Spec.Hash.Definitions.hash_length (hash_of_cs cs))))
  :  encryption_context cs
  =
  if is_valid_not_export_only_ciphersuite cs then (
    let key = labeled_expand (hash_of_cs cs) (suite_id_hpke cs) secret label_key context (size_aead_key cs) in
    let base_nonce = labeled_expand (hash_of_cs cs) (suite_id_hpke cs) secret label_base_nonce context (size_aead_nonce cs) in
    (key, base_nonce, 0, exporter_secret)

  ) else (
    (* if AEAD is Export-Only, then skip computation of key and base_nonce *)
    assert (size_aead_key cs = 0);
    assert (size_aead_nonce cs = 0);
    (lbytes_empty, lbytes_empty, 0, exporter_secret))

let key_schedule cs m shared_secret info opsk =
  let context, exporter_secret, secret = key_schedule_core cs m shared_secret info opsk in
  key_schedule_end cs m context exporter_secret secret

let key_of_ctx (cs:ciphersuite) (ctx:encryption_context cs) =
  let key, _, _, _ = ctx in key

let base_nonce_of_ctx (cs:ciphersuite) (ctx:encryption_context cs) =
  let _, base_nonce, _, _ = ctx in base_nonce

let seq_of_ctx (cs:ciphersuite) (ctx:encryption_context cs) =
  let _, _, seq, _ = ctx in seq

let exp_sec_of_ctx (cs:ciphersuite) (ctx:encryption_context cs) =
  let _, _, _, exp_sec = ctx in exp_sec

let set_seq (cs:ciphersuite) (ctx:encryption_context cs) (seq:seq_aead_s cs) =
  let key, base_nonce, _, exp_sec = ctx in
  (key, base_nonce, seq, exp_sec)


///
/// Encryption Context
///

let context_export cs ctx exp_ctx l =
  let exp_sec = exp_sec_of_ctx cs ctx in
  labeled_expand (hash_of_cs cs) (suite_id_hpke cs) exp_sec label_sec exp_ctx l


let context_compute_nonce cs ctx seq =
  let base_nonce = base_nonce_of_ctx cs ctx in
  let enc_seq = nat_to_bytes_be (size_aead_nonce cs) seq in
  Spec.Loops.seq_map2 logxor enc_seq base_nonce

let context_increment_seq cs ctx =
  let seq = seq_of_ctx cs ctx in
  if seq = max_seq cs then None else
  Some (set_seq cs ctx (seq + 1))

let context_seal cs ctx aad pt =
  let key = key_of_ctx cs ctx in
  let seq = seq_of_ctx cs ctx in
  let nonce = context_compute_nonce cs ctx seq in
  let ct = AEAD.encrypt key nonce aad pt in
  match context_increment_seq cs ctx with
  | None -> None
  | Some new_ctx -> Some (new_ctx, ct)

let context_open cs ctx aad ct =
  let key = key_of_ctx cs ctx in
  let seq = seq_of_ctx cs ctx in
  let nonce = context_compute_nonce cs ctx seq in
  match AEAD.decrypt key nonce aad ct with
  | None -> None
  | Some pt ->
    match context_increment_seq cs ctx with
    | None -> None
    | Some new_ctx -> Some (new_ctx, pt)

///
/// Base Mode
///

let setupBaseS cs skE pkR info =
  match encap cs skE pkR with
  | None -> None
  | Some (shared_secret, enc) ->
    let enc_ctx = key_schedule cs Base shared_secret info None in
    Some (enc, enc_ctx)

let setupBaseR cs enc skR info =
  let pkR = DH.secret_to_public (kem_dh_of_cs cs) skR in
  let shared_secret = decap cs enc skR in
  match pkR, shared_secret with
  | Some pkR, Some shared_secret ->
    Some (key_schedule cs Base shared_secret info None)
  | _ -> None

let sealBase cs skE pkR info aad pt =
  match setupBaseS cs skE pkR info with
  | None -> None
  | Some (enc, ctx) ->
    match context_seal cs ctx aad pt with
    | None -> None
    | Some (_, ct) -> Some (enc, ct)

let openBase cs enc skR info aad ct =
  match setupBaseR cs enc skR info with
  | None -> None
  | Some ctx ->
    match context_open cs ctx aad ct with
    | None -> None
    | Some (_, pt) -> Some pt

let sendExportBase cs skE pkR info exp_ctx l =
  match setupBaseS cs skE pkR info with
  | None -> None
  | Some (enc, ctx) ->
    Some (enc, context_export cs ctx exp_ctx l)

let receiveExportBase cs enc skR info exp_ctx l =
  match setupBaseR cs enc skR info with
  | None -> None
  | Some ctx ->
    Some (context_export cs ctx exp_ctx l)

///
/// PSK mode
///

let setupPSKS cs skE pkR info psk psk_id =
  match encap cs skE pkR with
  | None -> None
  | Some (shared_secret, enc) ->
    assert (verify_psk_inputs cs PSK (Some (psk, psk_id)));
    let enc_ctx = key_schedule cs PSK shared_secret info (Some (psk, psk_id)) in
    Some (enc, enc_ctx)

let setupPSKR cs enc skR info psk psk_id =
  let pkR = DH.secret_to_public (kem_dh_of_cs cs) skR in
  let shared_secret = decap cs enc skR in
  match pkR, shared_secret with
  | Some pkR, Some shared_secret ->
    Some (key_schedule cs PSK shared_secret info (Some (psk, psk_id)))
  | _ -> None

let sealPSK cs skE pkR info aad pt psk psk_id =
  match setupPSKS cs skE pkR info psk psk_id with
  | None -> None
  | Some (enc, ctx) ->
    match context_seal cs ctx aad pt with
    | None -> None
    | Some (_, ct) -> Some (enc, ct)

let openPSK cs enc skR info aad ct psk psk_id =
  match setupPSKR cs enc skR info psk psk_id with
  | None -> None
  | Some ctx ->
    match context_open cs ctx aad ct with
    | None -> None
    | Some (_, pt) -> Some pt

let sendExportPSK cs skE pkR info exp_ctx l psk psk_id =
  match setupPSKS cs skE pkR info psk psk_id with
  | None -> None
  | Some (enc, ctx) ->
    Some (enc, context_export cs ctx exp_ctx l)

let receiveExportPSK cs enc skR info exp_ctx l psk psk_id =
  match setupPSKR cs enc skR info psk psk_id with
  | None -> None
  | Some ctx ->
    Some (context_export cs ctx exp_ctx l)

///
/// Auth mode
///

let setupAuthS cs skE pkR info skS =
  match auth_encap cs skE pkR skS with
  | None -> None
  | Some (shared_secret, enc) ->
    let enc_ctx = key_schedule cs Auth shared_secret info None in
    Some (enc, enc_ctx)

let setupAuthR cs enc skR info pkS =
  let pkR = DH.secret_to_public (kem_dh_of_cs cs) skR in
  let shared_secret = auth_decap cs enc skR pkS in
  match pkR, shared_secret with
  | Some pkR, Some shared_secret ->
    Some (key_schedule cs Auth shared_secret info None)
  | _ -> None

let sealAuth cs skE pkR info aad pt skS =
  match setupAuthS cs skE pkR info skS with
  | None -> None
  | Some (enc, ctx) ->
    match context_seal cs ctx aad pt with
    | None -> None
    | Some (_, ct) -> Some (enc, ct)

let openAuth cs enc skR info aad ct pkS =
  match setupAuthR cs enc skR info pkS with
  | None -> None
  | Some ctx ->
    match context_open cs ctx aad ct with
    | None -> None
    | Some (_, pt) -> Some pt

let sendExportAuth cs skE pkR info exp_ctx l skS =
  match setupAuthS cs skE pkR info skS with
  | None -> None
  | Some (enc, ctx) ->
    Some (enc, context_export cs ctx exp_ctx l)

let receiveExportAuth cs enc skR info exp_ctx l pkS =
  match setupAuthR cs enc skR info pkS with
  | None -> None
  | Some ctx ->
    Some (context_export cs ctx exp_ctx l)

///
/// AuthPSK mode
///

let setupAuthPSKS cs skE pkR info psk psk_id skS =
  match auth_encap cs skE pkR skS with
  | None -> None
  | Some (shared_secret, enc) ->
    let enc_ctx = key_schedule cs AuthPSK shared_secret info (Some (psk, psk_id)) in
    Some (enc, enc_ctx)

let setupAuthPSKR cs enc skR info psk psk_id pkS =
  let pkR = DH.secret_to_public (kem_dh_of_cs cs) skR in
  let shared_secret = auth_decap cs enc skR pkS in
  match pkR, shared_secret with
  | Some pkR, Some shared_secret ->
    Some (key_schedule cs AuthPSK shared_secret info (Some (psk, psk_id)))
  | _ -> None

let sealAuthPSK cs skE pkR info aad pt psk psk_id skS =
  match setupAuthPSKS cs skE pkR info psk psk_id skS with
  | None -> None
  | Some (enc, ctx) ->
    match context_seal cs ctx aad pt with
    | None -> None
    | Some (_, ct) -> Some (enc, ct)

let openAuthPSK cs enc skR info aad ct psk psk_id pkS =
  match setupAuthPSKR cs enc skR info psk psk_id pkS with
  | None -> None
  | Some ctx ->
    match context_open cs ctx aad ct with
    | None -> None
    | Some (_, pt) -> Some pt

let sendExportAuthPSK cs skE pkR info exp_ctx l psk psk_id skS =
  match setupAuthPSKS cs skE pkR info psk psk_id skS with
  | None -> None
  | Some (enc, ctx) ->
    Some (enc, context_export cs ctx exp_ctx l)

let receiveExportAuthPSK cs enc skR info exp_ctx l psk psk_id pkS =
  match setupAuthPSKR cs enc skR info psk psk_id pkS with
  | None -> None
  | Some ctx ->
    Some (context_export cs ctx exp_ctx l)
