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
  | AEAD.AES128_GCM -> create 1 (u8 0) @| create 1 (u8 1)
  | AEAD.AES256_GCM -> create 1 (u8 0) @| create 1 (u8 2)
  | AEAD.CHACHA20_POLY1305 -> create 1 (u8 0) @| create 1 (u8 3)

val suite_id_kem: cs:ciphersuite -> Tot (lbytes size_suite_id_kem)
let suite_id_kem cs =
  Seq.append label_KEM (id_kem cs)

val suite_id_hpke: cs:ciphersuite -> Tot (lbytes size_suite_id_hpke)
// TODO This should already be in big endian each
let suite_id_hpke cs =
  Seq.append label_HPKE (id_kem cs @| id_kdf cs @| id_aead cs)

val id_of_mode: m:mode -> Tot (lbytes size_mode_identifier)
let id_of_mode m =
  match m with
  | Base -> create 1 (u8 0)
  | PSK -> create 1 (u8 1)
  | Auth -> create 1 (u8 2)
  | AuthPSK -> create 1 (u8 3)

//[@"opaque_to_smt"]
//let labeled_extract_pred_ikm (a:Hash.algorithm) (label:bytes) (ikm:bytes) (consts:nat) =
//   Seq.length label_rfcXXXX + Seq.length label + Seq.length ikm + Spec.Hash.Definitions.block_length a + consts <= Spec.Hash.Definitions.max_input_length a

//let labeled_extract_pred_ikm_elim (a:Hash.algorithm) (label:bytes) (ikm:bytes) (consts:nat) :Lemma
//  (requires labeled_extract_pred_ikm a label ikm consts)
//  (ensures Seq.length label_rfcXXXX + Seq.length label + Seq.length ikm + Spec.Hash.Definitions.block_length a + consts <= Spec.Hash.Definitions.max_input_length a)
//= ()
////  assert (Seq.length label_rfcXXXX + Seq.length label + Seq.length ikm + Spec.Hash.Definitions.block_length a + consts <= Spec.Hash.Definitions.max_input_length a) by (FStar.Tactics.fail "foobar")

let labeled_extract a suite_id salt label ikm =
//  labeled_extract_pred_ikm_elim a label ikm 0;
  let labeled_ikm1 = Seq.append label_rfcXXXX suite_id in
  let labeled_ikm2 = Seq.append labeled_ikm1 label in
  let labeled_ikm3 = Seq.append labeled_ikm2 ikm in
  HKDF.extract a salt labeled_ikm3

let labeled_expand a suite_id prk label info l =
  let labeled_info1 = nat_to_bytes_be 2 l in
  let labeled_info2 = Seq.append labeled_info1 label_rfcXXXX in
  let labeled_info3 = Seq.append labeled_info2 suite_id in
  let labeled_info4 = Seq.append labeled_info3 label in
  let labeled_info5 = Seq.append labeled_info4 info in
  HKDF.expand a prk labeled_info5 l

let extract_and_expand_dh_pred (cs:ciphersuite) (dh_length:nat) =
  labeled_extract_ikm_length_pred (kem_hash_of_cs cs) (size_suite_id_kem + Seq.length label_eae_prk + dh_length)

let extract_and_expand_ctx_pred (cs:ciphersuite) (ctx_length:nat) =
  labeled_expand_info_length_pred (kem_hash_of_cs cs) (size_suite_id_kem + Seq.length label_shared_secret + ctx_length)

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

let deserialize cs pk = match curve_of_cs cs with
  | DH.DH_Curve25519 -> pk
  // Extract the point coordinates by removing the first representation byte
  | DH.DH_P256 -> sub pk 1 64


let serialize cs pk = match curve_of_cs cs with
  | DH.DH_Curve25519 -> pk
  // Add the first representation byte to the point coordinates
  | DH.DH_P256 -> create 1 (u8 4) @| pk



val encap:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (curve_of_cs cs) ->
  Tot (option (key_kem_s cs & key_dh_public_s cs))

#set-options "--z3rlimit 100 --fuel 0 --ifuel 2"
let encap cs skE pkR =
  match DH.secret_to_public (curve_of_cs cs) skE with
  | None -> None
  | Some pkE ->
    let enc = serialize cs pkE in
    match DH.dh (curve_of_cs cs) skE pkR with
    | None -> None
    | Some dh ->
      let pkRm = serialize cs pkR in
      let kem_context:lbytes (2*size_dh_public cs) = concat enc pkRm in
      let dhm = serialize cs dh in
      assert (Seq.length enc + Seq.length pkRm = Seq.length kem_context);
      assert (extract_and_expand_ctx_pred cs (Seq.length enc + Seq.length pkRm));
      let shared_secret:key_kem_s cs = extract_and_expand cs dhm kem_context in
      Some (shared_secret, enc)


val decap:
    cs: ciphersuite
  -> enc: key_dh_public_s cs
  -> skR: key_dh_secret_s cs ->
  Tot (option (key_kem_s cs))

#set-options "--z3rlimit 150 --fuel 0 --ifuel 2"
let decap cs enc skR =
  let pkE = deserialize cs enc in
  match DH.dh (curve_of_cs cs) skR pkE with
  | None -> None
  | Some dh ->
    match DH.secret_to_public (curve_of_cs cs) skR with
    | None -> None
    | Some pkR ->
      let pkRm = serialize cs pkR in
      let kem_context:lbytes (2*size_dh_public cs) = concat enc pkRm in
      let dhm = serialize cs dh in
      assert (Seq.length enc + Seq.length pkRm = Seq.length kem_context);
      assert (extract_and_expand_ctx_pred cs (Seq.length kem_context));
      let shared_secret = extract_and_expand cs dhm kem_context in
      Some (shared_secret)

// TODO Correctness lemma for encap/decap?


val auth_encap:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (curve_of_cs cs)
  -> skS:key_dh_secret_s cs ->
  Tot (option (key_kem_s cs & key_dh_public_s cs))

#set-options "--z3rlimit 150 --fuel 0 --ifuel 2"
let auth_encap cs skE pkR skS =
  match DH.secret_to_public (curve_of_cs cs) skE with
  | None -> None
  | Some pkE ->
    match DH.dh (curve_of_cs cs) skE pkR with
    | None -> None
    | Some es ->
      match DH.dh (curve_of_cs cs) skS pkR with
      | None -> None
      | Some ss ->
        let esm = serialize cs es in
        let ssm = serialize cs ss in
        let dh = concat esm ssm in
        let enc = serialize cs pkE in
        match DH.secret_to_public (curve_of_cs cs) skS with
        | None -> None
        | Some pkS ->
          let pkSm = serialize cs pkS in
          let pkRm = serialize cs pkR in
          let kem_context:lbytes (3*size_dh_public cs) = concat enc (concat pkRm pkSm) in
          assert (Seq.length enc + Seq.length pkRm + Seq.length pkSm = Seq.length kem_context);
          assert (extract_and_expand_ctx_pred cs (Seq.length kem_context));
          assert (Seq.length dh = 2*size_dh_public cs);
          assert (extract_and_expand_dh_pred cs (Seq.length dh));
          let shared_secret = extract_and_expand cs dh kem_context in
          Some (shared_secret, enc)


val auth_decap:
    cs: ciphersuite
  -> enc: key_dh_public_s cs
  -> skR: key_dh_secret_s cs
  -> pkS: DH.serialized_point (curve_of_cs cs) ->
  Tot (option (key_kem_s cs))

#set-options "--z3rlimit 150 --fuel 0 --ifuel 2"
let auth_decap cs enc skR pkS =
  let pkE = deserialize cs enc in
  match DH.dh (curve_of_cs cs) skR pkE with
  | None -> None
  | Some es ->
    match DH.dh (curve_of_cs cs) skR pkS with
    | None -> None
    | Some ss ->
      let esm = serialize cs es in
      let ssm = serialize cs ss in
      let dh = concat esm ssm in
      let enc = serialize cs pkE in
      match DH.secret_to_public (curve_of_cs cs) skR with
      | None -> None
      | Some pkR ->
        let pkRm = serialize cs pkR in
        let pkSm = serialize cs pkS in
        let kem_context:lbytes (3*size_dh_public cs) = concat enc (concat pkRm pkSm) in
        assert (Seq.length enc + Seq.length pkRm + Seq.length pkSm = Seq.length kem_context);
        assert (extract_and_expand_ctx_pred cs (Seq.length kem_context));
        assert (Seq.length dh = 2*size_dh_public cs);
        assert (extract_and_expand_dh_pred cs (Seq.length dh));
        let shared_secret = extract_and_expand cs dh kem_context in
        Some (shared_secret)


//let default_psk (cs:ciphersuite):psk_s cs  = create (size_kdf cs) (u8 0)
//let default_psk_id (cs:ciphersuite):psk_id_s cs = create (size_kdf cs) (u8 0)
let default_psk = lbytes_empty
let default_psk_id = lbytes_empty


/// def VerifyPSKInputs(mode, psk, psk_id):
///   got_psk = (psk != default_psk)
///   if got_psk != (psk_id != default_psk_id):
///     raise Exception("Inconsistent PSK inputs")
///
///   if got_psk and (mode in [mode_base, mode_auth]):
///     raise Exception("PSK input provided when not needed")
///   if not got_psk and (mode in [mode_psk, mode_auth_psk]):
///     raise Exception("Missing required PSK input")///
///
/// BB. Implementing this function should not be necessary for us.
///     We are filtering those using our option type in `ks_derive`.

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

// TODO This could go into hacl-star/lib/Lib.ByteSequence?
//      However, it should be noted that this function leaks
//      if the two lbytes have the same length or not, i.e.
//      it is not constant time. lbytes_eq seems to be.
let lbytes_equal (#l1:nat) (#l2:size_nat) (b1:bytes{Seq.length b1 = l1}) (b2:lbytes l2) : bool =
  if not (Seq.length b1 = Seq.length b2) then false else
  lbytes_eq #l2 b1 b2

(* // TODO use heterogenous equality *)
(* // TODO replace got_psk and got_psk_id by match on an option type? *)
(* let verify_psk_inputs (cs:ciphersuite) (m:mode) (psk:psk_s cs) (psk_id:psk_id_s cs) : bool = *)
(*   let got_psk = not (lbytes_equal #(Seq.length psk) #(size_kdf cs) psk (default_psk cs)) in *)
(*   let got_psk_id = not (lbytes_equal #(Seq.length psk_id) #0 psk_id (default_psk_id cs)) in *)
(*   if not (got_psk = got_psk_id) then false else // Inconsistent PSK inputs *)
(*   match (m, got_psk) with *)
(*   | (Base, true) -> false     // PSK input provided when not needed *)
(*   | (Auth, true) -> false     // PSK input provided when not needed *)
(*   | (PSK, false) -> false     // Missing required PSK input *)
(*   | (AuthPSK, false) -> false // Missing required PSK input *)
(*   | _ -> true *)

let verify_psk_inputs (cs:ciphersuite) (m:mode) (opsk:option(psk_s cs & psk_id_s cs)) : bool =
  match (m, opsk) with
  | Base, None -> true
  | PSK, Some _ -> true
  | Auth, None -> true
  | AuthPSK, Some _ -> true
  | _, _ -> false

val key_schedule:
    cs:ciphersuite
  -> m:mode
  -> shared_secret:key_kem_s cs
  -> info:info_s cs
  -> opsk:option (psk_s cs & psk_id_s cs) ->
  Pure (encryption_context cs)
    (requires verify_psk_inputs cs m opsk)
    (ensures fun _ -> True)

let key_schedule cs m shared_secret info opsk =
  let (psk, psk_id) =
    match opsk with
    | None -> (default_psk, default_psk_id)
    | Some (psk, psk_id) -> (psk, psk_id) in
  let psk_id_hash = labeled_extract (hash_of_cs cs) (suite_id_hpke cs) lbytes_empty label_psk_id_hash psk_id in
  let info_hash = labeled_extract (hash_of_cs cs) (suite_id_hpke cs) lbytes_empty label_info_hash info in
  let context = build_context cs m psk_id_hash info_hash in
  let secret = labeled_extract (hash_of_cs cs) (suite_id_hpke cs) shared_secret label_secret psk in
  let key = labeled_expand (hash_of_cs cs) (suite_id_hpke cs) secret label_key context (size_aead_key cs) in
  let base_nonce = labeled_expand (hash_of_cs cs) (suite_id_hpke cs) secret label_base_nonce context (size_aead_nonce cs) in
  let exporter_secret = labeled_expand (hash_of_cs cs) (suite_id_hpke cs) secret label_exp context (size_kdf cs) in
  (key, base_nonce, 0, exporter_secret)

let key_of_ctx (cs:ciphersuite) (ctx:encryption_context cs) =
  let key, _, _, _ = ctx in key

let nonce_of_ctx (cs:ciphersuite) (ctx:encryption_context cs) =
  let _, nonce, _, _ = ctx in nonce

let seq_of_ctx (cs:ciphersuite) (ctx:encryption_context cs) =
  let _, _, seq, _ = ctx in seq

let exp_sec_of_ctx (cs:ciphersuite) (ctx:encryption_context cs) =
  let _, _, _, exp_sec = ctx in exp_sec

let set_seq (cs:ciphersuite) (ctx:encryption_context cs) (seq:seq_aead_s cs) =
  let key, nonce, _, exp_sec = ctx in
  (key, nonce, seq, exp_sec)

let context_export cs ctx exp_ctx l =
  let exp_sec = exp_sec_of_ctx cs ctx in
  labeled_expand (hash_of_cs cs) (suite_id_hpke cs) exp_sec label_sec exp_ctx l


let context_compute_nonce cs ctx seq =
  let nonce = nonce_of_ctx cs ctx in
  let enc_seq = nat_to_bytes_be (size_aead_nonce cs) seq in
  Spec.Loops.seq_map2 logxor enc_seq nonce

let context_increment_seq cs ctx =
  let key, nonce, seq, exporter_secret = ctx in
  if seq = max_seq cs then None else // TODO this should be a pre-condition. “no need for dynamic checks in the Pure world”
  Some (set_seq cs ctx (seq + 1))

// TODO In the spec world, I could enforce a pre-condition on ctx.seq
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


/// def SetupBaseS(pkR, info):
///   zz, enc = Encap(pkR)
///   return enc, KeySchedule(mode_base, zz, info, default_psk, default_psk_id)

let setupBaseS cs skE pkR info =
  match encap cs skE pkR with
  | None -> None
  | Some (shared_secret, enc) ->
    let enc_ctx = key_schedule cs Base shared_secret info None in
    Some (enc, enc_ctx)


/// def SetupBaseR(enc, skR, info):
///   zz = Decap(enc, skR)
///   return KeySchedule(mode_base, zz, info, default_psk, default_psk_id)

let setupBaseR cs enc skR info =
  let pkR = DH.secret_to_public (curve_of_cs cs) skR in
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
    | Some (ctx, ct) -> Some (enc, ct)

let openBase cs enc skR info aad ct =
  match setupBaseR cs enc skR info with
  | None -> None
  | Some ctx ->
    match context_open cs ctx aad ct with
    | None -> None
    | Some (ctx, pt) -> Some pt

/// def SetupPSKS(pkR, info, psk, psk_id):
///   zz, enc = Encap(pkR)
///   return enc, KeySchedule(mode_psk, zz, info, psk, psk_id)

let setupPSKS cs skE pkR info psk psk_id =
  match encap cs skE pkR with
  | None -> None
  | Some (shared_secret, enc) ->
    assert (verify_psk_inputs cs PSK (Some (psk, psk_id)));
    let enc_ctx = key_schedule cs PSK shared_secret info (Some (psk, psk_id)) in
    Some (enc, enc_ctx)


/// def SetupPSKR(enc, skR, info, psk, psk_id):
///   zz = Decap(enc, skR)
///   return KeySchedule(mode_psk, zz, info, psk, psk_id)

let setupPSKR cs enc skR info psk psk_id =
  let pkR = DH.secret_to_public (curve_of_cs cs) skR in
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
    | Some (ctx, ct) -> Some (enc, ct)

let openPSK cs enc skR info aad ct psk psk_id =
  match setupPSKR cs enc skR info psk psk_id with
  | None -> None
  | Some ctx ->
    match context_open cs ctx aad ct with
    | None -> None
    | Some (ctx, pt) -> Some pt

/// def SetupAuthS(pkR, info, skS):
///   zz, enc = AuthEncap(pkR, skS)
///   return enc, KeySchedule(mode_auth, zz, info, default_psk, default_psk_id)

let setupAuthS cs skE pkR info skS =
  match auth_encap cs skE pkR skS with
  | None -> None
  | Some (shared_secret, enc) ->
    let enc_ctx = key_schedule cs Auth shared_secret info None in
    Some (enc, enc_ctx)


/// def SetupAuthR(enc, skR, info, pkS):
///   zz = AuthDecap(enc, skR, pkS)
///   return KeySchedule(mode_auth, zz, info, default_psk, default_psk_id)

let setupAuthR cs enc skR info pkS =
  let pkR = DH.secret_to_public (curve_of_cs cs) skR in
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
    | Some (ctx, ct) -> Some (enc, ct)

let openAuth cs enc skR info aad ct pkS =
  match setupAuthR cs enc skR info pkS with
  | None -> None
  | Some ctx ->
    match context_open cs ctx aad ct with
    | None -> None
    | Some (ctx, pt) -> Some pt

/// def SetupAuthPSKS(pkR, info, psk, psk_id, skS):
///   zz, enc = AuthEncap(pkR, skS)
///   return enc, KeySchedule(mode_auth_psk, zz, info, psk, psk_id)

let setupAuthPSKS cs skE pkR info psk psk_id skS =
  match auth_encap cs skE pkR skS with
  | None -> None
  | Some (shared_secret, enc) ->
    let enc_ctx = key_schedule cs AuthPSK shared_secret info (Some (psk, psk_id)) in
    Some (enc, enc_ctx)


/// def SetupAuthPSKR(enc, skR, info, psk, psk_id, pkS):
///   zz = AuthDecap(enc, skR, pkS)
///   return KeySchedule(mode_auth_psk, zz, info, psk, psk_id)

let setupAuthPSKR cs enc skR info psk psk_id pkS =
  let pkR = DH.secret_to_public (curve_of_cs cs) skR in
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
    | Some (ctx, ct) -> Some (enc, ct)

let openAuthPSK cs enc skR info aad ct psk psk_id pkS =
  match setupAuthPSKR cs enc skR info psk psk_id pkS with
  | None -> None
  | Some ctx ->
    match context_open cs ctx aad ct with
    | None -> None
    | Some (ctx, pt) -> Some pt

// TODO rename nonce to base_nonce
// TODO single-shot export
