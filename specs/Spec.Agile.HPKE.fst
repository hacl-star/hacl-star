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

// TODO This must match the first two and set the id accordingly
val id_kem: cs:ciphersuite -> Tot (lbytes 2)
let id_kem cs = let dh, _, _, _ = cs in
  match dh with
  | DH.DH_P256 -> create 1 (u8 0) @| create 1 (u8 16)
  | DH.DH_Curve25519 -> create 1 (u8 0) @| create 1 (u8 32)

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


val id_of_cs: cs:ciphersuite -> Tot (lbytes size_cs_identifier)
// TODO This should already be in big endian each
let id_of_cs cs = id_kem cs @| id_kdf cs @| id_aead cs

val id_of_mode: m:mode -> Tot (lbytes size_mode_identifier)
let id_of_mode m =
  match m with
  | Base -> create 1 (u8 0)
  | PSK -> create 1 (u8 1)
  | Auth -> create 1 (u8 2)
  | PSKAuth -> create 1 (u8 3)

//[@"opaque_to_smt"]
//let labeled_extract_pred_ikm (a:Hash.algorithm) (label:bytes) (ikm:bytes) (consts:nat) =
//   Seq.length label_rfcXXXX + Seq.length label + Seq.length ikm + Spec.Hash.Definitions.block_length a + consts <= Spec.Hash.Definitions.max_input_length a

//let labeled_extract_pred_ikm_elim (a:Hash.algorithm) (label:bytes) (ikm:bytes) (consts:nat) :Lemma
//  (requires labeled_extract_pred_ikm a label ikm consts)
//  (ensures Seq.length label_rfcXXXX + Seq.length label + Seq.length ikm + Spec.Hash.Definitions.block_length a + consts <= Spec.Hash.Definitions.max_input_length a)
//= ()
////  assert (Seq.length label_rfcXXXX + Seq.length label + Seq.length ikm + Spec.Hash.Definitions.block_length a + consts <= Spec.Hash.Definitions.max_input_length a) by (FStar.Tactics.fail "foobar")

let labeled_extract a salt label ikm =
//  labeled_extract_pred_ikm_elim a label ikm 0;
  let labeledIKM = Seq.append label_rfcXXXX label in
  let labeledIKM = Seq.append labeledIKM ikm in
  HKDF.extract a salt labeledIKM

let labeled_expand a prk label info l =
  let labeledInfo = nat_to_bytes_be 2 l in
  let labeledInfo = Seq.append labeledInfo label_rfcXXXX in
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

let unmarshal cs pk = match curve_of_cs cs with
  | DH.DH_Curve25519 -> pk
  // Extract the point coordinates by removing the first representation byte
  | DH.DH_P256 -> sub pk 1 64


let marshal cs pk = match curve_of_cs cs with
  | DH.DH_Curve25519 -> pk
  // Add the first representation byte to the point coordinates
  | DH.DH_P256 -> create 1 (u8 4) @| pk


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
  -> pkR:DH.serialized_point (curve_of_cs cs) ->
  Tot (option (key_kem_s cs & key_dh_public_s cs))

#set-options "--z3rlimit 100 --fuel 0 --ifuel 2"
let encap cs skE pkR =
  match DH.secret_to_public (curve_of_cs cs) skE with
  | None -> None
  | Some pkE ->
    let enc = marshal cs pkE in
    match DH.dh (curve_of_cs cs) skE pkR with
    | None -> None
    | Some dh ->
      let pkRm = marshal cs pkR in
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

#set-options "--z3rlimit 100 --fuel 0 --ifuel 2"
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
        let esm = marshal cs es in
        let ssm = marshal cs ss in
        let dh = concat esm ssm in
        let enc = marshal cs pkE in
        match DH.secret_to_public (curve_of_cs cs) skE with
        | None -> None
        | Some pkS ->
          let pkSm = marshal cs pkS in
          let pkRm = marshal cs pkR in
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
  -> pkS: DH.serialized_point (curve_of_cs cs) ->
  Tot (option (key_kem_s cs))

#set-options "--z3rlimit 150 --fuel 0 --ifuel 2"
let auth_decap cs enc skR pkS =
  let pkE = unmarshal cs enc in
  match DH.dh (curve_of_cs cs) skR pkE with
  | None -> None
  | Some es ->
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
        let pkSm = marshal cs pkS in
        let kemContext:lbytes (3*size_dh_public cs) = concat enc (concat pkRm pkSm) in
        assert (Seq.length enc + Seq.length pkRm + Seq.length pkSm = Seq.length kemContext);
        assert (extract_and_expand_ctx_pred cs (Seq.length kemContext));
        assert (Seq.length dh = 2*size_dh_public cs);
        assert (extract_and_expand_dh_pred cs (Seq.length dh));
        let zz = extract_and_expand cs dh kemContext in
        Some (zz)

/// default_psk = zero(0)
/// default_pskId = zero(0)

let default_psk (cs:ciphersuite):psk_s cs  = create (size_kdf cs) (u8 0)
//let default_psk (cs:ciphersuite):psk_s cs  = lbytes_empty // TODO change as soon as test vectors have been updated
let default_pskID (cs:ciphersuite):pskID_s cs = lbytes_empty


/// def VerifyPSKInputs(mode, psk, pskID):
///   got_psk = (psk != default_psk)
///   if got_psk != (pskID != default_pskID):
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
  -> pskID_hash:lbytes (size_kdf cs)
  -> info_hash:lbytes (size_kdf cs) ->
  Tot (lbytes (size_ks_ctx cs))

let build_context cs m pskID_hash info_hash =
  let context = (id_of_cs cs) @| (id_of_mode m) in
  let context = Seq.append context pskID_hash in
  let context = Seq.append context info_hash in
  context

// TODO This could go into hacl-star/lib/Lib.ByteSequence?
//      However, it should be noted that this function leaks
//      if the two lbytes have the same length or not, i.e.
//      it is not constant time. lbytes_eq seems to be.
let lbytes_equal (#l1:nat) (#l2:size_nat) (b1:bytes{Seq.length b1 = l1}) (b2:lbytes l2) : bool =
  if not (Seq.length b1 = Seq.length b2) then false else
  lbytes_eq #l2 b1 b2

// TODO use heterogenous equality
// TODO replace got_psk and got_pskID by match on an option type?
let verify_psk_inputs (cs:ciphersuite) (m:mode) (psk:psk_s cs) (pskID:pskID_s cs) : bool =
  let got_psk = not (lbytes_equal #(Seq.length psk) #(size_kdf cs) psk (default_psk cs)) in
  let got_pskID = not (lbytes_equal #(Seq.length pskID) #0 pskID (default_pskID cs)) in
  if not (got_psk = got_pskID) then false else // Inconsistent PSK inputs
  match (m, got_psk) with
  | (Base, true) -> false     // PSK input provided when not needed
  | (Auth, true) -> false     // PSK input provided when not needed
  | (PSK, false) -> false     // Missing required PSK input
  | (PSKAuth, false) -> false // Missing required PSK input
  | _ -> true


val key_schedule:
    cs:ciphersuite
  -> m:mode
  -> zz:key_kem_s cs
  -> info:info_s cs
  -> psk:psk_s cs
  -> pskID:pskID_s cs ->
  Pure (encryption_context cs)
    (requires verify_psk_inputs cs m psk pskID)
    (ensures fun _ -> True)

let key_schedule cs m zz info psk pskID =
  let pskID_hash = labeled_extract (hash_of_cs cs) lbytes_empty label_pskID_hash pskID in
  let info_hash = labeled_extract (hash_of_cs cs) lbytes_empty label_info_hash info in
  let context = build_context cs m pskID_hash info_hash in
  let psk_hash = labeled_extract (hash_of_cs cs) lbytes_empty label_psk_hash psk in
  let secret = labeled_extract (hash_of_cs cs) psk_hash label_secret zz in
  let key = labeled_expand (hash_of_cs cs) secret label_key context (size_aead_key cs) in
  let nonce = labeled_expand (hash_of_cs cs) secret label_nonce context (size_aead_nonce cs) in
  let exporter_secret = labeled_expand (hash_of_cs cs) secret label_exp context (size_kdf cs) in
  (key, nonce, 0, exporter_secret)

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
  labeled_expand (hash_of_cs cs) exp_sec label_sec exp_ctx l


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
///   return enc, KeySchedule(mode_base, zz, info, default_psk, default_pskID)

let setupBaseS cs skE pkR info =
  match encap cs skE pkR with
  | None -> None
  | Some (zz, enc) ->
    let enc_ctx = key_schedule cs Base zz info (default_psk cs) (default_pskID cs) in
    Some (enc, enc_ctx)


/// def SetupBaseR(enc, skR, info):
///   zz = Decap(enc, skR)
///   return KeySchedule(mode_base, zz, info, default_psk, default_pskID)

let setupBaseR cs enc skR info =
  let pkR = DH.secret_to_public (curve_of_cs cs) skR in
  let zz = decap cs enc skR in
  match pkR, zz with
  | Some pkR, Some zz ->
    Some (key_schedule cs Base zz info (default_psk cs) (default_pskID cs))
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

// /// def SetupPSKS(pkR, info, psk, pskID):
// ///   zz, enc = Encap(pkR)
// ///   return enc, KeySchedule(mode_psk, zz, info, psk, pskID)

// let setupPSKS cs skE pkR info psk pskID =
//   match encap cs skE pkR with
//   | None -> None
//   | Some (zz, enc) ->
//     assert (verify_psk_inputs cs PSK psk pskID);
//     let enc_ctx = key_schedule cs PSK zz info psk pskID in
//     Some (enc, enc_ctx)


// /// def SetupPSKR(enc, skR, info, psk, pskID):
// ///   zz = Decap(enc, skR)
// ///   return KeySchedule(mode_psk, zz, info, psk, pskID)

// let setupPSKR cs enc skR info psk pskID =
//   let pkR = DH.secret_to_public (curve_of_cs cs) skR in
//   let zz = decap cs enc skR in
//   match pkR, zz with
//   | Some pkR, Some zz ->
//     Some (key_schedule cs PSK zz info psk pskID)
//   | _ -> None

// let sealPSK cs skE pkR info aad pt psk pskID =
//   match setupPSKS cs skE pkR info psk pskID with
//   | None -> None
//   | Some (enc, ctx) ->
//     match context_seal cs ctx aad pt with
//     | None -> None
//     | Some (ctx, ct) -> Some (enc, ct)

// let openPSK cs enc skR info aad ct psk pskID =
//   match setupBaseR cs enc skR info psk pskID with
//   | None -> None
//   | Some ctx ->
//     match context_open cs ctx aad ct with
//     | None -> None
//     | Some (ctx, pt) -> Some pt
