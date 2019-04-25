module EverCrypt.HKDF

open FStar.Integers
open EverCrypt.Helpers
open EverCrypt.Hash

open Spec.HKDF
open Spec.Hash.Definitions

/// IMPLEMENTATION

//open FStar.Ghost
open FStar.HyperStack.All
open LowStar.Buffer

//18-03-05 TODO drop hkdf_ prefix? conflicts with spec name

(** @type: true
*)
val hkdf_extract :
  a       : EverCrypt.HMAC.supported_alg ->
  prk     : uint8_pl (tagLength a) ->
  salt    : uint8_p { disjoint salt prk /\ Spec.HMAC.keysized a (length salt)} ->
  saltlen : uint8_l salt ->
  ikm     : uint8_p { length ikm + blockLength a < pow2 32 /\ disjoint ikm prk } ->
  ikmlen  : uint8_l ikm -> Stack unit
  (requires (fun h0 ->
    live h0 prk /\ live h0 salt /\ live h0 ikm ))
  (ensures  (fun h0 r h1 ->
    live h1 prk /\ LowStar.Modifies.(modifies (loc_buffer prk) h0 h1) /\
    length ikm + blockLength a < maxLength a /\
    as_seq h1 prk == Spec.HMAC.hmac a (as_seq h0 salt) (as_seq h0 ikm)))

(** @type: true
*)
val hkdf_expand :
  a       : EverCrypt.HMAC.supported_alg ->
  okm     : uint8_p ->
  prk     : uint8_p -> prklen  : uint8_l prk ->
  info    : uint8_p -> infolen : uint8_l info ->
  len     : uint8_l okm {
    disjoint okm prk /\
    Spec.HMAC.keysized a (v prklen) /\
    tagLength a + v infolen + 1 + blockLength a < pow2 32 /\
    v len <= 255 * tagLength a } ->
  Stack unit
  (requires (fun h0 -> live h0 okm /\ live h0 prk /\ live h0 info))
  (ensures  (fun h0 r h1 ->
    live h1 okm /\ LowStar.Modifies.(modifies (loc_buffer okm) h0 h1) /\
    tagLength a + pow2 32 + blockLength a < maxLength a /\ // required for v len below
    as_seq h1 okm = expand a (as_seq h0 prk) (as_seq h0 info) (v len) ))


/// HIGH-LEVEL WRAPPERS (TBC)
