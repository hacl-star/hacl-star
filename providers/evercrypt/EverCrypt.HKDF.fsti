module EverCrypt.HKDF

module B = LowStar.Buffer

open FStar.Integers
open EverCrypt.Helpers

open Spec.Agile.HKDF
open Spec.Hash.Definitions

/// IMPLEMENTATION

open FStar.HyperStack.ST

//18-03-05 TODO drop hkdf_ prefix? conflicts with spec name

(** @type: true
*)
val hkdf_extract :
  a       : EverCrypt.HMAC.supported_alg ->
  prk     : B.buffer Lib.IntTypes.uint8{B.length prk == hash_length a} ->
  salt    : B.buffer Lib.IntTypes.uint8 { B.disjoint salt prk /\ Spec.Agile.HMAC.keysized a (B.length salt)} ->
  saltlen : UInt32.t { UInt32.v saltlen == B.length salt } ->
  ikm     : B.buffer Lib.IntTypes.uint8 { B.length ikm + block_length a < pow2 32 /\ B.disjoint ikm prk } ->
  ikmlen  : UInt32.t { UInt32.v ikmlen == B.length ikm } -> Stack unit
  (requires (fun h0 ->
    B.live h0 prk /\ B.live h0 salt /\ B.live h0 ikm ))
  (ensures  (fun h0 r h1 ->
    Hacl.HMAC.key_and_data_fits a;
    LowStar.Modifies.(modifies (loc_buffer prk) h0 h1) /\
    B.as_seq h1 prk == Spec.Agile.HMAC.hmac a (B.as_seq h0 salt) (B.as_seq h0 ikm)))

let hash_block_length_fits (a: hash_alg): Lemma
  (ensures (hash_length a + pow2 32 + block_length a < max_input_length a))
=
  assert_norm (8 * 16 + 8 * 8 + pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125)

(** @type: true
*)
val hkdf_expand :
  a       : EverCrypt.HMAC.supported_alg ->
  okm     : B.buffer Lib.IntTypes.uint8 ->
  prk     : B.buffer Lib.IntTypes.uint8 ->
  prklen  : UInt32.t { UInt32.v prklen == B.length prk } ->
  info    : B.buffer Lib.IntTypes.uint8 ->
  infolen : UInt32.t { UInt32.v infolen == B.length info } ->
  len     : UInt32.t {
    UInt32.v len == B.length okm /\
    B.disjoint okm prk /\
    Spec.Agile.HMAC.keysized a (v prklen) /\
    hash_length a + v infolen + 1 + block_length a < pow2 32 /\
    v len <= 255 * hash_length a } ->
  Stack unit
  (requires (fun h0 -> B.live h0 okm /\ B.live h0 prk /\ B.live h0 info))
  (ensures  (fun h0 r h1 ->
    hash_block_length_fits a;
    LowStar.Modifies.(modifies (loc_buffer okm) h0 h1) /\
    B.as_seq h1 okm == expand a (B.as_seq h0 prk) (B.as_seq h0 info) (v len) ))
