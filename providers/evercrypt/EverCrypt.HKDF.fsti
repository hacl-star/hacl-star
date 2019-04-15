module EverCrypt.HKDF

open FStar.Integers
open EverCrypt.Helpers
open EverCrypt.Hash

noextract
unfold let bytes = Spec.Hash.Definitions.bytes
noextract
unfold let lbytes = EverCrypt.HMAC.lbytes

/// FUNCTIONAL SPECIFICATION:
///
/// * extraction is just HMAC using the salt as key and the input
///   keying materials as text.
///
/// * expansion does its own formatting of input key materials.

open FStar.Seq

let extract a salt ikm = EverCrypt.HMAC.hmac a salt ikm

// [a, prk, info] are fixed.
// [required] is the number of bytes to be extracted
// [count] is the number of extracted blocks so far
// [last] is empty for count=0 then set to the prior tag for chaining.
let rec expand0 :
  a: Hash.alg ->
  prk: bytes ->
  info: bytes ->
  required: nat ->
  count: nat ->
  last: bytes {
    let chainLength = if count = 0 then 0 else tagLength a in
    HMAC.keysized a (Seq.length prk) /\
    Seq.length last = chainLength /\
    tagLength a + length info + 1 + blockLength a < maxLength a /\
    count < 255 /\
    required <= (255 - count) * tagLength a } ->
  GTot (lbytes required)
=
  fun a prk info required count last ->
  let count = count + 1 in
  let text = last @| info @| Seq.create 1 (UInt8.uint_to_t count) in
  let tag = EverCrypt.HMAC.hmac a prk text in
  if required <= tagLength a
  then fst (split tag required)
  else tag @| expand0 a prk info (required - tagLength a) count tag

let expand:
  a: Hash.alg ->
  prk: bytes ->
  info: bytes ->
  required: nat {
    HMAC.keysized a (Seq.length prk) /\
    tagLength a + length info + 1 + blockLength a < maxLength a /\
    required <= 255 * tagLength a } ->
  GTot (lbytes required)
=
  fun a prk info required ->
  expand0 a prk info required 0 Seq.empty


(* 18-03-05 TBC, requires TLS libraries

/// Details specific to TLS 1.3; should move to its own module.
///
/// Since derivations depend on the concrete info,
/// we will need to prove format injective.

let tls13_prefix: Bytes.lbytes 6 =
  let s = Bytes.bytes_of_string "tls_13 " in
  assume(Bytes.length s = 6); // a bit lame; not sure how to deal with such constants
  s

let format: (
  a: Hash.alg ->
  label: string{length (Bytes.bytes_of_string label) < 256 - 6} ->
  hv: uint8_p {length hv < 256} ->
  len: UInt32.t {v len <= 255 * tagLength ha} ->
  Tot bytes )
=
  fun ha label hv len ->
  let label_bytes = tls13_prefix @| Bytes.reveal (Bytes.bytes_of_string label) in
  // lemma_repr_bytes_values (v len);
  // lemma_repr_bytes_values (length label_bytes);
  // lemma_repr_bytes_values (length hv);
  FStar.Bytes.(reveal (bytes_of_int 2 (v len) @| vlbytes 1 label_bytes @| vlbytes 1 hv))

val expand_label:
  #a: Hashing.alg ->
  prk: hkey a ->
  label: string{length (bytes_of_string label) < 256 - 6} -> // -9?
  hv: bytes{length hv < 256} ->
  length: nat {length <= 255 * tagLength a} -> luint8_p length
let expand_label #a prk label hv length =
  expand prk (format a label hv length) length

let expand_secret #a prk label hv = expand_label prk label hv (tagLength a)

/// Details specific to QUIC; could move to its own module

//18-04-10 TODO code in Low* [quic_provider.quic_crypto_hkdf_quic_label]

*)




/// IMPLEMENTATION

//open FStar.Ghost
open FStar.HyperStack.All
open LowStar.Buffer

//18-03-05 TODO drop hkdf_ prefix? conflicts with spec name

(** @type: true
*)
val hkdf_extract :
  a       : alg ->
  prk     : uint8_pl (tagLength a) ->
  salt    : uint8_p { disjoint salt prk /\ HMAC.keysized a (length salt)} ->
  saltlen : uint8_l salt ->
  ikm     : uint8_p { length ikm + blockLength a < pow2 32 /\ disjoint ikm prk } ->
  ikmlen  : uint8_l ikm -> ST unit
  (requires (fun h0 ->
    live h0 prk /\ live h0 salt /\ live h0 ikm ))
  (ensures  (fun h0 r h1 ->
    live h1 prk /\ LowStar.Modifies.(modifies (loc_buffer prk) h0 h1) /\
    length ikm + blockLength a < maxLength a /\
    as_seq h1 prk == HMAC.hmac a (as_seq h0 salt) (as_seq h0 ikm)))

(** @type: true
*)
val hkdf_expand :
  a       : alg ->
  okm     : uint8_p ->
  prk     : uint8_p -> prklen  : uint8_l prk ->
  info    : uint8_p -> infolen : uint8_l info ->
  len     : uint8_l okm {
    disjoint okm prk /\
    HMAC.keysized a (v prklen) /\
    tagLength a + v infolen + 1 + blockLength a < pow2 32 /\
    v len <= 255 * tagLength a } ->
  ST unit
  (requires (fun h0 -> live h0 okm /\ live h0 prk /\ live h0 info))
  (ensures  (fun h0 r h1 ->
    live h1 okm /\ LowStar.Modifies.(modifies (loc_buffer okm) h0 h1) /\
    tagLength a + pow2 32 + blockLength a < maxLength a /\ // required for v len below
    as_seq h1 okm = expand a (as_seq h0 prk) (as_seq h0 info) (v len) ))


/// HIGH-LEVEL WRAPPERS (TBC)
