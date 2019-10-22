(** Agile HKDF *)
module EverCrypt.HKDF

module B = LowStar.Buffer

open Spec.Agile.HKDF
open Spec.Hash.Definitions

open FStar.HyperStack.ST
open Lib.IntTypes

#set-options "--max_ifuel 0 --max_fuel 0 --z3rlimit 20"

/// Auxiliary lemmas

let key_and_data_fits (a:hash_alg) : 
  Lemma (block_length a + pow2 32 <= max_input_length a)
=
  let open FStar.Mul in
  assert_norm (8 * 16 + pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125)

let hash_block_length_fits (a:hash_alg) : 
  Lemma (hash_length a + pow2 32 + block_length a < max_input_length a)
=
  let open FStar.Mul in
  assert_norm (8 * 16 + 8 * 8 + pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125)

/// Types for expand and extract
/// Duplicated from Hacl.HKDF because we don't want clients to depend on Hacl.HKDF

inline_for_extraction
let extract_st (a:hash_alg) = 
  prk     : B.buffer uint8 ->
  salt    : B.buffer uint8 ->
  saltlen : pub_uint32 ->
  ikm     : B.buffer uint8 ->
  ikmlen  : pub_uint32 -> 
  Stack unit
  (requires fun h0 -> 
    B.live h0 prk /\ B.live h0 salt /\ B.live h0 ikm /\
    B.disjoint salt prk /\ B.disjoint ikm prk /\
    B.length prk == hash_length a /\
    v saltlen == B.length salt /\
    v ikmlen == B.length ikm /\
    Spec.Agile.HMAC.keysized a (v saltlen) /\
    B.length ikm + block_length a < pow2 32)
  (ensures fun h0 _ h1 ->
    key_and_data_fits a;
    B.modifies (B.loc_buffer prk) h0 h1 /\
    B.as_seq h1 prk == extract a (B.as_seq h0 salt) (B.as_seq h0 ikm))

inline_for_extraction
let expand_st (a:hash_alg) =
  okm     : B.buffer uint8 ->
  prk     : B.buffer uint8 ->
  prklen  : pub_uint32 ->
  info    : B.buffer uint8 ->
  infolen : pub_uint32 ->
  len     : pub_uint32 ->
  Stack unit
  (requires fun h0 -> 
    B.live h0 okm /\ B.live h0 prk /\ B.live h0 info /\
    B.disjoint okm prk /\
    v prklen == B.length prk /\
    v infolen == B.length info /\
    v len == B.length okm /\
    hash_length a <= v prklen /\
    Spec.Agile.HMAC.keysized a (v prklen) /\
    hash_length a + v infolen + 1 + block_length a < pow2 32 /\
    v len <= FStar.Mul.(255 * hash_length a))
  (ensures fun h0 _ h1 ->
    hash_block_length_fits a;
    B.modifies (B.loc_buffer okm) h0 h1 /\
    B.as_seq h1 okm == expand a (B.as_seq h0 prk) (B.as_seq h0 info) (v len))


/// Four monomorphized variants, for callers who already know which algorithm they want

(** @type: true
*)
val expand_sha1: expand_st SHA1

(** @type: true
*)
val extract_sha1: extract_st SHA1

(** @type: true
*)
val expand_sha2_256: expand_st SHA2_256

(** @type: true
*)
val extract_sha2_256: extract_st SHA2_256

(** @type: true
*)
val expand_sha2_384: expand_st SHA2_384

(** @type: true
*)
val extract_sha2_384: extract_st SHA2_384

(** @type: true
*)
val expand_sha2_512: expand_st SHA2_512

(** @type: true
*)
val extract_sha2_512: extract_st SHA2_512


/// Agile versions that dynamically dispatches between the above four

(** @type: true
*)
val expand: a:EverCrypt.HMAC.supported_alg -> expand_st a

(** @type: true
*)
val extract: a:EverCrypt.HMAC.supported_alg -> extract_st a

[@(deprecated "expand")]
let hkdf_expand a okm prk prklen info infolen len = 
  expand a okm prk prklen info infolen len

[@(deprecated "extract")]
let hkdf_extract a prk salt saltlen ikm ikmlen =
  extract a prk salt saltlen ikm ikmlen
