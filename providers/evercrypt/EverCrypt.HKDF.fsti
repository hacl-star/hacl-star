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
  Lemma ((block_length a + pow2 32) `less_than_max_input_length` a)
=
  let open FStar.Mul in
  assert_norm (8 * 16 + pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125)

let hash_block_length_fits (a:hash_alg) :
  Lemma (if is_keccak a then True else hash_length a + pow2 32 + block_length a < Some?.v(max_input_length a))
=
  let open FStar.Mul in
  assert_norm (8 * 16 + 8 * 8 + pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125)

/// Types for expand and extract
/// Duplicated from Hacl.HKDF because we don't want clients to depend on Hacl.HKDF

inline_for_extraction noextract
let extract_st (a:fixed_len_alg) =
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

inline_for_extraction noextract
let expand_st (a:fixed_len_alg) =
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




/// Agile versions that dynamically dispatch between the above four

(** @type: true
*)
[@@ Comment "Expand pseudorandom key to desired length.

@param a Hash function to use. Usually, the same as used in `EverCrypt_HKDF_extract`.
@param okm Pointer to `len` bytes of memory where output keying material is written to.
@param prk Pointer to at least `HashLen` bytes of memory where pseudorandom key is read from. Usually, this points to the output from the extract step.
@param prklen Length of pseudorandom key.
@param info Pointer to `infolen` bytes of memory where context and application specific information is read from.
@param infolen Length of context and application specific information. Can be 0.
@param len Length of output keying material."]
val expand: a:EverCrypt.HMAC.supported_alg -> expand_st a

(** @type: true
*)
[@@ Comment "Extract a fixed-length pseudorandom key from input keying material.

@param a Hash function to use. The allowed values are:
  * `Spec_Hash_Definitions_Blake2B` (`HashLen` = 64), 
  * `Spec_Hash_Definitions_Blake2S` (`HashLen` = 32), 
  * `Spec_Hash_Definitions_SHA2_256` (`HashLen` = 32), 
  * `Spec_Hash_Definitions_SHA2_384` (`HashLen` = 48), 
  * `Spec_Hash_Definitions_SHA2_512` (`HashLen` = 64), and
  * `Spec_Hash_Definitions_SHA1` (`HashLen` = 20).
@param prk Pointer to `HashLen` bytes of memory where pseudorandom key is written to.
  `HashLen` depends on the used algorithm `a`. See above.
@param salt Pointer to `saltlen` bytes of memory where salt value is read from.
@param saltlen Length of salt value.
@param ikm Pointer to `ikmlen` bytes of memory where input keying material is read from.
@param ikmlen Length of input keying material."]
val extract: a:EverCrypt.HMAC.supported_alg -> extract_st a
