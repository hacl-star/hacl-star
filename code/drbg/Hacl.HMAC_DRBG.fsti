module Hacl.HMAC_DRBG

open FStar.HyperStack.ST

open Spec.Hash.Definitions

open Lib.IntTypes
open Lib.Buffer

module HS = FStar.HyperStack
module B = LowStar.Buffer
module LSeq = Lib.Sequence

module HMAC = Hacl.HMAC
module S = Spec.HMAC_DRBG

/// HMAC-DRBG
///
/// See 10.1.2 and B.2 of
/// https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-90Ar1.pdf
///
/// This module implements the hash-algorithm-agile algorithms
/// - HMAC_DRBG_Update (not exposed by the interface)
/// - HMAC_DRBG_Instantiate_algorithm
/// - HMAC_DRBG_Reseed_algorithm
/// - HMAC_DRBG_Generate_algorithm
///
/// This is not linked to an appropriate Get_entropy_input function,
/// so these algorithms should be combined to get entropy from Get_entropy_input
/// for instantiation, reseeding, and optional prediction resistance.
///
/// - Supports SHA-1, SHA2-256, SHA2-384 and SHA2-512 hash algorithms
///
/// - Supports reseeding
///
/// - Supports optional personalization_string for instantiation
///
/// - Supports optional additional_input for reseeding and generation
///
/// - The internal state is (Key,V,reseed_counter)
///
/// - The security_strength is the HMAC-strength of the hash algorithm as per p.54 of
///   https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-57pt1r4.pdf
///
/// - The minimum entropy for instantiation is 3/2 * security_strength.
///    - entropy_input must have at least security_strength bits.
///    - nonce must have at least 1/2 security_strength bits.
///    - entropy_input and nonce can have at most max_length = 2^16 bits.
///
/// - At most max_number_of_bits_per_request = 2^16 bits can be generated per request.
///
/// - The reseed_interval is 2^10

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

unfold
let supported_alg = S.supported_alg

let reseed_interval: n:size_t{v n == S.reseed_interval} =
  assert_norm (S.reseed_interval < pow2 32);
  normalize_term (mk_int S.reseed_interval)

let max_output_length: n:size_t{v n == S.max_output_length} =
  assert_norm (S.max_output_length < pow2 32);
  normalize_term (mk_int S.max_output_length)

let max_length: n:size_t{v n == S.max_length} =
  assert_norm (S.max_length < pow2 32);
  normalize_term (mk_int S.max_length)

let max_personalization_string_length: n:size_t{v n == S.max_personalization_string_length} =
  assert_norm (S.max_personalization_string_length < pow2 32);
  normalize_term (mk_int S.max_personalization_string_length)

let max_additional_input_length: n:size_t{v n == S.max_additional_input_length} =
  assert_norm (S.max_additional_input_length < pow2 32);
  normalize_term (mk_int S.max_additional_input_length)

[@@ Comment "Return the minimal entropy input length of the desired hash function.

@param a Hash algorithm to use."]
let min_length (a:supported_alg) : n:size_t{v n == S.min_length a} =
  assert_norm (S.min_length a < pow2 32);
  match a with
  | SHA1 -> normalize_term (mk_int (S.min_length SHA1))
  | SHA2_256 | SHA2_384 | SHA2_512 -> normalize_term (mk_int (S.min_length SHA2_256))

val state: supported_alg -> Type0

inline_for_extraction noextract
val freeable: #a:supported_alg -> st:state a -> Type0

val footprint: #a:supported_alg -> st:state a -> GTot B.loc

inline_for_extraction noextract
val invariant: #a:supported_alg -> st:state a -> h:HS.mem -> Type0

inline_for_extraction noextract
let disjoint_st (#a:supported_alg) (st:state a) (b:buffer uint8) =
  B.loc_disjoint (footprint st) (B.loc_buffer b)

val repr: #a:supported_alg -> st:state a -> h:HS.mem -> GTot (S.state a)

inline_for_extraction noextract
val alloca: a:supported_alg -> StackInline (state a)
  (requires fun _ -> True)
  (ensures  fun h0 st h1 ->
    B.modifies B.loc_none h0 h1 /\
    B.fresh_loc (footprint st) h0 h1 /\
    B.(loc_includes (loc_region_only true (HS.get_tip h1)) (footprint st)) /\
    invariant st h1)

[@@ Comment "Create a DRBG state.

@param a Hash algorithm to use. The possible instantiations are ...
  * `Spec_Hash_Definitions_SHA2_256`,
  * `Spec_Hash_Definitions_SHA2_384`,
  * `Spec_Hash_Definitions_SHA2_512`, and
  * `Spec_Hash_Definitions_SHA1`."]
inline_for_extraction
val create_in: a:supported_alg -> r:HS.rid -> ST (state a)
  (requires fun _ -> is_eternal_region r)
  (ensures  fun h0 st h1 ->
    B.modifies B.loc_none h0 h1 /\
    B.fresh_loc (footprint st) h0 h1 /\
    B.(loc_includes (loc_region_only true r)) (footprint st) /\
    invariant st h1 /\
    freeable st)

inline_for_extraction noextract
let instantiate_st (a:supported_alg) =
    st:state a
  -> entropy_input_len:size_t
  -> entropy_input:lbuffer uint8 entropy_input_len
  -> nonce_len:size_t
  -> nonce:lbuffer uint8 nonce_len
  -> personalization_string_len:size_t
  -> personalization_string:lbuffer uint8 personalization_string_len
  -> Stack unit
  (requires fun h0 ->
    live h0 entropy_input /\ live h0 nonce /\ live h0 personalization_string /\
    invariant st h0 /\
    S.min_length a <= v entropy_input_len /\ v entropy_input_len <= v max_length /\
    S.min_length a / 2 <= v nonce_len /\ v nonce_len <= v max_length /\
    v personalization_string_len <= S.max_personalization_string_length)
  (ensures  fun h0 _ h1 ->
    S.hmac_input_bound a;
    invariant st h1 /\
    B.modifies (footprint st) h0 h1 /\
    repr st h1 ==
    S.instantiate
      (as_seq h0 entropy_input)
      (as_seq h0 nonce)
      (as_seq h0 personalization_string))

inline_for_extraction noextract
val mk_instantiate: #a:supported_alg -> hmac:HMAC.compute_st a -> instantiate_st a

[@@ Comment "Instantiate the DRBG.

@param a Hash algorithm to use. (Value must match the value used in `Hacl_HMAC_DRBG_create_in`.)
@param st Pointer to DRBG state.
@param entropy_input_len Length of entropy input.
@param entropy_input Pointer to `entropy_input_len` bytes of memory where entropy input is read from.
@param nonce_len Length of nonce.
@param nonce Pointer to `nonce_len` bytes of memory where nonce is read from.
@param personalization_string_len length of personalization string.
@param personalization_string Pointer to `personalization_string_len` bytes of memory where personalization string is read from."]
val instantiate: a:supported_alg -> instantiate_st a

inline_for_extraction noextract
let reseed_st (a:supported_alg) =
    st:state a
  -> entropy_input_len:size_t
  -> entropy_input:lbuffer uint8 entropy_input_len
  -> additional_input_len:size_t
  -> additional_input:lbuffer uint8 additional_input_len
  -> Stack unit
  (requires fun h0 ->
    invariant st h0 /\ live h0 entropy_input /\ live h0 additional_input /\
    disjoint_st st entropy_input /\ disjoint_st st additional_input /\
    S.min_length a <= v entropy_input_len /\ v entropy_input_len <= v max_length /\
    v additional_input_len <= S.max_additional_input_length)
  (ensures  fun h0 _ h1 ->
    S.hmac_input_bound a;
    invariant st h1 /\
    B.modifies (footprint st) h0 h1 /\
    repr st h1 ==
    S.reseed
      (repr st h0)
      (as_seq h0 entropy_input)
      (as_seq h0 additional_input))

inline_for_extraction noextract
val mk_reseed: #a:supported_alg -> hmac:HMAC.compute_st a -> reseed_st a

[@@ Comment "Reseed the DRBG.

@param a Hash algorithm to use. (Value must match the value used in `Hacl_HMAC_DRBG_create_in`.)
@param st Pointer to DRBG state.
@param entropy_input_len Length of entropy input.
@param entropy_input Pointer to `entropy_input_len` bytes of memory where entropy input is read from.
@param additional_input_input_len Length of additional input.
@param additional_input_input Pointer to `additional_input_input_len` bytes of memory where additional input is read from."]
val reseed: a:supported_alg -> reseed_st a

inline_for_extraction noextract
let generate_st (a:supported_alg) =
    output:buffer uint8
  -> st:state a
  -> n:size_t
  -> additional_input_len:size_t
  -> additional_input:lbuffer uint8 additional_input_len
  -> Stack bool
  (requires fun h0 ->
    live h0 output /\ invariant st h0 /\ live h0 additional_input /\
    disjoint_st st output /\ disjoint_st st additional_input /\
    disjoint output additional_input /\
    v n = length output /\
    v n <= S.max_output_length /\
    v additional_input_len <= S.max_additional_input_length)
  (ensures  fun h0 b h1 ->
    S.hmac_input_bound a;
    match S.generate (repr st h0) (v n) (as_seq h0 additional_input) with
    | None -> b = false /\ invariant st h1 /\ modifies0 h0 h1
    | Some (out, st_) ->
      b = true /\
      invariant st h1 /\
      B.modifies (loc output |+| footprint st) h0 h1 /\
      repr st h1 == st_ /\
      as_seq #MUT #_ #n h1 output == out)

inline_for_extraction noextract
val mk_generate: #a:supported_alg -> HMAC.compute_st a -> generate_st a

[@@ Comment "Generate output.

@param a Hash algorithm to use. (Value must match the value used in `create_in`.)
@param output Pointer to `n` bytes of memory where random output is written to.
@param st Pointer to DRBG state.
@param n Length of desired output.
@param additional_input_input_len Length of additional input.
@param additional_input_input Pointer to `additional_input_input_len` bytes of memory where additional input is read from."]
val generate: a:supported_alg -> generate_st a

inline_for_extraction noextract
let free_st (a: supported_alg) =
  s:state a -> ST unit
  (requires fun h0 ->
    freeable s /\
    invariant s h0)
  (ensures fun h0 _ h1 ->
    B.(modifies (footprint s) h0 h1))

val free: #a:supported_alg -> free_st a
