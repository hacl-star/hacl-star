module EverCrypt.DRBG

open FStar.HyperStack.ST
open Lib.IntTypes

open Spec.Hash.Definitions

module HS = FStar.HyperStack
module B = LowStar.Buffer
module S = Spec.HMAC_DRBG

#set-options "--max_ifuel 0 --max_fuel 0"

/// HMAC-DRBG
///
/// See 10.1.2 and B.2 of
/// https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-90Ar1.pdf
///
/// This module implements
/// - HMAC_DRBG_Instantiate_function
/// - HMAC_DRBG_Reseed_function
/// - HMAC_DRBG_Generate_function
/// - HMAC_DRBG_Uninstantiate_function
///
/// Internally, it uses Lib.RandomBuffer.System as the Get_entropy_input function,
/// for instantiation, reseeding, and prediction resistance.
///
/// - Supports SHA-1, SHA2-256, SHA2-384 and SHA2-512
///
/// - Supports reseeding
///
/// - Supports optional personalization_string for instantiation
///
/// - Supports optional additional_input for reseeding and generation
///
/// - Always provides prediction resistance (i.e. reseeds before generation)
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


/// Some duplication from Hacl.HMAC_DRBG because we don't want clients to depend on it

unfold
let supported_alg = S.supported_alg

//[@ CMacro ]
let reseed_interval: n:size_t{v n == S.reseed_interval} =
  assert_norm (S.reseed_interval < pow2 32);
  normalize_term (mk_int S.reseed_interval)

//[@ CMacro ]
let max_output_length: n:size_t{v n == S.max_output_length} =
  assert_norm (S.max_output_length < pow2 32);
  normalize_term (mk_int S.max_output_length)

//[@ CMacro ]
let max_length: n:size_t{v n == S.max_length} =
  assert_norm (S.max_length < pow2 32);
  normalize_term (mk_int S.max_length)

//[@ CMacro ]
let max_personalization_string_length: n:size_t{v n == S.max_personalization_string_length} =
  assert_norm (S.max_personalization_string_length < pow2 32);
  normalize_term (mk_int S.max_personalization_string_length)

//[@ CMacro ]
let max_additional_input_length: n:size_t{v n == S.max_additional_input_length} =
  assert_norm (S.max_additional_input_length < pow2 32);
  normalize_term (mk_int S.max_additional_input_length)

let min_length (a:supported_alg) : n:size_t{v n == S.min_length a} =
  assert_norm (S.min_length a < pow2 32);
  match a with
  | SHA1 -> normalize_term (mk_int (S.min_length SHA1))
  | SHA2_256 | SHA2_384 | SHA2_512 -> normalize_term (mk_int (S.min_length SHA2_256))

/// This has a @CAbstractStruct attribute in the implementation.
/// See https://github.com/FStarLang/kremlin/issues/153
/// 
/// It instructs KreMLin to include only a forward-declarartion
/// in the header file, forcing code to always use `state_s` abstractly
/// through a pointer.
val state_s: supported_alg -> Type0

let state a = B.pointer (state_s a)

val freeable_s: #a:supported_alg -> st:state_s a -> Type0

let freeable (#a:supported_alg) (st:state a) (h:HS.mem) =
  B.freeable st /\ freeable_s (B.deref h st)

val footprint_s: #a:supported_alg -> state_s a -> GTot B.loc

let footprint (#a:supported_alg) (st:state a) (h:HS.mem) =
  B.loc_union (B.loc_addr_of_buffer st) (footprint_s (B.deref h st))

val invariant_s: #a:supported_alg -> state_s a -> HS.mem -> Type0

let invariant (#a:supported_alg) (st:state a) (h:HS.mem) =
  B.live h st /\
  B.loc_disjoint (B.loc_addr_of_buffer st) (footprint_s (B.deref h st)) /\
  invariant_s (B.deref h st) h

let disjoint_st (#t:Type) (#a:supported_alg) 
  (st:state a) (b:B.buffer t) (h:HS.mem) 
=
  B.loc_disjoint (footprint st h) (B.loc_buffer b)
 
val repr: #a:supported_alg -> st:state a -> h:HS.mem -> GTot (S.state a)

/// TR: the following pattern is necessary because, if we generically
/// add such a pattern directly on `loc_includes_union_l`, then
/// verification will blowup whenever both sides of `loc_includes` are
/// `loc_union`s. We would like to break all unions on the
/// right-hand-side of `loc_includes` first, using
/// `loc_includes_union_r`.  Here the pattern is on `footprint_s`,
/// because we already expose the fact that `footprint` is a
/// `loc_union`. (In other words, the pattern should be on every
/// smallest location that is not exposed to be a `loc_union`.)
///
val loc_includes_union_l_footprint_s: #a:supported_alg -> l1:B.loc -> l2:B.loc -> st:state_s a
  -> Lemma
  (requires B.loc_includes l1 (footprint_s st) \/ B.loc_includes l2 (footprint_s st))
  (ensures  B.loc_includes (B.loc_union l1 l2) (footprint_s st))
  [SMTPat (B.loc_includes (B.loc_union l1 l2) (footprint_s st))]

/// Needed to prove that the footprint is disjoint from any fresh location
val invariant_loc_in_footprint: #a:supported_alg -> st:state a -> h:HS.mem 
  -> Lemma
  (requires invariant st h)
  (ensures  B.loc_in (footprint st h) h)
  [SMTPat (invariant st h)]

val frame_invariant: #a:supported_alg -> l:B.loc -> st:state a -> h0:HS.mem -> h1:HS.mem 
  -> Lemma
  (requires
    invariant st h0 /\
    B.loc_disjoint l (footprint st h0) /\
    B.modifies l h0 h1)
  (ensures
    invariant st h1 /\
    repr st h0 == repr st h1)

let preserves_freeable #a (st:state a) (h0 h1:HS.mem)  =
  freeable st h0 ==> freeable st h1

inline_for_extraction
val alloca: a:supported_alg -> StackInline (state a)
  (requires fun _ -> True)
  (ensures  fun h0 st h1 ->
    B.modifies B.loc_none h0 h1 /\
    B.fresh_loc (footprint st h1) h0 h1 /\
    B.(loc_includes (loc_region_only true (HS.get_tip h1)) (footprint st h1)) /\
    invariant st h1)

inline_for_extraction noextract
val create_in: a:supported_alg -> r:HS.rid -> ST (state a)
  (requires fun _ -> is_eternal_region r)
  (ensures  fun h0 st h1 ->
    B.modifies B.loc_none h0 h1 /\
    B.fresh_loc (footprint st h1) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint st h1)) /\
    invariant st h1 /\
    freeable st h1)

(** @type: true
*)
inline_for_extraction
val create: a:supported_alg -> ST (state a)
  (requires fun _ -> True)
  (ensures  fun h0 st h1 ->
    B.modifies B.loc_none h0 h1 /\
    B.fresh_loc (footprint st h1) h0 h1 /\
    invariant st h1 /\
    freeable st h1)


inline_for_extraction
let instantiate_st (a:supported_alg) =
    st:state a
  -> personalization_string:B.buffer uint8
  -> personalization_string_len:size_t
  -> Stack bool
  (requires fun h0 ->
    invariant st h0 /\
    B.live h0 personalization_string /\ 
    disjoint_st st personalization_string h0 /\
    B.length personalization_string = v personalization_string_len)
  (ensures  fun h0 b h1 ->
    S.hmac_input_bound a;
    if not b then
      B.modifies B.loc_none h0 h1
    else
      v personalization_string_len <= S.max_personalization_string_length /\
      invariant st h1 /\
      preserves_freeable st h0 h1 /\
      footprint st h0 == footprint st h1 /\
      B.modifies (footprint st h0) h0 h1 /\
      (exists entropy_input nonce.
        S.min_length a <= Seq.length entropy_input /\
        Seq.length entropy_input <= S.max_length /\
        S.min_length a / 2 <= Seq.length nonce /\
        Seq.length nonce <= S.max_length /\
        repr st h1 ==
        S.instantiate entropy_input nonce (B.as_seq h0 personalization_string)))

(** @type: true 
*)
val instantiate_sha1    : instantiate_st SHA1

(** @type: true 
*)
val instantiate_sha2_256: instantiate_st SHA2_256

(** @type: true 
*)
val instantiate_sha2_384: instantiate_st SHA2_384

(** @type: true 
*)
val instantiate_sha2_512: instantiate_st SHA2_512


inline_for_extraction
let reseed_st (a:supported_alg) =
    st:state a
  -> additional_input:B.buffer uint8
  -> additional_input_len:size_t
  -> Stack bool
  (requires fun h0 ->
    invariant st h0 /\
    B.live h0 additional_input /\
    disjoint_st st additional_input h0 /\
    B.length additional_input = v additional_input_len)
  (ensures  fun h0 b h1 ->
    S.hmac_input_bound a;
    if not b then
      B.modifies B.loc_none h0 h1
    else
      v additional_input_len <= S.max_additional_input_length /\
      footprint st h0 == footprint st h1 /\
      invariant st h1 /\
      preserves_freeable st h0 h1 /\
      B.modifies (footprint st h0) h0 h1 /\
      (exists entropy_input.
        S.min_length a <= Seq.length entropy_input /\
        Seq.length entropy_input <= S.max_length /\
        repr st h1 ==
        S.reseed (repr st h0) entropy_input (B.as_seq h0 additional_input)))

(** @type: true 
*)
val reseed_sha1    : reseed_st SHA1

(** @type: true 
*)
val reseed_sha2_256: reseed_st SHA2_256

(** @type: true 
*)
val reseed_sha2_384: reseed_st SHA2_384

(** @type: true 
*)
val reseed_sha2_512: reseed_st SHA2_512


inline_for_extraction
let generate_st (a:supported_alg) =
    output:B.buffer uint8
  -> st:state a
  -> n:size_t
  -> additional_input:B.buffer uint8
  -> additional_input_len:size_t
  -> Stack bool
  (requires fun h0 ->
    invariant st h0 /\
    B.live h0 output /\ B.live h0 additional_input /\
    disjoint_st st output h0 /\ disjoint_st st additional_input h0 /\
    B.disjoint output additional_input /\
    B.length additional_input = v additional_input_len /\
    v n = B.length output)
  (ensures  fun h0 b h1 ->
    S.hmac_input_bound a;
    if not b then
      B.modifies B.loc_none h0 h1
    else
      v n <= S.max_output_length /\
      v additional_input_len <= S.max_additional_input_length /\
      invariant st h1 /\
      preserves_freeable st h0 h1 /\
      footprint st h0 == footprint st h1 /\
      B.modifies (B.loc_union (B.loc_buffer output) (footprint st h0)) h0 h1 /\
      (exists entropy_input.
       S.min_length a <= Seq.length entropy_input /\
       Seq.length entropy_input <= S.max_length /\
       (let st1 = S.reseed (repr st h0) entropy_input (B.as_seq h0 additional_input) in
        match S.generate st1 (v n) (B.as_seq h0 additional_input) with
        | None -> False // Always reseeds, so generation cannot fail
        | Some (out, st_) ->
          repr st h1 == st_ /\
          B.as_seq h1 output == out)))

(** @type: true 
*)
val generate_sha1    : generate_st SHA1

(** @type: true 
*)
val generate_sha2_256: generate_st SHA2_256

(** @type: true 
*)
val generate_sha2_384: generate_st SHA2_384

(** @type: true 
*)
val generate_sha2_512: generate_st SHA2_512


inline_for_extraction
let uninstantiate_st (a:supported_alg) =
    st:state a
  -> ST unit
  (requires fun h0 -> freeable st h0 /\ invariant st h0)
  (ensures  fun h0 _ h1 -> B.modifies (footprint st h0) h0 h1)

(** @type: true 
*)
val uninstantiate_sha1    : uninstantiate_st SHA1

(** @type: true 
*)
val uninstantiate_sha2_256: uninstantiate_st SHA2_256

(** @type: true 
*)
val uninstantiate_sha2_384: uninstantiate_st SHA2_384

(** @type: true 
*)
val uninstantiate_sha2_512: uninstantiate_st SHA2_512


/// Agile variants that dispatch dynamically to the appropriate monomorphic variants above
/// by pattern matching on the struct tag (rather than the algorithm, which is erased)

(** @type: true 
*)
val instantiate: a:(Ghost.erased supported_alg) -> instantiate_st (Ghost.reveal a)

(** @type: true 
*)
val reseed: a:(Ghost.erased supported_alg) -> reseed_st (Ghost.reveal a)

(** @type: true 
*)
val generate:  a:(Ghost.erased supported_alg) -> generate_st (Ghost.reveal a)

(** @type: true
*)
val uninstantiate: a:(Ghost.erased supported_alg) -> uninstantiate_st (Ghost.reveal a)
