module EverCrypt.DRBG

open FStar.HyperStack.ST
open Lib.IntTypes

open Spec.Hash.Definitions

module HS = FStar.HyperStack
module B = LowStar.Buffer
module S = Spec.HMAC_DRBG

open Hacl.HMAC_DRBG
open Lib.RandomBuffer.System
open LowStar.BufferOps

friend Hacl.HMAC_DRBG

#set-options "--max_ifuel 0 --max_fuel 0 --z3rlimit 50"

/// Some duplication from Hacl.HMAC_DRBG because we don't want clients to depend on it
///
/// Respects EverCrypt convention and reverses order of buf_len, buf arguments

[@CAbstractStruct]
noeq
type state_s: supported_alg -> Type0 =
| SHA1_s    : state SHA1     -> state_s SHA1
| SHA2_256_s: state SHA2_256 -> state_s SHA2_256
| SHA2_384_s: state SHA2_384 -> state_s SHA2_384
| SHA2_512_s: state SHA2_512 -> state_s SHA2_512

let invert_state_s (a:supported_alg): Lemma
  (requires True)
  (ensures inversion (state_s a))
  [ SMTPat (state_s a) ]
=
  allow_inversion (state_s a)

/// Only call this function in extracted code with a known `a`
inline_for_extraction noextract
let p #a (s:state_s a) : Hacl.HMAC_DRBG.state a =
  match a with
  | SHA1 -> let SHA1_s p = s in p
  | SHA2_256 -> let SHA2_256_s p = s in p
  | SHA2_384 -> let SHA2_384_s p = s in p
  | SHA2_512 -> let SHA2_512_s p = s in p

let freeable_s #a st = freeable (p st)

let footprint_s #a st = footprint (p st)

let invariant_s #a st h = invariant (p st) h

let repr #a st h =
  let st = B.get h st 0 in
  repr (p st) h

let loc_includes_union_l_footprint_s #a l1 l2 st =
  B.loc_includes_union_l l1 l2 (footprint_s st)

let invariant_loc_in_footprint #a st m = ()

let frame_invariant #a l st h0 h1 = ()

/// State allocation

// Would like to specialize alloca in each branch, but two calls to StackInline
// functions in the same block lead to variable redefinitions at extraction.
let alloca a =
  let st =
    match a with
    | SHA1     -> SHA1_s (alloca a)
    | SHA2_256 -> SHA2_256_s (alloca a)
    | SHA2_384 -> SHA2_384_s (alloca a)
    | SHA2_512 -> SHA2_512_s (alloca a)
  in
  B.alloca st 1ul

let create_in a r =
  let st =
    match a with
    | SHA1     -> SHA1_s     (create_in SHA1 r)
    | SHA2_256 -> SHA2_256_s (create_in SHA2_256 r)
    | SHA2_384 -> SHA2_384_s (create_in SHA2_384 r)
    | SHA2_512 -> SHA2_512_s (create_in SHA2_512 r)
  in
  B.malloc r st 1ul

let create a = create_in a HS.root

/// Instantiate function

inline_for_extraction noextract
val mk_instantiate: #a:supported_alg -> EverCrypt.HMAC.compute_st a -> instantiate_st a
let mk_instantiate #a hmac st personalization_string personalization_string_len =
  if personalization_string_len >. max_personalization_string_length then
    false
  else
    let entropy_input_len = min_length a in
    let nonce_len = min_length a /. 2ul in
    let min_entropy = entropy_input_len +! nonce_len in
    push_frame();
    assert_norm (range (v min_entropy) U32);
    let entropy = B.alloca (u8 0) min_entropy in
    let ok = randombytes entropy min_entropy in
    let result =
      if not ok then
        false
      else
        begin
        let entropy_input = B.sub entropy 0ul entropy_input_len in
        let nonce = B.sub entropy entropy_input_len nonce_len in
        S.hmac_input_bound a;
        let st_s = !*st in
        mk_instantiate hmac (p st_s)
          entropy_input_len entropy_input
          nonce_len nonce
          personalization_string_len personalization_string;
        true
        end
    in
    pop_frame();
    result

let instantiate_sha1     = mk_instantiate EverCrypt.HMAC.compute_sha1
let instantiate_sha2_256 = mk_instantiate EverCrypt.HMAC.compute_sha2_256
let instantiate_sha2_384 = mk_instantiate EverCrypt.HMAC.compute_sha2_384
let instantiate_sha2_512 = mk_instantiate EverCrypt.HMAC.compute_sha2_512


/// Reseed function

inline_for_extraction noextract
val mk_reseed: #a:supported_alg -> EverCrypt.HMAC.compute_st a -> reseed_st a
let mk_reseed #a hmac st additional_input additional_input_len =
  if additional_input_len >. max_additional_input_length then
    false
  else
    let entropy_input_len = min_length a in
    push_frame();
    let entropy_input = B.alloca (u8 0) entropy_input_len in
    let ok = randombytes entropy_input entropy_input_len in
    let result =
      if not ok then
        false
      else
        begin
        S.hmac_input_bound a;
        let st_s = !*st in
        mk_reseed hmac (p st_s)
          entropy_input_len entropy_input
          additional_input_len additional_input;
        true
        end
    in
    pop_frame();
    result

let reseed_sha1     = mk_reseed EverCrypt.HMAC.compute_sha1
let reseed_sha2_256 = mk_reseed EverCrypt.HMAC.compute_sha2_256
let reseed_sha2_384 = mk_reseed EverCrypt.HMAC.compute_sha2_384
let reseed_sha2_512 = mk_reseed EverCrypt.HMAC.compute_sha2_512

/// Generate function

inline_for_extraction noextract
val mk_generate: #a:supported_alg -> EverCrypt.HMAC.compute_st a -> generate_st a
let mk_generate #a hmac output st n additional_input additional_input_len =
  if additional_input_len >. max_additional_input_length || n >. max_output_length then
    false
  else
  let entropy_input_len = min_length a in
  push_frame();
  let ok = mk_reseed hmac st additional_input additional_input_len in
  let result =
    if not ok then
      false
    else
      begin
      let st_s = !*st in
      let b = mk_generate hmac
        output (p st_s) n additional_input_len additional_input in
      true
      end
  in
  let h1 = get () in
  pop_frame();
  let h2 = get () in
  frame_invariant (B.loc_all_regions_from false (HS.get_tip h1)) st h1 h2;
  result

let generate_sha1     = mk_generate EverCrypt.HMAC.compute_sha1
let generate_sha2_256 = mk_generate EverCrypt.HMAC.compute_sha2_256
let generate_sha2_384 = mk_generate EverCrypt.HMAC.compute_sha2_384
let generate_sha2_512 = mk_generate EverCrypt.HMAC.compute_sha2_512

/// Uninstantiate function

inline_for_extraction noextract
val mk_uninstantiate: a:supported_alg -> uninstantiate_st a
let mk_uninstantiate a st =
  let st_s:state_s a = !*st in
  let s:Hacl.HMAC_DRBG.state a = p st_s in
  let k:B.buffer uint8 = s.k in
  let v:B.buffer uint8 = s.v in
  let ctr:B.buffer size_t = s.reseed_counter in
  assert (B.disjoint k v /\ B.disjoint k ctr /\ B.disjoint v ctr);
  assert (B.loc_disjoint (B.loc_addr_of_buffer st) (footprint_s st_s));
  Lib.Memzero.clear_words_u8 (hash_len a) k;
  Lib.Memzero.clear_words_u8 (hash_len a) v;
  ctr.(0ul) <- 0ul;
  B.free k;
  B.free v;
  B.free ctr;
  B.free st

let uninstantiate_sha1     = mk_uninstantiate SHA1
let uninstantiate_sha2_256 = mk_uninstantiate SHA2_256
let uninstantiate_sha2_384 = mk_uninstantiate SHA2_384
let uninstantiate_sha2_512 = mk_uninstantiate SHA2_512


/// Agile variants that dispatch dynamically to the appropriate monomorphic variants above

let instantiate a st personalization_string personalization_string_len =
  match !*st with
  | SHA1_s _     -> instantiate_sha1     st personalization_string personalization_string_len
  | SHA2_256_s _ -> instantiate_sha2_256 st personalization_string personalization_string_len
  | SHA2_384_s _ -> instantiate_sha2_384 st personalization_string personalization_string_len
  | SHA2_512_s _ -> instantiate_sha2_512 st personalization_string personalization_string_len

let reseed a st additional_input additional_input_len =
  match !*st with
  | SHA1_s _     -> reseed_sha1     st additional_input additional_input_len
  | SHA2_256_s _ -> reseed_sha2_256 st additional_input additional_input_len
  | SHA2_384_s _ -> reseed_sha2_384 st additional_input additional_input_len
  | SHA2_512_s _ -> reseed_sha2_512 st additional_input additional_input_len

let generate a output st n additional_input additional_input_len =
  match !*st with
  | SHA1_s _     -> generate_sha1     output st n additional_input additional_input_len
  | SHA2_256_s _ -> generate_sha2_256 output st n additional_input additional_input_len
  | SHA2_384_s _ -> generate_sha2_384 output st n additional_input additional_input_len
  | SHA2_512_s _ -> generate_sha2_512 output st n additional_input additional_input_len

let uninstantiate a st =
  match !* st with
  | SHA1_s _     -> uninstantiate_sha1 st
  | SHA2_256_s _ -> uninstantiate_sha2_256 st
  | SHA2_384_s _ -> uninstantiate_sha2_384 st
  | SHA2_512_s _ -> uninstantiate_sha2_512 st
