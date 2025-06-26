module EverCrypt.Hash.Incremental

open FStar.Mul

// Watch out: keep the module declarations in sync between fsti and fst
// (otherwise interleaving issues may bite).
module B = LowStar.Buffer
module S = FStar.Seq
module HS = FStar.HyperStack
module G = FStar.Ghost
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module F = Hacl.Streaming.Functor

module Hash = EverCrypt.Hash

open FStar.HyperStack.ST
open Spec.Hash.Definitions
open Hacl.Streaming.Interface

include Spec.Hash.Definitions
include Hacl.Hash.Definitions

open Spec.Hash.Lemmas

#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

// Definitions for instantiating the streaming functor
// ---------------------------------------------------

inline_for_extraction noextract
let agile_state: stateful Hash.alg =
  Stateful
    EverCrypt.Hash.state

    (fun #i h s -> EverCrypt.Hash.footprint s h)
    EverCrypt.Hash.freeable
    (fun #i h s -> EverCrypt.Hash.invariant s h)

    Spec.Hash.Definitions.words_state
    (fun i h s -> EverCrypt.Hash.repr s h)

    (fun #i h s -> EverCrypt.Hash.invariant_loc_in_footprint s h)
    (fun #i l s h0 h1 ->
      EverCrypt.Hash.frame_invariant l s h0 h1;
      EverCrypt.Hash.frame_invariant_implies_footprint_preservation l s h0 h1)
    (fun #i l s h0 h1 -> ())
    EverCrypt.Hash.alloca
    (fun a r -> EverCrypt.Hash.create_in a r)
    (fun i -> EverCrypt.Hash.free #i)
    (fun i -> EverCrypt.Hash.copy #i)

include EverCrypt.Hash.Incremental.Macros

#push-options "--ifuel 1"

(* Adding some non-inlined definitions to factorize code. This one is public
   because it's used by the WASM API, and is generally useful to callers. *)
let hash_len (a:Hash.alg) : (x:UInt32.t { UInt32.v x == Spec.Agile.Hash.hash_length a }) =
  match a with
  | MD5 -> md5_hash_len
  | SHA1 -> sha1_hash_len
  | SHA2_224 -> sha2_224_hash_len
  | SHA2_256 -> sha2_256_hash_len
  | SHA2_384 -> sha2_384_hash_len
  | SHA2_512 -> sha2_512_hash_len
  | SHA3_224 -> sha3_224_hash_len
  | SHA3_256 -> sha3_256_hash_len
  | SHA3_384 -> sha3_384_hash_len
  | SHA3_512 -> sha3_512_hash_len
  | Blake2S -> blake2s_hash_len
  | Blake2B -> blake2b_hash_len

#pop-options

private
let block_len a = Hacl.Hash.Definitions.block_len a

inline_for_extraction noextract
let extra_state_of_nat (a: hash_alg) (i: nat { i % U32.v (block_len a) = 0 }):
  Spec.Hash.Definitions.extra_state a
=
  if is_blake a then
    i
  else
    ()

inline_for_extraction noextract
let prev_length_of_nat (a: hash_alg) (i: nat { i % U32.v (block_len a) = 0 }):
  Spec.Hash.Incremental.prev_length_t a
=
  if is_keccak a then
    ()
  else
    i

#push-options "--z3rlimit 600"

inline_for_extraction noextract
let evercrypt_hash : block Hash.alg =
  Block
    Erased
    agile_state
    (stateful_unused Hash.alg)

    unit
    Hacl.Hash.Definitions.max_input_len64
    (fun a () -> Spec.Hash.Definitions.hash_length a)
    block_len
    block_len // No vectorization
    (fun _ -> 0ul)

    (fun _ _ -> S.empty)
    (fun a _ -> Spec.Agile.Hash.init a)
    (fun a s prevlen input ->
      let prevlen = extra_state_of_nat a prevlen in
      Spec.Agile.Hash.update_multi a s prevlen input)
    (fun a s prevlen input ->
      let prevlen = prev_length_of_nat a prevlen in
      Spec.Hash.Incremental.update_last a s prevlen input)
    (fun a _ s () -> Spec.Agile.Hash.finish a s ())

    (fun a _ s () -> Spec.Agile.Hash.hash a s)

    (fun a s prevlen ->
      if is_blake a then
        Spec.Hash.Lemmas.update_multi_zero_blake a prevlen s
      else
        Spec.Hash.Lemmas.update_multi_zero a s)
    (* update_multi_associative *)
    (fun a s prevlen1 prevlen2 input1 input2 ->
       if is_blake a then
         Spec.Hash.Lemmas.update_multi_associative_blake a s prevlen1 prevlen2 input1 input2
       else
         Spec.Hash.Lemmas.update_multi_associative a s input1 input2)
    (* spec_is_incremental *)
    (fun a _ input () ->
        let input1 = S.append S.empty input in
        assert (S.equal input1 input);
        Spec.Hash.Incremental.hash_is_hash_incremental' a input ())

    (fun a s _ -> EverCrypt.Hash.alg_of_state a s)
    (fun i _ _ -> EverCrypt.Hash.init #i)
    (fun i s prevlen blocks len -> EverCrypt.Hash.update_multi #i s prevlen blocks len)
    (fun i s prevlen last last_len ->
       EverCrypt.Hash.update_last #i s prevlen last last_len)
    (fun i _ s dst _ -> EverCrypt.Hash.finish #i s dst)

#pop-options

let state_t =
  F.state_s evercrypt_hash SHA2_256 ((agile_state).s SHA2_256) (G.erased unit)

// Public API (streaming)
// ----------------------

[@@ Comment
"Allocate initial state for the agile hash. The argument `a` stands for the
choice of algorithm (see Hacl_Spec.h). This API will automatically pick the most
efficient implementation, provided you have called EverCrypt_AutoConfig2_init()
before. The state is to be freed by calling `free`."]
let malloc a = F.malloc evercrypt_hash a (EverCrypt.Hash.state a) (G.erased unit) ()

[@@ Comment
"Reset an existing state to the initial hash state with empty data."]
let reset (a: G.erased Hash.alg) = F.reset evercrypt_hash a (EverCrypt.Hash.state a) (G.erased unit)

[@@ Comment
"Feed an arbitrary amount of data into the hash. This function returns
EverCrypt_Error_Success for success, or EverCrypt_Error_MaximumLengthExceeded if
the combined length of all of the data passed to `update` (since the last call
to `init`) exceeds 2^61-1 bytes or 2^64-1 bytes, depending on the choice of
algorithm. Both limits are unlikely to be attained in practice."]
let update (i: G.erased Hash.alg)
  (state:F.state evercrypt_hash i (EverCrypt.Hash.state i) (G.erased unit))
  (chunk: B.buffer uint8)
  (chunk_len: UInt32.t):
  Stack EverCrypt.Error.error_code
    (requires fun h0 -> F.update_pre evercrypt_hash i state chunk chunk_len h0)
    (ensures fun h0 e h1 ->
      match e with
      | EverCrypt.Error.Success ->
          S.length (F.seen evercrypt_hash i h0 state) + U32.v chunk_len <= U64.v (evercrypt_hash.max_input_len i) /\
          F.update_post evercrypt_hash i state chunk chunk_len h0 h1
      | EverCrypt.Error.MaximumLengthExceeded ->
          h0 == h1 /\
          not (S.length (F.seen evercrypt_hash i h0 state) + U32.v chunk_len <= U64.v (evercrypt_hash.max_input_len i))
      | _ -> False)
=
  match F.update evercrypt_hash i (EverCrypt.Hash.state i) (G.erased unit) state chunk chunk_len with
  | Hacl.Streaming.Types.Success -> EverCrypt.Error.Success
  | Hacl.Streaming.Types.MaximumLengthExceeded -> EverCrypt.Error.MaximumLengthExceeded

inline_for_extraction noextract
let digest_st a = F.digest_st evercrypt_hash a (EverCrypt.Hash.state a) (G.erased unit)

/// The wrapper pattern, to ensure that the stack-allocated state is properly
/// monomorphized.
private
let digest_md5: digest_st MD5 = F.digest evercrypt_hash MD5 (EverCrypt.Hash.state MD5) (G.erased unit)
private
let digest_sha1: digest_st SHA1 = F.digest evercrypt_hash SHA1 (EverCrypt.Hash.state SHA1) (G.erased unit)
private
let digest_sha224: digest_st SHA2_224 = F.digest evercrypt_hash SHA2_224 (EverCrypt.Hash.state SHA2_224) (G.erased unit)
private
let digest_sha256: digest_st SHA2_256 = F.digest evercrypt_hash SHA2_256 (EverCrypt.Hash.state SHA2_256) (G.erased unit)
private
let digest_sha3_224: digest_st SHA3_224 = F.digest evercrypt_hash SHA3_224 (EverCrypt.Hash.state SHA3_224) (G.erased unit)
private
let digest_sha3_256: digest_st SHA3_256 = F.digest evercrypt_hash SHA3_256 (EverCrypt.Hash.state SHA3_256) (G.erased unit)
private
let digest_sha3_384: digest_st SHA3_384 = F.digest evercrypt_hash SHA3_384 (EverCrypt.Hash.state SHA3_384) (G.erased unit)
private
let digest_sha3_512: digest_st SHA3_512 = F.digest evercrypt_hash SHA3_512 (EverCrypt.Hash.state SHA3_512) (G.erased unit)
private
let digest_sha384: digest_st SHA2_384 = F.digest evercrypt_hash SHA2_384 (EverCrypt.Hash.state SHA2_384) (G.erased unit)
private
let digest_sha512: digest_st SHA2_512 = F.digest evercrypt_hash SHA2_512 (EverCrypt.Hash.state SHA2_512) (G.erased unit)
private
let digest_blake2s: digest_st Blake2S = F.digest evercrypt_hash Blake2S (EverCrypt.Hash.state Blake2S) (G.erased unit)
private
let digest_blake2b: digest_st Blake2B = F.digest evercrypt_hash Blake2B (EverCrypt.Hash.state Blake2B) (G.erased unit)

[@@ Comment
"Perform a run-time test to determine which algorithm was chosen for the given piece of state."]
let alg_of_state (a: G.erased Hash.alg) = F.index_of_state evercrypt_hash a (EverCrypt.Hash.state a) (G.erased unit)

[@@ Comment
"Write the resulting hash into `output`, an array whose length is
algorithm-specific. You can use the macros defined earlier in this file to
allocate a destination buffer of the right length. The state remains valid after
a call to `digest`, meaning the user may feed more data into the hash via
`update`. (The finish function operates on an internal copy of the state and
therefore does not invalidate the client-held state.)"]
val digest: a:G.erased Hash.alg -> digest_st a
let digest a state output l =
  let a = alg_of_state a state in
  match a with
  | MD5 -> digest_md5 state output l
  | SHA1 -> digest_sha1 state output l
  | SHA2_224 -> digest_sha224 state output l
  | SHA2_256 -> digest_sha256 state output l
  | SHA2_384 -> digest_sha384 state output l
  | SHA2_512 -> digest_sha512 state output l
  | SHA3_224 -> digest_sha3_224 state output l
  | SHA3_256 -> digest_sha3_256 state output l
  | SHA3_384 -> digest_sha3_384 state output l
  | SHA3_512 -> digest_sha3_512 state output l
  | Blake2S -> digest_blake2s state output l
  | Blake2B -> digest_blake2b state output l

[@@ Comment
"Free a state previously allocated with `create_in`."]
let free (i: G.erased Hash.alg) = F.free evercrypt_hash i (EverCrypt.Hash.state i) (G.erased unit)

// Private API (one-shot, multiplexing)
// ------------------------------------

private
val hash_256: Hacl.Hash.Definitions.hash_st SHA2_256

// A full one-shot hash that relies on vale at each multiplexing point
let hash_256 output input input_len =
  let open EverCrypt.Hash in
  // TODO: This function now only exists for SHA1 and MD5
  Hacl.Hash.MD.mk_hash SHA2_256 Hacl.Hash.SHA2.alloca_256 update_multi_256
    Hacl.Hash.SHA2.update_last_256 Hacl.Hash.SHA2.finish_256 output input input_len

private
val hash_224: Hacl.Hash.Definitions.hash_st SHA2_224

let hash_224 output input input_len =
  let open EverCrypt.Hash in
  Hacl.Hash.MD.mk_hash SHA2_224 Hacl.Hash.SHA2.alloca_224 update_multi_224
    Hacl.Hash.SHA2.update_last_224 Hacl.Hash.SHA2.finish_224 output input input_len

// Public API (one-shot, agile and multiplexing)
// ---------------------------------------------

// NOTE: this function goes through all the Hacl.Hash.* wrappers which export
// the correct agile low-level type, and thus does not need to be aware of the
// implementation of Spec.Agile.Hash (no friend-ing).
//
// ALSO: for some reason, this function was historically exported with an order
// of arguments different from Hacl.Hash.Definitions.hash_st a. Would be worth
// fixing at some point.

[@@ Comment
"Hash `input`, of len `input_len`, into `output`, an array whose length is determined by
your choice of algorithm `a` (see Hacl_Spec.h). You can use the macros defined
earlier in this file to allocate a destination buffer of the right length. This
API will automatically pick the most efficient implementation, provided you have
called EverCrypt_AutoConfig2_init() before. "]
val hash:
  a:Hash.alg ->
  output:B.buffer Lib.IntTypes.uint8 {B.length output = hash_length a} ->
  input:B.buffer Lib.IntTypes.uint8 ->
  input_len:FStar.UInt32.t {B.length input = FStar.UInt32.v input_len /\ FStar.UInt32.v input_len `less_than_max_input_length` a} ->
  Stack unit
  (requires fun h0 ->
    B.live h0 output /\
    B.live h0 input /\
    B.(loc_disjoint (loc_buffer input) (loc_buffer output)))
  (ensures fun h0 _ h1 ->
    B.(modifies (loc_buffer output) h0 h1) /\
    B.as_seq h1 output == Spec.Agile.Hash.hash a (B.as_seq h0 input))
let hash a output input input_len =
  match a with
  | MD5 -> Hacl.Hash.MD5.hash_oneshot output input input_len
  | SHA1 -> Hacl.Hash.SHA1.hash_oneshot output input input_len
  | SHA2_224 -> hash_224 output input input_len
  | SHA2_256 -> hash_256 output input input_len
  | SHA2_384 -> Hacl.Streaming.SHA2.hash_384 output input input_len
  | SHA2_512 -> Hacl.Streaming.SHA2.hash_512 output input input_len
  | SHA3_224 -> Hacl.Hash.SHA3.hash SHA3_224 output input input_len
  | SHA3_256 -> Hacl.Hash.SHA3.hash SHA3_256 output input input_len
  | SHA3_384 -> Hacl.Hash.SHA3.hash SHA3_384 output input input_len
  | SHA3_512 -> Hacl.Hash.SHA3.hash SHA3_512 output input input_len
  | Blake2S ->
      if EverCrypt.TargetConfig.hacl_can_compile_vec128 then
        let vec128 = EverCrypt.AutoConfig2.has_vec128 () in
        if vec128 then
          Hacl.Hash.Blake2s_128.hash output input input_len
        else
          Hacl.Hash.Blake2s_32.hash output input input_len
      else
        Hacl.Hash.Blake2s_32.hash output input input_len
  | Blake2B ->
      if EverCrypt.TargetConfig.hacl_can_compile_vec256 then
        let vec256 = EverCrypt.AutoConfig2.has_vec256 () in
        if vec256 then
          Hacl.Hash.Blake2b_256.hash output input input_len
        else
          Hacl.Hash.Blake2b_32.hash output input input_len
      else
        Hacl.Hash.Blake2b_32.hash output input input_len

// Public API (verified clients)
// -----------------------------

/// Finally, a few helpers predicates to make things easier for clients...
inline_for_extraction noextract
let state (a: Hash.alg) = F.state evercrypt_hash a (EverCrypt.Hash.state a) (G.erased unit)

inline_for_extraction noextract
let hashed #a (h: HS.mem) (s: state a) =
  F.seen evercrypt_hash a h s
