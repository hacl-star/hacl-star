module Hacl.Streaming.Interface

open FStar.HyperStack.ST
open FStar.Integers

/// This is the interface that the streaming functor expects from a block-based
/// API. We need to be abstract vis à vis the state representations of the
/// underlying block-based API. For that, we use classic framing lemma and
/// invariant preservation techniques used in EverCrypt and elsewhere.

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module U32 = FStar.UInt32
module U64 = FStar.UInt64

open LowStar.BufferOps
open FStar.Mul

inline_for_extraction noextract
let uint8 = Lib.IntTypes.uint8

inline_for_extraction noextract
let uint32 = Lib.IntTypes.uint32

/// The type class of stateful types: a low-level representation, a high-level
/// value, and a ``v`` function to switch between the two.
///
/// The low-level representation needs to abide by all the important framing
/// principles to allow clients to efficiently work with a ``stateful index``.
///
/// More interestingly, we require some extra operations that arise in the
/// process of manipulating instances of this type class:
/// - the ability to allocate on the stack (useful for temporaries)
/// - the ability to allocate on the heap (useful for retaining a copy of a stateful)
/// - the ability to copy
/// - a predicate that captures the fact that the invariant depends only on the
///   footprint of the stateful, i.e. does not rely on some gcmalloc'd global
///   state in the global scope.
///
/// This may seem like a lot but actually most low-level representations satisfy
/// these principles!
inline_for_extraction noextract noeq
type stateful (index: Type0) =
| Stateful:
  // Low-level types
  s: (index -> Type0) ->

  // Astract footprint.
  footprint: (#i:index -> h:HS.mem -> s:s i -> GTot B.loc) ->
  freeable: (#i:index -> h:HS.mem -> p:s i -> Type) ->
  invariant: (#i:index -> h:HS.mem -> s:s i -> Type) ->

  // A pure representation of a s
  t: (index -> Type0) ->
  v: (i:index -> h:HS.mem -> s:s i -> GTot (t i)) ->

  // Adequate framing lemmas, relying on v.
  invariant_loc_in_footprint: (#i:index -> h:HS.mem -> s:s i -> Lemma
    (requires (invariant h s))
    (ensures (B.loc_in (footprint #i h s) h))
    [ SMTPat (invariant h s) ]) ->

  frame_invariant: (#i:index -> l:B.loc -> s:s i -> h0:HS.mem -> h1:HS.mem -> Lemma
    (requires (
      invariant h0 s /\
      B.loc_disjoint l (footprint #i h0 s) /\
      B.modifies l h0 h1))
    (ensures (
      invariant h1 s /\
      v i h0 s == v i h1 s /\
      footprint #i h1 s == footprint #i h0 s))) ->

  frame_freeable: (#i:index -> l:B.loc -> s:s i -> h0:HS.mem -> h1:HS.mem -> Lemma
    (requires (
      invariant h0 s /\
      freeable h0 s /\
      B.loc_disjoint l (footprint #i h0 s) /\
      B.modifies l h0 h1))
    (ensures (
      freeable h1 s))
    [ SMTPat (freeable h1 s); SMTPat (B.modifies l h0 h1) ]) ->

  // Stateful operations
  alloca: (i:index -> StackInline (s i)
    (requires (fun _ -> True))
    (ensures (fun h0 s h1 ->
      invariant #i h1 s /\
      B.(modifies loc_none h0 h1) /\
      B.fresh_loc (footprint #i h1 s) h0 h1 /\
      B.(loc_includes (loc_region_only true (HS.get_tip h1)) (footprint #i h1 s))))) ->

  create_in: (i:index ->
    r:HS.rid ->
    ST (s i)
    (requires (fun h0 ->
      HyperStack.ST.is_eternal_region r))
    (ensures (fun h0 s h1 ->
      invariant #i h1 s /\
      B.(modifies loc_none h0 h1) /\
      B.fresh_loc (footprint #i h1 s) h0 h1 /\
      B.(loc_includes (loc_region_only true r) (footprint #i h1 s)) /\
      freeable #i h1 s))) ->

  free: (
    i: G.erased index -> (
    let i = G.reveal i in
    s:s i -> ST unit
    (requires fun h0 ->
      freeable #i h0 s /\
      invariant #i h0 s)
    (ensures fun h0 _ h1 ->
      B.(modifies (footprint #i h0 s) h0 h1)))) ->

  copy: (
    i:G.erased index -> (
    let i = G.reveal i in
    s_src:s i ->
    s_dst:s i ->
    Stack unit
      (requires (fun h0 ->
        invariant #i h0 s_src /\
        invariant #i h0 s_dst /\
        B.(loc_disjoint (footprint #i h0 s_src) (footprint #i h0 s_dst))))
      (ensures fun h0 _ h1 ->
        B.(modifies (footprint #i h0 s_dst) h0 h1) /\
        footprint #i h0 s_dst == footprint #i h1 s_dst /\
        (freeable #i h0 s_dst ==> freeable #i h1 s_dst) /\
        invariant #i h1 s_dst /\
        v i h1 s_dst == v i h0 s_src))) ->

  stateful index

inline_for_extraction noextract
let stateful_buffer (a: Type) (l: UInt32.t { UInt32.v l > 0 }) (zero: a): stateful unit =
  Stateful
    (fun _ -> b:B.buffer a { B.len b == l })
    (fun #_ h s -> B.loc_addr_of_buffer s)
    (fun #_ h s -> B.freeable s)
    (fun #_ h s -> B.live h s)
    (fun _ -> s:S.seq a { S.length s == UInt32.v l })
    (fun _ h s -> B.as_seq h s)
    (fun #_ h s -> ())
    (fun #_ l s h0 h1 -> ())
    (fun #_ l s h0 h1 -> ())
    (fun () -> B.alloca zero l)
    (fun () r -> B.malloc r zero l)
    (fun _ s -> B.free s)
    (fun _ s_src s_dst -> B.blit s_src 0ul s_dst 0ul l)

inline_for_extraction noextract
let stateful_unused: stateful unit =
  Stateful
    (fun _ -> unit)
    (fun #_ h s -> B.loc_none)
    (fun #_ h s -> True)
    (fun #_ h s -> True)
    (fun _ -> unit)
    (fun _ h s -> ())
    (fun #_ h s -> ())
    (fun #_ l s h0 h1 -> ())
    (fun #_ l s h0 h1 -> ())
    (fun () -> ())
    (fun () r -> ())
    (fun _ s -> ())
    (fun _ _ _ -> ())

type key_management =
  | Erased
  | Runtime

inline_for_extraction noextract
let optional_key #index (i: index) (km: key_management) (key: stateful index) =
  allow_inversion key_management;
  match km with
  | Erased -> G.erased (key.t i)
  | Runtime -> key.s i

inline_for_extraction noextract
let optional_t #index
  (#i: index)
  (#km: key_management)
  (#key: stateful index)
  (h: HS.mem)
  (k: optional_key i km key):
  GTot (key.t i)
=
  allow_inversion key_management;
  match km with
  | Erased -> G.reveal k
  | Runtime -> key.v i h k

/// The type class of block-based operations. Equipped with a generic index. May
/// be unit if there's no agility, or hash algorithm for agility. The streaming
/// functor will take instances of this type class to generate corresponding
/// streaming APIs.
///
/// The value of `km` is a tweaking knob that influences both *the shape of the
/// block-based API*, i.e. the interface description encoded in the type class
/// that follows, and the resulting run-time key management performed by the
/// streaming API, once generated.
///
/// - Erased: a key is needed (only) at initialization-time (e.g. blake2, keyed
///   hash functionality). Streaming state retains a ghost key.
/// - Runtime: a key is needed both at initialization-time and at the end of
///   processing (e.g. poly1305). Streaming state retains key at run-time.
///
/// Some remarks.
/// - For algorithms that don't need a key at all (e.g. hash) it suffices to
///   pass stateful_unused for the key. (Kremlin unit argument elimination will
///   do the rest).
/// - The Runtime API is more general, and we could just dismiss `km` and always
///   choose to keep the key at run-time in the streaming state, except this is
///   un-necessary and inefficient.
/// - `km` influences the shape of the finish stateful function below:
///   the interface must advertise km = Runtime if its finish function wants to
///   reeive the actual key.
///
/// No such indexing occurs for spec-level functions, because they are always
/// free to ignore superfluous arguments, and the shape of the API does not
/// matter.
inline_for_extraction noextract noeq
type block (index: Type0) =
| Block:

  km: key_management ->

  // Low-level types
  state: stateful index ->
  key: stateful index ->

  // Introducing a notion of blocks and final result.
  max_input_length: (index -> x:nat { 0 < x /\ x < pow2 64 }) ->
  output_len: (index -> x:U32.t { U32.v x > 0 }) ->
  block_len: (index -> x:U32.t { U32.v x > 0 }) ->

  /// An init/update/update_last/finish specification. The long refinements were
  /// previously defined as blocks / small / output.
  init_s: (i:index -> key.t i -> state.t i) ->
  update_multi_s: (i:index -> state.t i -> s:S.seq uint8 { S.length s % U32.v (block_len i) = 0 } -> state.t i) ->
  update_last_s: (i:index ->
    state.t i ->
    prevlen:nat { prevlen % U32.v (block_len i) = 0 } ->
    s:S.seq uint8 { S.length s + prevlen <= max_input_length i /\ S.length s < U32.v (block_len i) } ->
    state.t i) ->
  finish_s: (i:index -> key.t i -> state.t i -> s:S.seq uint8 { S.length s = U32.v (output_len i) }) ->

  /// The specification in one shot.
  spec_s: (i:index -> key.t i -> input:S.seq uint8 { S.length input <= max_input_length i } ->
    output:S.seq uint8 { S.length output == U32.v (output_len i) }) ->

  // Required lemmas... clients can enjoy them in their local contexts with the SMT pattern via a let-binding.

  update_multi_zero: (i:index -> h:state.t i -> Lemma
    (ensures (update_multi_s i h S.empty == h))) ->

  update_multi_associative: (i:index ->
    h: state.t i ->
    input1:S.seq uint8 ->
    input2:S.seq uint8 ->
    Lemma
    (requires (
      S.length input1 % U32.v (block_len i) = 0 /\
      S.length input2 % U32.v (block_len i) = 0))
    (ensures (
      let input = S.append input1 input2 in
      S.length input % U32.v (block_len i) = 0 /\
      update_multi_s i (update_multi_s i h input1) input2 ==
        update_multi_s i h input))
    [ SMTPat (update_multi_s i (update_multi_s i h input1) input2) ]) ->

  spec_is_incremental: (i:index ->
    key: key.t i ->
    input:S.seq uint8 { S.length input <= max_input_length i } ->
    Lemma (ensures (
      let open FStar.Mul in
      let block_length = U32.v (block_len i) in
      let n = S.length input / block_length in
      let bs, l = S.split input (n * block_length) in
      FStar.Math.Lemmas.multiple_modulo_lemma n block_length;
      let hash = update_multi_s i (init_s i key) bs in
      let hash = update_last_s i hash (n * block_length) l in
      finish_s i key hash `S.equal` spec_s i key input))) ->

  // Stateful operations
  index_of_state: (i:G.erased index -> (
    let i = G.reveal i in
    s: state.s i -> Stack index
    (fun h0 -> state.invariant #i h0 s)
    (fun h0 i' h1 -> h0 == h1 /\ i' == i))) ->


  init: (i:G.erased index -> (
    let i = G.reveal i in
    k: key.s i ->
    s: state.s i -> Stack unit
    (requires fun h0 ->
      key.invariant #i h0 k /\
      state.invariant #i h0 s /\
      B.loc_disjoint (key.footprint #i h0 k) (state.footprint #i h0 s))
    (ensures fun h0 _ h1 ->
      key.invariant #i h1 k /\
      (key.freeable #i h0 k ==> key.freeable #i h1 k) /\
      state.invariant #i h1 s /\
      state.v i h1 s == init_s i (key.v i h0 k) /\
      B.(modifies (state.footprint #i h0 s) h0 h1) /\
      state.footprint #i h0 s == state.footprint #i h1 s /\
      (state.freeable #i h0 s ==> state.freeable #i h1 s)))) ->

  update_multi: (i:G.erased index -> (
    let i = G.reveal i in
    s:state.s i ->
    blocks:B.buffer uint8 { B.length blocks % U32.v (block_len i) = 0 } ->
    len: U32.t { U32.v len = B.length blocks } ->
    Stack unit
    (requires fun h0 ->
      state.invariant #i h0 s /\
      B.live h0 blocks /\
      B.(loc_disjoint (state.footprint #i h0 s) (loc_buffer blocks)))
    (ensures fun h0 _ h1 ->
      B.(modifies (state.footprint #i h0 s) h0 h1) /\
      state.footprint #i h0 s == state.footprint #i h1 s /\
      state.invariant #i h1 s /\
      state.v i h1 s == update_multi_s i (state.v i h0 s) (B.as_seq h0 blocks) /\
      (state.freeable #i h0 s ==> state.freeable #i h1 s)))) ->

  update_last: (
    i: G.erased index -> (
    let i = G.reveal i in
    s:state.s i ->
    last:B.buffer uint8 { B.len last < block_len i } ->
    total_len:U64.t {
      U64.v total_len <= max_input_length i /\
      (U64.v total_len - B.length last) % U32.v (block_len i) = 0 } ->
    Stack unit
    (requires fun h0 ->
      state.invariant #i h0 s /\
      B.live h0 last /\
      B.(loc_disjoint (state.footprint #i h0 s) (loc_buffer last)))
    (ensures fun h0 _ h1 ->
      state.invariant #i h1 s /\
      state.v i h1 s == update_last_s i (state.v i h0 s) (U64.v total_len - B.length last) (B.as_seq h0 last) /\
      B.(modifies (state.footprint #i h0 s) h0 h1) /\
      state.footprint #i h0 s == state.footprint #i h1 s /\
      (state.freeable #i h0 s ==> state.freeable #i h1 s)))) ->

  finish: (
    i: G.erased index -> (
    let i = G.reveal i in
    k: optional_key i km key ->
    s:state.s i ->
    dst:B.buffer uint8 { B.len dst = output_len i } ->
    Stack unit
    (requires fun h0 ->
      allow_inversion key_management;
      state.invariant #i h0 s /\
      B.live h0 dst /\
      B.(loc_disjoint (state.footprint #i h0 s) (loc_buffer dst)) /\ (
      match km with
      | Erased -> True
      | Runtime ->
          key.invariant #i h0 k /\
          B.(loc_disjoint (key.footprint #i h0 k) (loc_buffer dst)) /\
          B.(loc_disjoint (key.footprint #i h0 k) (state.footprint #i h0 s))))
    (ensures fun h0 _ h1 ->
      state.invariant #i h1 s /\
      B.(modifies (loc_buffer dst) h0 h1) /\
      state.footprint #i h0 s == state.footprint #i h1 s /\
      B.as_seq h1 dst == finish_s i (optional_t h0 k) (state.v i h0 s) /\
      (state.freeable #i h0 s ==> state.freeable #i h1 s)))) ->

  block index
