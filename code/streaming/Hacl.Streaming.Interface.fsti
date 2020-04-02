module Hacl.Streaming.Interface

open FStar.HyperStack.ST
open FStar.Integers

/// This is the interface that the streaming functor expects from a block-based
/// API. This interface is made abstract using the classic framing lemma and
/// invariant preservation technique (see EverCrypt).

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

module HS = FStar.HyperStack
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

/// The type class of stateful types.
/// Needs to obey framing principles. Standard notion of footprint & invariant.
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

  stateful index

inline_for_extraction noextract
let stateful_buffer (a: Type) (l: nat): stateful unit =
  Stateful
    (fun _ -> b:B.buffer a { B.length b == l })
    (fun #_ h s -> B.loc_addr_of_buffer s)
    (fun #_ h s -> B.freeable s)
    (fun #_ h s -> B.live h s)
    (fun _ -> s:S.seq a { S.length s == l })
    (fun _ h s -> B.as_seq h s)
    (fun #_ h s -> ())
    (fun #_ l s h0 h1 -> ())
    (fun #_ l s h0 h1 -> ())

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

type key_management =
  | None
  | Init
  | InitFinish

/// The type class of block-based operations. Equipped with a generic index. May
/// be unit if there's no agility, or hash algorithm for agility.
///
/// The first index determines the role of the key:
///
/// - None: no key is used by this algorithm (e.g. hash)
/// - Init: a key is needed at initialization-time (e.g. blake2, keyed hash
///   functionality). Implementation retains a ghost key.
/// - InitFinish: a key is needed at initialization-time and at the end of
///   processing (e.g. poly1305). Implementation retains key at run-time.
///
/// Two things to note. First, we could always do the latter but this would
/// retain useless state in the first two cases. Second, this distinction is
/// only relevant for low-level functions, as spec functions just need to ignore
/// their arguments.
inline_for_extraction noextract noeq
type block (index: Type0) =
| Block:

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

  alloca: (i:index -> StackInline (state.s i)
    (requires (fun _ -> True))
    (ensures (fun h0 s h1 ->
      state.invariant #i h1 s /\
      B.(modifies loc_none h0 h1) /\
      B.fresh_loc (state.footprint #i h1 s) h0 h1 /\
      B.(loc_includes (loc_region_only true (HS.get_tip h1)) (state.footprint #i h1 s))))) ->

  create_in: (i:index ->
    r:HS.rid ->
    ST (state.s i)
    (requires (fun h0 ->
      HyperStack.ST.is_eternal_region r))
    (ensures (fun h0 s h1 ->
      state.invariant #i h1 s /\
      B.(modifies loc_none h0 h1) /\
      B.fresh_loc (state.footprint #i h1 s) h0 h1 /\
      B.(loc_includes (loc_region_only true r) (state.footprint #i h1 s)) /\
      state.freeable #i h1 s))) ->

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
    s:state.s i ->
    dst:B.buffer uint8 { B.len dst = output_len i } ->
    Stack unit
    (requires fun h0 ->
      state.invariant #i h0 s /\
      B.live h0 dst /\
      B.(loc_disjoint (state.footprint #i h0 s) (loc_buffer dst)))
    (ensures fun h0 _ h1 ->
      state.invariant #i h1 s /\
      B.(modifies (loc_buffer dst) h0 h1) /\
      state.footprint #i h0 s == state.footprint #i h1 s /\
      B.as_seq h1 dst == finish_s i (state.v i h0 s) /\
      (state.freeable #i h0 s ==> state.freeable #i h1 s)))) ->

  free: (
    i: G.erased index -> (
    let i = G.reveal i in
    s:state.s i -> ST unit
    (requires fun h0 ->
      state.freeable #i h0 s /\
      state.invariant #i h0 s)
    (ensures fun h0 _ h1 ->
      B.(modifies (state.footprint #i h0 s) h0 h1)))) ->

  copy: (
    i:G.erased index -> (
    let i = G.reveal i in
    s_src:state.s i ->
    s_dst:state.s i ->
    Stack unit
      (requires (fun h0 ->
        state.invariant #i h0 s_src /\
        state.invariant #i h0 s_dst /\
        B.(loc_disjoint (state.footprint #i h0 s_src) (state.footprint #i h0 s_dst))))
      (ensures fun h0 _ h1 ->
        B.(modifies (state.footprint #i h0 s_dst) h0 h1) /\
        state.footprint #i h0 s_dst == state.footprint #i h1 s_dst /\
        (state.freeable #i h0 s_dst ==> state.freeable #i h1 s_dst) /\
        state.invariant #i h1 s_dst /\
        state.v i h1 s_dst == state.v i h0 s_src))) ->

  block index
