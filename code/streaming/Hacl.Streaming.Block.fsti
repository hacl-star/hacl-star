module Hacl.Streaming.Block

open FStar.HyperStack.ST
open FStar.Integers

/// Second abstract interface that the streaming functor is authored against: an
/// algorithm that obeys the block laws (see paper).

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
///   pass stateful_unused for the key. (KaRaMeL unit argument elimination will
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

/// SH: TODO: Maybe we should cut the functor in pieces (we could have a functional specifications
/// functor, containing only the functional specification definitions, and an
/// implementation and properties functor, which would be parameterized by a spec functor
/// and would contain all the lemmas and implementations).
/// It would actually make the proofs simpler, because after the spec functor is defined
/// could easily use its fields (the current workaround is to define every field before
/// defining the functor, which is tedious because we have to copy the signatures
/// correctly), and moreover because the signatures of the fields of the implementations
/// and properties functor would only depend on the signature functor: it would thus be
/// possible to define all those signatures indenpendantly, allowing the user to reuse
/// them rather than copy-paste big chunks of code (as what is done in Hacl.Streaming.Blake2).
/// Note that a workaround is to partially instanciate the functor at definition time.

#push-options "--z3rlimit 200"

type key_management =
  | Erased
  | Runtime

noeq
type index = {
  km: key_management;

  // Low-level types
  state: Stateful.index;
  key: Stateful.index;

  // Just a value type; useful for algorithms that have a variable output length.
  output_length_t: Type0;

  // Introducing a notion of blocks and final result.
  max_input_len: (x:U64.t { U64.v x > 0 });
  output_length: (output_length_t -> GTot Lib.IntTypes.(x:size_nat { x > 0 }));
  block_len: (x:U32.t { U32.v x > 0 });

  // The size of data to process at a time. Must be a multiple of block_len.
  // Controls the size of the internal buffer.
  blocks_state_len: (
    x:U32.t { U32.v x > 0 /\ U32.v x >= U32.v block_len /\ U32.v x % U32.v block_len = 0 });
  init_input_len: (x:U32.t { U32.v x <= U32.v block_len /\ U32.v x <= U64.v max_input_len });

  /// An init/update/update_last/finish specification. The long refinements were
  /// previously defined as blocks / small / output.
  init_input_s: (key.t -> s:S.seq uint8 { S.length s = U32.v init_input_len });

  init_s: (key.t -> state.t);
  update_multi_s: (
    state.t ->
    prevlen:nat { prevlen % U32.v block_len = 0 } ->
    s:S.seq uint8 { prevlen + S.length s <= U64.v max_input_len /\ S.length s % U32.v block_len = 0 } ->
    state.t);

  update_last_s: (
    state.t ->
    prevlen:nat { prevlen % U32.v block_len = 0 } ->
    s:S.seq uint8 { S.length s + prevlen <= U64.v max_input_len /\ S.length s <= U32.v block_len } ->
    state.t);

  finish_s: (key.t -> state.t -> l:output_length_t -> s:S.seq uint8 { S.length s = output_length l });

  /// The specification in one shot.
  spec_s: (key.t ->
    input:S.seq uint8 { U32.v init_input_len + S.length input <= U64.v max_input_len } ->
    l:output_length_t ->
    output:S.seq uint8 { S.length output == output_length l });

  // Required lemmas... clients can enjoy them in their local contexts with the SMT pattern via a let-binding.

  update_multi_zero: (
    h:state.t ->
    prevlen:nat { prevlen % U32.v block_len = 0 /\ prevlen <= U64.v max_input_len } ->
    Lemma
    (ensures (
      Math.Lemmas.modulo_lemma 0 (UInt32.v block_len);
      update_multi_s h prevlen S.empty == h)));

  update_multi_associative: (
    h:state.t ->
    prevlen1:nat ->
    prevlen2:nat ->
    input1:S.seq uint8 ->
    input2:S.seq uint8 ->
    Lemma
    (requires (
      prevlen1 % U32.v block_len = 0 /\
      S.length input1 % U32.v block_len = 0 /\
      S.length input2 % U32.v block_len = 0 /\
      prevlen1 + S.length input1 + S.length input2 <= U64.v max_input_len /\
      prevlen2 = prevlen1 + S.length input1))
    (ensures (
      let input = S.append input1 input2 in
      S.length input % U32.v block_len = 0 /\
      prevlen2 % U32.v block_len = 0 /\
      update_multi_s (update_multi_s h prevlen1 input1) prevlen2 input2 ==
        update_multi_s h prevlen1 input))
    [ SMTPat (update_multi_s prevlen2 (update_multi_s h prevlen1 input1) input2) ]);

  (* TODO: it might be possible to factorize more the proofs between Lib.UpdateMulti
   * and Spec.Hash.Incremental *)
  spec_is_incremental: (
    key: key.t ->
    input:S.seq uint8 { U32.v init_input_len + S.length input <= U64.v max_input_len } ->
    l:output_length_t ->
    Lemma (
      let input1 = S.append (init_input_s key) input in
      let bs, rest = Lib.UpdateMulti.split_at_last_lazy (U32.v block_len) input1 in
      (**) Math.Lemmas.modulo_lemma 0 (U32.v block_len);
      (* TODO: use update_full ? *)
      let hash0 = init_s key in
      let hash1 = update_multi_s hash0 0 bs in
      let hash2 = update_last_s hash1 (S.length bs) rest in
      let hash3 = finish_s key hash2 l in
      hash3 `S.equal` spec_s key input l));
}

inline_for_extraction noextract
let optional_key (i: index) =
  allow_inversion key_management;
  match i.km with
  | Erased -> G.erased i.key.t
  | Runtime -> i.key.s

inline_for_extraction noextract
let optional_t
  (#i: index)
  (h: HS.mem)
  (k: optional_key i):
  GTot i.key.t
=
  allow_inversion key_management;
  match i.km with
  | Erased -> G.reveal k
  | Runtime -> i.key.v h k

// Stateful operations
inline_for_extraction noextract
let index_of_state_st (i: index) =
  s: i.state.s -> Stack index
  (fun h0 -> i.state.invariant h0 s)
  (fun h0 i' h1 -> h0 == h1 /\ i' == i)

[@ Meta.Attribute.specialize ]
val index_of_state: i:G.erased index -> index_of_state_st i

inline_for_extraction noextract
let init_st (i: index) =
  k: i.key.s ->
  buf_: B.buffer uint8 { B.length buf_ = U32.v i.blocks_state_len } ->
  s: i.state.s -> Stack unit
  (requires fun h0 ->
    i.key.invariant h0 k /\
    B.live h0 buf_ /\
    i.state.invariant h0 s /\
    B.loc_disjoint (i.key.footprint h0 k) (i.state.footprint h0 s) /\
    B.loc_disjoint (i.key.footprint h0 k) (B.loc_buffer buf_) /\
    B.loc_disjoint (B.loc_buffer buf_) (i.state.footprint h0 s))
  (ensures fun h0 _ h1 ->
    i.key.invariant h1 k /\
    (i.key.freeable h0 k ==> i.key.freeable h1 k) /\
    i.state.invariant h1 s /\
    i.state.v h1 s == i.init_s (i.key.v h0 k) /\
    S.equal (S.slice (B.as_seq h1 buf_) 0 (U32.v i.init_input_len)) (i.init_input_s (i.key.v h0 k)) /\
    B.(modifies (loc_union (i.state.footprint h0 s) (loc_buffer buf_)) h0 h1) /\
    i.state.footprint h0 s == i.state.footprint h1 s /\
    (i.state.freeable h0 s ==> i.state.freeable h1 s))

[@ Meta.Attribute.specialize ]
val init: i:G.erased index -> init_st i

inline_for_extraction noextract
let update_multi_st (i: index) =
  s:i.state.s ->
  prevlen:U64.t { U64.v prevlen % U32.v i.block_len = 0 } ->
  blocks:B.buffer uint8 { B.length blocks % U32.v i.block_len = 0 } ->
  len: U32.t { U32.v len = B.length blocks /\
                U64.v prevlen + U32.v len <= U64.v i.max_input_len } ->
  Stack unit
  (requires fun h0 ->
    allow_inversion key_management;
    i.state.invariant h0 s /\
    B.live h0 blocks /\
    B.(loc_disjoint (i.state.footprint h0 s) (loc_buffer blocks)))
  (ensures fun h0 _ h1 ->
    B.(modifies (i.state.footprint h0 s) h0 h1) /\
    i.state.footprint h0 s == i.state.footprint h1 s /\
    i.state.invariant h1 s /\
    i.state.v h1 s == i.update_multi_s (i.state.v h0 s) (U64.v prevlen) (B.as_seq h0 blocks) /\
    (i.state.freeable h0 s ==> i.state.freeable h1 s))

[@ Meta.Attribute.specialize ]
val update_multi: i:G.erased index -> update_multi_st i

inline_for_extraction noextract
let update_last_st (i: index) =
  s:i.state.s ->
  prevlen:U64.t { U64.v prevlen % U32.v i.block_len = 0 } ->
  last:B.buffer uint8 ->
  last_len:U32.t{
    last_len = B.len last /\
    U32.v last_len <= U32.v i.block_len /\
    U64.v prevlen + U32.v last_len <= U64.v i.max_input_len } ->
  Stack unit
  (requires fun h0 ->
    allow_inversion key_management;
    i.state.invariant h0 s /\
    B.live h0 last /\
    B.(loc_disjoint (i.state.footprint h0 s) (loc_buffer last)))
  (ensures fun h0 _ h1 ->
    i.state.invariant h1 s /\
    i.state.v h1 s == i.update_last_s (i.state.v h0 s) (U64.v prevlen) (B.as_seq h0 last) /\
    B.(modifies (i.state.footprint h0 s) h0 h1) /\
    i.state.footprint h0 s == i.state.footprint h1 s /\
    (i.state.freeable h0 s ==> i.state.freeable h1 s))

[@ Meta.Attribute.specialize ]
val update_last: i:G.erased index -> update_last_st i

inline_for_extraction noextract
let finish_st_pre (i: index)
  (k: optional_key i)
  (s:i.state.s)
  (dst:B.buffer uint8)
  (l: i.output_length_t { B.length dst == i.output_length l })
  h0
=
  allow_inversion key_management;
  match i.km with
  | Erased -> True
  | Runtime ->
      i.key.invariant h0 k /\
      B.(loc_disjoint (i.key.footprint h0 k) (loc_buffer dst)) /\
      B.(loc_disjoint (i.key.footprint h0 k) (i.state.footprint h0 s))

inline_for_extraction noextract
let finish_st (i: index) =
  k: optional_key i ->
  s:i.state.s ->
  dst:B.buffer uint8 ->
  l: i.output_length_t { B.length dst == i.output_length l } ->
  Stack unit
  (requires fun h0 ->
    i.state.invariant h0 s /\
    B.live h0 dst /\
    B.(loc_disjoint (i.state.footprint h0 s) (loc_buffer dst)) /\
    finish_st_pre i k s dst l h0)
  (ensures fun h0 _ h1 ->
    i.state.invariant h1 s /\
    B.(modifies (loc_buffer dst `loc_union` (i.state.footprint h0 s)) h0 h1) /\
    i.state.footprint h0 s == i.state.footprint h1 s /\
    B.as_seq h1 dst == i.finish_s (optional_t h0 k) (i.state.v h0 s) l /\
    (i.state.freeable h0 s ==> i.state.freeable h1 s))

[@ Meta.Attribute.specialize ]
val finish: i:G.erased index -> finish_st i

[@ Meta.Attribute.specialize ]
val key_alloca: (#i: index) -> Stateful.alloca_st i.key
[@ Meta.Attribute.specialize ]
val key_create_in: (#i: index) -> Stateful.create_in_st i.key
[@ Meta.Attribute.specialize ]
val key_free: (#i: index) -> Stateful.free_st i.key
[@ Meta.Attribute.specialize ]
val key_copy: (#i: index) -> Stateful.copy_st i.key

[@ Meta.Attribute.specialize ]
val state_alloca: (#i: index) -> Stateful.alloca_st i.state
[@ Meta.Attribute.specialize ]
val state_create_in: (#i: index) -> Stateful.create_in_st i.state
[@ Meta.Attribute.specialize ]
val state_free: (#i: index) -> Stateful.free_st i.state
[@ Meta.Attribute.specialize ]
val state_copy: (#i: index) -> Stateful.copy_st i.state
