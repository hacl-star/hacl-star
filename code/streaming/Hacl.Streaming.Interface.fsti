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

let concat_blocks_modulo (block_len: pos) (s1 s2: S.seq uint8): Lemma
  (requires
    S.length s1 % block_len = 0 /\
    S.length s2 % block_len = 0)
  (ensures
    S.length (S.append s1 s2) % block_len = 0)
=
  let input = S.append s1 s2 in
  let input1 = s1 in
  let input2 = s2 in
  calc (==) {
    S.length input % block_len;
  (==) { S.lemma_len_append input1 input2 }
    (S.length input1 + S.length input2) % block_len;
  (==) {
    FStar.Math.Lemmas.modulo_distributivity (S.length input1) (S.length input2) (block_len)
  }
    (S.length input1 % block_len + S.length input2 % block_len) % block_len;
  (==) { (* hyp *) }
    0 % block_len;
  (==) { }
    0;
  }


/// The type class of block-based operations.
/// Equipped with a generic index. May be unit if there's no agility, or hash algorithm for agility.
inline_for_extraction noeq
type block (index: Type0) =
| Block:

  // Astract footprint.
  state: (index -> Type0) ->
  footprint: (#i:index -> h:HS.mem -> s:state i -> GTot B.loc) ->

  freeable: (#i:index -> h:HS.mem -> p:state i -> Type) ->
  invariant: (#i:index -> h:HS.mem -> s:state i -> Type) ->

  index_of_state: (i:G.erased index -> (
    let i = G.reveal i in
    s: state i -> Stack index
    (fun h0 -> invariant h0 s)
    (fun h0 i' h1 -> h0 == h1 /\ i' == i))) ->

  // A pure representation of a state
  t: (index -> Type0) ->
  v: (#i:index -> h:HS.mem -> s:state i -> GTot (t i)) ->

  // Introducing a notion of blocks and final result.
  max_input_length: (index -> x:nat { 0 < x /\ x < pow2 64 }) ->
  output_len: (index -> x:U32.t { U32.v x > 0 }) ->
  block_len: (index -> x:U32.t { U32.v x > 0 }) ->

  /// An init/update/update_last/finish specification. The long refinements were
  /// previously defined as blocks / small / output.
  init_s: (i:index -> t i) ->
  update_multi_s: (i:index -> t i -> s:S.seq uint8 { S.length s % U32.v (block_len i) = 0 } -> t i) ->
  update_last_s: (i:index ->
    t i ->
    prevlen:nat { prevlen % U32.v (block_len i) = 0 } ->
    s:S.seq uint8 { S.length s + prevlen <= max_input_length i } ->
    t i) ->
  finish_s: (i:index -> t i -> s:S.seq uint8 { S.length s = U32.v (output_len i) }) ->

  /// The specification in one shot.
  spec_s: (i:index -> input:S.seq uint8 { S.length input <= max_input_length i } ->
    output:S.seq uint8 { S.length output == U32.v (output_len i) }) ->

  // Required lemmas... clients need to introduce these into their context via a local SMTPat.
  // Note: the way I authored update_multi_associative is terrible to work with,
  // see comment starting with "GHA" in update_round.

  update_multi_zero: (i:index -> h:t i -> Lemma
    (ensures (update_multi_s i h S.empty == h))) ->

  update_multi_associative: (i:index ->
    h: t i ->
    input1:S.seq uint8 { S.length input1 % U32.v (block_len i) = 0 } ->
    input2:S.seq uint8 { S.length input2 % U32.v (block_len i) = 0 } ->
    Lemma (ensures (
      let input = S.append input1 input2 in
      concat_blocks_modulo (U32.v (block_len i)) input1 input2;
      update_multi_s i (update_multi_s i h input1) input2 ==
        update_multi_s i h input))) ->

  spec_is_incremental: (i:index ->
    input:S.seq uint8 { S.length input <= max_input_length i } ->
    Lemma (ensures (
      let open FStar.Mul in
      let block_length = U32.v (block_len i) in
      let n = S.length input / block_length in
      let bs, l = S.split input (n * block_length) in
      FStar.Math.Lemmas.multiple_modulo_lemma n block_length;
      let hash = update_multi_s i (init_s i) bs in
      let hash = update_last_s i hash (n * block_length) l in
      finish_s i hash `S.equal` spec_s i input))) ->

  // Adequate framing lemmas
  invariant_loc_in_footprint: (#i:index -> h:HS.mem -> s:state i -> Lemma
    (requires (invariant h s))
    (ensures (B.loc_in (footprint #i h s) h))) ->

  frame_invariant: (#i:index -> l:B.loc -> s:state i -> h0:HS.mem -> h1:HS.mem -> Lemma
    (requires (
      invariant h0 s /\
      B.loc_disjoint l (footprint #i h0 s) /\
      B.modifies l h0 h1))
    (ensures (
      invariant h1 s /\
      v h0 s == v h1 s /\
      footprint #i h1 s == footprint #i h0 s))) ->

  frame_freeable: (#i:index -> l:B.loc -> s:state i -> h0:HS.mem -> h1:HS.mem -> Lemma
    (requires (
      invariant h0 s /\
      freeable h0 s /\
      B.loc_disjoint l (footprint #i h0 s) /\
      B.modifies l h0 h1))
    (ensures (
      freeable h1 s))) ->

  // Stateful operations
  alloca: (i:index -> StackInline (state i)
    (requires (fun _ -> True))
    (ensures (fun h0 s h1 ->
      invariant h1 s /\
      B.(modifies loc_none h0 h1) /\
      B.fresh_loc (footprint #i h1 s) h0 h1 /\
      B.(loc_includes (loc_region_only true (HS.get_tip h1)) (footprint #i h1 s))))) ->

  create_in: (i:index -> r:HS.rid -> ST (state i)
    (requires (fun _ ->
      HyperStack.ST.is_eternal_region r))
    (ensures (fun h0 s h1 ->
      invariant h1 s /\
      B.(modifies loc_none h0 h1) /\
      B.fresh_loc (footprint #i h1 s) h0 h1 /\
      B.(loc_includes (loc_region_only true r) (footprint #i h1 s)) /\
      freeable h1 s))) ->

  init: (i:G.erased index -> (
    let i = G.reveal i in
    s: state i -> Stack unit
    (requires fun h0 -> invariant #i h0 s)
    (ensures fun h0 _ h1 ->
      invariant #i h1 s /\
      v h1 s == init_s i /\
      B.(modifies (footprint #i h0 s) h0 h1) /\
      footprint #i h0 s == footprint #i h1 s /\
      (freeable h0 s ==> freeable h1 s)))) ->

  update_multi: (i:G.erased index -> (
    let i = G.reveal i in
    s:state i ->
    blocks:B.buffer uint8 { B.length blocks % U32.v (block_len i) = 0 } ->
    len: U32.t { U32.v len = B.length blocks } ->
    Stack unit
    (requires fun h0 ->
      invariant #i h0 s /\
      B.live h0 blocks /\
      B.(loc_disjoint (footprint #i h0 s) (loc_buffer blocks)))
    (ensures fun h0 _ h1 ->
      B.(modifies (footprint #i h0 s) h0 h1) /\
      footprint #i h0 s == footprint #i h1 s /\
      invariant #i h1 s /\
      v h1 s == update_multi_s i (v h0 s) (B.as_seq h0 blocks) /\
      (freeable #i h0 s ==> freeable #i h1 s)))) ->

  update_last: (
    i: G.erased index -> (
    let i = G.reveal i in
    s:state i ->
    last:B.buffer uint8 { B.len last < block_len i } ->
    total_len:U64.t {
      U64.v total_len <= max_input_length i /\
      U64.v total_len - B.length last >= 0 /\
      (U64.v total_len - B.length last) % U32.v (block_len i) = 0 } ->
    Stack unit
    (requires fun h0 ->
      invariant #i h0 s /\
      B.live h0 last /\
      B.(loc_disjoint (footprint #i h0 s) (loc_buffer last)))
    (ensures fun h0 _ h1 ->
      invariant #i h1 s /\
      v h1 s == update_last_s i (v h0 s) (U64.v total_len - B.length last) (B.as_seq h0 last) /\
      B.(modifies (footprint #i h0 s) h0 h1) /\
      footprint #i h0 s == footprint #i h1 s /\
      (freeable #i h0 s ==> freeable #i h1 s)))) ->

  finish: (
    i: G.erased index -> (
    let i = G.reveal i in
    s:state i ->
    dst:B.buffer uint8 { B.len dst = output_len i } ->
    Stack unit
    (requires fun h0 ->
      invariant #i h0 s /\
      B.live h0 dst /\
      B.(loc_disjoint (footprint #i h0 s) (loc_buffer dst)))
    (ensures fun h0 _ h1 ->
      invariant #i h1 s /\
      B.(modifies (loc_buffer dst) h0 h1) /\
      footprint #i h0 s == footprint #i h1 s /\
      B.as_seq h1 dst == finish_s i (v h0 s) /\
      (freeable #i h0 s ==> freeable #i h1 s)))) ->

  free: (
    i: G.erased index -> (
    let i = G.reveal i in
    s:state i -> ST unit
    (requires fun h0 ->
      freeable h0 s /\
      invariant #i h0 s)
    (ensures fun h0 _ h1 ->
      B.(modifies (footprint #i h0 s) h0 h1)))) ->

  copy: (
    i:G.erased index -> (
    let i = G.reveal i in
    s_src:state i ->
    s_dst:state i ->
    Stack unit
      (requires (fun h0 ->
        invariant #i h0 s_src /\
        invariant #i h0 s_dst /\
        B.(loc_disjoint (footprint #i h0 s_src) (footprint #i h0 s_dst))))
      (ensures fun h0 _ h1 ->
        B.(modifies (footprint #i h0 s_dst) h0 h1) /\
        footprint #i h0 s_dst == footprint #i h1 s_dst /\
        (freeable h0 s_dst ==> freeable h1 s_dst) /\
        invariant #i h1 s_dst /\
        v h1 s_dst == v h0 s_src))) ->

  block index

(*
/// Maximum input length, but fitting on a 64-bit integer (since the streaming
/// module doesn't bother taking into account lengths that are greater than
/// that).
let max_input_length64 a: x:nat { 0 < x /\ x < pow2 64 /\ x <= Spec.Hash.Definitions.max_input_length a } =
  let open Spec.Hash.Definitions in
  let _ = allow_inversion hash_alg in
  match a with
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> assert_norm (0 < pow2 61 - 1 && pow2 61 < pow2 64); pow2 61 - 1
  | SHA2_384 | SHA2_512 -> assert_norm (pow2 64 < pow2 125 - 1); pow2 64 - 1


inline_for_extraction
let evercrypt_hash: block Spec.Hash.Definitions.hash_alg =
  Block
    EverCrypt.Hash.state
    (fun #i h s -> EverCrypt.Hash.footprint s h)
    EverCrypt.Hash.freeable
    (fun #i h s -> EverCrypt.Hash.invariant s h)
    EverCrypt.Hash.alg_of_state
    Spec.Hash.Definitions.words_state
    (fun #i h s -> EverCrypt.Hash.repr s h)
    max_input_length64
    Hacl.Hash.Definitions.hash_len
    Hacl.Hash.Definitions.block_len
    Spec.Agile.Hash.init
    Spec.Agile.Hash.update_multi
    Spec.Hash.Incremental.update_last
    Spec.Hash.PadFinish.finish
    Spec.Agile.Hash.hash
    Spec.Hash.Lemmas.update_multi_zero
    Spec.Hash.Lemmas.update_multi_associative'
    Spec.Hash.Lemmas.hash_is_hash_incremental
    (fun #i h s -> EverCrypt.Hash.invariant_loc_in_footprint s h)
    (fun #i l s h0 h1 ->
      EverCrypt.Hash.frame_invariant l s h0 h1;
      EverCrypt.Hash.frame_invariant_implies_footprint_preservation l s h0 h1)
    (fun #i l s h0 h1 -> ())
    EverCrypt.Hash.alloca
    EverCrypt.Hash.create_in
    (fun i -> EverCrypt.Hash.init #i)
    (fun i -> EverCrypt.Hash.update_multi #i)
    (fun i -> EverCrypt.Hash.update_last #i)
    (fun i -> EverCrypt.Hash.finish #i)
    (fun i -> EverCrypt.Hash.free #i)
    (fun i -> EverCrypt.Hash.copy #i)

inline_for_extraction
let hacl_sha2_256: block unit =
  let open Spec.Hash.Definitions in
  Block
    (fun _ -> s:B.buffer uint32 { B.length s == state_word_length SHA2_256})
    (fun #_ h s -> B.loc_addr_of_buffer s)
    (fun #_ h s -> B.freeable s)
    (fun #_ h s -> B.live h s)
    (fun _ _ -> ())
    (fun _ -> words_state SHA2_256)
    (fun #_ h s -> B.as_seq h s)
    (fun () -> max_input_length64 SHA2_256)
    (fun () -> Hacl.Hash.Definitions.hash_len SHA2_256)
    (fun () -> Hacl.Hash.Definitions.block_len SHA2_256)
    (fun () -> Spec.Agile.Hash.(init SHA2_256))
    (fun () -> Spec.Agile.Hash.(update_multi SHA2_256))
    (fun () -> Spec.Hash.Incremental.(update_last SHA2_256))
    (fun () -> Spec.Hash.PadFinish.(finish SHA2_256))
    (fun () s -> Spec.Agile.Hash.(hash SHA2_256 s))
    (fun _ _ -> ())
    (fun _ _ _ _ -> ())
    (fun _ input -> Spec.Hash.Lemmas.hash_is_hash_incremental SHA2_256 input)
    (fun #_ h s -> ())
    (fun #_ l s h0 h1 -> ())
    (fun #_ l s h0 h1 -> ())
    (fun () -> B.alloca (Lib.IntTypes.u32 0) 8ul)
    (fun () r -> B.malloc r (Lib.IntTypes.u32 0) 8ul)
    (fun _ s -> Hacl.Hash.SHA2.init_256 s)
    (fun _ s blocks len -> Hacl.Hash.SHA2.update_multi_256 s blocks (len `U32.div` Hacl.Hash.Definitions.(block_len SHA2_256)))
    (fun _ s last total_len ->
      [@inline_let]
      let block_len64 = 64UL in
      assert_norm (U64.v block_len64 == block_length SHA2_256);
      let last_len: len_t SHA2_256 = U64.(total_len `rem` block_len64) in
      let prev_len = U64.(total_len `sub` last_len) in
      let last_len = FStar.Int.Cast.Full.uint64_to_uint32 last_len in
      assert (U64.v prev_len % block_length SHA2_256 = 0);
      Hacl.Hash.SHA2.update_last_256 s prev_len last last_len)
    (fun _ s dst -> Hacl.Hash.SHA2.finish_256 s dst)
    (fun _ s -> B.free s)
    (fun _ src dst -> B.blit src 0ul dst 0ul 8ul)
*)
