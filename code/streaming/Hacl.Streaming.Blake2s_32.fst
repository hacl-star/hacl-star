module Hacl.Streaming.Blake2s_32

// Blake2s_32 is hand-written, other files generated with:
// sed 's/2S/2S/g;s/2s/2s/g;' Hacl.Streaming.Blake2s_32.fst > Hacl.Streaming.Blake2s_32.fst; sed 's/32/128/g' Hacl.Streaming.Blake2s_32.fst > Hacl.Streaming.Blake2s_128.fst; sed 's/32/256/g' Hacl.Streaming.Blake2s_32.fst > Hacl.Streaming.Blake2s_256.fst

module HS = FStar.HyperStack
module Blake2s32 = Hacl.Blake2s_32
module Common = Hacl.Streaming.Blake2.Common
module Core = Hacl.Impl.Blake2.Core
module F = Hacl.Streaming.Functor
module I = Hacl.Streaming.Interface
module G = FStar.Ghost
module B = LowStar.Buffer
module S = FStar.Seq
module Impl = Hacl.Impl.Blake2.Generic
module Spec = Spec.Blake2

open FStar.HyperStack.ST

#set-options "--fuel 0 --ifuel 0"

inline_for_extraction noextract
let blake2s_32 =
  Common.blake2 Spec.Blake2S Core.M32 Blake2s32.init Blake2s32.update_multi
         Blake2s32.update_last Blake2s32.finish

/// Type abbreviations - makes Karamel use pretty names in the generated code

let block_state_t (kk: G.erased (Common.key_size_t Spec.Blake2S)) = Common.s Spec.Blake2S kk Core.M32
let state_t (kk: G.erased (Common.key_size_t Spec.Blake2S)) =
  F.state_s blake2s_32 kk (Common.s Spec.Blake2S kk Core.M32) (Common.blake_key Spec.Blake2S kk)

/// The incremental hash functions instantiations. Note that we can't write a
/// generic one, because the normalization then performed by KaRaMeL explodes.

/// All those implementations are for non-keyed hash.

inline_for_extraction noextract
[@ (Comment "  State allocation function when there is no key")]
let alloca_raw (kk: Common.key_size_t Spec.Blake2S): Tot _ =
  F.alloca blake2s_32 kk (Common.s Spec.Blake2S kk Core.M32) (Common.blake_key Spec.Blake2S kk)

private
let malloc_raw (kk: Common.key_size_t Spec.Blake2S): Tot _ =
  F.malloc blake2s_32 kk (Common.s Spec.Blake2S kk Core.M32) (Common.blake_key Spec.Blake2S kk)

[@ (Comment "  State allocation function when there is a key")]
val malloc_with_key:
  k:LowStar.Buffer.buffer Lib.IntTypes.uint8 ->
  kk:Common.key_size_t Spec.Blake2S { LowStar.Buffer.len k == kk } -> (
  let open F in
  let c = blake2s_32 in
  let i = kk in
  let t: Type0 = c.state.s i in
  let t': Type0 = I.optional_key i c.km c.key in
  let k: Common.stateful_key_t Spec.Blake2S kk = kk, k in
  r: HS.rid ->
  ST (state c i t t')
  (requires (fun h0 ->
    c.key.invariant #i h0 k /\
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    invariant c i h1 s /\
    freeable c i h1 s /\
    seen c i h1 s == S.empty /\
    reveal_key c i h1 s == c.key.v i h0 k /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint c i h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint c i h1 s))))
)

let malloc_with_key k kk r =
  malloc_raw kk (kk, k) r

// I generally don't like skipping signatures since there's a danger that a
// partial application generates a GTot that later on gives errors that are hard
// to debug (hence the Tot _ in this file), but this signature is just too
// painful to write and the refinement seems to be sufficient, so, there we go.
[@ (Comment "  State allocation function when there is no key")]
let malloc (r: HS.rid { HyperStack.ST.is_eternal_region r }) =
  malloc_with_key B.null 0ul r

[@ (Comment " Re-initialization function when there is a key. Note that the key
size is not allowed to change, which is why this function does not take a key
length -- the key has to be same key size that was originally passed to
`malloc_with_key`")]
val reset_with_key: (i: G.erased (Common.key_size_t Spec.Blake2S)) -> (
  let open F in
  let c = blake2s_32 in
  let t: Type0 = c.state.s (G.reveal i) in
  let t': Type0 = I.optional_key (G.reveal i) c.km c.key in
  state:state c (G.reveal i) t t' ->
  k:LowStar.Buffer.buffer Lib.IntTypes.uint8 { LowStar.Buffer.len k == G.reveal i} -> (
  let key: Common.stateful_key_t Spec.Blake2S (G.reveal i) = G.reveal i, k in
  unit ->
  Stack unit
  (requires (fun h0 ->
    blake2s_32.key.invariant #i h0 key /\
    B.loc_disjoint (blake2s_32.key.footprint #i h0 key) (footprint c i h0 state) /\
    invariant c i h0 state))
  (ensures (fun h0 _ h1 ->
    invariant c i h1 state /\
    seen c i h1 state == S.empty /\
    reveal_key c i h1 state == blake2s_32.key.v i h0 key /\
    footprint c i h0 state == footprint c i h1 state /\
    B.(modifies (footprint c i h0 state) h0 h1) /\
    preserves_freeable c i state h0 h1))))

private
let reset_raw (kk: G.erased (Common.key_size_t Spec.Blake2S)): Tot _ =
  F.reset blake2s_32 kk (Common.s Spec.Blake2S kk Core.M32) (Common.blake_key Spec.Blake2S kk)

private
let index_of_state (kk: G.erased (Common.key_size_t Spec.Blake2S)): Tot _ =
  F.index_of_state blake2s_32 kk (Common.s Spec.Blake2S kk Core.M32) (Common.blake_key Spec.Blake2S kk)

let reset_with_key (i: G.erased (Common.key_size_t Spec.Blake2S)) s k () =
  let kk = index_of_state i s in
  reset_raw i s (kk, k)

[@ (Comment "  Re-initialization function when there is no key")]
val reset: (
  let i: Common.key_size_t Spec.Blake2S = 0ul in
  let open F in
  let c = blake2s_32 in
  let t: Type0 = c.state.s i in
  let t': Type0 = I.optional_key i c.km c.key in
  let k:LowStar.Buffer.buffer Lib.IntTypes.uint8 = B.null in
  let key: Common.stateful_key_t Spec.Blake2S i = i, k in
  state:state c i t t' ->
  Stack unit
  (requires (fun h0 ->
    // WHAT THE HECK. Using `c` here breaks typing?!!!
    blake2s_32.key.invariant #i h0 key /\
    B.loc_disjoint (blake2s_32.key.footprint #i h0 key) (footprint c i h0 state) /\
    invariant c i h0 state))
  (ensures (fun h0 _ h1 ->
    invariant c i h1 state /\
    seen c i h1 state == S.empty /\
    reveal_key c i h1 state == blake2s_32.key.v i h0 key /\
    footprint c i h0 state == footprint c i h1 state /\
    B.(modifies (footprint c i h0 state) h0 h1) /\
    preserves_freeable c i state h0 h1)))

let reset s =
  reset_with_key (G.hide 0ul) s B.null ()

[@ (Comment "  Update function when there is no key; 0 = success, 1 = max length exceeded")]
let update (kk: G.erased (Common.key_size_t Spec.Blake2S)): Tot _ =
  F.update blake2s_32 kk (Common.s Spec.Blake2S kk Core.M32) (Common.blake_key Spec.Blake2S kk)

[@ (Comment "  Finish function when there is no key")]
let digest (kk: G.erased (Common.key_size_t Spec.Blake2S)): Tot _ =
  F.digest_erased blake2s_32 kk (Common.s Spec.Blake2S kk Core.M32) (Common.blake_key Spec.Blake2S kk)

[@ (Comment "  Free state function when there is no key")]
let free (kk: G.erased (Common.key_size_t Spec.Blake2S)): Tot _ =
  F.free blake2s_32 kk (Common.s Spec.Blake2S kk Core.M32) (Common.blake_key Spec.Blake2S kk)

[@ (Comment "  Copying. The key length (or absence thereof) must match between source and destination.")]
let copy (kk: G.erased (Common.key_size_t Spec.Blake2S)): Tot _ =
  F.copy blake2s_32 kk (Common.s Spec.Blake2S kk Core.M32) (Common.blake_key Spec.Blake2S kk)

(* The one-shot hash *)
[@@ Comment "Write the BLAKE2s digest of message `input` using key `key` into `output`.

@param output Pointer to `output_len` bytes of memory where the digest is written to.
@param output_len Length of the to-be-generated digest with 1 <= `output_len` <= 64.
@param input Pointer to `input_len` bytes of memory where the input message is read from.
@param input_len Length of the input message.
@param key Pointer to `key_len` bytes of memory where the key is read from.
@param key_len Length of the key. Can be 0."]
let hash_with_key : Impl.blake2_st Spec.Blake2S Core.M32 =
  Impl.blake2 #Spec.Blake2S #Core.M32 Blake2s32.init Blake2s32.update Blake2s32.finish
