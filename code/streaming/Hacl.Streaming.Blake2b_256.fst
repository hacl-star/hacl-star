module Hacl.Streaming.Blake2b_256

// Blake2b_256 is hand-written, other files generated with:
// sed 's/2B/2S/g;s/2b/2s/g;' Hacl.Streaming.Blake2b_256.fst > Hacl.Streaming.Blake2s_256.fst; sed 's/256/128/g' Hacl.Streaming.Blake2s_256.fst > Hacl.Streaming.Blake2s_128.fst; sed 's/256/256/g' Hacl.Streaming.Blake2b_256.fst > Hacl.Streaming.Blake2b_256.fst

module HS = FStar.HyperStack
module Blake2b256 = Hacl.Blake2b_256
module Common = Hacl.Streaming.Blake2.Common
module Core = Hacl.Impl.Blake2.Core
module F = Hacl.Streaming.Functor
module P = Hacl.Streaming.Blake2.Params
module I = Hacl.Streaming.Interface
module G = FStar.Ghost
module B = LowStar.Buffer
module S = FStar.Seq
module Impl = Hacl.Impl.Blake2.Generic
module Spec = Spec.Blake2

open FStar.HyperStack.ST

#set-options "--fuel 0 --ifuel 0"

inline_for_extraction noextract
let blake2b_256 =
  Common.blake2 Spec.Blake2B Core.M256 Blake2b256.init_with_params Blake2b256.update_multi
         Blake2b256.update_last Blake2b256.finish

/// Type abbreviations - makes Karamel use pretty names in the generated code

let block_state_t (kk: G.erased (Common.index Spec.Blake2B)) = Common.s Spec.Blake2B kk Core.M256
let state_t (kk: G.erased (Common.index Spec.Blake2B)) =
  F.state_s blake2b_256 kk (Common.s Spec.Blake2B kk Core.M256) (Common.blake_key Spec.Blake2B kk)

/// The incremental hash functions instantiations. Note that we can't write a
/// generic one, because the normalization then performed by KaRaMeL explodes.

/// All those implementations are for non-keyed hash.

inline_for_extraction noextract
[@ (Comment "  State allocation function when there is no key")]
let alloca_raw (kk: Common.index Spec.Blake2B): Tot _ =
  F.alloca blake2b_256 kk (Common.s Spec.Blake2B kk Core.M256) (Common.blake_key Spec.Blake2B kk)

private
let malloc_raw (kk: Common.index Spec.Blake2B): Tot _ =
  F.malloc blake2b_256 kk (Common.s Spec.Blake2B kk Core.M256) (Common.blake_key Spec.Blake2B kk)

[@ (Comment " State allocation function when there are parameters and a key. The
length of the key k MUST match the value of the field key_length in the
parameters. Furthermore, there is a static (not dynamically checked) requirement
that key_length does not exceed max_key (256 for S, 64 for B).)")]
val malloc_with_params_and_key:
  i:G.erased (P.index Spec.Blake2B) ->
  p:P.params Spec.Blake2B i ->
  k:LowStar.Buffer.buffer Lib.IntTypes.uint8 { LowStar.Buffer.length k == UInt8.v (fst i) } -> (
  let open F in
  let c = blake2b_256 in
  let t: Type0 = c.state.s i in
  let t': Type0 = I.optional_key (G.reveal i) c.km c.key in
  let k: Common.stateful_key_t Spec.Blake2B (G.reveal i) = p, k in
  r: HS.rid ->
  ST (state c i t t')
  (requires (fun h0 ->
    blake2b_256.key.invariant #i h0 k /\
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    invariant c i h1 s /\
    freeable c i h1 s /\
    seen c i h1 s == S.empty /\
    reveal_key blake2b_256 i h1 s == blake2b_256.key.v i h0 k /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint c i h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint c i h1 s))))
)

let malloc_with_params_and_key i p k r =
  let pv = P.get_params p in
  let i = pv.Core.key_length, pv.Core.digest_length in
  malloc_raw i (p, k) r

[@ (Comment " State allocation function when there is just a custom key. All
other parameters are set to their respective default values, meaning the output
length is the maximum allowed output (256 for S, 64 for B).")]
val malloc_with_key:
  k:LowStar.Buffer.buffer Lib.IntTypes.uint8 ->
  kk:Spec.key_length_t Spec.Blake2B { LowStar.Buffer.length k == UInt8.v kk } -> (
  let open F in
  let c = blake2b_256 in
  let i: Common.index Spec.Blake2B = kk, UInt8.uint_to_t (Spec.max_output Spec.Blake2B) in
  let t: Type0 = c.state.s i in
  let t': Type0 = I.optional_key (G.reveal i) c.km c.key in
  r: HS.rid ->
  ST (state c i t t')
  (requires (fun h0 ->
    // This type is rather annoying to write, since we can't just copy-paste
    // from Functor (with a few suitable names in scope).
    B.live h0 k /\ // The other few bits required to conclude key_invariant will materialize after stack-allocating
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    invariant c i h1 s /\
    freeable c i h1 s /\
    seen c i h1 s == S.empty /\
    reveal_key blake2b_256 i h1 s ==
      ({ Spec.blake2_default_params Spec.Blake2B with Spec.key_length = kk },
      (if fst i = 0uy then S.empty #uint8 else B.as_seq h0 (k <: B.buffer uint8))) /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint c i h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint c i h1 s))))
)

module ST = FStar.HyperStack.ST

let malloc_with_key k kk r =
  let _ = allow_inversion Spec.alg in
  let nn = UInt8.uint_to_t (Spec.max_output Spec.Blake2B) in
  let i: Common.index Spec.Blake2B = kk, nn in
  let h00 = ST.get () in

  let p = P.create_in Spec.Blake2B i r in
  let h0 = ST.get () in
  assert B.(as_seq h00 k == as_seq h0 k);

  let s = malloc_with_params_and_key (G.hide i) p k r in
  let h1 = ST.get () in
  assert F.(freeable blake2b_256 i h1 s);
  assert (nn == (Spec.blake2_default_params Spec.Blake2B).digest_length);
  calc (==) {
    F.reveal_key blake2b_256 i h1 s;
  (==) { }
    blake2b_256.key.v i h0 (p, k);
  (==) { }
    Common.key_v i h0 (p, k);
  (==) { _ by (FStar.Tactics.trefl ()) }
    P.v #Spec.Blake2B h0 p, (if fst i = 0uy then S.empty #Lib.IntTypes.uint8 else B.as_seq h0 (k <: B.buffer Lib.IntTypes.uint8));
  (==) { }
    { Spec.blake2_default_params Spec.Blake2B with Spec.key_length = kk; Spec.digest_length = nn }, (if fst i = 0uy then S.empty #Lib.IntTypes.uint8 else B.as_seq h0 (k <: B.buffer Lib.IntTypes.uint8));
  (==) { }
    { Spec.blake2_default_params Spec.Blake2B with Spec.key_length = kk }, (if fst i = 0uy then S.empty #Lib.IntTypes.uint8 else B.as_seq h0 (k <: B.buffer Lib.IntTypes.uint8));
  };
  assert (P.invariant h1 p);
  P.invariant_loc_in_footprint h1 p;
  assert B.(loc_disjoint (P.footprint h1 p) (F.footprint blake2b_256 i h1 s));
  P.free p;
  let h2 = ST.get () in
  F.frame_invariant blake2b_256 i (P.footprint h1 p) s h1 h2;
  F.frame_seen blake2b_256 i (P.footprint h1 p) s h1 h2;
  assert F.(freeable blake2b_256 i h2 s);
  s

// I generally don't like skipping signatures since there's a danger that a
// partial application generates a GTot that later on gives errors that are hard
// to debug (hence the Tot _ in this file), but this signature is just too
// painful to write and the refinement seems to be sufficient, so, there we go.
[@ (Comment "  State allocation function when there is no key")]
let malloc (r: HS.rid { HyperStack.ST.is_eternal_region r }) =
  malloc_with_key B.null 0uy r

private
let index_of_state (kk: G.erased (Common.index Spec.Blake2B)): Tot _ =
  F.index_of_state blake2b_256 kk (Common.s Spec.Blake2B kk Core.M256) (Common.blake_key Spec.Blake2B kk)

private
let reset_raw (kk: G.erased (Common.index Spec.Blake2B)): Tot _ =
  F.reset blake2b_256 kk (Common.s Spec.Blake2B kk Core.M256) (Common.blake_key Spec.Blake2B kk)

[@ (Comment " Re-initialization function. The reinitialization API is tricky --
you MUST reuse the same original parameters for digest (output) length and key
length.")]
val reset_with_key_and_params: (i: G.erased (Common.index Spec.Blake2B)) -> (
  let open F in
  let c = blake2b_256 in
  let t: Type0 = c.state.s (G.reveal i) in
  let t': Type0 = I.optional_key (G.reveal i) c.km c.key in
  state:state c (G.reveal i) t t' ->
  p:P.params Spec.Blake2B i ->
  k:LowStar.Buffer.buffer Lib.IntTypes.uint8 { LowStar.Buffer.length k == UInt8.v (fst i) } -> (
  let key: Common.stateful_key_t Spec.Blake2B (G.reveal i) = (p, k) in
  unit ->
  Stack unit
  (requires (fun h0 ->
    blake2b_256.key.invariant #i h0 key /\
    B.loc_disjoint (blake2b_256.key.footprint #i h0 key) (footprint c i h0 state) /\
    invariant c i h0 state))
  (ensures (fun h0 _ h1 ->
    invariant c i h1 state /\
    seen c i h1 state == S.empty /\
    reveal_key c i h1 state == blake2b_256.key.v i h0 key /\
    footprint c i h0 state == footprint c i h1 state /\
    B.(modifies (footprint c i h0 state) h0 h1) /\
    preserves_freeable c i state h0 h1))))

let reset_with_key_and_params i s p k () =
  let i = index_of_state i s in
  reset_raw i s (p, k)

(*
[@ (Comment " Re-initialization function when there is a key. Note that the key
size is not allowed to change, which is why this function does not take a key
length -- the key has to be same key size that was originally passed to
`malloc_with_key`")]
val reset_with_key: (i: G.erased (Common.key_size_t Spec.Blake2B)) -> (
  let open F in
  let c = blake2b_256 in
  let t: Type0 = c.state.s (G.reveal i) in
  let t': Type0 = I.optional_key (G.reveal i) c.km c.key in
  state:state c (G.reveal i) t t' ->
  k:LowStar.Buffer.buffer Lib.IntTypes.uint8 { LowStar.Buffer.len k == G.reveal i} -> (
  let key: Common.stateful_key_t Spec.Blake2B (G.reveal i) = G.reveal i, k in
  unit ->
  Stack unit
  (requires (fun h0 ->
    blake2b_256.key.invariant #i h0 key /\
    B.loc_disjoint (blake2b_256.key.footprint #i h0 key) (footprint c i h0 state) /\
    invariant c i h0 state))
  (ensures (fun h0 _ h1 ->
    invariant c i h1 state /\
    seen c i h1 state == S.empty /\
    reveal_key c i h1 state == blake2b_256.key.v i h0 key /\
    footprint c i h0 state == footprint c i h1 state /\
    B.(modifies (footprint c i h0 state) h0 h1) /\
    preserves_freeable c i state h0 h1))))

let reset_with_key (i: G.erased (Common.key_size_t Spec.Blake2B)) s k () =
  let kk = index_of_state i s in
  reset_raw i s (kk, k)

[@ (Comment "  Re-initialization function when there is no key")]
val reset: (
  let i: Common.key_size_t Spec.Blake2B = 0ul in
  let open F in
  let c = blake2b_256 in
  let t: Type0 = c.state.s i in
  let t': Type0 = I.optional_key i c.km c.key in
  let k:LowStar.Buffer.buffer Lib.IntTypes.uint8 = B.null in
  let key: Common.stateful_key_t Spec.Blake2B i = i, k in
  state:state c i t t' ->
  Stack unit
  (requires (fun h0 ->
    // WHAT THE HECK. Using `c` here breaks typing?!!!
    blake2b_256.key.invariant #i h0 key /\
    B.loc_disjoint (blake2b_256.key.footprint #i h0 key) (footprint c i h0 state) /\
    invariant c i h0 state))
  (ensures (fun h0 _ h1 ->
    invariant c i h1 state /\
    seen c i h1 state == S.empty /\
    reveal_key c i h1 state == blake2b_256.key.v i h0 key /\
    footprint c i h0 state == footprint c i h1 state /\
    B.(modifies (footprint c i h0 state) h0 h1) /\
    preserves_freeable c i state h0 h1)))

let reset s =
  reset_with_key (G.hide 0ul) s B.null ()
*)

[@ (Comment "  Update function when there is no key; 0 = success, 1 = max length exceeded")]
let update (kk: G.erased (Common.index Spec.Blake2B)): Tot _ =
  F.update blake2b_256 kk (Common.s Spec.Blake2B kk Core.M256) (Common.blake_key Spec.Blake2B kk)

[@ (Comment "  Finish function when there is no key")]
let digest (kk: G.erased (Common.index Spec.Blake2B)): Tot _ =
  F.digest_erased blake2b_256 kk (Common.s Spec.Blake2B kk Core.M256) (Common.blake_key Spec.Blake2B kk)

[@ (Comment "  Free state function when there is no key")]
let free (kk: G.erased (Common.index Spec.Blake2B)): Tot _ =
  F.free blake2b_256 kk (Common.s Spec.Blake2B kk Core.M256) (Common.blake_key Spec.Blake2B kk)

[@ (Comment "  Copying. The key length (or absence thereof) must match between source and destination.")]
let copy (kk: G.erased (Common.index Spec.Blake2B)): Tot _ =
  F.copy blake2b_256 kk (Common.s Spec.Blake2B kk Core.M256) (Common.blake_key Spec.Blake2B kk)

(* The one-shot hash *)
[@@ Comment "Write the BLAKE2b digest of message `input` using key `key` into `output`.

@param output Pointer to `output_len` bytes of memory where the digest is written to.
@param output_len Length of the to-be-generated digest with 1 <= `output_len` <= 64.
@param input Pointer to `input_len` bytes of memory where the input message is read from.
@param input_len Length of the input message.
@param key Pointer to `key_len` bytes of memory where the key is read from.
@param key_len Length of the key. Can be 0."]
let hash_with_key : Impl.blake2_st Spec.Blake2B Core.M256 =
  Impl.blake2 #Spec.Blake2B #Core.M256 Blake2b256.init Blake2b256.update Blake2b256.finish

let hash_with_key_and_paramas : Impl.blake2_with_params_st Spec.Blake2B Core.M256 =
  Impl.blake2_with_params #Spec.Blake2B #Core.M256 Blake2b256.init_with_params Blake2b256.update Blake2b256.finish
