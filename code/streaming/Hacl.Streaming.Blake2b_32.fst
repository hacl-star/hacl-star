module Hacl.Streaming.Blake2b_32

// Blake2b_32 is hand-written, other files generated with:
// sed 's/2B/2S/g;s/2b/2s/g;' Hacl.Streaming.Blake2b_32.fst > Hacl.Streaming.Blake2s_32.fst; sed 's/32/128/g' Hacl.Streaming.Blake2s_32.fst > Hacl.Streaming.Blake2s_128.fst; sed 's/32/256/g' Hacl.Streaming.Blake2b_32.fst > Hacl.Streaming.Blake2b_256.fst

module HS = FStar.HyperStack
module Blake2b32 = Hacl.Blake2b_32
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
let blake2b_32 =
  Common.blake2 Spec.Blake2B Core.M32 Blake2b32.init_with_params Blake2b32.update_multi
         Blake2b32.update_last Blake2b32.finish

/// Type abbreviations - makes Karamel use pretty names in the generated code
let block_state_t (kk: G.erased (Common.index Spec.Blake2B)) = Common.s Spec.Blake2B kk Core.M32

let state_t (kk: G.erased (Common.index Spec.Blake2B)) =
  F.state_s blake2b_32 kk (Common.s Spec.Blake2B kk Core.M32) (Common.blake_key Spec.Blake2B kk)

/// The incremental hash functions instantiations. Note that we can't write a
/// generic one, because the normalization then performed by KaRaMeL explodes.

/// All those implementations are for non-keyed hash.

inline_for_extraction noextract
[@ (Comment "  State allocation function when there is no key")]
let alloca_raw (kk: Common.index Spec.Blake2B): Tot _ =
  F.alloca blake2b_32 kk (Common.s Spec.Blake2B kk Core.M32) (Common.blake_key Spec.Blake2B kk)

private
let malloc_raw (kk: Common.index Spec.Blake2B): Tot _ =
  F.malloc blake2b_32 kk (Common.s Spec.Blake2B kk Core.M32) (Common.blake_key Spec.Blake2B kk)

[@ (Comment " General-purpose allocation function that gives control over all
Blake2 parameters, including the key. Further resettings of the state SHALL be
done with `reset_with_params_and_key`, and SHALL feature the exact same values
for the `key_length` and `digest_length` fields as passed here. In other words,
once you commit to a digest and key length, the only way to change these
parameters is to allocate a new object.

The caller must satisfy the following requirements.
- The length of the key k MUST match the value of the field key_length in the
  parameters.
- The key_length must not exceed 32 for S, 64 for B.
- The digest_length must not exceed 32 for S, 64 for B.
")]
val malloc_with_params_and_key:
  i:G.erased (P.index Spec.Blake2B) ->
  p:P.params Spec.Blake2B i ->
  k:LowStar.Buffer.buffer Lib.IntTypes.uint8 { LowStar.Buffer.length k == UInt8.v ((G.reveal i).key_length) } -> (
  let open F in
  let c = blake2b_32 in
  let t: Type0 = c.state.s i in
  let t': Type0 = I.optional_key (G.reveal i) c.km c.key in
  let k: Common.stateful_key_t Spec.Blake2B (G.reveal i) = p, k in
  r: HS.rid ->
  ST (state c i t t')
  (requires (fun h0 ->
    blake2b_32.key.invariant #i h0 k /\
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    invariant c i h1 s /\
    freeable c i h1 s /\
    seen c i h1 s == S.empty /\
    reveal_key blake2b_32 i h1 s == blake2b_32.key.v i h0 k /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint c i h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint c i h1 s))))
)

let malloc_with_params_and_key i p k r =
  let pv = P.get_params p in
  let i = { P.key_length = pv.Core.key_length; digest_length = pv.Core.digest_length } in
  malloc_raw i (p, k) r

[@ (Comment " Specialized allocation function that picks default values for all
parameters, except for the key_length. Further resettings of the state SHALL be
done with `reset_with_key`, and SHALL feature the exact same key length `kk` as
passed here. In other words, once you commit to a key length, the only way to
change this parameter is to allocate a new object.

The caller must satisfy the following requirements.
- The key_length must not exceed 32 for S, 64 for B.
")]
val malloc_with_key:
  k:LowStar.Buffer.buffer Lib.IntTypes.uint8 ->
  kk:Spec.key_length_t Spec.Blake2B { LowStar.Buffer.length k == UInt8.v kk } -> (
  let open F in
  let c = blake2b_32 in
  let i: Common.index Spec.Blake2B = { P.key_length = kk; digest_length = UInt8.uint_to_t (Spec.max_output Spec.Blake2B) } in
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
    reveal_key blake2b_32 i h1 s ==
      ({ Spec.blake2_default_params Spec.Blake2B with Spec.key_length = kk },
      (if i.key_length = 0uy then S.empty #uint8 else B.as_seq h0 (k <: B.buffer uint8))) /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint c i h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint c i h1 s))))
)

module ST = FStar.HyperStack.ST

let malloc_with_key k kk r =
  let hi = ST.get () in
  push_frame ();
  let _ = allow_inversion Spec.alg in
  let nn = UInt8.uint_to_t (Spec.max_output Spec.Blake2B) in
  let i: Common.index Spec.Blake2B = { key_length = kk; digest_length = nn } in
  let h00 = ST.get () in

  let p = P.alloca Spec.Blake2B i in
  let h0 = ST.get () in
  assert B.(as_seq h00 k == as_seq h0 k);

  let s = malloc_with_params_and_key (G.hide i) p k r in
  let h1 = ST.get () in
  assert F.(freeable blake2b_32 i h1 s);
  assert (nn == (Spec.blake2_default_params Spec.Blake2B).digest_length);
  calc (==) {
    F.reveal_key blake2b_32 i h1 s;
  (==) { }
    blake2b_32.key.v i h0 (p, k);
  (==) { }
    Common.key_v i h0 (p, k);
  (==) { _ by (FStar.Tactics.trefl ()) }
    P.v #Spec.Blake2B h0 p, (if i.key_length = 0uy then S.empty #Lib.IntTypes.uint8 else B.as_seq h0 (k <: B.buffer Lib.IntTypes.uint8));
  (==) { }
    { Spec.blake2_default_params Spec.Blake2B with Spec.key_length = kk; Spec.digest_length = nn }, (if i.key_length = 0uy then S.empty #Lib.IntTypes.uint8 else B.as_seq h0 (k <: B.buffer Lib.IntTypes.uint8));
  (==) { }
    { Spec.blake2_default_params Spec.Blake2B with Spec.key_length = kk }, (if i.key_length = 0uy then S.empty #Lib.IntTypes.uint8 else B.as_seq h0 (k <: B.buffer Lib.IntTypes.uint8));
  };
  pop_frame ();
  let hf = ST.get () in
  F.frame_invariant blake2b_32 i (B.loc_region_only false (HS.get_tip h1)) s h1 hf;
  s

// I generally don't like skipping signatures since there's a danger that a
// partial application generates a GTot that later on gives errors that are hard
// to debug (hence the Tot _ in this file), but this signature is just too
// painful to write and the refinement seems to be sufficient, so, there we go.
[@ (Comment " Specialized allocation function that picks default values for all
parameters, and has no key. Effectively, this is what you want if you intend to
use Blake2 as a hash function. Further resettings of the state SHALL be done with `reset`.")]
let malloc (r: HS.rid { HyperStack.ST.is_eternal_region r }) =
  malloc_with_key B.null 0uy r

private
let index_of_state (kk: G.erased (Common.index Spec.Blake2B)): Tot _ =
  F.index_of_state blake2b_32 kk (Common.s Spec.Blake2B kk Core.M32) (Common.blake_key Spec.Blake2B kk)

private
let reset_raw (kk: G.erased (Common.index Spec.Blake2B)): Tot _ =
  F.reset blake2b_32 kk (Common.s Spec.Blake2B kk Core.M32) (Common.blake_key Spec.Blake2B kk)

[@ (Comment " General-purpose re-initialization function with parameters and
key. You cannot change digest_length or key_length, meaning those values in
the parameters object must be the same as originally decided via one of the
malloc functions. All other values of the parameter can be changed. The behavior
is unspecified if you violate this precondition.")]
val reset_with_key_and_params: (i: G.erased (Common.index Spec.Blake2B)) -> (
  let open F in
  let c = blake2b_32 in
  let t: Type0 = c.state.s (G.reveal i) in
  let t': Type0 = I.optional_key (G.reveal i) c.km c.key in
  state:state c (G.reveal i) t t' ->
  p:P.params Spec.Blake2B i ->
  k:LowStar.Buffer.buffer Lib.IntTypes.uint8 { LowStar.Buffer.length k == UInt8.v ((G.reveal i).key_length) } -> (
  let key: Common.stateful_key_t Spec.Blake2B (G.reveal i) = (p, k) in
  unit ->
  Stack unit
  (requires (fun h0 ->
    blake2b_32.key.invariant #i h0 key /\
    B.loc_disjoint (blake2b_32.key.footprint #i h0 key) (footprint c i h0 state) /\
    invariant c i h0 state))
  (ensures (fun h0 _ h1 ->
    invariant c i h1 state /\
    seen c i h1 state == S.empty /\
    reveal_key c i h1 state == blake2b_32.key.v i h0 key /\
    footprint c i h0 state == footprint c i h1 state /\
    B.(modifies (footprint c i h0 state) h0 h1) /\
    preserves_freeable c i state h0 h1))))

let reset_with_key_and_params i s p k () =
  let i = index_of_state i s in
  reset_raw i s (p, k)

[@ (Comment " Specialized-purpose re-initialization function with no parameters,
and a key. The key length must be the same as originally decided via your choice
of malloc function. All other parameters are reset to their default values. The
original call to malloc MUST have set digest_length to the default value. The
behavior is unspecified if you violate this precondition.")]
val reset_with_key: (i: G.erased (Common.index Spec.Blake2B)) -> (
  let open F in
  let c = blake2b_32 in
  let i: Common.index Spec.Blake2B = G.reveal i in
  let t: Type0 = c.state.s i in
  let t': Type0 = I.optional_key i c.km c.key in
  state:state c i t t' ->
  k:LowStar.Buffer.buffer Lib.IntTypes.uint8 { LowStar.Buffer.length k == UInt8.v (i.key_length)} -> (
  unit ->
  Stack unit
  (requires (fun h0 ->
//    blake2b_32.key.invariant #i h0 key /\
    (i.key_length <> 0uy ==> B.live h0 k /\ B.loc_disjoint (B.loc_addr_of_buffer k) (footprint c i h0 state)) /\
    invariant c i h0 state))
  (ensures (fun h0 _ h1 ->
    invariant c i h1 state /\
    seen c i h1 state == S.empty /\
    reveal_key blake2b_32 i h1 state ==
      ({ Spec.blake2_default_params Spec.Blake2B with Spec.key_length = (i.key_length); Spec.digest_length = (i.digest_length) },
      (if i.key_length = 0uy then S.empty #uint8 else B.as_seq h0 (k <: B.buffer uint8))) /\
    footprint c i h0 state == footprint c i h1 state /\
    B.(modifies (footprint c i h0 state) h0 h1) /\
    preserves_freeable c i state h0 h1))))

#push-options "--z3rlimit 400"
let reset_with_key (i: G.erased (Common.index Spec.Blake2B)) s k () =
  let hi = ST.get () in
  push_frame();
  let h0 = ST.get () in
  let idx = index_of_state i s in
  let p = P.alloca Spec.Blake2B idx in

  let h1 = ST.get () in

  F.frame_invariant blake2b_32 i (P.footprint h1 p) s hi h1;

  reset_raw idx s (p, k);
  let h2 = ST.get () in

  calc (==) {
    F.reveal_key blake2b_32 idx h2 s;
  (==) { }
    blake2b_32.key.v idx h1 (p, k);
  (==) { }
    Common.key_v idx h1 (p, k);
  (==) { _ by (FStar.Tactics.trefl())  }
    P.v #Spec.Blake2B h1 p, (if idx.key_length = 0uy then S.empty #Lib.IntTypes.uint8 else B.as_seq h1 (k <: B.buffer Lib.IntTypes.uint8));
  (==) { }
    { Spec.blake2_default_params Spec.Blake2B with Spec.key_length = idx.key_length; Spec.digest_length = idx.digest_length }, (if idx.key_length = 0uy then S.empty #Lib.IntTypes.uint8 else B.as_seq h1 (k <: B.buffer Lib.IntTypes.uint8));
  };

  assert (G.reveal i == idx);
  assert (F.reveal_key blake2b_32 i h2 s ==
   ({ Spec.blake2_default_params Spec.Blake2B with Spec.key_length = (G.reveal i).key_length; Spec.digest_length = (G.reveal i).digest_length },
      (if (G.reveal i).key_length = 0uy then S.empty #F.uint8 else B.as_seq h0 (k <: B.buffer F.uint8))));

  // AF: Not strong enough, need to manually reason about push/pop_frame
  assert (F.footprint blake2b_32 i hi s == F.footprint blake2b_32 i h2 s);
  assert (F.preserves_freeable blake2b_32 i s hi h2);

  pop_frame();
  let hf = ST.get() in
  // The modifies below is obtained from B.popped_modifies
  F.frame_invariant blake2b_32 i (B.loc_region_only false (HS.get_tip h2)) s h2 hf;

  B.modifies_fresh_frame_popped hi h0 (F.footprint blake2b_32 (G.reveal i) hi s) h2 hf;
  let h0 = hi in
  let h1 = ST.get () in
  let c = blake2b_32 in
  let i = G.reveal i in
  let s = s in
  let open F in
  assert (invariant c i h1 s);
  assert (seen c i h1 s == S.empty);
  assert (
    reveal_key blake2b_32 i h1 s ==
      ({ Spec.blake2_default_params Spec.Blake2B with Spec.key_length = (i.key_length); Spec.digest_length = (i.digest_length) },
      (if i.key_length = 0uy then S.empty #uint8 else B.as_seq h0 (k <: B.buffer uint8))));
  assert (footprint c i h0 s == footprint c i h1 s);
  assert (preserves_freeable c i s h0 h1);
  assert B.(modifies (footprint c i h0 s) h0 h1)
#pop-options

[@ (Comment " Specialized-purpose re-initialization function with no parameters
and no key. This is what you want if you intend to use Blake2 as a hash
function. The key length and digest length must have been set to their
respective default values via your choice of malloc function (always true if you
used `malloc`). All other parameters are reset to their default values. The
behavior is unspecified if you violate this precondition.")]
val reset: (i: G.erased (Common.index Spec.Blake2B)) -> (
  let open F in
  let c = blake2b_32 in
  let i = G.reveal i in
  let t: Type0 = c.state.s i in
  let t': Type0 = I.optional_key i c.km c.key in
  state:state c i t t' ->
  Stack unit
  (requires (fun h0 ->
    // No invariants required for key or params since there are none, EXCEPT
    // this function may only be called when there is no key.
    i.key_length = 0uy /\
    invariant c i h0 state))
  (ensures (fun h0 _ h1 ->
    invariant c i h1 state /\
    seen c i h1 state == S.empty /\
    reveal_key blake2b_32 i h1 state ==
      ({ Spec.blake2_default_params Spec.Blake2B with Spec.key_length = i.key_length; Spec.digest_length = i.digest_length },
      Seq.empty #Lib.IntTypes.uint8) /\
    footprint c i h0 state == footprint c i h1 state /\
    B.(modifies (footprint c i h0 state) h0 h1) /\
    preserves_freeable c i state h0 h1)))

let reset i s =
  reset_with_key i s B.null ()

[@ (Comment "  Update function; 0 = success, 1 = max length exceeded")]
let update (kk: G.erased (Common.index Spec.Blake2B)): Tot _ =
  F.update blake2b_32 kk (Common.s Spec.Blake2B kk Core.M32) (Common.blake_key Spec.Blake2B kk)

[@ (Comment " Digest function. This function expects the `output` array to hold
at least `digest_length` bytes, where `digest_length` was determined by your
choice of `malloc` function. Concretely, if you used `malloc` or
`malloc_with_key`, then the expected length is 32 for S, or 64 for B (default
digest length). If you used `malloc_with_params_and_key`, then the expected
length is whatever you chose for the `digest_length` field of your
parameters.")]
let digest (kk: G.erased (Common.index Spec.Blake2B)): Tot _ =
  F.digest_erased blake2b_32 kk (Common.s Spec.Blake2B kk Core.M32) (Common.blake_key Spec.Blake2B kk)

[@ (Comment "  Free state function when there is no key")]
let free (kk: G.erased (Common.index Spec.Blake2B)): Tot _ =
  F.free blake2b_32 kk (Common.s Spec.Blake2B kk Core.M32) (Common.blake_key Spec.Blake2B kk)

[@ (Comment "  Copying. This preserves all parameters.")]
let copy (kk: G.erased (Common.index Spec.Blake2B)): Tot _ =
  F.copy blake2b_32 kk (Common.s Spec.Blake2B kk Core.M32) (Common.blake_key Spec.Blake2B kk)

(* The one-shot hash *)
[@@ Comment "Write the BLAKE2b digest of message `input` using key `key` into `output`.

@param output Pointer to `output_len` bytes of memory where the digest is written to.
@param output_len Length of the to-be-generated digest with 1 <= `output_len` <= 64.
@param input Pointer to `input_len` bytes of memory where the input message is read from.
@param input_len Length of the input message.
@param key Pointer to `key_len` bytes of memory where the key is read from.
@param key_len Length of the key. Can be 0."]
let hash_with_key : Impl.blake2_st Spec.Blake2B Core.M32 =
  Impl.blake2 #Spec.Blake2B #Core.M32 Blake2b32.init Blake2b32.update Blake2b32.finish

[@@ Comment "Write the BLAKE2b digest of message `input` using key `key` and
parameters `params` into `output`. The `key` array must be of length
`params.key_length`. The `output` array must be of length
`params.digest_length`. "]
let hash_with_key_and_paramas : Impl.blake2_with_params_st Spec.Blake2B Core.M32 =
  Impl.blake2_with_params #Spec.Blake2B #Core.M32 Blake2b32.init_with_params Blake2b32.update Blake2b32.finish
