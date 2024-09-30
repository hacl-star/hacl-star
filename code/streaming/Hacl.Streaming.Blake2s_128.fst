module Hacl.Streaming.Blake2s_128

// Blake2s_128 is hand-written, other files generated with:
// sed 's/2S/2S/g;s/2s/2s/g;' Hacl.Streaming.Blake2s_128.fst > Hacl.Streaming.Blake2s_128.fst; sed 's/128/128/g' Hacl.Streaming.Blake2s_128.fst > Hacl.Streaming.Blake2s_128.fst; sed 's/128/256/g' Hacl.Streaming.Blake2s_128.fst > Hacl.Streaming.Blake2s_256.fst

module HS = FStar.HyperStack
module Blake2s128 = Hacl.Blake2s_128
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

[@ CMacro ] let block_bytes = Lib.IntTypes.size (Spec.Blake2.Definitions.size_block Spec.Blake2S)
[@ CMacro ] let out_bytes = Lib.IntTypes.size (Spec.Blake2.Definitions.max_output Spec.Blake2S)
[@ CMacro ] let key_bytes = Lib.IntTypes.size (Spec.Blake2.Definitions.max_key Spec.Blake2S)
[@ CMacro ] let salt_bytes = Lib.IntTypes.size (Spec.Blake2.Definitions.salt_length Spec.Blake2S)
[@ CMacro ] let personal_bytes = Lib.IntTypes.size (Spec.Blake2.Definitions.personal_length Spec.Blake2S)

inline_for_extraction noextract
let blake2s_128 =
  Common.blake2 Spec.Blake2S Core.M128 Blake2s128.init_with_params Blake2s128.update_multi
         Blake2s128.update_last Blake2s128.finish

/// Type abbreviations - makes Karamel use pretty names in the generated code
let block_state_t (kk: G.erased (Common.index Spec.Blake2S)) = Common.s Spec.Blake2S kk Core.M128

let state_t (kk: G.erased (Common.index Spec.Blake2S)) =
  F.state_s blake2s_128 kk (Common.s Spec.Blake2S kk Core.M128) (Common.blake_key Spec.Blake2S kk)

/// The incremental hash functions instantiations. Note that we can't write a
/// generic one, because the normalization then performed by KaRaMeL explodes.

/// All those implementations are for non-keyed hash.

inline_for_extraction noextract
[@ (Comment "  State allocation function when there is no key")]
let alloca_raw (kk: Common.index Spec.Blake2S): Tot _ =
  F.alloca blake2s_128 kk (Common.s Spec.Blake2S kk Core.M128) (Common.blake_key Spec.Blake2S kk)

private
let malloc_raw (kk: Common.index Spec.Blake2S): Tot _ =
  F.malloc blake2s_128 kk (Common.s Spec.Blake2S kk Core.M128) (Common.blake_key Spec.Blake2S kk)

[@ (Comment " General-purpose allocation function that gives control over all
Blake2 parameters, including the key. Further resettings of the state SHALL be
done with `reset_with_params_and_key`, and SHALL feature the exact same values
for the `key_length` and `digest_length` fields as passed here. In other words,
once you commit to a digest and key length, the only way to change these
parameters is to allocate a new object.

The caller must satisfy the following requirements.
- The length of the key k MUST match the value of the field key_length in the
  parameters.
- The key_length must not exceed 128 for S, 64 for B.
- The digest_length must not exceed 128 for S, 64 for B.
")]
val malloc_with_params_and_key:
  i:G.erased (P.index Spec.Blake2S) ->
  p:P.params Spec.Blake2S i ->
  last_node:bool{last_node = i.P.last_node} ->
  k:LowStar.Buffer.buffer Lib.IntTypes.uint8 { LowStar.Buffer.length k == UInt8.v ((G.reveal i).key_length) } -> (
  let open F in
  let c = blake2s_128 in
  let t: Type0 = c.state.s i in
  let t': Type0 = I.optional_key (G.reveal i) c.km c.key in
  let k: Common.params_and_key Spec.Blake2S (G.reveal i) = p, k in
  r: HS.rid ->
  ST (state c i t t')
  (requires (fun h0 ->
    blake2s_128.key.invariant #i h0 k /\
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    invariant c i h1 s /\
    freeable c i h1 s /\
    seen c i h1 s == S.empty /\
    reveal_key blake2s_128 i h1 s == blake2s_128.key.v i h0 k /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint c i h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint c i h1 s))))
)

let malloc_with_params_and_key i p last_node k r =
  let pv = P.get_params p in
  let i = { P.key_length = pv.Core.key_length; digest_length = pv.Core.digest_length; last_node } in
  malloc_raw i (p, k) r

[@ (Comment " Specialized allocation function that picks default values for all
parameters, except for the key_length. Further resettings of the state SHALL be
done with `reset_with_key`, and SHALL feature the exact same key length `kk` as
passed here. In other words, once you commit to a key length, the only way to
change this parameter is to allocate a new object.

The caller must satisfy the following requirements.
- The key_length must not exceed 128 for S, 64 for B.
")]
val malloc_with_key:
  k:LowStar.Buffer.buffer Lib.IntTypes.uint8 ->
  kk:Spec.key_length_t Spec.Blake2S { LowStar.Buffer.length k == UInt8.v kk } -> (
  let open F in
  let c = blake2s_128 in
  let i: Common.index Spec.Blake2S = { P.key_length = kk; digest_length = UInt8.uint_to_t (Spec.max_output Spec.Blake2S); last_node = false } in
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
    reveal_key blake2s_128 i h1 s ==
      ({ Spec.blake2_default_params Spec.Blake2S with Spec.key_length = kk },
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
  let nn = UInt8.uint_to_t (Spec.max_output Spec.Blake2S) in
  let i: Common.index Spec.Blake2S = { key_length = kk; digest_length = nn; last_node = false } in
  let h00 = ST.get () in

  let p = P.alloca Spec.Blake2S i in
  let h0 = ST.get () in
  assert B.(as_seq h00 k == as_seq h0 k);

  let s = malloc_with_params_and_key (G.hide i) p false k r in
  let h1 = ST.get () in
  assert F.(freeable blake2s_128 i h1 s);
  assert (nn == (Spec.blake2_default_params Spec.Blake2S).digest_length);
  calc (==) {
    F.reveal_key blake2s_128 i h1 s;
  (==) { }
    blake2s_128.key.v i h0 (p, k);
  (==) { }
    Common.key_v i h0 (p, k);
  (==) { _ by (FStar.Tactics.trefl ()) }
    P.v #Spec.Blake2S h0 p, (if i.key_length = 0uy then S.empty #Lib.IntTypes.uint8 else B.as_seq h0 (k <: B.buffer Lib.IntTypes.uint8));
  (==) { }
    { Spec.blake2_default_params Spec.Blake2S with Spec.key_length = kk; Spec.digest_length = nn }, (if i.key_length = 0uy then S.empty #Lib.IntTypes.uint8 else B.as_seq h0 (k <: B.buffer Lib.IntTypes.uint8));
  (==) { }
    { Spec.blake2_default_params Spec.Blake2S with Spec.key_length = kk }, (if i.key_length = 0uy then S.empty #Lib.IntTypes.uint8 else B.as_seq h0 (k <: B.buffer Lib.IntTypes.uint8));
  };
  pop_frame ();
  let hf = ST.get () in
  F.frame_invariant blake2s_128 i (B.loc_region_only false (HS.get_tip h1)) s h1 hf;
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
let index_of_state (kk: G.erased (Common.index Spec.Blake2S)): Tot _ =
  F.index_of_state blake2s_128 kk (Common.s Spec.Blake2S kk Core.M128) (Common.blake_key Spec.Blake2S kk)

private
let reset_raw (kk: G.erased (Common.index Spec.Blake2S)): Tot _ =
  F.reset blake2s_128 kk (Common.s Spec.Blake2S kk Core.M128) (Common.blake_key Spec.Blake2S kk)

[@ (Comment " General-purpose re-initialization function with parameters and
key. You cannot change digest_length, key_length, or last_node, meaning those values in
the parameters object must be the same as originally decided via one of the
malloc functions. All other values of the parameter can be changed. The behavior
is unspecified if you violate this precondition.")]
val reset_with_key_and_params: (i: G.erased (Common.index Spec.Blake2S)) -> (
  let open F in
  let c = blake2s_128 in
  let t: Type0 = c.state.s (G.reveal i) in
  let t': Type0 = I.optional_key (G.reveal i) c.km c.key in
  state:state c (G.reveal i) t t' ->
  p:P.params Spec.Blake2S i ->
  k:LowStar.Buffer.buffer Lib.IntTypes.uint8 { LowStar.Buffer.length k == UInt8.v ((G.reveal i).key_length) } -> (
  let key: Common.params_and_key Spec.Blake2S (G.reveal i) = (p, k) in
  unit ->
  Stack unit
  (requires (fun h0 ->
    blake2s_128.key.invariant #i h0 key /\
    B.loc_disjoint (blake2s_128.key.footprint #i h0 key) (footprint c i h0 state) /\
    invariant c i h0 state))
  (ensures (fun h0 _ h1 ->
    invariant c i h1 state /\
    seen c i h1 state == S.empty /\
    reveal_key c i h1 state == blake2s_128.key.v i h0 key /\
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
val reset_with_key: (i: G.erased (Common.index Spec.Blake2S)) -> (
  let open F in
  let c = blake2s_128 in
  let i: Common.index Spec.Blake2S = G.reveal i in
  let t: Type0 = c.state.s i in
  let t': Type0 = I.optional_key i c.km c.key in
  state:state c i t t' ->
  k:LowStar.Buffer.buffer Lib.IntTypes.uint8 { LowStar.Buffer.length k == UInt8.v (i.key_length)} -> (
  unit ->
  Stack unit
  (requires (fun h0 ->
//    blake2s_128.key.invariant #i h0 key /\
    (i.key_length <> 0uy ==> B.live h0 k /\ B.loc_disjoint (B.loc_addr_of_buffer k) (footprint c i h0 state)) /\
    invariant c i h0 state))
  (ensures (fun h0 _ h1 ->
    invariant c i h1 state /\
    seen c i h1 state == S.empty /\
    reveal_key blake2s_128 i h1 state ==
      ({ Spec.blake2_default_params Spec.Blake2S with Spec.key_length = (i.key_length); Spec.digest_length = (i.digest_length) },
      (if i.key_length = 0uy then S.empty #uint8 else B.as_seq h0 (k <: B.buffer uint8))) /\
    footprint c i h0 state == footprint c i h1 state /\
    B.(modifies (footprint c i h0 state) h0 h1) /\
    preserves_freeable c i state h0 h1))))

#push-options "--z3rlimit 400"
let reset_with_key (i: G.erased (Common.index Spec.Blake2S)) s k () =
  let hi = ST.get () in
  push_frame();
  let h0 = ST.get () in
  let idx = index_of_state i s in
  let p = P.alloca Spec.Blake2S idx in

  let h1 = ST.get () in

  F.frame_invariant blake2s_128 i (P.footprint h1 p) s hi h1;

  reset_raw idx s (p, k);
  let h2 = ST.get () in

  calc (==) {
    F.reveal_key blake2s_128 idx h2 s;
  (==) { }
    blake2s_128.key.v idx h1 (p, k);
  (==) { }
    Common.key_v idx h1 (p, k);
  (==) { _ by (FStar.Tactics.trefl())  }
    P.v #Spec.Blake2S h1 p, (if idx.key_length = 0uy then S.empty #Lib.IntTypes.uint8 else B.as_seq h1 (k <: B.buffer Lib.IntTypes.uint8));
  (==) { }
    { Spec.blake2_default_params Spec.Blake2S with Spec.key_length = idx.key_length; Spec.digest_length = idx.digest_length }, (if idx.key_length = 0uy then S.empty #Lib.IntTypes.uint8 else B.as_seq h1 (k <: B.buffer Lib.IntTypes.uint8));
  };

  assert (G.reveal i == idx);
  assert (F.reveal_key blake2s_128 i h2 s ==
   ({ Spec.blake2_default_params Spec.Blake2S with Spec.key_length = (G.reveal i).key_length; Spec.digest_length = (G.reveal i).digest_length },
      (if (G.reveal i).key_length = 0uy then S.empty #F.uint8 else B.as_seq h0 (k <: B.buffer F.uint8))));

  // AF: Not strong enough, need to manually reason about push/pop_frame
  assert (F.footprint blake2s_128 i hi s == F.footprint blake2s_128 i h2 s);
  assert (F.preserves_freeable blake2s_128 i s hi h2);

  pop_frame();
  let hf = ST.get() in
  // The modifies below is obtained from B.popped_modifies
  F.frame_invariant blake2s_128 i (B.loc_region_only false (HS.get_tip h2)) s h2 hf;

  B.modifies_fresh_frame_popped hi h0 (F.footprint blake2s_128 (G.reveal i) hi s) h2 hf;
  let h0 = hi in
  let h1 = ST.get () in
  let c = blake2s_128 in
  let i = G.reveal i in
  let s = s in
  let open F in
  assert (invariant c i h1 s);
  assert (seen c i h1 s == S.empty);
  assert (
    reveal_key blake2s_128 i h1 s ==
      ({ Spec.blake2_default_params Spec.Blake2S with Spec.key_length = (i.key_length); Spec.digest_length = (i.digest_length) },
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
val reset: (i: G.erased (Common.index Spec.Blake2S)) -> (
  let open F in
  let c = blake2s_128 in
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
    reveal_key blake2s_128 i h1 state ==
      ({ Spec.blake2_default_params Spec.Blake2S with Spec.key_length = i.key_length; Spec.digest_length = i.digest_length },
      Seq.empty #Lib.IntTypes.uint8) /\
    footprint c i h0 state == footprint c i h1 state /\
    B.(modifies (footprint c i h0 state) h0 h1) /\
    preserves_freeable c i state h0 h1)))

let reset i s =
  reset_with_key i s B.null ()

[@ (Comment "  Update function; 0 = success, 1 = max length exceeded")]
let update (kk: G.erased (Common.index Spec.Blake2S)): Tot _ =
  F.update blake2s_128 kk (Common.s Spec.Blake2S kk Core.M128) (Common.blake_key Spec.Blake2S kk)

[@ (Comment " Digest function. This function expects the `output` array to hold
at least `digest_length` bytes, where `digest_length` was determined by your
choice of `malloc` function. Concretely, if you used `malloc` or
`malloc_with_key`, then the expected length is 128 for S, or 64 for B (default
digest length). If you used `malloc_with_params_and_key`, then the expected
length is whatever you chose for the `digest_length` field of your parameters.
For convenience, this function returns `digest_length`. When in doubt, callers
can pass an array of size HACL_BLAKE2S_128_OUT_BYTES, then use the return value
to see how many bytes were actually written. ")]
val digest: (i: G.erased (Common.index Spec.Blake2S)) -> (
  let open F in
  let c = blake2s_128 in
  let i = G.reveal i in
  let t: Type0 = c.state.s i in
  let t': Type0 = I.optional_key i c.km c.key in
  s:state c i t t' ->
  dst:B.buffer uint8 ->
  l:c.output_length_t { B.length dst == c.output_length i l } ->
  Stack UInt8.t
    (requires fun h0 ->
      invariant c i h0 s /\
      B.live h0 dst /\
      B.(loc_disjoint (loc_buffer dst) (footprint c i h0 s)))
    (ensures fun h0 s' h1 ->
      s' == i.digest_length /\
      invariant c i h1 s /\
      seen c i h0 s == seen c i h1 s /\
      reveal_key c i h1 s == reveal_key c i h0 s /\
      footprint c i h0 s == footprint c i h1 s /\
      B.(modifies (loc_union (loc_buffer dst) (footprint c i h0 s)) h0 h1) /\ (
      seen_bounded c i h0 s;
      S.equal (B.as_seq h1 dst) (c.spec_s i (reveal_key c i h0 s) (seen c i h0 s) l)) /\
      preserves_freeable c i s h0 h1)
)
let digest (i: G.erased (Common.index Spec.Blake2S)) s dst l =
  F.digest_erased blake2s_128 i (Common.s Spec.Blake2S i Core.M128) (Common.blake_key Spec.Blake2S i) s dst l;
  (F.index_of_state blake2s_128 i (Common.s Spec.Blake2S i Core.M128) (Common.blake_key Spec.Blake2S i) s).digest_length

let info (i: G.erased (Common.index Spec.Blake2S)): Tot _ =
  F.index_of_state blake2s_128 i (Common.s Spec.Blake2S i Core.M128) (Common.blake_key Spec.Blake2S i)

[@ (Comment "  Free state function when there is no key")]
let free (kk: G.erased (Common.index Spec.Blake2S)): Tot _ =
  F.free blake2s_128 kk (Common.s Spec.Blake2S kk Core.M128) (Common.blake_key Spec.Blake2S kk)

[@ (Comment "  Copying. This preserves all parameters.")]
let copy (kk: G.erased (Common.index Spec.Blake2S)): Tot _ =
  F.copy blake2s_128 kk (Common.s Spec.Blake2S kk Core.M128) (Common.blake_key Spec.Blake2S kk)

(* The one-shot hash *)
[@@ Comment "Write the BLAKE2s digest of message `input` using key `key` into `output`.

@param output Pointer to `output_len` bytes of memory where the digest is written to.
@param output_len Length of the to-be-generated digest with 1 <= `output_len` <= 64.
@param input Pointer to `input_len` bytes of memory where the input message is read from.
@param input_len Length of the input message.
@param key Pointer to `key_len` bytes of memory where the key is read from.
@param key_len Length of the key. Can be 0."]
let hash_with_key : Impl.blake2_st Spec.Blake2S Core.M128 =
  Impl.blake2 #Spec.Blake2S #Core.M128 Blake2s128.init Blake2s128.update Blake2s128.finish

[@@ Comment "Write the BLAKE2s digest of message `input` using key `key` and
parameters `params` into `output`. The `key` array must be of length
`params.key_length`. The `output` array must be of length
`params.digest_length`. "]
let hash_with_key_and_params : Impl.blake2_with_params_st Spec.Blake2S Core.M128 =
  Impl.blake2_with_params #Spec.Blake2S #Core.M128 Blake2s128.init_with_params Blake2s128.update Blake2s128.finish
