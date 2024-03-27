module Hacl.Streaming.Blake2b_32

module Blake2b32 = Hacl.Blake2b_32
module Common = Hacl.Streaming.Blake2.Common
module Params = Hacl.Streaming.Blake2.Params
module Core = Hacl.Impl.Blake2.Core
module F = Hacl.Streaming.Functor
module B = LowStar.Buffer
module I = Hacl.Streaming.Interface
module G = FStar.Ghost
module Impl = Hacl.Impl.Blake2.Generic
module Spec = Spec.Blake2
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.HyperStack.ST

inline_for_extraction noextract
let blake2b_32 kk =
  Common.blake2 Spec.Blake2B Core.M32 false kk Blake2b32.init Blake2b32.update_multi
         Blake2b32.update_last Blake2b32.finish

inline_for_extraction noextract
let blake2b_32_params kk =
  Common.blake2 Spec.Blake2B Core.M32 true kk Blake2b32.init_with_params Blake2b32.update_multi
         Blake2b32.update_last Blake2b32.finish

/// Type abbreviations - makes Karamel use pretty names in the generated code

let block_state_t = Common.s Spec.Blake2B Core.M32
let state_t = F.state_s (blake2b_32 0) () (Common.s Spec.Blake2B Core.M32) (Common.empty_key Spec.Blake2B)

/// The incremental hash functions instantiations. Note that we can't write a
/// generic one, because the normalization then performed by KaRaMeL explodes.

inline_for_extraction noextract
let key_t kk =
  let c = blake2b_32 kk in
  I.optional_key () c.km c.key

inline_for_extraction noextract
[@ (Comment "  State stack allocation function with key, no parameters")]
let alloca (kk: Common.key_size_t Spec.Blake2B) =
  F.alloca (blake2b_32 (UInt32.v kk)) () (Common.s Spec.Blake2B Core.M32) (key_t (UInt32.v kk))

// Copy of what's in Hacl.Streaming.Functor.fsti
inline_for_extraction noextract
let malloc_st_1
  (#index: Type0)
  (c:I.block index)
  (i:index)
  (t:Type0 { t == c.state.s i })
  (t':Type0 { t' == I.optional_key i c.km c.key })
  (key_length_t: Type0)
=
  k:c.key.s i ->
  key_length: key_length_t ->
  r: HS.rid ->
  ST (F.state c i t t')
  (requires (fun h0 ->
    c.key.invariant #i h0 k /\
    is_eternal_region r))
  (ensures (fun h0 s h1 ->
    let open F in
    invariant c i h1 s /\
    freeable c i h1 s /\
    seen c i h1 s == Seq.empty /\
    reveal_key c i h1 s == c.key.v i h0 k /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint c i h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint c i h1 s))))

let key_b = Common.key_size_t Spec.Blake2B

inline_for_extraction noextract
let cast (k: G.erased (Common.key_size Spec.Blake2B)) (k': G.erased (Common.key_size Spec.Blake2B) { k == k' })
  (s: F.state (blake2b_32 k) () (Common.s Spec.Blake2B Core.M32) (key_t k)):
  F.state (blake2b_32 k') () (Common.s Spec.Blake2B Core.M32) (key_t k')
=
  s

#push-options "--fuel 0 --ifuel 0"
[@ (Comment "  State allocation function with key, no parameters")]
let malloc_with_key (kkg: Ghost.erased key_b):
  malloc_st_1
    (blake2b_32 (UInt32.v kkg)) () (Common.s Spec.Blake2B Core.M32) (key_t (UInt32.v kkg))
    (kk: key_b { kk == Ghost.reveal kkg })
=
  fun k kk r ->
  assert (G.hide (UInt32.v kk) == G.hide (UInt32.v kkg));
  let uu__ = F.malloc (blake2b_32 (UInt32.v kk)) () (Common.s Spec.Blake2B Core.M32) (key_t (UInt32.v kk)) k r in
  // WHYYYYYYYYYY
  cast (G.hide (UInt32.v kk)) (G.hide (UInt32.v kkg)) uu__

[@ (Comment "  State allocation function with no key, no parameters")]
let malloc (r: FStar.Monotonic.HyperHeap.rid { is_eternal_region r }) =
  malloc_with_key (G.hide 0ul) ((), ()) 0ul r

[@ (Comment "  State allocation function when there are parameters but no key")]
private
let malloc_general (kk: Common.key_size_t Spec.Blake2B) =
  F.malloc (blake2b_32_params (UInt32.v kk)) () (Common.s Spec.Blake2B Core.M32) (key_t (UInt32.v kk))

inline_for_extraction noextract
let to_keyb (x: Lib.IntTypes.uint8 { Lib.IntTypes.v x <= Spec.(max_key Blake2B) }): key_b =
  // TODO: need to reveal
  admit ();
  Lib.IntTypes.to_u32 x

// Copy of what's in Hacl.Streaming.Functor.fsti
inline_for_extraction noextract
let malloc_st_2
  (#index: Type0)
  (c:I.block index)
  (i:index)
  (t:Type0 { t == c.state.s i })
  (t':Type0 { t' == I.optional_key i c.km c.key })
  (k:c.key.s i)
  (extra_precondition: HS.mem -> Type0)
=
  r: HS.rid ->
  ST (F.state c i t t')
  (requires (fun h0 ->
    extra_precondition h0 /\
    c.key.invariant #i h0 k /\
    is_eternal_region r))
  (ensures (fun h0 s h1 ->
    let open F in
    invariant c i h1 s /\
    freeable c i h1 s /\
    seen c i h1 s == Seq.empty /\
    reveal_key c i h1 s == c.key.v i h0 k /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint c i h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint c i h1 s))))

inline_for_extraction noextract
let cast_params (k: G.erased (Common.key_size Spec.Blake2B)) (k': G.erased (Common.key_size Spec.Blake2B) { k == k' })
  (s: F.state (blake2b_32_params k) () (Common.s Spec.Blake2B Core.M32) (key_t k)):
  F.state (blake2b_32_params k') () (Common.s Spec.Blake2B Core.M32) (key_t k')
=
  s

[@ (Comment "  State allocation function when there are parameters and a key. If you care about parameters but not the key, pass in NULL for the key, and set params.key_length=0")]
let malloc_with_key_and_params
  (g_key_size: Ghost.erased (Common.key_size_t Spec.Blake2B) { G.reveal g_key_size <> 0ul })
  (g_key: Ghost.erased (Params.params Spec.Blake2B & b:B.buffer Lib.IntTypes.uint8 { B.len b == G.reveal g_key_size }))
  (p: Params.params Spec.Blake2B)
  (k: B.buffer Lib.IntTypes.uint8 { B.len k == G.reveal g_key_size }):
  malloc_st_2
    (blake2b_32_params (UInt32.v g_key_size)) () (Common.s Spec.Blake2B Core.M32) (key_t (UInt32.v g_key_size))
    (p, k)
    (fun h0 ->
      G.reveal g_key_size <> 0ul /\
      Params.invariant h0 p /\
      to_keyb (Params.v h0 p).key_length == Ghost.reveal g_key_size)
= fun r ->
  let pv = Params.get_params p in
  let kl = to_keyb pv.Core.key_length in
  if kl = 0ul then
    B.null
  else begin
    assert (UInt32.v kl <> 0);
    assert (B.length k == UInt32.v kl);
    let uu__ = malloc_general kl (p, k) r in
    cast_params (G.hide (UInt32.v kl)) (G.hide (UInt32.v g_key_size)) uu__
  end

[@ (Comment "  Re-initialization function when there is no key")]
let reset =
  F.reset (blake2b_32 0) () (Common.s Spec.Blake2B Core.M32) (Common.empty_key Spec.Blake2B)

[@ (Comment "  Re-initialization function when there are parameters but no key")]
let reset_with_params =
  F.reset (blake2b_32_params 0) () (Common.s Spec.Blake2B Core.M32) (Common.empty_key Spec.Blake2B)

[@ (Comment "  Update function when there is no key; 0 = success, 1 = max length exceeded")]
let update =
  F.update (blake2b_32 0) (G.hide ()) (Common.s Spec.Blake2B Core.M32) (Common.empty_key Spec.Blake2B)

[@ (Comment "  Finish function when there is no key")]
let digest =
  F.digest (blake2b_32 0) () (Common.s Spec.Blake2B Core.M32) (Common.empty_key Spec.Blake2B)

[@ (Comment "  Free state function when there is no key")]
let free =
  F.free (blake2b_32 0) (G.hide ()) (Common.s Spec.Blake2B Core.M32) (Common.empty_key Spec.Blake2B)

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
