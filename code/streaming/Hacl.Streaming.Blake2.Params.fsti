module Hacl.Streaming.Blake2.Params

module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost

open FStar.HyperStack.ST

module Spec = Spec.Blake2
module Core = Hacl.Impl.Blake2.Core

val _align: unit

inline_for_extraction
type index (a: Spec.alg) = {
  key_length: Spec.key_length_t a;
  digest_length: Spec.digest_length_t a;
  last_node: bool;
}

inline_for_extraction noextract
val params (a: Spec.alg) (i: index a): Type0

inline_for_extraction noextract
val footprint (#a: Spec.alg) #i (h: HS.mem) (p: params a i) : GTot B.loc

inline_for_extraction noextract
val freeable (#a: Spec.alg) #i (h: HS.mem) (p: params a i) : GTot prop

inline_for_extraction noextract
val invariant (#a: Spec.alg) #i (h: HS.mem) (p: params a i) : GTot prop

val v (#a: Spec.alg) #i (h: HS.mem) (p: params a i) : GTot (p:Spec.blake2_params a{
  p.key_length == i.key_length /\ p.digest_length == i.digest_length
})

val invariant_loc_in_footprint: #a: Spec.alg -> #i:index a -> h:HS.mem -> s:params a i -> Lemma
    (requires (invariant h s))
    (ensures (B.loc_in (footprint h s) h))
    [ SMTPat (invariant h s) ]

val frame_invariant: #a: Spec.alg -> #i:index a -> l:B.loc -> s: params a i -> h0:HS.mem -> h1:HS.mem -> Lemma
    (requires (
      invariant h0 s /\
      B.loc_disjoint l (footprint h0 s) /\
      B.modifies l h0 h1))
    (ensures (
      invariant h1 s /\
      v h0 s == v h1 s /\
      footprint h1 s == footprint h0 s))
    [ SMTPat (invariant h1 s); SMTPat (B.modifies l h0 h1) ]

val frame_freeable: #a: Spec.alg -> #i:index a -> l:B.loc -> s:params a i -> h0:HS.mem -> h1:HS.mem -> Lemma
    (requires (
      invariant h0 s /\
      freeable h0 s /\
      B.loc_disjoint l (footprint h0 s) /\
      B.modifies l h0 h1))
    (ensures (
      freeable h1 s))
    [ SMTPat (freeable h1 s); SMTPat (B.modifies l h0 h1) ]

inline_for_extraction noextract
val get_params: #a: Spec.alg -> #i:G.erased (index a) -> s: params a i -> ST (p:Core.blake2_params a {
  p.key_length == i.key_length /\ p.digest_length == i.digest_length
  })
  (requires fun h -> invariant h s)
  (ensures fun h0 p h1 ->
    h0 == h1 /\
    Core.blake2_params_inv h1 p /\
    B.(loc_includes (footprint h0 s) (Core.blake2_params_loc p)) /\
    Core.blake2_params_v h1 p == v h1 s)

inline_for_extraction noextract
val alloca: a: Spec.alg -> i:index a -> StackInline (params a i)
  (requires (fun _ -> True))
  (ensures (fun h0 s h1 ->
    invariant h1 s /\
    v h1 s == { Spec.blake2_default_params a with Spec.key_length = i.key_length; Spec.digest_length = i.digest_length } /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true (HS.get_tip h1)) (footprint h1 s))))

inline_for_extraction noextract
val create_in: a: Spec.alg -> i:index a -> r:HS.rid -> ST (params a i)
  (requires (fun h0 ->
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    invariant h1 s /\
    v h1 s == { Spec.blake2_default_params a with Spec.key_length = i.key_length; Spec.digest_length = i.digest_length } /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint h1 s)) /\
    freeable h1 s))

inline_for_extraction noextract
val free: #a: Spec.alg -> #i:G.erased (index a) -> s:params a i -> ST unit
    (requires fun h0 ->
      freeable h0 s /\
      invariant h0 s)
    (ensures fun h0 _ h1 ->
      B.(modifies (footprint h0 s) h0 h1))

inline_for_extraction noextract
val copy: #a:Spec.alg -> #i:G.erased (index a) -> s_src:params a i -> s_dst:params a i ->
    Stack unit
      (requires (fun h0 ->
        invariant h0 s_src /\
        invariant h0 s_dst /\
        B.(loc_disjoint (footprint h0 s_src) (footprint h0 s_dst))))
      (ensures fun h0 _ h1 ->
        B.(modifies (footprint h0 s_dst) h0 h1) /\
        footprint h0 s_dst == footprint h1 s_dst /\
        (freeable h0 s_dst ==> freeable h1 s_dst) /\
        invariant h1 s_dst /\
        v h1 s_dst == v h0 s_src)
