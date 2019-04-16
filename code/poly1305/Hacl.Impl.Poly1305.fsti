module Hacl.Impl.Poly1305

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Poly1305.Fields
module S = Hacl.Spec.Poly1305.Vec
module F32xN = Hacl.Impl.Poly1305.Field32xN

#reset-options "--z3rlimit 50"

inline_for_extraction noextract
let poly1305_ctx (s:field_spec) = lbuffer (limb s) (nlimb s +. precomplen s)

noextract
val as_get_acc: #s:field_spec -> h:mem -> ctx:poly1305_ctx s -> GTot (S.elem (width s))
noextract
val as_get_r: #s:field_spec -> h:mem -> ctx:poly1305_ctx s -> GTot (S.elem (width s))
noextract
val state_inv_t: #s:field_spec -> h:mem -> ctx:poly1305_ctx s -> Type0

// If the ctx is not modified, all the components and invariants are preserved
val reveal_ctx_inv: #s:field_spec -> ctx:poly1305_ctx s -> h0:mem -> h1:mem ->
  Lemma
    (requires Seq.equal (as_seq h0 ctx) (as_seq h1 ctx) /\ state_inv_t h0 ctx)
    (ensures 
      as_get_r h0 ctx == as_get_r h1 ctx /\
      as_get_acc h0 ctx == as_get_acc h1 ctx /\
      state_inv_t h1 ctx
    )

inline_for_extraction noextract
let poly1305_init_st (s: field_spec) =
    ctx:poly1305_ctx s
  -> key:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h ->
      live h ctx /\ live h key /\ disjoint ctx key)
    (ensures  fun h0 _ h1 ->
      modifies (loc ctx) h0 h1 /\
      state_inv_t #s h1 ctx /\
      (as_get_acc h1 ctx, as_get_r h1 ctx) == S.poly1305_init (as_seq h0 key))

inline_for_extraction noextract
val mk_poly1305_init: #s:field_spec -> poly1305_init_st s

inline_for_extraction noextract
let poly1305_update_st (s: field_spec) =
    ctx:poly1305_ctx s
  -> len:size_t
  -> text:lbuffer uint8 len
  -> Stack unit
    (requires fun h ->
      live h text /\ live h ctx /\ disjoint ctx text /\
      state_inv_t #s h ctx)
    (ensures  fun h0 _ h1 ->
      modifies (loc ctx) h0 h1 /\
      state_inv_t #s h1 ctx /\
      as_get_r h0 ctx == as_get_r h1 ctx /\
      Lib.Sequence.index (as_get_acc h1 ctx) 0 ==
      S.poly_update #(width s) (as_seq h0 text) (as_get_acc h0 ctx) (as_get_r h0 ctx))

inline_for_extraction noextract
val mk_poly1305_update: #s:field_spec -> poly1305_update_st s

inline_for_extraction noextract
let poly1305_finish_st (s: field_spec) =
    tag:lbuffer uint8 16ul
  -> key:lbuffer uint8 32ul
  -> ctx:poly1305_ctx s
  -> Stack unit
    (requires fun h ->
      live h tag /\ live h key /\ live h ctx /\
      disjoint tag key /\ disjoint tag ctx /\ disjoint key ctx /\
      state_inv_t #s h ctx)
    (ensures  fun h0 _ h1 ->
      modifies (loc tag |+| loc ctx) h0 h1 /\
      as_seq h1 tag == S.finish (as_seq h0 key) (Lib.Sequence.index (as_get_acc h0 ctx) 0))

inline_for_extraction noextract
val mk_poly1305_finish: #s:field_spec -> poly1305_finish_st s

inline_for_extraction noextract
let poly1305_mac_st (s: field_spec) =
    tag:lbuffer uint8 16ul
  -> len:size_t
  -> text:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h ->
      live h text /\ live h tag /\ live h key /\
      disjoint tag text /\ disjoint tag key)
    (ensures  fun h0 _ h1 ->
      modifies (loc tag) h0 h1 /\
      as_seq h1 tag == S.poly1305 #(width s) (as_seq h0 text) (as_seq h0 key))

inline_for_extraction noextract
val mk_poly1305_mac: #s:field_spec ->
  init:poly1305_init_st s ->
  update:poly1305_update_st s ->
  finish:poly1305_finish_st s ->
  poly1305_mac_st s
