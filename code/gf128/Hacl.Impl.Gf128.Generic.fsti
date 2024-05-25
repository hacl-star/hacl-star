module Hacl.Impl.Gf128.Generic

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Gf128.Fields

module S = Spec.GF128


#set-options "--z3rlimit 50 --max_fuel 0"

inline_for_extraction noextract
let gcm_ctx (s:field_spec) = lbuffer (elem_t s) (felem_len s +! precomp_len s)

noextract
val as_get_acc: #s:field_spec -> h:mem -> ctx:gcm_ctx s -> GTot S.elem
noextract
val as_get_r: #s:field_spec -> h:mem -> ctx:gcm_ctx s -> GTot S.elem
noextract
val state_inv_t: #s:field_spec -> h:mem -> ctx:gcm_ctx s -> Type0

inline_for_extraction noextract
let gf128_init_st (s:field_spec) =
    ctx:gcm_ctx s
  -> key:block ->
  Stack unit
  (requires fun h ->
    live h ctx /\ live h key /\ disjoint ctx key)
  (ensures  fun h0 _ h1 ->
    modifies1 ctx h0 h1 /\ state_inv_t h1 ctx /\
    (as_get_acc h1 ctx, as_get_r h1 ctx) == S.gf128_init (as_seq h0 key))


inline_for_extraction noextract
val gf128_init: #s:field_spec -> gf128_init_st s


inline_for_extraction noextract
let gf128_update_st (s:field_spec) =
    ctx:gcm_ctx s
  -> len:size_t
  -> text:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h ctx /\ live h text /\ disjoint ctx text /\
    state_inv_t h ctx)
  (ensures  fun h0 _ h1 ->
    modifies1 ctx h0 h1 /\ state_inv_t h1 ctx /\
    as_get_acc h1 ctx == S.gf128_update (as_seq h0 text) (as_get_acc h0 ctx) (as_get_r h0 ctx))
//as_get_acc h1 ctx == Vec.gf128_update_vec s (as_seq h0 text) (as_get_acc h0 ctx) (as_get_r h0 ctx)


inline_for_extraction noextract
val gf128_update: #s:field_spec -> gf128_update_st s


inline_for_extraction noextract
let gf128_emit_st (s:field_spec) =
  tag:lbuffer uint8 16ul
  -> ctx:gcm_ctx s ->
  Stack unit
  (requires fun h -> live h ctx /\ live h tag /\ disjoint ctx tag)
  (ensures  fun h0 _ h1 -> modifies1 tag h0 h1 /\
    as_seq h1 tag == S.decode (as_get_acc h0 ctx))


inline_for_extraction noextract
val gf128_emit: #s:field_spec -> gf128_emit_st s


inline_for_extraction noextract
let ghash_st (s:field_spec) =
    tag:block
  -> len:size_t
  -> text:lbuffer uint8 len
  -> key:block ->
  Stack unit
  (requires fun h -> live h tag /\ live h text /\ live h key)
  (ensures  fun h0 _ h1 -> modifies1 tag h0 h1 /\
    as_seq h1 tag == S.gmul (as_seq h0 text) (as_seq h0 key))


inline_for_extraction noextract
val ghash: #s:field_spec -> ghash_st s
