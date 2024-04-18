module Hacl.AES_128.CTR32.NI

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul
open Lib.IntTypes
open Lib.IntVector
open Lib.Buffer
open Hacl.Impl.AES.Core
open Hacl.Impl.AES.Generic
open Hacl.AES.Common

module ST = FStar.HyperStack.ST
module M = LowStar.Modifies
module B = LowStar.Buffer
module LSeq = Lib.Sequence
module Spec = Spec.AES

let aes_ctx = aes_ctx MAES Spec.AES128
let skey = skey Spec.AES128

inline_for_extraction noextract
val state_alloca: unit ->
  StackInline aes_ctx
  (requires (fun h -> True))
  (ensures  (fun h0 f h1 -> live h1 f /\
    stack_allocated f h0 h1 (Seq.create (size_v (ctxlen MAES Spec.AES128))
    (elem_zero MAES))))

inline_for_extraction noextract
let state_alloca () = create_ctx MAES Spec.AES128

inline_for_extraction
val state_malloc:
    r:rid
  -> ST.ST (s:buffer (stelem MAES) { length s = v (ctxlen MAES Spec.AES128) })
  (requires (fun _ ->
    ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    live h1 s /\
    M.(modifies loc_none h0 h1) /\
    B.fresh_loc (loc_addr_of_buffer s) h0 h1 /\
    (M.loc_includes (M.loc_region_only true r) (loc_addr_of_buffer s)) /\
    freeable s))

let state_malloc r =
  assert (v (ctxlen MAES Spec.AES128) == 12);
  B.malloc r (elem_zero MAES) (ctxlen MAES Spec.AES128)

inline_for_extraction
val state_free:
    s:buffer (stelem MAES) { length s = v (ctxlen MAES Spec.AES128) }
  -> ST.ST unit
  (requires fun h0 ->
    freeable s /\ live h0 s)
  (ensures fun h0 _ h1 ->
    M.modifies (loc_addr_of_buffer s) h0 h1)

let state_free s =
  B.free s


[@ CInline ]
val aes128_init:
    ctx: aes_ctx
  -> key: skey
  -> nonce: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key /\ disjoint ctx key /\
    as_seq h ctx == Seq.create (size_v (ctxlen MAES Spec.AES128)) (elem_zero MAES)))
  (ensures  (fun h0 _ h1 -> modifies1 ctx h0 h1 /\
    (let state = Spec.aes_ctr32_init_LE Spec.AES128
      (as_seq h0 key) (as_seq h0 nonce) in
    get_nonce_s MAES Spec.AES128 h1 ctx == state.block /\
    get_kex_s MAES Spec.AES128 h1 ctx == state.key_ex)))

[@ CInline ]
let aes128_init ctx key nonce = aes128_ni_init ctx key nonce


[@ CInline ]
val aes128_set_nonce:
    ctx: aes_ctx
  -> nonce: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h nonce))
  (ensures  (fun h0 _ h1 -> modifies1 ctx h0 h1 /\
    get_nonce_s MAES Spec.AES128 h1 ctx ==
      u8_16_to_le (LSeq.update_sub
      (LSeq.create 16 (u8 0)) 0 12 (as_seq h0 nonce))))

[@ CInline ]
let aes128_set_nonce ctx nonce = aes_set_nonce ctx nonce


inline_for_extraction noextract
val aes128_update4:
    out: lbuffer uint8 64ul
  -> inp: lbuffer uint8 64ul
  -> ctx: aes_ctx
  -> counter: uint32 ->
  Stack unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures  (fun h0 _ h1 -> modifies1 out h0 h1 /\
    as_seq h1 out == Spec.aes_ctr32_encrypt_block_4_LE Spec.AES128
      (get_kex_s MAES Spec.AES128 h0 ctx)
      (get_nonce_s MAES Spec.AES128 h0 ctx)
      counter (as_seq h0 inp)))

let aes128_update4 out inp ctx ctr = aes_update4 out inp ctx ctr

inline_for_extraction noextract
val aes128_ctr:
  len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx
  -> counter: uint32
  -> ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx /\
    disjoint out inp /\ disjoint out ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.aes_ctr32_encrypt_stream_LE Spec.AES128
      (get_kex_s MAES Spec.AES128 h0 ctx)
      (get_nonce_s MAES Spec.AES128 h0 ctx)
      counter (as_seq h0 inp)))

let aes128_ctr len out inp ctx c = aes_ctr #MAES #Spec.AES128 len out inp ctx c


[@ CInline ]
val aes128_ctr_encrypt:
    len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> k:skey
  -> n:lbuffer uint8 12ul
  -> counter:uint32
  -> ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h k /\ live h n /\
    disjoint out inp))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.aes_ctr32_encrypt_bytes_LE Spec.AES128
    (as_seq h0 k) (as_seq h0 n) counter (as_seq h0 inp)))

let aes128_ctr_encrypt len out inp k n c = aes_ctr_encrypt #MAES #Spec.AES128 len out inp k n c


[@ CInline ]
val aes128_ctr_decrypt:
    len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> k:skey
  -> n:lbuffer uint8 12ul
  -> counter:uint32
  -> ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h k /\ live h n /\
    disjoint out inp))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.aes_ctr32_decrypt_bytes_LE Spec.AES128
    (as_seq h0 k) (as_seq h0 n) counter (as_seq h0 inp)))
let aes128_ctr_decrypt len out inp k n c = aes_ctr_decrypt #MAES #Spec.AES128 len out inp k n c

