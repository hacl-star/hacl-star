module Hacl.AES_256.CTR32.BitSlice

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul
open Lib.IntTypes
open Lib.Buffer
open Hacl.Impl.AES.Core
open Hacl.Impl.AES.Generic
open Hacl.AES.Common

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module Spec = Spec.AES

let aes_ctx = aes_ctx M32 Spec.AES256
let skey = skey Spec.AES256

[@ CInline ]
val create_ctx: unit ->
  StackInline aes_ctx
  (requires (fun h -> True))
  (ensures  (fun h0 f h1 -> live h1 f /\
    stack_allocated f h0 h1 (Seq.create (size_v (ctxlen M32 Spec.AES256))
    (elem_zero M32))))

[@ CInline ]
let create_ctx () = create_ctx M32 Spec.AES256


[@ CInline ]
val aes256_init:
    ctx: aes_ctx
  -> key: skey
  -> nonce: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key /\ disjoint ctx key /\
    as_seq h ctx == Seq.create (size_v (ctxlen M32 Spec.AES256)) (elem_zero M32)))
  (ensures  (fun h0 _ h1 -> modifies1 ctx h0 h1 /\
    (let n = LSeq.sub (as_seq h1 ctx) 0 (v (nlen M32)) in
    let kex = LSeq.sub (as_seq h1 ctx)
      (v (nlen M32)) ((Spec.num_rounds Spec.AES256+1) * v (klen M32)) in
    let state = Spec.aes_ctr32_init_LE Spec.AES256
      (as_seq h0 key) (as_seq h0 nonce) in
    nonce_to_bytes M32 n == state.block /\
    keyx_to_bytes M32 Spec.AES256 kex == state.key_ex)))

[@ CInline ]
let aes256_init ctx key nonce = aes256_bitslice_init ctx key nonce

[@ CInline ]
inline_for_extraction noextract
val aes256_encrypt_block:
    ob: lbuffer uint8 16ul
  -> ctx: aes_ctx 
  -> ib: lbuffer uint8 16ul ->
  ST unit
  (requires (fun h -> live h ob /\ live h ctx /\ live h ib))
  (ensures (fun h0 _ h1 -> modifies (loc ob) h0 h1 /\
    (let k = LSeq.sub (as_seq h0 ctx) (v (nlen M32))
      ((Spec.num_rounds Spec.AES256+1) * v (klen M32)) in
    as_seq h1 ob == u8_16_to_le (Spec.aes_encrypt_block Spec.AES256
      (keyx_to_bytes M32 Spec.AES256 k) (u8_16_to_le (as_seq h0 ib))))))

let aes256_encrypt_block ob ctx ib =
    aes_encrypt_block #M32 #Spec.AES256 ob ctx ib

[@ CInline ]
val aes256_set_nonce:
    ctx: aes_ctx
  -> nonce: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h nonce))
  (ensures  (fun h0 _ h1 -> modifies1 ctx h0 h1 /\
    nonce_to_bytes M32 (LSeq.sub (as_seq h1 ctx) 0 (v (nlen M32))) ==
      u8_16_to_le (LSeq.update_sub
      (LSeq.create 16 (u8 0)) 0 12 (as_seq h0 nonce))))

[@ CInline ]
let aes256_set_nonce ctx nonce = aes_set_nonce ctx nonce


[@ CInline ]
val aes256_key_block:
    kb: lbuffer uint8 16ul
  -> ctx:aes_ctx
  -> counter:uint32 ->
  Stack unit
  (requires (fun h -> live h kb /\ live h ctx))
  (ensures  (fun h0 _ h1 -> modifies1 kb h0 h1 /\
    (let k = LSeq.sub (as_seq h0 ctx) (v (nlen M32))
      ((Spec.num_rounds Spec.AES256+1) * v (klen M32)) in
    let n = LSeq.sub (as_seq h0 ctx) 0 (v (nlen M32)) in
    as_seq h1 kb == u8_16_to_le (Spec.aes_encrypt_block Spec.AES256
      (keyx_to_bytes M32 Spec.AES256 k) (Spec.aes_ctr32_set_counter_LE
      (nonce_to_bytes M32 n) counter)))))

[@ CInline ]
let aes256_key_block kb ctx counter = aes_key_block #M32 #Spec.AES256 kb ctx counter


inline_for_extraction noextract
val aes256_update4:
    out: lbuffer uint8 64ul
  -> inp: lbuffer uint8 64ul
  -> ctx: aes_ctx
  -> counter: uint32 ->
  Stack unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures  (fun h0 _ h1 -> modifies1 out h0 h1 /\
    (let k = LSeq.sub (as_seq h0 ctx) (v (nlen M32))
      ((Spec.num_rounds Spec.AES256+1) * v (klen M32)) in
    let n = LSeq.sub (as_seq h0 ctx) 0 (v (nlen M32)) in
    as_seq h1 out == Spec.aes_ctr32_encrypt_block_4_LE Spec.AES256
      (keyx_to_bytes M32 Spec.AES256 k) (nonce_to_bytes M32 n)
      counter (as_seq h0 inp))))

let aes256_update4 out inp ctx ctr = aes_update4 out inp ctx ctr


[@ CInline ]
val aes256_ctr:
  len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx
  -> counter: uint32
  -> ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx /\
    disjoint out inp /\ disjoint out ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    (let k = LSeq.sub (as_seq h0 ctx) (v (nlen M32))
      ((Spec.num_rounds Spec.AES256+1) * v (klen M32)) in
    let n = LSeq.sub (as_seq h0 ctx) 0 (v (nlen M32)) in
    as_seq h1 out == Spec.aes_ctr32_encrypt_stream_LE Spec.AES256
      (keyx_to_bytes M32 Spec.AES256 k) (nonce_to_bytes M32 n)
      counter (as_seq h0 inp))))

let aes256_ctr len out inp ctx c =  aes_ctr #M32 #Spec.AES256 len out inp ctx c


[@ CInline ]
val aes256_ctr_encrypt:
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
    as_seq h1 out == Spec.aes_ctr32_encrypt_bytes_LE Spec.AES256
    (as_seq h0 k) (as_seq h0 n) counter (as_seq h0 inp)))

let aes256_ctr_encrypt len out inp k n c = aes_ctr_encrypt #M32 #Spec.AES256 len out inp k n c


[@ CInline ]
val aes256_ctr_decrypt:
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
    as_seq h1 out == Spec.aes_ctr32_decrypt_bytes_LE Spec.AES256
    (as_seq h0 k) (as_seq h0 n) counter (as_seq h0 inp)))
let aes256_ctr_decrypt len out inp k n c = aes_ctr_decrypt #M32 #Spec.AES256 len out inp k n c
