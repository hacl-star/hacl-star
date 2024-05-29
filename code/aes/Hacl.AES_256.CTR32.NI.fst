module Hacl.AES_256.CTR32.NI

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

let aes_ctx = aes_ctx MAES Spec.AES256
let skey = skey Spec.AES256

[@@ CPrologue
"/*******************************************************************************

A verified AES-CTR32-256 library.

This is a 128-bit optimized specific version of counter mode of operation for
GCM, it uses AES-256 cipher for data confidentiality.

AES-CTR32 always uses the forward version of AES cipher.

*******************************************************************************/

/************************/
/* AES-CTR32-256 API */
/************************/\n";
Comment
"Allocate a buffer on stack for AES-256 key expansion and nonce"]
inline_for_extraction noextract
val context_alloca: unit ->
  StackInline aes_ctx
  (requires (fun h -> True))
  (ensures  (fun h0 f h1 -> live h1 f /\
    stack_allocated f h0 h1 (Seq.create (size_v (ctxlen MAES Spec.AES256))
    (elem_zero MAES))))

inline_for_extraction noextract
let context_alloca () = create_ctx MAES Spec.AES256

[@@ Comment "Allocate AES-256 context buffer using malloc for key expansion and nonce"]
inline_for_extraction
val context_malloc:
    r:rid
  -> ST.ST (s:buffer (stelem MAES) { length s = v (ctxlen MAES Spec.AES256) })
  (requires (fun _ ->
    ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    live h1 s /\
    M.(modifies loc_none h0 h1) /\
    B.fresh_loc (loc_addr_of_buffer s) h0 h1 /\
    (M.loc_includes (M.loc_region_only true r) (loc_addr_of_buffer s)) /\
    freeable s))

let context_malloc r =
  assert (v (ctxlen MAES Spec.AES256) == 16);
  B.malloc r (elem_zero MAES) (ctxlen MAES Spec.AES256)

[@@ Comment "Free AES-256 context buffer"]
inline_for_extraction
val context_free:
    s:buffer (stelem MAES) { length s = v (ctxlen MAES Spec.AES256) }
  -> ST.ST unit
  (requires fun h0 ->
    freeable s /\ live h0 s)
  (ensures fun h0 _ h1 ->
    M.modifies (loc_addr_of_buffer s) h0 h1)

let context_free s =
  B.free s


[@@ Comment "Initiate AES-256 context buffer with key expansion and nonce"]
val init:
    ctx: aes_ctx
  -> key: skey 
  -> nonce: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key /\ disjoint ctx key /\
    as_seq h ctx == Seq.create (size_v (ctxlen MAES Spec.AES256)) (elem_zero MAES)))
  (ensures  (fun h0 _ h1 -> modifies1 ctx h0 h1 /\
    (let state = Spec.aes_ctr32_init_LE Spec.AES256
      (as_seq h0 key) (as_seq h0 nonce) in
    get_nonce_s MAES Spec.AES256 h1 ctx == state.block /\
    get_kex_s MAES Spec.AES256 h1 ctx == state.key_ex)))

let init ctx key nonce = aes256_ni_init ctx key nonce

[@@ Comment "Encrypt a block (128-bit) with AES-256 cipher.

  Given that `ctx` is initiated with AES-256 key."]
inline_for_extraction noextract
val encrypt_block:
    ob: lbuffer uint8 16ul
  -> ctx: aes_ctx
  -> ib: lbuffer uint8 16ul ->
  ST unit
  (requires (fun h -> live h ob /\ live h ctx /\ live h ib))
  (ensures (fun h0 _ h1 -> modifies (loc ob) h0 h1 /\
    as_seq h1 ob == u8_16_to_le (Spec.aes_encrypt_block Spec.AES256
      (get_kex_s MAES Spec.AES256 h0 ctx) (u8_16_to_le (as_seq h0 ib)))))

let encrypt_block ob ctx ib =
    aes_encrypt_block #MAES #Spec.AES256 ob ctx ib


[@@ Comment "Set nonce in AES-256 context buffer"]
val set_nonce:
    ctx: aes_ctx
  -> nonce: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h nonce))
  (ensures  (fun h0 _ h1 -> modifies1 ctx h0 h1 /\
    get_nonce_s MAES Spec.AES256 h1 ctx ==
      u8_16_to_le (LSeq.update_sub
      (LSeq.create 16 (u8 0)) 0 12 (as_seq h0 nonce))))

let set_nonce ctx nonce = aes_set_nonce ctx nonce


[@@ Comment "Process 4-blocks (128-bit for each) in AES-CTR32 mode.

  Given that `ctx` is initiated with AES-256 key and nonce, and
  
  `counter` is the current value of counter state."]
inline_for_extraction noextract
val update4:
    out: lbuffer uint8 64ul
  -> inp: lbuffer uint8 64ul
  -> ctx: aes_ctx
  -> counter: uint32 ->
  Stack unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures  (fun h0 _ h1 -> modifies1 out h0 h1 /\
    as_seq h1 out == Spec.aes_ctr32_encrypt_block_4_LE Spec.AES256
      (get_kex_s MAES Spec.AES256 h0 ctx)
      (get_nonce_s MAES Spec.AES256 h0 ctx)
      counter (as_seq h0 inp)))

let update4 out inp ctx ctr = aes_update4 out inp ctx ctr


[@@ Comment "Process number of bytes in AES-CTR32 mode.

  Given that `ctx` is initiated with AES-256 key and nonce, and
  
  `counter` is the initial value of counter state."]
val ctr:
  len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx
  -> counter: uint32
  -> ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx /\
    disjoint out inp /\ disjoint out ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.aes_ctr32_encrypt_stream_LE Spec.AES256
      (get_kex_s MAES Spec.AES256 h0 ctx)
      (get_nonce_s MAES Spec.AES256 h0 ctx)
      counter (as_seq h0 inp)))

let ctr len out inp ctx c =  aes_ctr #MAES #Spec.AES256 len out inp ctx c


[@@ Comment "Initiate AES-CTR32-256 context with key and nonce, and

  encrypt number of bytes in AES-CTR32 mode.
  
  `counter` is the initial value of counter state."]
val ctr_encrypt:
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

let ctr_encrypt len out inp k n c = aes_ctr_encrypt #MAES #Spec.AES256 len out inp k n c


[@@ Comment "Initiate AES-CTR32-256 context with key and nonce, and

  decrypt number of bytes in AES-CTR32 mode.
  
  `counter` is the initial value of counter state.
  
  Decryption uses the forward version of AES cipher"]
val ctr_decrypt:
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
let ctr_decrypt len out inp k n c = aes_ctr_decrypt #MAES #Spec.AES256 len out inp k n c
