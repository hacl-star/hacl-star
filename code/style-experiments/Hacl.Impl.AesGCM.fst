module Hacl.Impl.AesGCM
module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
open Lib.Utils
open Lib.Vec128
open Hacl.Impl.Aes.NI
open Hacl.Impl.Gf128.NI

type aes_gcm_ctx = 
     lbuffer vec128 22

[@ CInline ]
val aes128_gcm_init: ctx:aes_gcm_ctx -> key:lbytes 16 -> nonce:lbytes 12 -> Stack unit
	  (requires (fun h -> live h ctx /\ live h key /\ live h nonce))
	  (ensures (fun h0 _ h1 -> modifies (loc_buffer ctx) h0 h1))
[@ CInline ]
let aes128_gcm_init ctx key nonce = 
    push_frame();
    let gcm_key = alloca 0uy 16ul in
    let tag_mix = alloca 0uy 16ul in
    let nonce0 = alloca 0uy 12ul in
    let aes_ctx = sub ctx (size 0) (size 16) in
    aes128_init aes_ctx key nonce0;
    aes128_key_block gcm_key aes_ctx (size 0);
    aes128_set_nonce aes_ctx nonce;
    aes128_key_block tag_mix aes_ctx (size 1);
    let acc = sub ctx (size 16) (size 1) in
    let r4 = sub ctx (size 17) (size 4) in
    gcm_init acc r4 gcm_key;  
    ctx.(21ul) <- vec128_load_le tag_mix;
    pop_frame()
    

[@ CInline ]
val aes128_gcm_encrypt: ctx:aes_gcm_ctx -> out:bytes -> text:bytes -> len:size_t{length text == size_v len} -> 
			aad:bytes -> aad_len:size_t{length aad == size_v aad_len} -> Stack unit
	  (requires (fun h -> live h out /\ live h text /\ live h aad /\ live h ctx))
	  (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
[@ CInline ]
let aes128_gcm_encrypt ctx out text len aad aad_len =
    push_frame();
    let cip = sub out (size 0) len in
    let aes_ctx = sub ctx (size 0) (size 16) in
    aes_ctr cip text len aes_ctx (size 2) (size 10);
    let acc = sub ctx (size 16) (size 1) in
    let r4 = sub ctx (size 17) (size 4) in
    let tag_mix = ctx.(21ul) in
    poly4 acc aad aad_len r4;
    poly4 acc cip len r4;
    let tmp = alloca 0uy 16ul in
    store64_be (sub tmp (size 0) (size 8)) (to_u64 (size_to_uint32 aad_len *. u32 8));
    store64_be (sub tmp (size 8) (size 8)) (to_u64 (size_to_uint32 len *. u32 8));
    poly4 acc tmp (size 16) r4;
    decode tmp acc;
    let tmp_vec = vec128_load_le tmp in
    let tmp_vec = vec128_xor tmp_vec tag_mix in
    vec128_store_le (sub out len (size 16)) tmp_vec;
    pop_frame()

[@ CInline ]
val aes128_gcm_decrypt: ctx:aes_gcm_ctx -> out:bytes -> cipher:bytes -> len:size_t{length cipher == size_v len /\ length out == length cipher - 16} -> 
			aad:bytes -> aad_len:size_t{length aad == size_v aad_len} -> Stack size_t
	  (requires (fun h -> live h out /\ live h cipher /\ live h aad /\ live h ctx))
	  (ensures (fun h0 r h1 -> modifies (loc_buffer out) h0 h1 /\ size_v r <= length cipher - 16 ))
[@ CInline ]
let aes128_gcm_decrypt ctx out cipher len aad aad_len =
    push_frame();
    let acc = sub ctx (size 16) (size 1) in
    let r4 = sub ctx (size 17) (size 4) in
    let tag_mix = ctx.(21ul) in
    let plen = len -. size 16 in
    poly4 acc aad aad_len r4;
    poly4 acc cipher plen r4;
    let tmp = alloca 0uy 16ul in
    store64_be (sub tmp (size 0) (size 8)) (to_u64 (size_to_uint32 aad_len *. u32 8));
    store64_be (sub tmp (size 8) (size 8)) (to_u64 (size_to_uint32 plen *. u32 8));
    poly4 acc tmp (size 16) r4;
    decode tmp acc;
    let tmp_vec = vec128_load_le tmp in
    let tmp_vec = vec128_xor tmp_vec tag_mix in
    vec128_store_le tmp tmp_vec;
    let tag = sub cipher plen (size 16) in
    let res = alloca 0uy 1ul in
    let h1 = ST.get() in
    loop_nospec #h1 (size 16) res
      (fun i -> res.(0ul) <- res.(0ul) |. (tmp.(i) ^. tag.(i)));
    if res.(0ul) <> 0uy then
    (
      let cip = sub cipher (size 0) plen in
      let aes_ctx = sub ctx (size 0) (size 16) in
      aes_ctr out cip plen aes_ctx (size 2) (size 10);
      pop_frame();
      plen
    )
    else (
      pop_frame(); 
      0ul)
