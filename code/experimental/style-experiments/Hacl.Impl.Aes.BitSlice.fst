module Hacl.Impl.Aes.BitSlice

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
open Lib.Utils

open Hacl.Impl.Aes.Core
open Hacl.Impl.Aes.Generic


let state = state M32
let key1 = key1 M32
let keyr = keyr M32
let keyex = keyex M32
let aes_ctx = aes_ctx M32

[@ CInline ]
val enc_rounds: st:state -> key:keyr -> n:size_t -> ST unit
	     (requires (fun h -> live h st /\ live h key))
	     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
[@ CInline ]
let enc_rounds st key n = enc_rounds #M32 st key n


[@ CInline ]
val key_expansion128: keyx:keyex -> key:lbytes 16 -> ST unit
		     (requires (fun h -> live h keyx /\ live h key))
		     (ensures (fun h0 _ h1 -> live h1 keyx /\ live h1 key /\ modifies (loc_buffer keyx) h0 h1))
[@ CInline ]
let key_expansion128 keyx key = key_expansion128 #M32 keyx key
       

[@ CInline ]
val key_expansion256: keyx:keyex -> key:lbytes 32 -> ST unit
			     (requires (fun h -> live h keyx /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 keyx /\ live h1 key /\ modifies (loc_buffer keyx) h0 h1))
[@ CInline ]
let key_expansion256 keyx key = key_expansion256 #M32 keyx key
    

[@ CInline ]
val aes128_init: ctx:aes_ctx -> key:skey -> nonce:lbytes 12 -> ST unit
			     (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
			     (ensures (fun h0 b h1 -> modifies (loc_buffer ctx) h0 h1))
[@ CInline ]
let aes128_init ctx key nonce = aes128_init #M32 ctx key nonce

[@ CInline ]
val aes256_init: ctx:aes_ctx -> key:skey -> nonce:lbytes 12 -> ST unit
			     (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
			     (ensures (fun h0 b h1 -> modifies (loc_buffer ctx) h0 h1))
[@ CInline ]
let aes256_init ctx key nonce = aes256_init #M32 ctx key nonce


[@ CInline ]
val aes128_key_block: kb:lbytes 16 -> ctx:aes_ctx -> counter:size_t -> ST unit
			     (requires (fun h -> live h kb /\ live h ctx))
			     (ensures (fun h0 _ h1 -> modifies (loc_buffer kb) h0 h1))
[@ CInline ]
let aes128_key_block kb ctx counter = aes128_key_block #M32 kb ctx counter


inline_for_extraction
val aes_update4: out:lbytes 64 -> inp:lbytes 64 -> ctx:aes_ctx -> counter:size_t -> rounds:size_t -> ST unit
			     (requires (fun h -> live h out /\ live h inp /\ live h ctx))
			     (ensures (fun h0 b h1 -> modifies (loc_buffer out) h0 h1))
let aes_update4 out inp ctx ctr rounds = aes_update4 out inp ctx ctr rounds


[@ CInline ]
val aes_ctr: out:bytes -> inp:bytes -> len:size_t -> ctx:aes_ctx -> counter:size_t -> rounds:size_t -> ST unit
			     (requires (fun h -> live h out /\ live h inp /\ live h ctx))
			     (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
[@ CInline ]
let aes_ctr out inp len ctx counter rounds = aes_ctr #M32 out inp len ctx counter rounds

[@ CInline ]
let aes128_ctr_encrypt out inp in_len k n c = aes128_ctr_encrypt #M32 out inp in_len k n c

[@ CInline ]
let aes128_ctr_decrypt out inp in_len k n c = aes128_ctr_decrypt #M32 out inp in_len k n c

[@ CInline ]
let aes256_ctr_encrypt out inp in_len k n c = aes256_ctr_encrypt #M32 out inp in_len k n c

[@ CInline ]
let aes256_ctr_decrypt out inp in_len k n c = aes256_ctr_decrypt #M32 out inp in_len k n c
