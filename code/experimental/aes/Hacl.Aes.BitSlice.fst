module Hacl.Aes.BitSlice

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Aes.Core
open Hacl.Impl.Aes.Generic

let state = state M32
let key1 = key1 M32
let keyr = keyr M32
let keyex = keyex M32

let aes_ctx_len = 128ul
let aes_ctx = lbuffer uint64 aes_ctx_len

[@ CInline ]
val aes128_init: ctx:aes_ctx -> key:skey -> nonce:lbuffer uint8 12ul -> ST unit
			     (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
			     (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))
[@ CInline ]
let aes128_init ctx key nonce = aes128_init #M32 ctx key nonce

[@ CInline ]
val aes128_set_nonce: ctx:aes_ctx -> nonce:lbuffer uint8 12ul -> ST unit
			     (requires (fun h -> live h ctx /\ live h nonce))
			     (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))
[@ CInline ]
let aes128_set_nonce ctx nonce = aes128_set_nonce #M32 ctx nonce


[@ CInline ]
val aes128_key_block: kb:lbuffer uint8 16ul -> ctx:aes_ctx -> counter:size_t -> ST unit
			     (requires (fun h -> live h kb /\ live h ctx))
			     (ensures (fun h0 _ h1 -> modifies (loc kb) h0 h1))
[@ CInline ]
let aes128_key_block kb ctx counter = aes128_key_block #M32 kb ctx counter


inline_for_extraction
val aes128_update4: out:lbuffer uint8 64ul -> inp:lbuffer uint8 64ul -> ctx:aes_ctx -> counter:size_t -> ST unit
			     (requires (fun h -> live h out /\ live h inp /\ live h ctx))
			     (ensures (fun h0 b h1 -> modifies (loc out) h0 h1))
let aes128_update4 out inp ctx ctr = aes_update4 #M32 out inp ctx ctr 10ul

[@ CInline ]
val aes128_ctr: len:size_t -> out:lbuffer uint8 len -> inp:lbuffer uint8 len -> ctx:aes_ctx -> counter:size_t -> ST unit
			     (requires (fun h -> live h out /\ live h inp /\ live h ctx))
			     (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline ]
let aes128_ctr len out inp ctx counter = aes_ctr #M32 len out inp ctx counter 10ul

[@ CInline ]
let aes128_ctr_encrypt len out inp k n c = aes128_ctr_encrypt #M32 len out inp k n c

[@ CInline ]
let aes128_ctr_decrypt len out inp k n c = aes128_ctr_decrypt #M32 len out inp k n c

