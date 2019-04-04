module Hacl.AES_256.BitSlice

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.AES_128.Core
open Hacl.Impl.AES_256.Generic


let state = state M32
let key1 = key1 M32
let keyr = keyr M32
let keyex = keyex M32

let aes_ctx_len = 128ul
let aes_ctx = lbuffer uint64 aes_ctx_len

[@ CInline ]
val aes256_encrypt_block_bitsliced:
     ob: lbuffer uint8 16ul
  -> k: skey
  -> ib: lbuffer uint8 16ul ->
  ST unit
  (requires (fun h -> live h ob /\ live h ib /\ live h k /\ disjoint k ob /\ disjoint ob ib))
  (ensures (fun h0 _ h1 -> modifies1 ob h0 h1))

[@ CInline ]
let aes256_encrypt_block_bitsliced out k inp =
  push_frame();
  let ctx = create (ctxlen M32) (u64 0) in
  let kex = get_kex ctx in
  let h0 = ST.get () in
  key_expansion256 #M32 kex k ;
  aes256_encrypt_block_generic_ #M32 out ctx inp;
  pop_frame()

[@ CInline ]
val key_expansion256:
     keyx: keyex
  -> key: lbuffer uint8 32ul ->
  ST unit
  (requires (fun h -> live h keyx /\ live h key /\ disjoint keyx key))
  (ensures (fun h0 _ h1 -> modifies1 keyx h0 h1))

let key_expansion256 keyx key = key_expansion256 #M32 keyx key
