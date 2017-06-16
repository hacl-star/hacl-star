//
//   Copyright 2016-2017  INRIA
//
//   Maintainers: Jean-Karim Zinzindohoué
//                Karthikeyan Bhargavan
//                Benjamin Beurdouche
//
//   Licensed under the Apache License, Version 2.0 (the "License");
//   you may not use this file except in compliance with the License.
//   You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in writing, software
//   distributed under the License is distributed on an "AS IS" BASIS,
//   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//   See the License for the specific language governing permissions and
//   limitations under the License.
//

module Hacl.Chacha20

// proposed imperative API for Chacha20
open FStar.HyperStack
open FStar.ST
open FStar.Ghost
open FStar.Buffer
//open Hacl.Cast
open FStar.UInt32

module Spec = Hacl.Spec.Chacha20

// 17-02-13 We use ordinary intergers;
// hopefully, we will switch to Hacl* secure integers under type abstrations.

type uint8_p = buffer UInt8.t 
type uint8_pl (l:nat) = p:uint8_p {length p = l}
type block = uint8_pl Spec.blocklen

//NB omitting important inline qualifiers for now.


(* STATE *) 

// This abstraction should not affect Kremlin extraction.
// We will use it instead of abstract keys in secure_api (with a modifies_2 in Cipher)

type state_buffer = b:buffer UInt32.t {length b = Spec.blocklen / 4}
abstract type state = state_buffer
// 17-02-13 named chacha_ctx in code
// for abstraction, we need a ghost function from contexts to buffers, 
// and custom allocators; a bit heavy (see e.g. Plain.fst)

val as_buffer: state -> GTot state_buffer 
val as_spec: h:HyperStack.mem -> ctx:state {live h (as_buffer ctx)} -> Tot (Spec.state)
//let as_spec h s = as_seq h (as_buffer s)

val alloc: unit -> StackInline state_buffer 
  (requires (fun h -> True))
  (ensures (fun h0 s h1 -> 
    let b = as_buffer s in 
    let len = Spec.blocklen / 4 in // copied from Buffer.create, not great.
        live h1 b 
     /\ frameOf b = h0.tip
     /\ Map.domain h1.h == Map.domain h0.h
     /\ modifies_0 h0 h1))

(* initializes a context with a given key *)
val chacha20_keysetup: 
  ctx: state -> 
  key: uint8_pl Spec.keylen -> 
  Stack unit
    (requires (fun h0 -> live h0 (as_buffer ctx)))
    (ensures (fun h0 __ h1 -> 
        let b = as_buffer ctx in 
        live h0 b /\ live h0 key /\ live h1 b /\ modifies_1 b h0 h1 /\
        as_seq h1 b = Spec.init (as_seq h0 key) (Seq.create Spec.ivlen 0uy) 0ul))

(* specializes a context to a given iv and counter, typically at the beginning of each encryption/decryption *)
//17-02-13 would prefer swapping counter and nonce
val chacha20_ivsetup: 
  ctx: state -> 
  counter: UInt32.t -> 
  nonce: uint8_pl Spec.ivlen {disjoint (as_buffer ctx) nonce} -> 
  Stack unit
    (requires (fun h0 -> live h0 (as_buffer ctx) /\ live h0 nonce)) 
    (ensures (fun h0 __ h1 -> 
        let b = as_buffer ctx in 
        live h0 b /\ live h0 nonce /\ live h1 b /\ modifies_1 b h0 h1 /\
        ( forall k iv c.{:pattern Spec.init k iv c}
        as_seq h0 b = Spec.init k iv c ==>
        as_seq h1 b = Spec.init k (as_seq h0 nonce) counter)))

let chacha_init ctx key counter nonce = 
  chacha20_keysetup ctx key; 
  chacha20_ivsetup ctx counter nonce 
// TODO check we get the expected full spec.  

(* increments the counter by one; could be bundled with core, or not. *) 
val chacha20_incr:
  ctx: state ->
  Stack unit
    (requires (fun h0 -> live h0 (as_buffer ctx))) 
    (ensures (fun h0 __ h1 -> 
        let b = as_buffer ctx in 
        live h0 b /\ live h1 b /\ modifies_1 b h0 h1 /\
        (forall k iv c. // convenient style? could also take ghost k iv c
          as_seq h0 b = Spec.init k iv c /\ UInt.size (v c + 1) 32 ==> 
          as_seq h1 b = Spec.init k iv (c +^ 1ul))))
// let chacha20_incr ctx = ctx.(12ul) <- ctx.(12ul) +^ 1ul

// we get disjointness for ctx by typing; not a great style

val chacha20_block:  (* was named stream, strangely *)
  ctx: state -> 
  cipher: block {disjoint cipher (as_buffer ctx)} -> (* I prefer tighter buffers; to be discussed *) 
  Stack unit
    (requires (fun h0 -> live h0 (as_buffer ctx) /\ live h0 cipher))
    (ensures  (fun h0 _ h1 -> 
        let b = as_buffer ctx in 
        live h0 b /\ live h1 cipher /\ modifies_1 cipher h0 h1 /\ 
        (forall k iv c. 
          as_seq h0 b = Spec.init k iv c ==>
          as_seq h1 cipher = Spec.compute k iv c  )))

val chacha20_xor_block:  (* was named core *)
  ctx: state -> 
  plain: block -> cipher: block {disjoint_2 cipher plain (as_buffer ctx)} -> (* I prefer tighter buffers; to be discussed *) 
  Stack unit
    (requires (fun h0 -> live h0 (as_buffer ctx) /\ live h0 plain /\ live h0 cipher))
    (ensures  (fun h0 _ h1 -> 
        let b = as_buffer ctx in 
        live h0 b /\ live h0 plain /\ 
        live h1 cipher /\ modifies_1 cipher h0 h1 /\ 
        (forall k iv c. 
          as_seq h0 b = Spec.init k iv c ==>
          Seq.equal (as_seq h1 cipher) (Spec.xor_block (as_seq h0 plain) (Spec.compute k iv c)
        ))))

// hopefully the rest can be built abstractly on top of these blocks. 



(*
// TODO deal with overflows 
open FStar.Seq

let xor_blocks (b:block) (b':block) : Tot block = seq_of_list (map2 FStar.UInt8.logxor
                                                                    (seq_to_list b)
                                                                    (seq_to_list b'))


val chacha20_update:
  current_log:log_t ->
  ctx:chacha_ctx ->
  m:uint8_p{length m >= 64} ->
  c:uint8_p{length c >= 64 /\ disjoint ctx c} ->
  Stack log_t
    (requires (fun h -> live h ctx /\ live h c /\ live h m
      /\ (let key, ctr, nonce = reveal current_log in
         as_seq h ctx == chacha_state_setup_spec key ctr nonce)
    ))
    (ensures  (fun h0 _ h1 -> modifies_1 c h0 h1 /\ live h1 c
      /\ (let key, ctr, nonce = reveal current_log in
         let key', ctr', nonce' = reveal current_log in
         let c = Seq.slice (as_seq h1 c) 0 64 in
         let m = Seq.slice (as_seq h0 m) 0 64 in
         let state = as_seq h0 ctx in
         let state' = as_seq h1 ctx in
         key == key' /\ nonce == nonce' /\ ctr' == FStar.UInt32.(ctr +%^ 1ul)
         /\ state' == chacha_state_setup_spec key ctr nonce
         /\ c == xor_blocks (chacha_state_serialize state) m)
    ))
let chacha20_update log ctx m c =
  let log' = elift1 (fun (a,x,b) -> a,FStar.UInt32.(x+%^1ul),b) log in
  chacha_encrypt_bytes_core ctx m c;
  let ctr = ctx.(12ul) in
  ctx.(12ul) <- Hacl.UInt32.(ctr +%^ 1ul);
  log'


val chacha20_finish:
  current_log:log_t ->
  ctx:chacha_ctx ->
  m:uint8_p ->
  c:uint8_p{disjoint ctx c} ->
  len:UInt32.t{U32.v len <= length m /\ U32.v len <= length c /\ U32.v len < 64} ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h ctx
      /\ (let key, ctr, nonce = reveal current_log in
         as_seq h ctx == chacha_state_setup_spec key ctr nonce)
    ))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_2 ctx c h0 h1
      /\ (let key, ctr, nonce = reveal current_log in
         let c = Seq.slice (as_seq h1 c) 0 (U32.v len) in
         let m = Seq.slice (as_seq h0 m) 0 (U32.v len) in
         let state = as_seq h0 ctx in
         c == xor_blocks (Seq.slice (chacha_state_serialize state) 0 (U32.v len)) m)
    ))
let chacha20_finish log ctx m c len =
  chacha_encrypt_bytes_finish ctx m c len


val chacha20_encrypt_bytes:
  m:uint8_p ->
  c:uint8_p ->
  len:UInt32.t{U32.v len <= length m /\ U32.v len <= length c} ->
  k:uint8_p{length k = 32} ->
  counter:u32 ->
  n:uint8_p{length n = 12} ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h k /\ live h n
      /\ disjoint k c /\ disjoint n c))
    (ensures  (fun h0 _ h1 -> live h0 c /\ live h0 m /\ live h0 k /\ live h0 n
      /\ live h1 c /\ modifies_1 c h0 h1
      /\ (let ciphertext = Seq.slice (as_seq h1 c) 0 (U32.v len) in
         let plaintext  = Seq.slice (as_seq h0 m) 0 (U32.v len) in
         let key        = as_seq h0 k in
         let nonce      = as_seq h0 n in
         ciphertext == chacha20_encrypt key counter nonce plaintext)
    ))
let chacha20_encrypt_bytes m c len k counter n =
  push_frame();
  let ctx = create (uint32_to_sint32 0ul) 16ul in
  let _ = chacha20_init ctx k counter n in
  chacha_encrypt_bytes ctx m c len;
  pop_frame()

*)
