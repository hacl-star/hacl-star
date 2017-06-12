module Hacl.Chacha20


open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Ghost
open FStar.Buffer
open Hacl.Cast
open Hacl.UInt32
open Hacl.Symmetric.Chacha20
open Hacl.Spec.Chacha20


module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

#set-options "--lax"

let log_t = erased (key * ctr * nonce)

val chacha20_init:
  ctx:chacha_ctx ->
  k:uint8_p{length k = 32} ->
  counter:u32 ->
  n:uint8_p{length n = 12} ->
  Stack log_t
    (requires (fun h -> live h ctx /\ live h k /\ live h n))
    (ensures (fun h0 log h1 -> live h0 ctx /\ live h0 k /\ live h0 n
      /\ live h1 ctx /\ live h1 k /\ live h1 n
      /\ (let key, ctr, nonce = reveal log in
         let state = as_seq h1 ctx in
         key == as_seq h0 k
         /\ nonce == as_seq h0 n
         /\ ctr == counter
         /\ state == chacha_state_setup_spec key ctr nonce)
    ))
let chacha20_init ctx k counter n =
  let h = ST.get() in
  let log = elift1 (fun h -> as_seq h k, counter, as_seq h n) (hide h) in
  chacha_keysetup ctx k;
  chacha_ietf_ivsetup ctx n counter;
  log

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
