module Chacha20

open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.Cast
open Hacl.UInt32
open FStar.Buffer
open Hacl.Spec.Symmetric.Chacha20

module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t
type chacha_ctx = b:Buffer.buffer h32{length b = 16}

val chacha_keysetup:
  ctx:chacha_ctx ->
  k:uint8_p{length k = 32 /\ disjoint ctx k} ->
  Stack unit
    (requires (fun h -> live h ctx /\ live h k))
    (ensures  (fun h0 _ h1 -> live h0 ctx /\ live h0 k /\ live h1 ctx /\ modifies_1 ctx h0 h1
      /\ as_seq h1 ctx == chacha_keysetup_spec (as_seq h0 ctx) (as_seq h0 k)))
let chacha_keysetup ctx k = Hacl.Symmetric.Chacha20.chacha_keysetup ctx k

val chacha_ietf_ivsetup:
  ctx:chacha_ctx ->
  k:uint8_p{length k = 12 /\ disjoint ctx k} ->
  counter:u32 ->
  Stack unit
    (requires (fun h -> live h ctx /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 ctx /\ modifies_1 ctx h0 h1 /\ live h0 ctx /\ live h0 k
      /\ as_seq h1 ctx == chacha_ietf_ivsetup_spec (as_seq h0 ctx) (as_seq h0 k) counter))
let chacha_ietf_ivsetup ctx k ctr = Hacl.Symmetric.Chacha20.chacha_ietf_ivsetup ctx k ctr

val chacha_encrypt_bytes:
  ctx:chacha_ctx ->
  m:uint8_p ->
  c:uint8_p{disjoint ctx c} ->
  len:UInt32.t{U32.v len <= length m /\ U32.v len <= length c} ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h ctx))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_2 ctx c h0 h1))
let chacha_encrypt_bytes ctx m c l = Hacl.Symmetric.Chacha20.chacha_encrypt_bytes ctx m c l
