module Hacl.Chacha20Poly1305

open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Buffer
open FStar.HyperStack.ST
open Hacl.Constants
open Hacl.Policies
open Hacl.Cast
open Hacl.Spec.Endianness
open FStar.Endianness
open Hacl.Endianness

open Spec.Chacha20Poly1305

(* Module abbreviations *)
module ST = FStar.HyperStack.ST
module HS  = FStar.HyperStack
module B   = FStar.Buffer
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64


(* The following values should point to Spec.Chacha20Poly1305 *)
noextract let noncelen = 12
noextract let keylen = 32
noextract let maclen = 16


let state = Hacl.Impl.Poly1305_64.State.poly1305_state
inline_for_extraction let log_t = Ghost.erased (Spec.Poly1305.text)

open FStar.Mul
open FStar.Endianness


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 300"

val encode_length:
  lb:uint8_p{length lb = 16} ->
  aad_len:u32 -> mlen:u32 ->
  Stack unit
    (requires (fun h -> live h lb))
    (ensures (fun h0 _ h1 -> live h1 lb /\ modifies_1 lb h0 h1
      /\ (reveal_sbytes (as_seq h1 lb) == little_bytes 8ul (U32.v aad_len) @| little_bytes 8ul (U32.v mlen))))


val aead_encrypt:
  c:uint8_p ->
  mac:uint8_p{length mac = maclen /\ disjoint mac c} ->
  m:uint8_p{disjoint c m} ->
  mlen:u32{let len = U32.v mlen in len = length m /\ len = length c}  ->
  aad:uint8_p{disjoint aad c} ->
  aadlen:u32{let len = U32.v aadlen in len = length aad}  ->
  k:uint8_p{length k = keylen /\ disjoint k mac /\ disjoint k c} ->
  n:uint8_p{length n = noncelen /\ disjoint n mac /\ disjoint n c} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h k /\ live h aad))
    (ensures  (fun h0 z h1 -> modifies_2 c mac h0 h1 /\ live h1 c /\ live h1 mac
      /\ live h0 c /\ live h0 mac /\ live h0 m /\ live h0 n /\ live h0 k /\ live h0 aad
      /\ (length c + length aad) / 64 < pow2 32
      /\ (let cipher = reveal_sbytes (as_seq h1 c) in
       let mac    = reveal_sbytes (as_seq h1 mac) in
       let k      = reveal_sbytes (as_seq h0 k) in
       let n      = reveal_sbytes (as_seq h0 n) in
       let m      = reveal_sbytes (as_seq h0 m) in
       let aad    = reveal_sbytes (as_seq h0 aad) in
       let cipher', mac' = aead_chacha20_poly1305_encrypt k n m aad in
       cipher == cipher' /\ mac == mac')
      ))


val aead_decrypt:
  m:uint8_p ->
  c:uint8_p{disjoint m c} ->
  mlen:u32{let len = U32.v mlen in len = length m /\ len = length c}  ->
  mac:uint8_p{length mac = maclen /\ disjoint mac m} ->
  aad:uint8_p{disjoint aad m /\ ((length c + length aad) / 64) < pow2 32} ->
  aadlen:u32{let len = U32.v aadlen in len = length aad}  ->
  k:uint8_p{length k = keylen /\ disjoint k m} ->
  n:uint8_p{length n = noncelen /\ disjoint n m} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h k /\ live h aad))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m
      /\ live h0 c /\ live h0 mac /\ live h0 m /\ live h0 n /\ live h0 k /\ live h0 aad
      /\ (let m = reveal_sbytes (as_seq h1 m) in
         let c = reveal_sbytes (as_seq h0 c) in
         let aad = reveal_sbytes (as_seq h0 aad) in
         let mac = reveal_sbytes (as_seq h0 mac) in
         let k = reveal_sbytes (as_seq h0 k) in
         let n = reveal_sbytes (as_seq h0 n) in
         let plain = aead_chacha20_poly1305_decrypt k n c mac aad in
         (z == 0ul ==> (Some? plain /\ m == Some?.v plain)
         /\ (z == 1ul ==> (None? plain))))))
