module Hacl.Symmetric.XSalsa20

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.ST
open FStar.UInt32
open Hacl.UInt8
open Hacl.UInt32
open Hacl.Cast
open FStar.Buffer

open Utils

#reset-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"

(* Module abbreviations *)
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64

open Hacl.Symmetric.Salsa20

val initialize_hsalsa_state:
  state:uint32_p{length state >= 16} ->
  key:uint8_p{length key = 32 /\ disjoint state key} ->
  nonce:uint8_p{length nonce = 16 /\ disjoint state nonce} ->
  Stack unit
    (requires (fun h -> live h state /\ live h key /\ live h nonce))
    (ensures (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let initialize_hsalsa_state state key nonce =
  (* Key part *)
  let k0 = sub key 0ul  4ul in
  let k1 = sub key 4ul  4ul in
  let k2 = sub key 8ul  4ul in
  let k3 = sub key 12ul 4ul in
  let k4 = sub key 16ul 4ul in
  let k5 = sub key 20ul 4ul in
  let k6 = sub key 24ul 4ul in
  let k7 = sub key 28ul 4ul in
  let k0 =  (uint32_of_bytes k0) in
  let k1 =  (uint32_of_bytes k1) in
  let k2 =  (uint32_of_bytes k2) in
  let k3 =  (uint32_of_bytes k3) in
  let k4 =  (uint32_of_bytes k4) in
  let k5 =  (uint32_of_bytes k5) in
  let k6 =  (uint32_of_bytes k6) in
  let k7 =  (uint32_of_bytes k7) in
  (* Nonce part *)
  let n0 = sub nonce 0ul  4ul in
  let n1 = sub nonce 4ul  4ul in
  let n2 = sub nonce 8ul  4ul in
  let n3 = sub nonce 12ul 4ul in
  let n0 =  (uint32_of_bytes n0) in
  let n1 =  (uint32_of_bytes n1) in
  let n2 =  (uint32_of_bytes n2) in
  let n3 =  (uint32_of_bytes n3) in
  let h0 = ST.get() in
  (* Constant part *)
  state.(0ul) <- (uint32_to_sint32 0x61707865ul);
  state.(5ul) <- (uint32_to_sint32 0x3320646eul);
  state.(10ul) <- (uint32_to_sint32 0x79622d32ul);
  state.(15ul) <- (uint32_to_sint32 0x6b206574ul);
  (* Update with key *)
  state.(1ul) <-  (k0);
  state.(2ul) <-  (k1);
  state.(3ul) <-  (k2);
  state.(4ul) <-  (k3);
  state.(11ul) <- (k4);
  state.(12ul) <- (k5);
  state.(13ul) <- (k6);
  state.(14ul) <- (k7);
  (* Update with nonces *)
  state.(6ul) <- (n0);
  state.(7ul) <- (n1);
  state.(8ul) <- (n2);
  state.(9ul) <- (n3)


val hsalsa_init:
  subkey:uint8_p{length subkey = 32} ->
  key:uint8_p{length key = 32 /\ disjoint key subkey} ->
  nonce:uint8_p{length nonce = 16 /\ disjoint nonce subkey} ->
  Stack unit
    (requires (fun h -> live h subkey /\ live h key /\ live h nonce))
    (ensures  (fun h0 _ h1 -> modifies_1 subkey h0 h1 /\ live h1 subkey))
let hsalsa_init subkey key nonce_16 =
  push_frame ();
  let m = create (uint32_to_sint32 0ul) 16ul in
  initialize_hsalsa_state m key nonce_16;
  rounds m;
  (* Subkey *)
  bytes_of_uint32s (offset subkey  0ul) (offset m  0ul)  4ul;
  bytes_of_uint32s (offset subkey  4ul) (offset m  5ul)  4ul;
  bytes_of_uint32s (offset subkey  8ul) (offset m 10ul)  4ul;
  bytes_of_uint32s (offset subkey 12ul) (offset m 15ul)  4ul;
  bytes_of_uint32s (offset subkey 16ul) (offset m  6ul) 16ul;
  pop_frame()


val xsalsa20_encrypt:
  ciphertext:uint8_p ->
  key:uint8_p{length key = 32 /\ disjoint ciphertext key} ->
  nonce:uint8_p{length nonce = 24 /\ disjoint ciphertext nonce /\ disjoint key nonce} ->
  plaintext:uint8_p{disjoint ciphertext plaintext /\ disjoint key plaintext /\ disjoint nonce plaintext} ->
  len:u32{length ciphertext >= FStar.UInt32.v len /\ length plaintext >= FStar.UInt32.v len /\ FStar.UInt32.v len / 64 < pow2 32} ->
  Stack unit
    (requires (fun h -> live h ciphertext /\ live h key /\ live h nonce /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ modifies_1 ciphertext h0 h1))
let xsalsa20_encrypt ciphertext key nonce plaintext len =
  push_frame ();
  let subkey = create (uint8_to_sint8 0uy) 32ul in
  let nonce_16 = sub nonce 0ul 16ul in
  let nonce_8 = sub nonce 16ul 8ul in
  (* HSalsa run *)
  hsalsa_init subkey key nonce_16;
  (* Salsa20 run *)
  let counter = uint64_to_sint64 0uL in
  salsa20_encrypt ciphertext subkey nonce_8 plaintext len;
  pop_frame()
