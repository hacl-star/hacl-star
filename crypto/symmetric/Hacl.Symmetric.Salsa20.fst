module Hacl.Symmetric.Salsa20

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open FStar.UInt32
open FStar.Buffer

open Hacl.UInt8
open Hacl.UInt32
open Hacl.Cast

open Utils

#reset-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3timeout 5"

(* Module abbreviations *)
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8   = FStar.UInt8
module U32  = FStar.UInt32
module H8   = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64

(* This HAS to go in some more appropriate place *)
assume MaxUInt32: pow2 32 = 4294967296

(* Public machine integer types *)
let u32 = U32.t
let u8  = U8.t
(* Secret machine integer types *)
let h64 = H64.t
let h32 = H32.t
let h8  = H8.t

let uint8_p = buffer H8.t
let uint32_p = buffer H32.t
let bytes = uint8_p


(* Salsa 20 code *)
val quarter_round:
  m:uint32_p{length m = 16} ->
  a:u32{FStar.UInt32.v a < 16} ->
  b:u32{FStar.UInt32.v b<16} ->
  c:u32{FStar.UInt32.v c<16} ->
  d:u32{FStar.UInt32.v d<16} ->
  Stack unit
    (requires (fun h -> live h m))
    (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))
let quarter_round m a b c d =
  let md = m.(d) in let mc = m.(c) in m.(a) <- m.(a) ^^ ((md +%^ mc) <<< 7ul);
  let ma = m.(a) in let md = m.(d) in m.(b) <- m.(b) ^^ ((ma +%^ md) <<< 9ul);
  let mb = m.(b) in let ma = m.(a) in m.(c) <- m.(c) ^^ ((mb +%^ ma) <<< 13ul);
  let mc = m.(c) in let mb = m.(b) in m.(d) <- m.(d) ^^ ((mc +%^ mb) <<< 18ul)


(* Salsa20 block function *)
val double_round:
  m:uint32_p{length m = 16} ->
  Stack unit
    (requires (fun h -> live h m))
    (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1 ))
let double_round m =
  quarter_round m  4ul  8ul 12ul  0ul;
  quarter_round m  9ul 13ul  1ul  5ul;
  quarter_round m 14ul  2ul  6ul 10ul;
  quarter_round m  3ul  7ul 11ul 15ul;
  quarter_round m  1ul  2ul  3ul  0ul;
  quarter_round m  6ul  7ul  4ul  5ul;
  quarter_round m 11ul  8ul  9ul 10ul;
  quarter_round m 12ul 13ul 14ul 15ul


(* 10 double rounds *)
val rounds:
  m:uint32_p{length m = 16} -> Stack unit
    (requires (fun h -> live h m))
    (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1 ))
let rounds m =
  double_round m;
  double_round m;
  double_round m;
  double_round m;
  double_round m;
  double_round m;
  double_round m;
  double_round m;
  double_round m;
  double_round m


#reset-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val initialize_state:
  state:uint32_p{length state >= 16} ->
  key:uint8_p{length key = 32 /\ disjoint state key} ->
  counter:h64 ->
  nonce:uint8_p{length nonce = 8 /\ disjoint state nonce} ->
  Stack unit
    (requires (fun h -> live h state /\ live h key /\ live h nonce))
    (ensures (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let initialize_state state key counter nonce =
  (* Key part *)
  let open FStar.Buffer in // Shadowing the 'sub' definition
  let h0 = HST.get() in
  let k0 = sub key 0ul  4ul in
  let k1 = sub key 4ul  4ul in
  let k2 = sub key 8ul  4ul in
  let k3 = sub key 12ul 4ul in
  let k4 = sub key 16ul 4ul in
  let k5 = sub key 20ul 4ul in
  let k6 = sub key 24ul 4ul in
  let k7 = sub key 28ul 4ul in
  let k0 = (uint32_of_bytes k0) in
  let k1 = (uint32_of_bytes k1) in
  let k2 = (uint32_of_bytes k2) in
  let k3 = (uint32_of_bytes k3) in
  let k4 = (uint32_of_bytes k4) in
  let k5 = (uint32_of_bytes k5) in
  let k6 = (uint32_of_bytes k6) in
  let k7 = (uint32_of_bytes k7) in
  (* Nonce part *)
  let n0 = sub nonce 0ul 4ul in
  let n1 = sub nonce 4ul 4ul in
  let n0 =  (uint32_of_bytes n0) in
  let n1 =  (uint32_of_bytes n1) in
  (* Constant part *)
  state.(0ul) <-  (uint32_to_sint32 0x61707865ul);
  state.(5ul) <-  (uint32_to_sint32 0x3320646eul);
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
  (* Block counter part *)
  let c0 = sint64_to_sint32 counter in
  let c1 = sint64_to_sint32 (H64 (counter >>^ 32ul)) in
  state.(8ul) <- c0;
  state.(9ul) <- c1


val sum_matrixes:
  new_state:uint32_p{length new_state >= 16} ->
  old_state:uint32_p{length old_state >= 16 /\ disjoint new_state old_state} ->
  Stack unit
    (requires (fun h -> live h new_state /\ live h old_state))
    (ensures (fun h0 _ h1 -> live h1 new_state /\ modifies_1 new_state h0 h1))
let sum_matrixes m m0 =
  let m_0 = m.(0ul) in let m0_0 = m0.(0ul) in m.(0ul) <- (m_0 +%^ m0_0);
  let m_1 = m.(1ul) in let m0_1 = m0.(1ul) in m.(1ul) <- (m_1 +%^ m0_1);
  let m_2 = m.(2ul) in let m0_2 = m0.(2ul) in m.(2ul) <- (m_2 +%^ m0_2);
  let m_3 = m.(3ul) in let m0_3 = m0.(3ul) in m.(3ul) <- (m_3 +%^ m0_3);
  let m_4 = m.(4ul) in let m0_4 = m0.(4ul) in m.(4ul) <- (m_4 +%^ m0_4);
  let m_5 = m.(5ul) in let m0_5 = m0.(5ul) in m.(5ul) <- (m_5 +%^ m0_5);
  let m_6 = m.(6ul) in let m0_6 = m0.(6ul) in m.(6ul) <- (m_6 +%^ m0_6);
  let m_7 = m.(7ul) in let m0_7 = m0.(7ul) in m.(7ul) <- (m_7 +%^ m0_7);
  let m_8 = m.(8ul) in let m0_8 = m0.(8ul) in m.(8ul) <- (m_8 +%^ m0_8);
  let m_9 = m.(9ul) in let m0_9 = m0.(9ul) in m.(9ul) <- (m_9 +%^ m0_9);
  let m_10 = m.(10ul) in let m0_10 = m0.(10ul) in m.(10ul) <- (m_10 +%^ m0_10);
  let m_11 = m.(11ul) in let m0_11 = m0.(11ul) in m.(11ul) <- (m_11 +%^ m0_11);
  let m_12 = m.(12ul) in let m0_12 = m0.(12ul) in m.(12ul) <- (m_12 +%^ m0_12);
  let m_13 = m.(13ul) in let m0_13 = m0.(13ul) in m.(13ul) <- (m_13 +%^ m0_13);
  let m_14 = m.(14ul) in let m0_14 = m0.(14ul) in m.(14ul) <- (m_14 +%^ m0_14);
  let m_15 = m.(15ul) in let m0_15 = m0.(15ul) in m.(15ul) <- (m_15 +%^ m0_15)


val salsa20_core:
  output:uint8_p ->
  state:uint32_p{length state >= 32 /\ disjoint state output} ->
  key:uint8_p{length key = 32 /\ disjoint state key /\ disjoint output key} ->
  counter:h64 ->
  nonce:uint8_p{length nonce = 8 /\ disjoint state nonce /\ disjoint output nonce} ->
  len:u32{FStar.UInt32.v len <= 64 /\ length output >= FStar.UInt32.v len} ->
  Stack unit
    (requires (fun h -> live h state /\ live h output /\ live h key /\ live h nonce))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h1 state /\ modifies_2 output state h0 h1 ))
let salsa20_core output state key counter nonce len =
  let open FStar.Buffer in // local shadowing of the 'sub' definition
  (* Initialize internal state *)
  let m = sub state 0ul 16ul in
  let m0 = sub state 16ul 16ul in
  initialize_state m key counter nonce;
  (* Initial state *)
  blit m 0ul m0 0ul 16ul;
  (* 20 rounds *)
  rounds m;
  (* Sum the matrixes *)
  sum_matrixes m m0;
  (* Serialize the state into byte stream *)
  bytes_of_uint32s output m len


val salsa20_encrypt_loop:
  state:uint32_p{length state >= 32} ->
  key:uint8_p{length key = 32 /\ disjoint state key} ->
  counter:h64 ->
  nonce:uint8_p{length nonce = 8 /\ disjoint state nonce} ->
  plaintext:uint8_p{disjoint state plaintext} ->
  ciphertext:uint8_p{disjoint state ciphertext /\ disjoint key ciphertext /\ disjoint nonce ciphertext /\ disjoint plaintext ciphertext} ->
  j:u32 ->
  max:u32{FStar.UInt32.v j <= FStar.UInt32.v max /\ Hacl.UInt64.v counter + FStar.UInt32.v max < pow2 n} ->
  Stack unit
    (requires (fun h -> live h state /\ live h key /\ live h nonce /\ live h plaintext  /\ live h ciphertext
      /\ length plaintext >= (FStar.UInt32.v max-FStar.UInt32.v j) * 64  /\ length ciphertext >= (FStar.UInt32.v max-FStar.UInt32.v j) * 64 ))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 state /\ modifies_2 ciphertext state h0 h1 ))
let rec salsa20_encrypt_loop state key counter nonce plaintext ciphertext j max =
  if j =^ max then ()
  else
    begin
      (* Generate new state for block *)
      let open FStar.Buffer in
      let cipher_block = sub ciphertext 0ul 64ul in
      let ciphertext' = sub ciphertext 64ul (U32 (64ul *^ (max -^ j -^ 1ul))) in
      let plain_block = sub plaintext 0ul 64ul in
      let plaintext' = sub plaintext 64ul (U32 (64ul *^ (max -^ j -^ 1ul))) in
      salsa20_core cipher_block state key (H64 (counter +^ (uint32_to_sint64 j))) nonce 64ul;
      (* XOR the key stream with the plaintext *)
      xor_uint8_p_2 cipher_block plain_block 64ul;
      (* Apply Salsa20 to the next blocks *)
      salsa20_encrypt_loop state key counter nonce plaintext' ciphertext' (U32 (j +^ 1ul)) max
    end


#reset-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3timeout 5"

val salsa20_encrypt_body:
  state:uint32_p{length state = 32} ->
  ciphertext:uint8_p{disjoint state ciphertext} ->
  key:uint8_p{length key = 32 /\ disjoint ciphertext key /\ disjoint key state} ->
  counter:h64 ->
  nonce:uint8_p{length nonce = 8 /\ disjoint ciphertext nonce /\ disjoint state nonce} ->
  plaintext:uint8_p{disjoint ciphertext plaintext /\ disjoint state plaintext} ->
  len:u32{length ciphertext >= FStar.UInt32.v len /\ length plaintext >= FStar.UInt32.v len /\ Hacl.UInt64.v counter + FStar.UInt32.v len / 64 < pow2 32} ->
  Stack unit
    (requires (fun h -> live h state /\ live h ciphertext /\ live h key /\ live h nonce /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 state /\ modifies_2 ciphertext state h0 h1))
let salsa20_encrypt_body state ciphertext key counter nonce plaintext len =
  let max = U32 (len /^ 64ul) in
  let rem = U32 (len %^ 64ul) in
  (* Apply Salsa20 max times **)
  salsa20_encrypt_loop state key counter nonce plaintext ciphertext 0ul max;
  if rem =^ 0ul then ()
  else
    begin
      let open FStar.Buffer in
      let cipher_block = sub ciphertext (U32 (64ul *^ max)) rem in
      let plain_block = sub plaintext (U32 (64ul *^ max)) rem in
      let h = HST.get() in
      salsa20_core cipher_block state key (H64 (counter +^ (uint32_to_sint64 max))) nonce rem;
      xor_uint8_p_2 cipher_block plain_block rem
    end


val salsa20_encrypt:
  ciphertext:uint8_p ->
  key:uint8_p{length key = 32 /\ disjoint ciphertext key} ->
  nonce:uint8_p{length nonce = 8 /\ disjoint ciphertext nonce /\ disjoint key nonce} ->
  plaintext:uint8_p{disjoint ciphertext plaintext /\ disjoint key plaintext /\ disjoint nonce plaintext} ->
  len:u32{length ciphertext >= FStar.UInt32.v len /\ length plaintext >= FStar.UInt32.v len /\ FStar.UInt32.v len / 64 < pow2 32} ->
  Stack unit
    (requires (fun h -> live h ciphertext /\ live h key /\ live h nonce /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ modifies_1 ciphertext h0 h1))
let salsa20_encrypt ciphertext key nonce plaintext len =
  push_frame ();
  let state = create (uint32_to_sint32 0ul) 32ul in
  (* Compute number of iterations *)
  let counter = uint64_to_sint64 0uL in
  salsa20_encrypt_body state ciphertext key counter nonce plaintext len;
  pop_frame()


val salsa20_encrypt_with_counter:
  ciphertext:uint8_p ->
  key:uint8_p{length key = 32 /\ disjoint ciphertext key} ->
  nonce:uint8_p{length nonce = 8 /\ disjoint ciphertext nonce /\ disjoint key nonce} ->
  plaintext:uint8_p{disjoint ciphertext plaintext /\ disjoint key plaintext /\ disjoint nonce plaintext} ->
  len:u32{length ciphertext >= U32.v len /\ length plaintext >= U32.v len} ->
  counter:h64{H64.v counter + U32.v len / 64 < pow2 32} ->
  Stack unit
    (requires (fun h -> live h ciphertext /\ live h key /\ live h nonce /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ modifies_1 ciphertext h0 h1))
let salsa20_encrypt_with_counter ciphertext key nonce plaintext len counter =
  push_frame ();
  let state = create (uint32_to_sint32 0ul) 32ul in
  (* Compute number of iterations *)
  salsa20_encrypt_body state ciphertext key counter nonce plaintext len;
  pop_frame()
