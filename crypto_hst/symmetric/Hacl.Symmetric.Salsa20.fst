module Hacl.Symmetric.Salsa20

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open FStar.UInt32
open Hacl.UInt8
open Hacl.UInt32
open Hacl.Cast
(* open Hacl.SBuffer *)
open FStar.Buffer

#reset-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3timeout 50"

(* Module abbreviations *)
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
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

(* 'Rotate' operators, to inline *)
let op_Greater_Greater_Greater (a:h32) (s:u32{FStar.UInt32.v s <= 32}) : Tot h32 =
  let (m:u32{FStar.UInt32.v m = 32}) = 32ul in
  (a >>^ s) |^ (a <<^ (U32 (m -^ s)))
let op_Less_Less_Less (a:h32) (s:u32{FStar.UInt32.v s <= 32}) : Tot h32 =
  let (m:u32{FStar.UInt32.v m = 32}) = 32ul in
  (a <<^ s) |^ (a >>^ (U32 (m -^ s)))

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
  m.(a) <- m.(a) ^^ (( m.(d) +%^ m.(c) ) <<< 7ul);
  m.(b) <- m.(b) ^^ (( m.(a) +%^ m.(d) ) <<< 9ul);
  m.(c) <- m.(c) ^^ (( m.(b) +%^ m.(a) ) <<< 13ul);
  m.(d) <- m.(d) ^^ (( m.(c) +%^ m.(b) ) <<< 18ul)

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

val h32_of_uint8_p: b:uint8_p{length b >= 4} -> STL h32
  (requires (fun h -> live h b))
  (ensures (fun h0 r h1 -> h0 == h1 /\ live h0 b))
let h32_of_uint8_p (b:uint8_p{length b >= 4}) =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let r = (sint8_to_sint32 b3 <<^ 24ul)
	  +%^ (sint8_to_sint32 b2 <<^ 16ul)
	  +%^ (sint8_to_sint32 b1 <<^ 8ul)
	  +%^ sint8_to_sint32 b0 in
  r

val uint8_p_of_uint32_p:
  output:uint8_p ->
  m:uint32_p{disjoint output m} ->
  len:u32{FStar.UInt32.v len <=length output /\ FStar.UInt32.v len<=op_Multiply 4 (length m)} ->
  Stack unit
    (requires (fun h -> live h output /\ live h m))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h0 m /\ live h1 output /\ live h1 m
      /\ modifies_1 output h0 h1 ))
let rec uint8_p_of_uint32_p output m l =
  if U32 (l >^ 0ul) then
    begin
    let rem = U32 (l %^ 4ul) in
    if U32 (rem >^ 0ul) then
      begin
      let l = U32 (l -^ rem) in
      let x = m.(U32 (l /^ 4ul)) in
      let b0 = sint32_to_sint8 (x &^ (uint32_to_sint32 255ul)) in
      output.(l) <- b0;
      if U32 (rem >^ 1ul) then
        begin
        let b1 = sint32_to_sint8 ((x >>^ 8ul) &^ (uint32_to_sint32 255ul)) in
        output.(U32 (l +^ 1ul)) <- b1;
	if U32 (rem >^ 2ul) then
	  begin
	  let b2 = sint32_to_sint8 ((x >>^ 16ul) &^ (uint32_to_sint32 255ul)) in
	  output.(U32 (l +^ 2ul)) <- b2
          end
	else ()
	end
      else ();
      uint8_p_of_uint32_p output m l
      end
    else
      begin
      let l = U32 (l -^ 4ul) in
      let x = m.(U32 (l /^ 4ul)) in
      let b0 = sint32_to_sint8 (x &^ (uint32_to_sint32 255ul)) in
      let b1 = sint32_to_sint8 ((x >>^ 8ul) &^ (uint32_to_sint32 255ul)) in
      let b2 = sint32_to_sint8 ((x >>^ 16ul) &^ (uint32_to_sint32 255ul)) in
      let b3 = sint32_to_sint8 ((x >>^ 24ul) &^ (uint32_to_sint32 255ul)) in
      output.(l) <- b0;
      output.(U32 (l +^ 1ul)) <- b1;
      output.(U32 (l +^ 2ul)) <- b2;
      output.(U32 (l +^ 3ul)) <- b3;
      uint8_p_of_uint32_p output m l
      end
    end

val xor_uint8_p_2: output:uint8_p -> in1:uint8_p{disjoint in1 output} ->
  len:u32{FStar.UInt32.v len <= length output /\ FStar.UInt32.v len <= length in1} -> STL unit
  (requires (fun h -> live h output /\ live h in1))
  (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 in1 /\ live h1 output /\ live h1 in1
    /\ modifies_1 output h0 h1 ))
let rec xor_uint8_p_2 output in1 len =
  if len =^ 0ul then ()
  else
    begin
      let i    = U32 (len -^ 1ul) in
      let in1i = in1.(i) in
      let oi   = output.(i) in
      let oi   = H8 (in1i ^^ oi) in
      output.(i) <- oi;
      xor_uint8_p_2 output in1 i
    end

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
  let k0 = sub key 0ul  4ul in
  let k1 = sub key 4ul  4ul in
  let k2 = sub key 8ul  4ul in
  let k3 = sub key 12ul 4ul in
  let k4 = sub key 16ul 4ul in
  let k5 = sub key 20ul 4ul in
  let k6 = sub key 24ul 4ul in
  let k7 = sub key 28ul 4ul in
  let k0 =  (h32_of_uint8_p k0) in
  let k1 =  (h32_of_uint8_p k1) in
  let k2 =  (h32_of_uint8_p k2) in
  let k3 =  (h32_of_uint8_p k3) in
  let k4 =  (h32_of_uint8_p k4) in
  let k5 =  (h32_of_uint8_p k5) in
  let k6 =  (h32_of_uint8_p k6) in
  let k7 =  (h32_of_uint8_p k7) in
  (* Nonce part *)
  let n0 = sub nonce 0ul 4ul in
  let n1 = sub nonce 4ul 4ul in
  let n0 =  (h32_of_uint8_p n0) in
  let n1 =  (h32_of_uint8_p n1) in
  let h0 = HST.get() in
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
  (* Block counter part *)
  let c0 = sint64_to_sint32 counter in
  let c1 = sint64_to_sint32 (H64 (counter >>^ 32ul)) in
  state.(8ul) <- c0;
  state.(9ul) <- c1;
  let h1 = HST.get() in
  assert(modifies_1 state h0 h1);
  assert(live h1 state)

val sum_matrixes: new_state:uint32_p{length new_state >= 16} -> old_state:uint32_p{length old_state >= 16 /\ disjoint new_state old_state} -> STL unit
  (requires (fun h -> live h new_state /\ live h old_state))
  (ensures (fun h0 _ h1 -> live h1 new_state /\ modifies_1 new_state h0 h1))
let sum_matrixes m m0 =
  let h0 = HST.get() in
  m.(0ul) <- (m.(0ul) +%^ m0.(0ul));
  m.(1ul) <- (m.(1ul) +%^ m0.(1ul));
  m.(2ul) <- (m.(2ul) +%^ m0.(2ul));
  m.(3ul) <- (m.(3ul) +%^ m0.(3ul));
  m.(4ul) <- (m.(4ul) +%^ m0.(4ul));
  m.(5ul) <- (m.(5ul) +%^ m0.(5ul));
  m.(6ul) <- (m.(6ul) +%^ m0.(6ul));
  m.(7ul) <- (m.(7ul) +%^ m0.(7ul));
  m.(8ul) <- (m.(8ul) +%^ m0.(8ul));
  m.(9ul) <- (m.(9ul) +%^ m0.(9ul));
  m.(10ul) <- (m.(10ul) +%^ m0.(10ul));
  m.(11ul) <- (m.(11ul) +%^ m0.(11ul));
  m.(12ul) <- (m.(12ul) +%^ m0.(12ul));
  m.(13ul) <- (m.(13ul) +%^ m0.(13ul));
  m.(14ul) <- (m.(14ul) +%^ m0.(14ul));
  m.(15ul) <- (m.(15ul) +%^ m0.(15ul));
  let h1 = HST.get() in
  assert(modifies_1 m h0 h1);
  assert(live h1 m)

val salsa20_core: output:uint8_p ->
  state:uint32_p{length state >= 32 /\ disjoint state output} ->
  key:uint8_p{length key = 32 /\ disjoint state key /\ disjoint output key} ->
  counter:h64 ->
  nonce:uint8_p{length nonce = 8 /\ disjoint state nonce /\ disjoint output nonce} ->
  len:u32{FStar.UInt32.v len <= 64 /\ length output >= FStar.UInt32.v len} ->
  Stack unit
    (requires (fun h -> live h state /\ live h output /\ live h key /\ live h nonce))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h1 state /\ modifies_2 output state h0 h1 ))
let salsa20_core output state key counter nonce len =
  let h0 = HST.get() in
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
  let h1 = HST.get() in
  assert(modifies_1 state h0 h1);
  uint8_p_of_uint32_p output m len;
  let h2 = HST.get() in
  cut(live h2 output);
  cut(modifies_2 output state h0 h2);
  cut(live h2 state)

val salsa20_encrypt_loop:
  state:uint32_p{length state >= 32} ->
  key:uint8_p{length key = 32 /\ disjoint state key} ->
  counter:h64 ->
  nonce:uint8_p{length nonce = 12 /\ disjoint state nonce} ->
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

val salsa20_encrypt_body:
  state:uint32_p{length state = 32} ->
  ciphertext:uint8_p{disjoint state ciphertext} ->
  key:uint8_p{length key = 32 /\ disjoint ciphertext key /\ disjoint key state} ->
  counter:h64 ->
  nonce:uint8_p{length nonce = 12 /\ disjoint ciphertext nonce /\ disjoint state nonce} ->
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
