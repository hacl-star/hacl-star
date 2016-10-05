module Hacl.Symmetric.Chacha20

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

(* This HAS to go in some more appropriate place *)
assume MaxUInt32: pow2 32 = 4294967296

(* Public machine integer types *)
let u32 = U32.t
let u8  = U8.t
(* Secret machine integer types *)
let s32 = H32.t
let s8  = H8.t

let u8s = buffer H8.t
let u32s = buffer H32.t
let bytes = u8s

(* 'Rotate' operators, to inline *)
let op_Greater_Greater_Greater (a:s32) (s:u32{FStar.UInt32.v s <= 32}) : Tot s32 =
  let (m:u32{FStar.UInt32.v m = 32}) = 32ul in
  (a >>^ s) |^ (a <<^ (U32 (m -^ s)))
let op_Less_Less_Less (a:s32) (s:u32{FStar.UInt32.v s <= 32}) : Tot s32 =
  let (m:u32{FStar.UInt32.v m = 32}) = 32ul in  
  (a <<^ s) |^ (a >>^ (U32 (m -^ s)))

(* Chacha 20 code *)
val quarter_round: m:u32s{length m = 16} -> 
  a:u32{FStar.UInt32.v a < 16} -> b:u32{FStar.UInt32.v b<16} -> c:u32{FStar.UInt32.v c<16} -> d:u32{FStar.UInt32.v d<16} -> STL unit 
  (requires (fun h -> live h m)) 
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))
let quarter_round m a b c d =
  m.(a) <- (m.(a) +%^ m.(b));
  m.(d) <- (m.(d) ^^ m.(a));
  let tmp = m.(d) in 
  m.(d) <- (tmp <<< 16ul);
  m.(c) <- (m.(c) +%^ m.(d)); 
  m.(b) <- (m.(b) ^^ m.(c));
  let tmp = m.(b) in
  m.(b) <- (tmp <<< 12ul);
  m.(a) <- (m.(a) +%^ m.(b)); 
  m.(d) <- (m.(d) ^^ m.(a)); 
  let tmp = m.(d) in
  m.(d) <- (tmp <<< 8ul);
  m.(c) <- (m.(c) +%^ m.(d)); 
  m.(b) <- (m.(b) ^^ m.(c)); 
  let tmp = m.(b) in
  m.(b) <- (tmp <<< 7ul)

(* Chacha20 block function *)
val column_round: m:u32s{length m = 16} -> STL unit
    (requires (fun h -> live h m))
    (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1 ))
let column_round m =
  quarter_round m 0ul 4ul 8ul 12ul;
  quarter_round m 1ul 5ul 9ul 13ul;
  quarter_round m 2ul 6ul 10ul 14ul;
  quarter_round m 3ul 7ul 11ul 15ul

val diagonal_round: m:u32s{length m = 16} -> STL unit
    (requires (fun h -> live h m))
    (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1 ))
let diagonal_round m =
  quarter_round m 0ul 5ul 10ul 15ul;
  quarter_round m 1ul 6ul 11ul 12ul;
  quarter_round m 2ul 7ul 8ul 13ul;
  quarter_round m 3ul 4ul 9ul 14ul

val s32_of_bytes: b:bytes{length b >= 4} -> STL s32
  (requires (fun h -> live h b))
  (ensures (fun h0 r h1 -> h0 == h1 /\ live h0 b))
let s32_of_bytes (b:bytes{length b >= 4}) =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let r = (sint8_to_sint32 b3 <<^ 24ul)
	  +%^ (sint8_to_sint32 b2 <<^ 16ul)
	  +%^ (sint8_to_sint32 b1 <<^ 8ul)
	  +%^ sint8_to_sint32 b0 in
  r

val bytes_of_u32s: output:bytes -> m:u32s{disjoint output m} -> len:u32{FStar.UInt32.v len <=length output /\ FStar.UInt32.v len<=op_Multiply 4 (length m)} -> STL unit
  (requires (fun h -> live h output /\ live h m))
  (ensures (fun h0 _ h1 -> live h0 output /\ live h0 m /\ live h1 output /\ live h1 m
    /\ modifies_1 output h0 h1 ))
let rec bytes_of_u32s output m l =
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
      bytes_of_u32s output m l
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
      bytes_of_u32s output m l
      end
    end

val xor_bytes_2: output:bytes -> in1:bytes{disjoint in1 output} -> 
  len:u32{FStar.UInt32.v len <= length output /\ FStar.UInt32.v len <= length in1} -> STL unit
  (requires (fun h -> live h output /\ live h in1))
  (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 in1 /\ live h1 output /\ live h1 in1
    /\ modifies_1 output h0 h1 ))
let rec xor_bytes_2 output in1 len =
  if len =^ 0ul then ()
  else
    begin
      let i    = U32 (len -^ 1ul) in
      let in1i = in1.(i) in
      let oi   = output.(i) in
      let oi   = H8 (in1i ^^ oi) in
      output.(i) <- oi;
      xor_bytes_2 output in1 i
    end

val initialize_state: state:u32s{length state >= 16} -> 
  key:bytes{length key = 32 /\ disjoint state key} -> counter:s32 -> 
  nonce:bytes{length nonce = 12 /\ disjoint state nonce} -> STL unit
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
  let k0 =  (s32_of_bytes k0) in
  let k1 =  (s32_of_bytes k1) in 
  let k2 =  (s32_of_bytes k2) in 
  let k3 =  (s32_of_bytes k3) in 
  let k4 =  (s32_of_bytes k4) in
  let k5 =  (s32_of_bytes k5) in
  let k6 =  (s32_of_bytes k6) in
  let k7 =  (s32_of_bytes k7) in
  (* Nonce part *)
  let n0 = sub nonce 0ul 4ul in 
  let n1 = sub nonce 4ul 4ul in 
  let n2 = sub nonce 8ul 4ul in
  let n0 =  (s32_of_bytes n0) in
  let n1 =  (s32_of_bytes n1) in
  let n2 =  (s32_of_bytes n2) in
  let h0 = HST.get() in
  (* Constant part *)
  state.(0ul) <- (uint32_to_sint32 0x61707865ul);
  state.(1ul) <- (uint32_to_sint32 0x3320646eul);
  state.(2ul) <- (uint32_to_sint32 0x79622d32ul);
  state.(3ul) <- (uint32_to_sint32 0x6b206574ul);
  (* Update with key *)
  state.(4ul) <-  (k0);
  state.(5ul) <-  (k1); 
  state.(6ul) <-  (k2); 
  state.(7ul) <-  (k3); 
  state.(8ul) <-  (k4);
  state.(9ul) <-  (k5);
  state.(10ul) <- (k6);
  state.(11ul) <- (k7);
  (* Block counter part *)
  state.(12ul) <- counter;
  (* Update with nonces *)
  state.(13ul) <- (n0);
  state.(14ul) <- (n1);
  state.(15ul) <- (n2);
  let h1 = HST.get() in
  assert(modifies_1 state h0 h1);
  assert(live h1 state)

val sum_matrixes: new_state:u32s{length new_state >= 16} -> old_state:u32s{length old_state >= 16 /\ disjoint new_state old_state} -> STL unit
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

val chacha20_block: output:bytes -> 
  state:u32s{length state >= 32 /\ disjoint state output} ->
  key:bytes{length key = 32 /\ disjoint state key /\ disjoint output key} -> counter:s32 -> 
  nonce:bytes{length nonce = 12 /\ disjoint state nonce /\ disjoint output nonce} ->
  len:u32{FStar.UInt32.v len <= 64 /\ length output >= FStar.UInt32.v len} ->
  STL unit
    (requires (fun h -> live h state /\ live h output /\ live h key /\ live h nonce))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h1 state /\ modifies_2 output state h0 h1 ))
let chacha20_block output state key counter nonce len =
  let h0 = HST.get() in
  (* Initialize internal state *)
  let m = sub state 0ul 16ul in
  let m0 = sub state 16ul 16ul in
  initialize_state m key counter nonce;
  (* Initial state *) 
  blit m 0ul m0 0ul 16ul;
  (* 20 rounds *)
  column_round m; diagonal_round m; 
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  (* Sum the matrixes *)
  sum_matrixes m m0;
  (* Serialize the state into byte stream *)
  let h1 = HST.get() in
  assert(modifies_1 state h0 h1);
  bytes_of_u32s output m len;
  let h2 = HST.get() in
  cut(live h2 output);
  cut(modifies_2 output state h0 h2);
  cut(live h2 state)

val chacha20_encrypt_loop: 
  state:u32s{length state >= 32} -> key:bytes{length key = 32 /\ disjoint state key} -> 
  counter:s32 -> nonce:bytes{length nonce = 12 /\ disjoint state nonce (* /\ disjoint key nonce *)} -> 
  plaintext:bytes{disjoint state plaintext (* /\ disjoint key plaintext /\ disjoint nonce plaintext *)} -> 
  ciphertext:bytes{disjoint state ciphertext /\ disjoint key ciphertext /\ disjoint nonce ciphertext /\ disjoint plaintext ciphertext} -> j:u32 -> max:u32{FStar.UInt32.v j <= FStar.UInt32.v max /\ Hacl.UInt32.v counter + FStar.UInt32.v max < pow2 n} ->
  STL unit
    (requires (fun h -> live h state /\ live h key /\ live h nonce /\ live h plaintext  /\ live h ciphertext
      /\ length plaintext >= (FStar.UInt32.v max-FStar.UInt32.v j) * 64  /\ length ciphertext >= (FStar.UInt32.v max-FStar.UInt32.v j) * 64 ))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 state /\ modifies_2 ciphertext state h0 h1 ))
let rec chacha20_encrypt_loop state key counter nonce plaintext ciphertext j max =
  if j =^ max then ()
  else 
    begin
      (* Generate new state for block *)
      let cipher_block = sub ciphertext 0ul 64ul in
      let ciphertext' = sub ciphertext 64ul (U32 (64ul *^ (max -^ j -^ 1ul))) in
      let plain_block = sub plaintext 0ul 64ul in
      let plaintext' = sub plaintext 64ul (U32 (64ul *^ (max -^ j -^ 1ul))) in
      chacha20_block cipher_block state key (counter +^ (uint32_to_sint32 j)) nonce 64ul;
      (* XOR the key stream with the plaintext *)
      xor_bytes_2 cipher_block plain_block 64ul;
      (* Apply Chacha20 to the next blocks *)
      chacha20_encrypt_loop state key counter nonce plaintext' ciphertext' (U32 (j +^ 1ul)) max
    end

val chacha20_encrypt_body: 
  state:u32s{length state = 32} ->
  ciphertext:bytes{disjoint state ciphertext} -> 
  key:bytes{length key = 32 /\ disjoint ciphertext key /\ disjoint key state} -> 
  counter:s32 -> 
  nonce:bytes{length nonce = 12 /\ disjoint ciphertext nonce /\ disjoint state nonce (* /\ disjoint key nonce *)} -> 
  plaintext:bytes{disjoint ciphertext plaintext /\ disjoint state plaintext} -> 
  len:u32{length ciphertext >= FStar.UInt32.v len /\ length plaintext >= FStar.UInt32.v len /\ Hacl.UInt32.v counter + FStar.UInt32.v len / 64 < pow2 32} -> STL unit
    (requires (fun h -> live h state /\ live h ciphertext /\ live h key /\ live h nonce /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 state /\ modifies_2 ciphertext state h0 h1))
let chacha20_encrypt_body state ciphertext key counter nonce plaintext len =
  let max = U32 (len /^ 64ul) in
  let rem = U32 (len %^ 64ul) in
  (* Apply Chacha20 max times **)  
  chacha20_encrypt_loop state key counter nonce plaintext ciphertext 0ul max;
  if rem =^ 0ul then ()
  else 
    begin 
      let cipher_block = sub ciphertext (U32 (64ul *^ max)) rem in 
      let plain_block = sub plaintext (U32 (64ul *^ max)) rem in 
      let h = HST.get() in
      chacha20_block cipher_block state key (counter +^ (uint32_to_sint32 max)) nonce rem;
      xor_bytes_2 cipher_block plain_block rem
    end

val chacha20_encrypt: 
  ciphertext:bytes -> key:bytes{length key = 32 /\ disjoint ciphertext key} -> counter:s32 -> 
  nonce:bytes{length nonce = 12 /\ disjoint ciphertext nonce /\ disjoint key nonce} -> 
  plaintext:bytes{disjoint ciphertext plaintext /\ disjoint key plaintext /\ disjoint nonce plaintext} -> 
  len:u32{length ciphertext >= FStar.UInt32.v len /\ length plaintext >= FStar.UInt32.v len /\ v counter + FStar.UInt32.v len / 64 < pow2 32} -> STL unit
    (requires (fun h -> live h ciphertext /\ live h key /\ live h nonce /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ modifies_1 ciphertext h0 h1))
let chacha20_encrypt ciphertext key counter nonce plaintext len = 
  push_frame ();
  let state = create (uint32_to_sint32 0ul) 32ul in
  (* Compute number of iterations *)
  chacha20_encrypt_body state ciphertext key counter nonce plaintext len;
  pop_frame()
