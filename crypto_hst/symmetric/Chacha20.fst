module Chacha20

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open FStar.UInt32
open Hacl.UInt8
open Hacl.UInt32
open Hacl.Cast
open Hacl.SBuffer

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

#reset-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3timeout 50"

(* Public machine integer types *)
let u32 = FStar.UInt32.t
let u8 = FStar.UInt8.t

(* Secret machine integer types *)
let s32 = Hacl.UInt32.t
let s8 = Hacl.UInt8.t
let bytes = u8s

(* Operators on u32 *)
let op_Bar_Plus = UInt32.add
let op_Bar_Subtraction = UInt32.sub
let op_Bar_Star = UInt32.mul
let op_Bar_Percent = UInt32.rem
let op_Bar_Slash = UInt32.div

(* 'Rotate' operators, to inline *)
let op_Greater_Greater_Greater (a:s32) (s:u32{FStar.UInt32.v s <= 32}) : Tot s32 =
  let (m:u32{FStar.UInt32.v m = 32}) = 32ul in
  (op_Greater_Greater_Hat a s) |^ (a <<^ (m |- s))
let op_Less_Less_Less (a:s32) (s:u32{FStar.UInt32.v s <= 32}) : Tot s32 =
  let (m:u32{FStar.UInt32.v m = 32}) = 32ul in  
  (op_Less_Less_Hat a s) |^ (op_Greater_Greater_Hat a (m |- s))

(* Chacha 20 code *)
val quarter_round: m:u32s{length m = 16} -> 
  a:u32{FStar.UInt32.v a < 16} -> b:u32{FStar.UInt32.v b<16} -> c:u32{FStar.UInt32.v c<16} -> d:u32{FStar.UInt32.v d<16} -> STL unit 
  (requires (fun h -> live h m)) 
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))
let quarter_round m a b c d =
  upd m a (index m a +%^ index m b);
  upd m d (index m d ^^ index m a);
  let tmp = index m d in 
  upd m d (tmp <<< UInt32.uint_to_t 16);
  upd m c (index m c +%^ index m d); 
  upd m b (index m b ^^ index m c);
  let tmp = index m b in
  upd m b (tmp <<< UInt32.uint_to_t 12);
  upd m a (index m a +%^ index m b); 
  upd m d (index m d ^^ index m a); 
  let tmp = index m d in
  upd m d (tmp <<< UInt32.uint_to_t 8);
  upd m c (index m c +%^ index m d); 
  upd m b (index m b ^^ index m c); 
  let tmp = index m b in
  upd m b (tmp <<< UInt32.uint_to_t 7)

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
  let b0 = (index b 0ul) in
  let b1 = (index b 1ul) in
  let b2 = (index b 2ul) in
  let b3 = (index b 3ul) in
  let r = (op_Less_Less_Hat (sint8_to_sint32 b3) 24ul)
	+%^ (op_Less_Less_Hat (sint8_to_sint32 b2) 16ul)
	+%^ (op_Less_Less_Hat (sint8_to_sint32 b1) 8ul)
	+%^ sint8_to_sint32 b0 in
  r

let op_Hat_Greater_Greater: a:s32 -> s:u32 -> Pure s32
  (requires True)
  (ensures (fun c -> v c = v a / (pow2 (FStar.UInt32.v s))))
  = op_Greater_Greater_Hat

val bytes_of_u32s: output:bytes -> m:u32s{disjoint output m} -> len:u32{FStar.UInt32.v len <=length output /\ FStar.UInt32.v len<=op_Multiply 4 (length m)} -> STL unit
  (requires (fun h -> live h output /\ live h m))
  (ensures (fun h0 _ h1 -> live h0 output /\ live h0 m /\ live h1 output /\ live h1 m
    /\ modifies_1 output h0 h1 ))
let rec bytes_of_u32s output m l =
  if UInt32.gt l 0ul then
    begin
    let rem = l |% 4ul in
    if UInt32.gt rem 0ul then
      begin
      let l = l |- rem in
      let x = index m (l |/ 4ul) in
      let b0 = sint32_to_sint8 (x &^ (uint32_to_sint32 255ul)) in
      upd output l b0;
      if UInt32.gt rem 1ul then
        begin
        let b1 = sint32_to_sint8 ((x ^>> 8ul) &^ (uint32_to_sint32 255ul)) in
        upd output (l |+ 1ul) b1;
	if UInt32.gt rem 2ul then
	  begin
	  let b2 = sint32_to_sint8 ((x ^>> 16ul) &^ (uint32_to_sint32 255ul)) in
	  upd output (l |+ 2ul) b2
          end
	else ()
	end
      else ();
      bytes_of_u32s output m l
      end
    else
      begin
      let l = l |- 4ul in
      let x = index m (l |/ 4ul) in
      let b0 = sint32_to_sint8 (x &^ (uint32_to_sint32 255ul)) in
      let b1 = sint32_to_sint8 ((x ^>> 8ul) &^ (uint32_to_sint32 255ul)) in
      let b2 = sint32_to_sint8 ((x ^>> 16ul) &^ (uint32_to_sint32 255ul)) in
      let b3 = sint32_to_sint8 ((x ^>> 24ul) &^ (uint32_to_sint32 255ul)) in
      upd output l b0;
      upd output (l |+ 1ul) b1;
      upd output (l |+ 2ul) b2;
      upd output (l |+ 3ul) b3;
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
      let i    = len |- 1ul in
      let in1i = index in1 i in
      let oi   = index output i in
      let oi   = Hacl.UInt8.logxor in1i oi in
      upd output i oi;
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
  upd state 0ul (uint32_to_sint32 0x61707865ul);
  upd state 1ul (uint32_to_sint32 0x3320646eul);
  upd state 2ul (uint32_to_sint32 0x79622d32ul);
  upd state 3ul (uint32_to_sint32 0x6b206574ul);
  (* Update with key *)
  upd state 4ul  (k0);
  upd state 5ul  (k1); 
  upd state 6ul  (k2); 
  upd state 7ul  (k3); 
  upd state 8ul  (k4);
  upd state 9ul  (k5);
  upd state 10ul (k6);
  upd state 11ul (k7);
  (* Block counter part *)
  upd state 12ul counter;
  (* Update with nonces *)
  upd state 13ul (n0);
  upd state 14ul (n1);
  upd state 15ul (n2);
  let h1 = HST.get() in
  assert(modifies_1 state h0 h1);
  assert(live h1 state)

val sum_matrixes: new_state:u32s{length new_state >= 16} -> old_state:u32s{length old_state >= 16 /\ disjoint new_state old_state} -> STL unit
  (requires (fun h -> live h new_state /\ live h old_state))
  (ensures (fun h0 _ h1 -> live h1 new_state /\ modifies_1 new_state h0 h1))
let sum_matrixes m m0 =
  let h0 = HST.get() in
  upd m 0ul (index m 0ul +%^ index m0 0ul);
  upd m 1ul (index m 1ul +%^ index m0 1ul);
  upd m 2ul (index m 2ul +%^ index m0 2ul);
  upd m 3ul (index m 3ul +%^ index m0 3ul);
  upd m 4ul (index m 4ul +%^ index m0 4ul);
  upd m 5ul (index m 5ul +%^ index m0 5ul);
  upd m 6ul (index m 6ul +%^ index m0 6ul);
  upd m 7ul (index m 7ul +%^ index m0 7ul); 
  upd m 8ul (index m 8ul +%^ index m0 8ul);
  upd m 9ul (index m 9ul +%^ index m0 9ul); 
  upd m 10ul (index m 10ul +%^ index m0 10ul);
  upd m 11ul (index m 11ul +%^ index m0 11ul);
  upd m 12ul (index m 12ul +%^ index m0 12ul);
  upd m 13ul (index m 13ul +%^ index m0 13ul);
  upd m 14ul (index m 14ul +%^ index m0 14ul);
  upd m 15ul (index m 15ul +%^ index m0 15ul);
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
      let ciphertext' = sub ciphertext 64ul (64ul |* (max |- j |- 1ul)) in
      let plain_block = sub plaintext 0ul 64ul in
      let plaintext' = sub plaintext 64ul (64ul |* (max |- j |- 1ul)) in
      chacha20_block cipher_block state key (counter +^ (uint32_to_sint32 j)) nonce 64ul;
      (* XOR the key stream with the plaintext *)
      xor_bytes_2 cipher_block plain_block 64ul;
      (* Apply Chacha20 to the next blocks *)
      chacha20_encrypt_loop state key counter nonce plaintext' ciphertext' (j |+ 1ul) max
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
  let max = (len |/ 64ul) in
  let rem = len |% 64ul in
  (* Apply Chacha20 max times **)  
  chacha20_encrypt_loop state key counter nonce plaintext ciphertext 0ul max;
  if rem =^ 0ul then ()
  else 
    begin 
      let cipher_block = sub ciphertext (64ul |* max) rem in 
      let plain_block = sub plaintext (64ul |* max) rem in 
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
