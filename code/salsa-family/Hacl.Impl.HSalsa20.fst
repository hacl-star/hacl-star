module Hacl.Impl.HSalsa20

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open Hacl.UInt32
open Hacl.Cast
open Spec.HSalsa20
open Hacl.Spec.Endianness
open Hacl.Lib.LoadStore32
open Hacl.Lib.Create


module Salsa20 = Spec.Salsa20


let h32     = Hacl.UInt32.t
let u32     = FStar.UInt32.t
let uint8_p = buffer Hacl.UInt8.t
let state   = b:buffer h32{length b = 16}

#reset-options "--max_fuel 0 --z3rlimit 100"

[@ CInline]
val setup:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 16 /\ disjoint st n} ->
  Stack unit
    (requires (fun h -> live h st /\ live h k /\ live h n))
    (ensures (fun h0 _ h1 -> live h0 k /\ live h0 n /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = reveal_h32s (as_seq h1 st) in
         let k = reveal_sbytes (as_seq h0 k) in
         let n = reveal_sbytes (as_seq h0 n) in
         s == setup k n)))
[@ CInline]
let setup st k n =
  let h0 = ST.get() in
  push_frame();
  let tmp = Buffer.create (uint32_to_sint32 0ul) 12ul in
  let k'  = Buffer.sub tmp 0ul 8ul in
  let n'  = Buffer.sub tmp 8ul 4ul in
  uint32s_from_le_bytes k' k 8ul;
  uint32s_from_le_bytes n' n 4ul;
  let k0 = k'.(0ul) in
  let k1 = k'.(1ul) in
  let k2 = k'.(2ul) in
  let k3 = k'.(3ul) in
  let k4 = k'.(4ul) in
  let k5 = k'.(5ul) in
  let k6 = k'.(6ul) in
  let k7 = k'.(7ul) in
  let n0 = n'.(0ul) in
  let n1 = n'.(1ul) in
  let n2 = n'.(2ul) in
  let n3 = n'.(3ul) in
  let h0 = ST.get() in
  make_h32_16 st (uint32_to_sint32 Salsa20.constant0) k0 k1 k2 k3 (uint32_to_sint32 Salsa20.constant1) n0 n1 n2 n3
               (uint32_to_sint32 Salsa20.constant2) k4 k5 k6 k7 (uint32_to_sint32 Salsa20.constant3);
  pop_frame()


#reset-options "--max_fuel 0 --z3rlimit 100"

let op_String_Access h (b:uint8_p{live h b}) = reveal_sbytes (as_seq h b)

val crypto_core_hsalsa20:
  output:uint8_p{length output = 32} ->
  nonce:uint8_p{length nonce = 16} ->
  key:uint8_p{length key = 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h nonce /\ live h key))
    (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 nonce /\ live h0 key /\
      modifies_1 output h0 h1 /\ live h1 output
      /\ (h1.[output] == hsalsa20 h0.[key] h0.[nonce])))
let crypto_core_hsalsa20 output nonce key =
  push_frame();
  let tmp = create (uint32_to_sint32 0ul) 24ul in
  let st  = Buffer.sub tmp 0ul 16ul in
  let hs  = Buffer.sub tmp 16ul 8ul in
  setup st key nonce;
  Hacl.Impl.Salsa20.rounds st;
  let hs0 = st.(0ul) in
  let hs1 = st.(5ul) in
  let hs2 = st.(10ul) in
  let hs3 = st.(15ul) in
  let hs4 = st.(6ul) in
  let hs5 = st.(7ul) in
  let hs6 = st.(8ul) in
  let hs7 = st.(9ul) in
  make_h32_8 hs hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7;
  uint32s_to_le_bytes output hs 8ul;
  pop_frame()
