module Hacl.Symmetric.HSalsa20


open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.UInt32
open Hacl.Cast


let h32 = Hacl.UInt32.t
let u32 = FStar.UInt32.t
let uint8_p = buffer Hacl.UInt8.t


#reset-options "--initial_fuel 0 --max_fuel 0"

private val lemma_max_uint32: n:nat -> Lemma
  (requires (n = 32))
  (ensures  (pow2 n = 4294967296))
  [SMTPat (pow2 n)]
let lemma_max_uint32 n = assert_norm(pow2 32 = 4294967296)
private val lemma_max_uint64: n:nat -> Lemma
  (requires (n = 64))
  (ensures  (pow2 n = 18446744073709551616))
  [SMTPat (pow2 n)]
let lemma_max_uint64 n = assert_norm(pow2 64 = 18446744073709551616)


let rotate (a:h32) (s:u32{FStar.UInt32.v s <= 32}) : Tot h32 =
  (a <<^ s) |^ (a >>^ (FStar.UInt32.(32ul -^ s)))


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

let load32_le (k:uint8_p) : Stack h32
  (requires (fun h -> live h k /\ length k >= 4))
  (ensures  (fun h0 _ h1 -> h0 == h1))
  = let k0 = k.(0ul) in
    let k1 = k.(1ul) in
    let k2 = k.(2ul) in
    let k3 = k.(3ul) in
    let z = sint8_to_sint32 k0
            |^ (sint8_to_sint32 k1 <<^ 8ul)
            |^ (sint8_to_sint32 k2 <<^ 16ul)
            |^ (sint8_to_sint32 k3 <<^ 24ul) in
    z

let store32_le (k:uint8_p) (x:h32) : Stack unit
  (requires (fun h -> live h k /\ length k >= 4))
  (ensures  (fun h0 _ h1 -> modifies_1 k h0 h1 /\ live h1 k))
  = k.(0ul) <- sint32_to_sint8 x;
    k.(1ul) <- sint32_to_sint8 (x >>^ 8ul);
    k.(2ul) <- sint32_to_sint8 (x >>^ 16ul);
    k.(3ul) <- sint32_to_sint8 (x >>^ 24ul)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 1000"

val crypto_core_hsalsa20:
  output:uint8_p{length output = 32} ->
  input:uint8_p{length input = 16} ->
  key:uint8_p{length key = 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h key))
    (ensures  (fun h0 _ h1 -> modifies_1 output h0 h1 /\ live h1 output))
let crypto_core_hsalsa20 output input key =
  let x0 = uint32_to_sint32 0x61707865ul in
  let x5 = uint32_to_sint32 0x3320646eul in
  let x10 = uint32_to_sint32 0x79622d32ul in
  let x15 = uint32_to_sint32 0x6b206574ul in
  let x1 = load32_le(offset key 0ul) in
  let x2 = load32_le(offset key 4ul) in
  let x3 = load32_le(offset key 8ul) in
  let x4 = load32_le(offset key 12ul) in
  let x11 = load32_le(offset key 16ul) in
  let x12 = load32_le(offset key 20ul) in
  let x13 = load32_le(offset key 24ul) in
  let x14 = load32_le(offset key 28ul) in
  let x6 = load32_le(offset input 0ul) in
  let x7 = load32_le(offset input 4ul) in
  let x8 = load32_le(offset input 8ul) in
  let x9 = load32_le(offset input 12ul) in
  (* *)
  let x4 = x4 ^^ rotate( x0+%^x12)  7ul in
  let x8 = x8 ^^ rotate( x4+%^ x0)  9ul in
  let x12 = x12 ^^ rotate( x8+%^ x4) 13ul in
  let x0 = x0 ^^ rotate(x12+%^ x8) 18ul in
  let x9 = x9 ^^ rotate( x5+%^ x1)  7ul in
  let x13 = x13 ^^ rotate( x9+%^ x5)  9ul in
  let x1 = x1 ^^ rotate(x13+%^ x9) 13ul in
  let x5 = x5 ^^ rotate( x1+%^x13) 18ul in
  let x14 = x14 ^^ rotate(x10+%^ x6)  7ul in
  let x2 = x2 ^^ rotate(x14+%^x10)  9ul in
  let x6 = x6 ^^ rotate( x2+%^x14) 13ul in
  let x10 = x10 ^^ rotate( x6+%^ x2) 18ul in
  let x3 = x3 ^^ rotate(x15+%^x11)  7ul in
  let x7 = x7 ^^ rotate( x3+%^x15)  9ul in
  let x11 = x11 ^^ rotate( x7+%^ x3) 13ul in
  let x15 = x15 ^^ rotate(x11+%^ x7) 18ul in
  let x1 = x1 ^^ rotate( x0+%^ x3)  7ul in
  let x2 = x2 ^^ rotate( x1+%^ x0)  9ul in
  let x3 = x3 ^^ rotate( x2+%^ x1) 13ul in
  let x0 = x0 ^^ rotate( x3+%^ x2) 18ul in
  let x6 = x6 ^^ rotate( x5+%^ x4)  7ul in
  let x7 = x7 ^^ rotate( x6+%^ x5)  9ul in
  let x4 = x4 ^^ rotate( x7+%^ x6) 13ul in
  let x5 = x5 ^^ rotate( x4+%^ x7) 18ul in
  let x11 = x11 ^^ rotate(x10+%^ x9)  7ul in
  let x8 = x8 ^^ rotate(x11+%^x10)  9ul in
  let x9 = x9 ^^ rotate( x8+%^x11) 13ul in
  let x10 = x10 ^^ rotate( x9+%^ x8) 18ul in
  let x12 = x12 ^^ rotate(x15+%^x14)  7ul in
  let x13 = x13 ^^ rotate(x12+%^x15)  9ul in
  let x14 = x14 ^^ rotate(x13+%^x12) 13ul in
  let x15 = x15 ^^ rotate(x14+%^x13) 18ul in
  (* *)
  let x4 = x4 ^^ rotate( x0+%^x12)  7ul in
  let x8 = x8 ^^ rotate( x4+%^ x0)  9ul in
  let x12 = x12 ^^ rotate( x8+%^ x4) 13ul in
  let x0 = x0 ^^ rotate(x12+%^ x8) 18ul in
  let x9 = x9 ^^ rotate( x5+%^ x1)  7ul in
  let x13 = x13 ^^ rotate( x9+%^ x5)  9ul in
  let x1 = x1 ^^ rotate(x13+%^ x9) 13ul in
  let x5 = x5 ^^ rotate( x1+%^x13) 18ul in
  let x14 = x14 ^^ rotate(x10+%^ x6)  7ul in
  let x2 = x2 ^^ rotate(x14+%^x10)  9ul in
  let x6 = x6 ^^ rotate( x2+%^x14) 13ul in
  let x10 = x10 ^^ rotate( x6+%^ x2) 18ul in
  let x3 = x3 ^^ rotate(x15+%^x11)  7ul in
  let x7 = x7 ^^ rotate( x3+%^x15)  9ul in
  let x11 = x11 ^^ rotate( x7+%^ x3) 13ul in
  let x15 = x15 ^^ rotate(x11+%^ x7) 18ul in
  let x1 = x1 ^^ rotate( x0+%^ x3)  7ul in
  let x2 = x2 ^^ rotate( x1+%^ x0)  9ul in
  let x3 = x3 ^^ rotate( x2+%^ x1) 13ul in
  let x0 = x0 ^^ rotate( x3+%^ x2) 18ul in
  let x6 = x6 ^^ rotate( x5+%^ x4)  7ul in
  let x7 = x7 ^^ rotate( x6+%^ x5)  9ul in
  let x4 = x4 ^^ rotate( x7+%^ x6) 13ul in
  let x5 = x5 ^^ rotate( x4+%^ x7) 18ul in
  let x11 = x11 ^^ rotate(x10+%^ x9)  7ul in
  let x8 = x8 ^^ rotate(x11+%^x10)  9ul in
  let x9 = x9 ^^ rotate( x8+%^x11) 13ul in
  let x10 = x10 ^^ rotate( x9+%^ x8) 18ul in
  let x12 = x12 ^^ rotate(x15+%^x14)  7ul in
  let x13 = x13 ^^ rotate(x12+%^x15)  9ul in
  let x14 = x14 ^^ rotate(x13+%^x12) 13ul in
  let x15 = x15 ^^ rotate(x14+%^x13) 18ul in
  (* *)
  let x4 = x4 ^^ rotate( x0+%^x12)  7ul in
  let x8 = x8 ^^ rotate( x4+%^ x0)  9ul in
  let x12 = x12 ^^ rotate( x8+%^ x4) 13ul in
  let x0 = x0 ^^ rotate(x12+%^ x8) 18ul in
  let x9 = x9 ^^ rotate( x5+%^ x1)  7ul in
  let x13 = x13 ^^ rotate( x9+%^ x5)  9ul in
  let x1 = x1 ^^ rotate(x13+%^ x9) 13ul in
  let x5 = x5 ^^ rotate( x1+%^x13) 18ul in
  let x14 = x14 ^^ rotate(x10+%^ x6)  7ul in
  let x2 = x2 ^^ rotate(x14+%^x10)  9ul in
  let x6 = x6 ^^ rotate( x2+%^x14) 13ul in
  let x10 = x10 ^^ rotate( x6+%^ x2) 18ul in
  let x3 = x3 ^^ rotate(x15+%^x11)  7ul in
  let x7 = x7 ^^ rotate( x3+%^x15)  9ul in
  let x11 = x11 ^^ rotate( x7+%^ x3) 13ul in
  let x15 = x15 ^^ rotate(x11+%^ x7) 18ul in
  let x1 = x1 ^^ rotate( x0+%^ x3)  7ul in
  let x2 = x2 ^^ rotate( x1+%^ x0)  9ul in
  let x3 = x3 ^^ rotate( x2+%^ x1) 13ul in
  let x0 = x0 ^^ rotate( x3+%^ x2) 18ul in
  let x6 = x6 ^^ rotate( x5+%^ x4)  7ul in
  let x7 = x7 ^^ rotate( x6+%^ x5)  9ul in
  let x4 = x4 ^^ rotate( x7+%^ x6) 13ul in
  let x5 = x5 ^^ rotate( x4+%^ x7) 18ul in
  let x11 = x11 ^^ rotate(x10+%^ x9)  7ul in
  let x8 = x8 ^^ rotate(x11+%^x10)  9ul in
  let x9 = x9 ^^ rotate( x8+%^x11) 13ul in
  let x10 = x10 ^^ rotate( x9+%^ x8) 18ul in
  let x12 = x12 ^^ rotate(x15+%^x14)  7ul in
  let x13 = x13 ^^ rotate(x12+%^x15)  9ul in
  let x14 = x14 ^^ rotate(x13+%^x12) 13ul in
  let x15 = x15 ^^ rotate(x14+%^x13) 18ul in
  (* *)
  let x4 = x4 ^^ rotate( x0+%^x12)  7ul in
  let x8 = x8 ^^ rotate( x4+%^ x0)  9ul in
  let x12 = x12 ^^ rotate( x8+%^ x4) 13ul in
  let x0 = x0 ^^ rotate(x12+%^ x8) 18ul in
  let x9 = x9 ^^ rotate( x5+%^ x1)  7ul in
  let x13 = x13 ^^ rotate( x9+%^ x5)  9ul in
  let x1 = x1 ^^ rotate(x13+%^ x9) 13ul in
  let x5 = x5 ^^ rotate( x1+%^x13) 18ul in
  let x14 = x14 ^^ rotate(x10+%^ x6)  7ul in
  let x2 = x2 ^^ rotate(x14+%^x10)  9ul in
  let x6 = x6 ^^ rotate( x2+%^x14) 13ul in
  let x10 = x10 ^^ rotate( x6+%^ x2) 18ul in
  let x3 = x3 ^^ rotate(x15+%^x11)  7ul in
  let x7 = x7 ^^ rotate( x3+%^x15)  9ul in
  let x11 = x11 ^^ rotate( x7+%^ x3) 13ul in
  let x15 = x15 ^^ rotate(x11+%^ x7) 18ul in
  let x1 = x1 ^^ rotate( x0+%^ x3)  7ul in
  let x2 = x2 ^^ rotate( x1+%^ x0)  9ul in
  let x3 = x3 ^^ rotate( x2+%^ x1) 13ul in
  let x0 = x0 ^^ rotate( x3+%^ x2) 18ul in
  let x6 = x6 ^^ rotate( x5+%^ x4)  7ul in
  let x7 = x7 ^^ rotate( x6+%^ x5)  9ul in
  let x4 = x4 ^^ rotate( x7+%^ x6) 13ul in
  let x5 = x5 ^^ rotate( x4+%^ x7) 18ul in
  let x11 = x11 ^^ rotate(x10+%^ x9)  7ul in
  let x8 = x8 ^^ rotate(x11+%^x10)  9ul in
  let x9 = x9 ^^ rotate( x8+%^x11) 13ul in
  let x10 = x10 ^^ rotate( x9+%^ x8) 18ul in
  let x12 = x12 ^^ rotate(x15+%^x14)  7ul in
  let x13 = x13 ^^ rotate(x12+%^x15)  9ul in
  let x14 = x14 ^^ rotate(x13+%^x12) 13ul in
  let x15 = x15 ^^ rotate(x14+%^x13) 18ul in
  (* *)
  let x4 = x4 ^^ rotate( x0+%^x12)  7ul in
  let x8 = x8 ^^ rotate( x4+%^ x0)  9ul in
  let x12 = x12 ^^ rotate( x8+%^ x4) 13ul in
  let x0 = x0 ^^ rotate(x12+%^ x8) 18ul in
  let x9 = x9 ^^ rotate( x5+%^ x1)  7ul in
  let x13 = x13 ^^ rotate( x9+%^ x5)  9ul in
  let x1 = x1 ^^ rotate(x13+%^ x9) 13ul in
  let x5 = x5 ^^ rotate( x1+%^x13) 18ul in
  let x14 = x14 ^^ rotate(x10+%^ x6)  7ul in
  let x2 = x2 ^^ rotate(x14+%^x10)  9ul in
  let x6 = x6 ^^ rotate( x2+%^x14) 13ul in
  let x10 = x10 ^^ rotate( x6+%^ x2) 18ul in
  let x3 = x3 ^^ rotate(x15+%^x11)  7ul in
  let x7 = x7 ^^ rotate( x3+%^x15)  9ul in
  let x11 = x11 ^^ rotate( x7+%^ x3) 13ul in
  let x15 = x15 ^^ rotate(x11+%^ x7) 18ul in
  let x1 = x1 ^^ rotate( x0+%^ x3)  7ul in
  let x2 = x2 ^^ rotate( x1+%^ x0)  9ul in
  let x3 = x3 ^^ rotate( x2+%^ x1) 13ul in
  let x0 = x0 ^^ rotate( x3+%^ x2) 18ul in
  let x6 = x6 ^^ rotate( x5+%^ x4)  7ul in
  let x7 = x7 ^^ rotate( x6+%^ x5)  9ul in
  let x4 = x4 ^^ rotate( x7+%^ x6) 13ul in
  let x5 = x5 ^^ rotate( x4+%^ x7) 18ul in
  let x11 = x11 ^^ rotate(x10+%^ x9)  7ul in
  let x8 = x8 ^^ rotate(x11+%^x10)  9ul in
  let x9 = x9 ^^ rotate( x8+%^x11) 13ul in
  let x10 = x10 ^^ rotate( x9+%^ x8) 18ul in
  let x12 = x12 ^^ rotate(x15+%^x14)  7ul in
  let x13 = x13 ^^ rotate(x12+%^x15)  9ul in
  let x14 = x14 ^^ rotate(x13+%^x12) 13ul in
  let x15 = x15 ^^ rotate(x14+%^x13) 18ul in
  (* *)
  let x4 = x4 ^^ rotate( x0+%^x12)  7ul in
  let x8 = x8 ^^ rotate( x4+%^ x0)  9ul in
  let x12 = x12 ^^ rotate( x8+%^ x4) 13ul in
  let x0 = x0 ^^ rotate(x12+%^ x8) 18ul in
  let x9 = x9 ^^ rotate( x5+%^ x1)  7ul in
  let x13 = x13 ^^ rotate( x9+%^ x5)  9ul in
  let x1 = x1 ^^ rotate(x13+%^ x9) 13ul in
  let x5 = x5 ^^ rotate( x1+%^x13) 18ul in
  let x14 = x14 ^^ rotate(x10+%^ x6)  7ul in
  let x2 = x2 ^^ rotate(x14+%^x10)  9ul in
  let x6 = x6 ^^ rotate( x2+%^x14) 13ul in
  let x10 = x10 ^^ rotate( x6+%^ x2) 18ul in
  let x3 = x3 ^^ rotate(x15+%^x11)  7ul in
  let x7 = x7 ^^ rotate( x3+%^x15)  9ul in
  let x11 = x11 ^^ rotate( x7+%^ x3) 13ul in
  let x15 = x15 ^^ rotate(x11+%^ x7) 18ul in
  let x1 = x1 ^^ rotate( x0+%^ x3)  7ul in
  let x2 = x2 ^^ rotate( x1+%^ x0)  9ul in
  let x3 = x3 ^^ rotate( x2+%^ x1) 13ul in
  let x0 = x0 ^^ rotate( x3+%^ x2) 18ul in
  let x6 = x6 ^^ rotate( x5+%^ x4)  7ul in
  let x7 = x7 ^^ rotate( x6+%^ x5)  9ul in
  let x4 = x4 ^^ rotate( x7+%^ x6) 13ul in
  let x5 = x5 ^^ rotate( x4+%^ x7) 18ul in
  let x11 = x11 ^^ rotate(x10+%^ x9)  7ul in
  let x8 = x8 ^^ rotate(x11+%^x10)  9ul in
  let x9 = x9 ^^ rotate( x8+%^x11) 13ul in
  let x10 = x10 ^^ rotate( x9+%^ x8) 18ul in
  let x12 = x12 ^^ rotate(x15+%^x14)  7ul in
  let x13 = x13 ^^ rotate(x12+%^x15)  9ul in
  let x14 = x14 ^^ rotate(x13+%^x12) 13ul in
  let x15 = x15 ^^ rotate(x14+%^x13) 18ul in
  (* *)
  let x4 = x4 ^^ rotate( x0+%^x12)  7ul in
  let x8 = x8 ^^ rotate( x4+%^ x0)  9ul in
  let x12 = x12 ^^ rotate( x8+%^ x4) 13ul in
  let x0 = x0 ^^ rotate(x12+%^ x8) 18ul in
  let x9 = x9 ^^ rotate( x5+%^ x1)  7ul in
  let x13 = x13 ^^ rotate( x9+%^ x5)  9ul in
  let x1 = x1 ^^ rotate(x13+%^ x9) 13ul in
  let x5 = x5 ^^ rotate( x1+%^x13) 18ul in
  let x14 = x14 ^^ rotate(x10+%^ x6)  7ul in
  let x2 = x2 ^^ rotate(x14+%^x10)  9ul in
  let x6 = x6 ^^ rotate( x2+%^x14) 13ul in
  let x10 = x10 ^^ rotate( x6+%^ x2) 18ul in
  let x3 = x3 ^^ rotate(x15+%^x11)  7ul in
  let x7 = x7 ^^ rotate( x3+%^x15)  9ul in
  let x11 = x11 ^^ rotate( x7+%^ x3) 13ul in
  let x15 = x15 ^^ rotate(x11+%^ x7) 18ul in
  let x1 = x1 ^^ rotate( x0+%^ x3)  7ul in
  let x2 = x2 ^^ rotate( x1+%^ x0)  9ul in
  let x3 = x3 ^^ rotate( x2+%^ x1) 13ul in
  let x0 = x0 ^^ rotate( x3+%^ x2) 18ul in
  let x6 = x6 ^^ rotate( x5+%^ x4)  7ul in
  let x7 = x7 ^^ rotate( x6+%^ x5)  9ul in
  let x4 = x4 ^^ rotate( x7+%^ x6) 13ul in
  let x5 = x5 ^^ rotate( x4+%^ x7) 18ul in
  let x11 = x11 ^^ rotate(x10+%^ x9)  7ul in
  let x8 = x8 ^^ rotate(x11+%^x10)  9ul in
  let x9 = x9 ^^ rotate( x8+%^x11) 13ul in
  let x10 = x10 ^^ rotate( x9+%^ x8) 18ul in
  let x12 = x12 ^^ rotate(x15+%^x14)  7ul in
  let x13 = x13 ^^ rotate(x12+%^x15)  9ul in
  let x14 = x14 ^^ rotate(x13+%^x12) 13ul in
  let x15 = x15 ^^ rotate(x14+%^x13) 18ul in
  (* *)
  let x4 = x4 ^^ rotate( x0+%^x12)  7ul in
  let x8 = x8 ^^ rotate( x4+%^ x0)  9ul in
  let x12 = x12 ^^ rotate( x8+%^ x4) 13ul in
  let x0 = x0 ^^ rotate(x12+%^ x8) 18ul in
  let x9 = x9 ^^ rotate( x5+%^ x1)  7ul in
  let x13 = x13 ^^ rotate( x9+%^ x5)  9ul in
  let x1 = x1 ^^ rotate(x13+%^ x9) 13ul in
  let x5 = x5 ^^ rotate( x1+%^x13) 18ul in
  let x14 = x14 ^^ rotate(x10+%^ x6)  7ul in
  let x2 = x2 ^^ rotate(x14+%^x10)  9ul in
  let x6 = x6 ^^ rotate( x2+%^x14) 13ul in
  let x10 = x10 ^^ rotate( x6+%^ x2) 18ul in
  let x3 = x3 ^^ rotate(x15+%^x11)  7ul in
  let x7 = x7 ^^ rotate( x3+%^x15)  9ul in
  let x11 = x11 ^^ rotate( x7+%^ x3) 13ul in
  let x15 = x15 ^^ rotate(x11+%^ x7) 18ul in
  let x1 = x1 ^^ rotate( x0+%^ x3)  7ul in
  let x2 = x2 ^^ rotate( x1+%^ x0)  9ul in
  let x3 = x3 ^^ rotate( x2+%^ x1) 13ul in
  let x0 = x0 ^^ rotate( x3+%^ x2) 18ul in
  let x6 = x6 ^^ rotate( x5+%^ x4)  7ul in
  let x7 = x7 ^^ rotate( x6+%^ x5)  9ul in
  let x4 = x4 ^^ rotate( x7+%^ x6) 13ul in
  let x5 = x5 ^^ rotate( x4+%^ x7) 18ul in
  let x11 = x11 ^^ rotate(x10+%^ x9)  7ul in
  let x8 = x8 ^^ rotate(x11+%^x10)  9ul in
  let x9 = x9 ^^ rotate( x8+%^x11) 13ul in
  let x10 = x10 ^^ rotate( x9+%^ x8) 18ul in
  let x12 = x12 ^^ rotate(x15+%^x14)  7ul in
  let x13 = x13 ^^ rotate(x12+%^x15)  9ul in
  let x14 = x14 ^^ rotate(x13+%^x12) 13ul in
  let x15 = x15 ^^ rotate(x14+%^x13) 18ul in
  (* *)
  let x4 = x4 ^^ rotate( x0+%^x12)  7ul in
  let x8 = x8 ^^ rotate( x4+%^ x0)  9ul in
  let x12 = x12 ^^ rotate( x8+%^ x4) 13ul in
  let x0 = x0 ^^ rotate(x12+%^ x8) 18ul in
  let x9 = x9 ^^ rotate( x5+%^ x1)  7ul in
  let x13 = x13 ^^ rotate( x9+%^ x5)  9ul in
  let x1 = x1 ^^ rotate(x13+%^ x9) 13ul in
  let x5 = x5 ^^ rotate( x1+%^x13) 18ul in
  let x14 = x14 ^^ rotate(x10+%^ x6)  7ul in
  let x2 = x2 ^^ rotate(x14+%^x10)  9ul in
  let x6 = x6 ^^ rotate( x2+%^x14) 13ul in
  let x10 = x10 ^^ rotate( x6+%^ x2) 18ul in
  let x3 = x3 ^^ rotate(x15+%^x11)  7ul in
  let x7 = x7 ^^ rotate( x3+%^x15)  9ul in
  let x11 = x11 ^^ rotate( x7+%^ x3) 13ul in
  let x15 = x15 ^^ rotate(x11+%^ x7) 18ul in
  let x1 = x1 ^^ rotate( x0+%^ x3)  7ul in
  let x2 = x2 ^^ rotate( x1+%^ x0)  9ul in
  let x3 = x3 ^^ rotate( x2+%^ x1) 13ul in
  let x0 = x0 ^^ rotate( x3+%^ x2) 18ul in
  let x6 = x6 ^^ rotate( x5+%^ x4)  7ul in
  let x7 = x7 ^^ rotate( x6+%^ x5)  9ul in
  let x4 = x4 ^^ rotate( x7+%^ x6) 13ul in
  let x5 = x5 ^^ rotate( x4+%^ x7) 18ul in
  let x11 = x11 ^^ rotate(x10+%^ x9)  7ul in
  let x8 = x8 ^^ rotate(x11+%^x10)  9ul in
  let x9 = x9 ^^ rotate( x8+%^x11) 13ul in
  let x10 = x10 ^^ rotate( x9+%^ x8) 18ul in
  let x12 = x12 ^^ rotate(x15+%^x14)  7ul in
  let x13 = x13 ^^ rotate(x12+%^x15)  9ul in
  let x14 = x14 ^^ rotate(x13+%^x12) 13ul in
  let x15 = x15 ^^ rotate(x14+%^x13) 18ul in
  (* *)
  let x4 = x4 ^^ rotate( x0+%^x12)  7ul in
  let x8 = x8 ^^ rotate( x4+%^ x0)  9ul in
  let x12 = x12 ^^ rotate( x8+%^ x4) 13ul in
  let x0 = x0 ^^ rotate(x12+%^ x8) 18ul in
  let x9 = x9 ^^ rotate( x5+%^ x1)  7ul in
  let x13 = x13 ^^ rotate( x9+%^ x5)  9ul in
  let x1 = x1 ^^ rotate(x13+%^ x9) 13ul in
  let x5 = x5 ^^ rotate( x1+%^x13) 18ul in
  let x14 = x14 ^^ rotate(x10+%^ x6)  7ul in
  let x2 = x2 ^^ rotate(x14+%^x10)  9ul in
  let x6 = x6 ^^ rotate( x2+%^x14) 13ul in
  let x10 = x10 ^^ rotate( x6+%^ x2) 18ul in
  let x3 = x3 ^^ rotate(x15+%^x11)  7ul in
  let x7 = x7 ^^ rotate( x3+%^x15)  9ul in
  let x11 = x11 ^^ rotate( x7+%^ x3) 13ul in
  let x15 = x15 ^^ rotate(x11+%^ x7) 18ul in
  let x1 = x1 ^^ rotate( x0+%^ x3)  7ul in
  let x2 = x2 ^^ rotate( x1+%^ x0)  9ul in
  let x3 = x3 ^^ rotate( x2+%^ x1) 13ul in
  let x0 = x0 ^^ rotate( x3+%^ x2) 18ul in
  let x6 = x6 ^^ rotate( x5+%^ x4)  7ul in
  let x7 = x7 ^^ rotate( x6+%^ x5)  9ul in
  let x4 = x4 ^^ rotate( x7+%^ x6) 13ul in
  let x5 = x5 ^^ rotate( x4+%^ x7) 18ul in
  let x11 = x11 ^^ rotate(x10+%^ x9)  7ul in
  let x8 = x8 ^^ rotate(x11+%^x10)  9ul in
  let x9 = x9 ^^ rotate( x8+%^x11) 13ul in
  let x10 = x10 ^^ rotate( x9+%^ x8) 18ul in
  let x12 = x12 ^^ rotate(x15+%^x14)  7ul in
  let x13 = x13 ^^ rotate(x12+%^x15)  9ul in
  let x14 = x14 ^^ rotate(x13+%^x12) 13ul in
  let x15 = x15 ^^ rotate(x14+%^x13) 18ul in
  (* *)
  store32_le output                 x0;
  store32_le (offset output 4ul)  x5;
  store32_le (offset output 8ul)  x10;
  store32_le (offset output 12ul) x15;
  store32_le (offset output 16ul) x6;
  store32_le (offset output 20ul) x7;
  store32_le (offset output 24ul) x8;
  store32_le (offset output 28ul) x9
