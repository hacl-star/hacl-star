module Hacl.Symmetric.HSalsa20

open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.UInt32
open Hacl.Cast

let h32 = Hacl.UInt32.t
let u32 = FStar.UInt32.t
let uint8_p = buffer Hacl.UInt8.t

assume MaxUInt32: pow2 32 = 4294967296

let rotate (a:h32) (s:u32{FStar.UInt32.v s <= 32}) : Tot h32 =
  (a <<^ s) |^ (a >>^ (FStar.UInt32 (32ul -^ s)))


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"

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

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 100"

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

  store32_le output                 x0;
  store32_le (offset output 4ul)  x5;
  store32_le (offset output 8ul)  x10;
  store32_le (offset output 12ul) x15;
  store32_le (offset output 16ul) x6;
  store32_le (offset output 20ul) x7;
  store32_le (offset output 24ul) x8;
  store32_le (offset output 28ul) x9


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 100"

val crypto_core_salsa20:
  output:uint8_p{length output = 64} ->
  input :uint8_p{length input = 16 /\ disjoint output input} ->
  key   :uint8_p{length key = 32 /\ disjoint output key} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h key))
    (ensures  (fun h0 _ h1 -> modifies_1 output h0 h1 /\ live h1 output))
let crypto_core_salsa20 output input key =
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
  let j0 = x0 in
  let j1 = x1 in
  let j2 = x2 in
  let j3 = x3 in
  let j4 = x4 in
  let j5 = x5 in
  let j6 = x6 in
  let j7 = x7 in
  let j8 = x8 in
  let j9 = x9 in
  let j10 = x10 in
  let j11 = x11 in
  let j12 = x12 in
  let j13 = x13 in
  let j14 = x14 in
  let j15 = x15 in

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

  let x0 = x0 +%^ j0 in
  let x1 = x1 +%^ j1 in
  let x2 = x2 +%^ j2 in
  let x3 = x3 +%^ j3 in
  let x4 = x4 +%^ j4 in
  let x5 = x5 +%^ j5 in
  let x6 = x6 +%^ j6 in
  let x7 = x7 +%^ j7 in
  let x8 = x8 +%^ j8 in
  let x9 = x9 +%^ j9 in
  let x10 = x10 +%^ j10 in
  let x11 = x11 +%^ j11 in
  let x12 = x12 +%^ j12 in
  let x13 = x13 +%^ j13 in
  let x14 = x14 +%^ j14 in
  let x15 = x15 +%^ j15 in

  store32_le (offset output 0ul) x0;
  store32_le (offset output 4ul) x1;
  store32_le (offset output 8ul) x2;
  store32_le (offset output 12ul) x3;
  store32_le (offset output 16ul) x4;
  store32_le (offset output 20ul) x5;
  store32_le (offset output 24ul) x6;
  store32_le (offset output 28ul) x7;
  store32_le (offset output 32ul) x8;
  store32_le (offset output 36ul) x9;
  store32_le (offset output 40ul) x10;
  store32_le (offset output 44ul) x11;
  store32_le (offset output 48ul) x12;
  store32_le (offset output 52ul) x13;
  store32_le (offset output 56ul) x14;
  store32_le (offset output 60ul) x15


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5 --lax"

val crypto_stream_salsa20_xor_ic_loop:
  c:uint8_p{length c >= 64} ->
  m:uint8_p{length m >= 64} ->
  block:uint8_p{length block = 64} ->
  input:uint8_p{length input = 16} ->
  kcopy:uint8_p{length kcopy = 32} ->
  mlen:FStar.UInt64.t ->
  Stack FStar.UInt64.t
    (requires (fun h -> live h c /\ live h m /\ live h block))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1))
let rec crypto_stream_salsa20_xor_ic_loop c m block input kcopy mlen =
  if (FStar.UInt64 (mlen <^ 64uL)) then mlen
  else (
    let open Hacl.UInt8 in
    crypto_core_salsa20 block input kcopy;
    let m0 = m.(0ul) in let block0 = block.(0ul) in c.(0ul) <- m0 ^^ block0;
    let m1 = m.(1ul) in let block1 = block.(1ul) in c.(1ul) <- m1 ^^ block1;
    let m2 = m.(2ul) in let block2 = block.(2ul) in c.(2ul) <- m2 ^^ block2;
    let m3 = m.(3ul) in let block3 = block.(3ul) in c.(3ul) <- m3 ^^ block3;
    let m4 = m.(4ul) in let block4 = block.(4ul) in c.(4ul) <- m4 ^^ block4;
    let m5 = m.(5ul) in let block5 = block.(5ul) in c.(5ul) <- m5 ^^ block5;
    let m6 = m.(6ul) in let block6 = block.(6ul) in c.(6ul) <- m6 ^^ block6;
    let m7 = m.(7ul) in let block7 = block.(7ul) in c.(7ul) <- m7 ^^ block7;
    let m8 = m.(8ul) in let block8 = block.(8ul) in c.(8ul) <- m8 ^^ block8;
    let m9 = m.(9ul) in let block9 = block.(9ul) in c.(9ul) <- m9 ^^ block9;
    let m10 = m.(10ul) in let block10 = block.(10ul) in c.(10ul) <- m10 ^^ block10;
    let m11 = m.(11ul) in let block11 = block.(11ul) in c.(11ul) <- m11 ^^ block11;
    let m12 = m.(12ul) in let block12 = block.(12ul) in c.(12ul) <- m12 ^^ block12;
    let m13 = m.(13ul) in let block13 = block.(13ul) in c.(13ul) <- m13 ^^ block13;
    let m14 = m.(14ul) in let block14 = block.(14ul) in c.(14ul) <- m14 ^^ block14;
    let m15 = m.(15ul) in let block15 = block.(15ul) in c.(15ul) <- m15 ^^ block15;
    let m16 = m.(16ul) in let block16 = block.(16ul) in c.(16ul) <- m16 ^^ block16;
    let m17 = m.(17ul) in let block17 = block.(17ul) in c.(17ul) <- m17 ^^ block17;
    let m18 = m.(18ul) in let block18 = block.(18ul) in c.(18ul) <- m18 ^^ block18;
    let m19 = m.(19ul) in let block19 = block.(19ul) in c.(19ul) <- m19 ^^ block19;
    let m20 = m.(20ul) in let block20 = block.(20ul) in c.(20ul) <- m20 ^^ block20;
    let m21 = m.(21ul) in let block21 = block.(21ul) in c.(21ul) <- m21 ^^ block21;
    let m22 = m.(22ul) in let block22 = block.(22ul) in c.(22ul) <- m22 ^^ block22;
    let m23 = m.(23ul) in let block23 = block.(23ul) in c.(23ul) <- m23 ^^ block23;
    let m24 = m.(24ul) in let block24 = block.(24ul) in c.(24ul) <- m24 ^^ block24;
    let m25 = m.(25ul) in let block25 = block.(25ul) in c.(25ul) <- m25 ^^ block25;
    let m26 = m.(26ul) in let block26 = block.(26ul) in c.(26ul) <- m26 ^^ block26;
    let m27 = m.(27ul) in let block27 = block.(27ul) in c.(27ul) <- m27 ^^ block27;
    let m28 = m.(28ul) in let block28 = block.(28ul) in c.(28ul) <- m28 ^^ block28;
    let m29 = m.(29ul) in let block29 = block.(29ul) in c.(29ul) <- m29 ^^ block29;
    let m30 = m.(30ul) in let block30 = block.(30ul) in c.(30ul) <- m30 ^^ block30;
    let m31 = m.(31ul) in let block31 = block.(31ul) in c.(31ul) <- m31 ^^ block31;
    let m32 = m.(32ul) in let block32 = block.(32ul) in c.(32ul) <- m32 ^^ block32;
    let m33 = m.(33ul) in let block33 = block.(33ul) in c.(33ul) <- m33 ^^ block33;
    let m34 = m.(34ul) in let block34 = block.(34ul) in c.(34ul) <- m34 ^^ block34;
    let m35 = m.(35ul) in let block35 = block.(35ul) in c.(35ul) <- m35 ^^ block35;
    let m36 = m.(36ul) in let block36 = block.(36ul) in c.(36ul) <- m36 ^^ block36;
    let m37 = m.(37ul) in let block37 = block.(37ul) in c.(37ul) <- m37 ^^ block37;
    let m38 = m.(38ul) in let block38 = block.(38ul) in c.(38ul) <- m38 ^^ block38;
    let m39 = m.(39ul) in let block39 = block.(39ul) in c.(39ul) <- m39 ^^ block39;
    let m40 = m.(40ul) in let block40 = block.(40ul) in c.(40ul) <- m40 ^^ block40;
    let m41 = m.(41ul) in let block41 = block.(41ul) in c.(41ul) <- m41 ^^ block41;
    let m42 = m.(42ul) in let block42 = block.(42ul) in c.(42ul) <- m42 ^^ block42;
    let m43 = m.(43ul) in let block43 = block.(43ul) in c.(43ul) <- m43 ^^ block43;
    let m44 = m.(44ul) in let block44 = block.(44ul) in c.(44ul) <- m44 ^^ block44;
    let m45 = m.(45ul) in let block45 = block.(45ul) in c.(45ul) <- m45 ^^ block45;
    let m46 = m.(46ul) in let block46 = block.(46ul) in c.(46ul) <- m46 ^^ block46;
    let m47 = m.(47ul) in let block47 = block.(47ul) in c.(47ul) <- m47 ^^ block47;
    let m48 = m.(48ul) in let block48 = block.(48ul) in c.(48ul) <- m48 ^^ block48;
    let m49 = m.(49ul) in let block49 = block.(49ul) in c.(49ul) <- m49 ^^ block49;
    let m50 = m.(50ul) in let block50 = block.(50ul) in c.(50ul) <- m50 ^^ block50;
    let m51 = m.(51ul) in let block51 = block.(51ul) in c.(51ul) <- m51 ^^ block51;
    let m52 = m.(52ul) in let block52 = block.(52ul) in c.(52ul) <- m52 ^^ block52;
    let m53 = m.(53ul) in let block53 = block.(53ul) in c.(53ul) <- m53 ^^ block53;
    let m54 = m.(54ul) in let block54 = block.(54ul) in c.(54ul) <- m54 ^^ block54;
    let m55 = m.(55ul) in let block55 = block.(55ul) in c.(55ul) <- m55 ^^ block55;
    let m56 = m.(56ul) in let block56 = block.(56ul) in c.(56ul) <- m56 ^^ block56;
    let m57 = m.(57ul) in let block57 = block.(57ul) in c.(57ul) <- m57 ^^ block57;
    let m58 = m.(58ul) in let block58 = block.(58ul) in c.(58ul) <- m58 ^^ block58;
    let m59 = m.(59ul) in let block59 = block.(59ul) in c.(59ul) <- m59 ^^ block59;
    let m60 = m.(60ul) in let block60 = block.(60ul) in c.(60ul) <- m60 ^^ block60;
    let m61 = m.(61ul) in let block61 = block.(61ul) in c.(61ul) <- m61 ^^ block61;
    let m62 = m.(62ul) in let block62 = block.(62ul) in c.(62ul) <- m62 ^^ block62;
    let m63 = m.(63ul) in let block63 = block.(63ul) in c.(63ul) <- m63 ^^ block63;

    let i8 = input.(8ul) in
    let i9 = input.(9ul) in
    let i10 = input.(10ul) in
    let i11 = input.(11ul) in
    let i12 = input.(12ul) in
    let i13 = input.(13ul) in
    let i14 = input.(14ul) in
    let i15 = input.(15ul) in

    let u = Hacl.UInt64(
      sint8_to_sint64 i8
      +%^ (sint8_to_sint64 i9 <<^ 8ul)
      +%^ (sint8_to_sint64 i10 <<^ 16ul)
      +%^ (sint8_to_sint64 i11 <<^ 24ul)
      +%^ (sint8_to_sint64 i12 <<^ 32ul)
      +%^ (sint8_to_sint64 i13 <<^ 40ul)
      +%^ (sint8_to_sint64 i14 <<^ 48ul)
      +%^ (sint8_to_sint64 i15 <<^ 56ul)
      +%^ (uint64_to_sint64 1uL)
    ) in

    input.(8ul)  <- sint64_to_sint8 u;
    input.(9ul)  <- sint64_to_sint8 (Hacl.UInt64 (u >>^ 8ul));
    input.(10ul) <- sint64_to_sint8 (Hacl.UInt64 (u >>^ 16ul));
    input.(11ul) <- sint64_to_sint8 (Hacl.UInt64 (u >>^ 24ul));
    input.(12ul) <- sint64_to_sint8 (Hacl.UInt64 (u >>^ 32ul));
    input.(13ul) <- sint64_to_sint8 (Hacl.UInt64 (u >>^ 40ul));
    input.(14ul) <- sint64_to_sint8 (Hacl.UInt64 (u >>^ 48ul));
    input.(15ul) <- sint64_to_sint8 (Hacl.UInt64 (u >>^ 56ul));

    let mlen = FStar.UInt64 (mlen -^ 64uL) in
    let c = offset c 64ul in
    let m = offset m 64ul in

    crypto_stream_salsa20_xor_ic_loop c m block input kcopy mlen
  )


val xor_bytes:
  x:uint8_p ->
  y:uint8_p ->
  z:uint8_p ->
  len:FStar.UInt32.t ->
  Stack unit
    (requires (fun h -> live h x /\ live h y /\ live h z))
    (ensures  (fun h0 _ h1 -> live h1 x /\ modifies_1 x h0 h1))
let rec xor_bytes x y z len =
  if FStar.UInt32 (len =^ 0ul) then ()
  else (
    let i = FStar.UInt32 (len -^ 1ul) in
    let yi = y.(i) in let zi = z.(i) in
    x.(i) <- Hacl.UInt8 (yi ^^ zi);
    xor_bytes x y z i
  )


val crypto_stream_salsa20_xor_ic:
  c:uint8_p ->
  m:uint8_p ->
  mlen:FStar.UInt64.t ->
  n:uint8_p ->
  ic:FStar.UInt64.t ->
  k:uint8_p ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))
let crypto_stream_salsa20_xor_ic c m mlen n ic k =
  push_frame();
  if FStar.UInt64 (mlen =^ 0uL) then ()
  else (
    let zero = uint8_to_sint8 0uy in
    let input = create zero 16ul in
    let block = create zero 64ul in
    let kcopy = create zero 32ul in
    kcopy.(0ul) <- k.(0ul);   kcopy.(1ul) <-  k.(1ul);
    kcopy.(2ul) <- k.(2ul);   kcopy.(3ul) <- k.(3ul);
    kcopy.(4ul) <- k.(4ul);   kcopy.(5ul) <-  k.(5ul);
    kcopy.(6ul) <- k.(6ul);   kcopy.(7ul) <- k.(7ul);
    kcopy.(8ul) <- k.(8ul);   kcopy.(9ul) <-  k.(9ul);
    kcopy.(10ul) <- k.(10ul); kcopy.(11ul) <- k.(11ul);
    kcopy.(12ul) <- k.(12ul); kcopy.(13ul) <- k.(13ul);
    kcopy.(14ul) <- k.(14ul); kcopy.(15ul) <- k.(15ul);
    kcopy.(16ul) <- k.(16ul); kcopy.(17ul) <- k.(17ul);
    kcopy.(18ul) <- k.(18ul); kcopy.(19ul) <- k.(19ul);
    kcopy.(20ul) <- k.(20ul); kcopy.(21ul) <- k.(21ul);
    kcopy.(22ul) <- k.(22ul); kcopy.(23ul) <- k.(23ul);
    kcopy.(24ul) <- k.(24ul); kcopy.(25ul) <- k.(25ul);
    kcopy.(26ul) <- k.(26ul); kcopy.(27ul) <- k.(27ul);
    kcopy.(28ul) <- k.(28ul); kcopy.(29ul) <- k.(29ul);
    kcopy.(30ul) <- k.(30ul); kcopy.(31ul) <- k.(31ul);

    input.(0ul) <- n.(0ul);   input.(1ul) <- n.(1ul);
    input.(2ul) <- n.(2ul);   input.(3ul) <- n.(3ul);
    input.(4ul) <- n.(4ul);   input.(5ul) <- n.(5ul);
    input.(6ul) <- n.(6ul);   input.(7ul) <- n .(7ul);

    input.(8ul)  <- uint64_to_sint8 ic;
    input.(9ul)  <- uint64_to_sint8 (FStar.UInt64 (ic >>^ 8ul));
    input.(10ul) <- uint64_to_sint8 (FStar.UInt64 (ic >>^ 16ul));
    input.(11ul) <- uint64_to_sint8 (FStar.UInt64 (ic >>^ 24ul));
    input.(12ul) <- uint64_to_sint8 (FStar.UInt64 (ic >>^ 32ul));
    input.(13ul) <- uint64_to_sint8 (FStar.UInt64 (ic >>^ 40ul));
    input.(14ul) <- uint64_to_sint8 (FStar.UInt64 (ic >>^ 48ul));
    input.(15ul) <- uint64_to_sint8 (FStar.UInt64 (ic >>^ 56ul));

    let mlen' = crypto_stream_salsa20_xor_ic_loop c m block input kcopy mlen in

    if FStar.UInt64 (mlen' >=^ 0uL) then (
      crypto_core_salsa20 block input kcopy;
      let off = FStar.Int.Cast.uint64_to_uint32 (FStar.UInt64 (mlen -^ mlen')) in
      xor_bytes (offset c off) (offset m off) block (FStar.Int.Cast.uint64_to_uint32 mlen')
    );
    ()
  );
  pop_frame()


val crypto_stream_salsa20_loop:
  c:uint8_p ->
  clen:FStar.UInt64.t ->
  n:uint8_p ->
  k:uint8_p ->
  input:uint8_p ->
  Stack FStar.UInt64.t
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))
let rec crypto_stream_salsa20_loop c clen n k input =
  if FStar.UInt64 (clen <^ 64uL) then clen
  else (
    crypto_core_salsa20 c input k;
    let i8 = input.(8ul) in
    let i9 = input.(9ul) in
    let i10 = input.(10ul) in
    let i11 = input.(11ul) in
    let i12 = input.(12ul) in
    let i13 = input.(13ul) in
    let i14 = input.(14ul) in
    let i15 = input.(15ul) in
    let u = Hacl.UInt64(
      sint8_to_sint64 i8
      +%^ (sint8_to_sint64 i9 <<^ 8ul)
      +%^ (sint8_to_sint64 i10 <<^ 16ul)
      +%^ (sint8_to_sint64 i11 <<^ 24ul)
      +%^ (sint8_to_sint64 i12 <<^ 32ul)
      +%^ (sint8_to_sint64 i13 <<^ 40ul)
      +%^ (sint8_to_sint64 i14 <<^ 48ul)
      +%^ (sint8_to_sint64 i15 <<^ 56ul)
      +%^ (uint64_to_sint64 1uL)
    ) in
    input.(8ul)  <- sint64_to_sint8 u;
    input.(9ul)  <- sint64_to_sint8 (Hacl.UInt64 (u >>^ 8ul));
    input.(10ul) <- sint64_to_sint8 (Hacl.UInt64 (u >>^ 16ul));
    input.(11ul) <- sint64_to_sint8 (Hacl.UInt64 (u >>^ 24ul));
    input.(12ul) <- sint64_to_sint8 (Hacl.UInt64 (u >>^ 32ul));
    input.(13ul) <- sint64_to_sint8 (Hacl.UInt64 (u >>^ 40ul));
    input.(14ul) <- sint64_to_sint8 (Hacl.UInt64 (u >>^ 48ul));
    input.(15ul) <- sint64_to_sint8 (Hacl.UInt64 (u >>^ 56ul));
    let clen = FStar.UInt64 (clen -^ 64uL) in
    let c = offset c 64ul in
    crypto_stream_salsa20_loop c clen n k input
  )


val crypto_stream_salsa20:
  c:uint8_p ->
  clen:FStar.UInt64.t ->
  n:uint8_p ->
  k:uint8_p ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))
let crypto_stream_salsa20 c clen n k =
  push_frame();
  if (FStar.UInt64 (clen =^ 0uL)) then ()
  else (
    let zero = uint8_to_sint8 0uy in
    let input = create zero 16ul in
    let block = create zero 64ul in
    let kcopy = create zero 32ul in
    kcopy.(0ul) <- k.(0ul);   kcopy.(1ul) <-  k.(1ul);
    kcopy.(2ul) <- k.(2ul);   kcopy.(3ul) <- k.(3ul);
    kcopy.(4ul) <- k.(4ul);   kcopy.(5ul) <-  k.(5ul);
    kcopy.(6ul) <- k.(6ul);   kcopy.(7ul) <- k.(7ul);
    kcopy.(8ul) <- k.(8ul);   kcopy.(9ul) <-  k.(9ul);
    kcopy.(10ul) <- k.(10ul); kcopy.(11ul) <- k.(11ul);
    kcopy.(12ul) <- k.(12ul); kcopy.(13ul) <- k.(13ul);
    kcopy.(14ul) <- k.(14ul); kcopy.(15ul) <- k.(15ul);
    kcopy.(16ul) <- k.(16ul); kcopy.(17ul) <- k.(17ul);
    kcopy.(18ul) <- k.(18ul); kcopy.(19ul) <- k.(19ul);
    kcopy.(20ul) <- k.(20ul); kcopy.(21ul) <- k.(21ul);
    kcopy.(22ul) <- k.(22ul); kcopy.(23ul) <- k.(23ul);
    kcopy.(24ul) <- k.(24ul); kcopy.(25ul) <- k.(25ul);
    kcopy.(26ul) <- k.(26ul); kcopy.(27ul) <- k.(27ul);
    kcopy.(28ul) <- k.(28ul); kcopy.(29ul) <- k.(29ul);
    kcopy.(30ul) <- k.(30ul); kcopy.(31ul) <- k.(31ul);

    input.(0ul) <- n.(0ul);   input.(1ul) <-  n.(1ul);
    input.(2ul) <- n.(2ul);   input.(3ul) <- n.(3ul);
    input.(4ul) <- n.(4ul);   input.(5ul) <-  n.(5ul);
    input.(6ul) <- n.(6ul);   input.(7ul) <- n .(7ul);

    input.(8ul)  <- zero;
    input.(9ul)  <- zero;
    input.(10ul) <- zero;
    input.(11ul) <- zero;
    input.(12ul) <- zero;
    input.(13ul) <- zero;
    input.(14ul) <- zero;
    input.(15ul) <- zero;

    let clen' = crypto_stream_salsa20_loop c clen n kcopy input in

    if FStar.UInt64 (clen' >=^ 0uL) then (
      crypto_core_salsa20 block input kcopy;
      blit block 0ul 
           (offset c (FStar.Int.Cast.uint64_to_uint32(FStar.UInt64 (clen -^ clen')))) 0ul 
           (FStar.Int.Cast.uint64_to_uint32 clen')
    );
    ()
  );
  pop_frame()


val crypto_stream_xsalsa20:
  c:uint8_p ->
  clen:FStar.UInt64.t ->
  n:uint8_p ->
  k:uint8_p ->
  Stack unit
    (requires (fun h -> live h c /\ live h n /\ live h k))
    (ensures  (fun h0 _ h1 -> modifies_1 c h0 h1 /\ live h1 c))
let crypto_stream_xsalsa20 c clen n k =
  push_frame();
  let subkey = create (uint8_to_sint8 0uy) 32ul in
  crypto_core_hsalsa20 subkey n k;
  crypto_stream_salsa20 c clen (offset n 16ul) subkey;
  pop_frame()


val crypto_stream_xsalsa20_xor_ic:
  c:uint8_p ->
  m:uint8_p ->
  mlen:FStar.UInt64.t ->
  n:uint8_p ->
  ic:FStar.UInt64.t ->
  k:uint8_p ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))
let crypto_stream_xsalsa20_xor_ic c m mlen n ic k =
  push_frame();
  let subkey = create (uint8_to_sint8 0uy) 32ul in
  crypto_core_hsalsa20 subkey n k;
  crypto_stream_salsa20_xor_ic c m mlen (offset n 16ul) ic subkey;
  pop_frame()


val crypto_stream_xsalsa20_xor:
  c:uint8_p ->
  m:uint8_p ->
  mlen:FStar.UInt64.t ->
  n:uint8_p ->
  k:uint8_p ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))
let crypto_stream_xsalsa20_xor c m mlen n k =
  crypto_stream_xsalsa20_xor_ic c m mlen n 0uL k


val crypto_stream_salsa20_xor:
  c:uint8_p ->
  m:uint8_p ->
  mlen:FStar.UInt64.t ->
  n:uint8_p ->
  k:uint8_p ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))
let crypto_stream_salsa20_xor c m mlen n k =
  crypto_stream_salsa20_xor_ic c m mlen n 0uL k
