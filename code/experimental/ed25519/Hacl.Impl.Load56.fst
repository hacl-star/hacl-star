module Hacl.Impl.Load56

open FStar.Mul
open FStar.Buffer
open FStar.Endianness
open Hacl.Endianness
open Hacl.UInt64

let u32 = UInt32.t
let h8 = Hacl.UInt8.t
let h64 = Hacl.UInt64.t
let hint8_p = buffer h8

val load_64_bytes:
  out:buffer h64{length out = 10} ->
  b:hint8_p{length b = 64} ->
  Stack unit
    (requires (fun h -> live h out /\ live h b))
    (ensures (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1
      (* /\ (let out = as_seq h1 out in *)
      (*    little_endian (as_seq h0 b) *)
      (*     == eval_q_10 out.[0] out.[1] out.[2] out.[3] out.[4] out.[5] out.[6] out.[7] out.[8] out.[9]) *)
    ))
let load_64_bytes out b =
  let b0 = hload64_le (Buffer.sub b 0ul 8ul) in
  let b1 = hload64_le (Buffer.sub b 7ul 8ul) in
  let b2 = hload64_le (Buffer.sub b 14ul 8ul) in
  let b3 = hload64_le (Buffer.sub b 21ul 8ul) in
  let b4 = hload64_le (Buffer.sub b 28ul 8ul) in
  let b5 = hload64_le (Buffer.sub b 35ul 8ul) in
  let b6 = hload64_le (Buffer.sub b 42ul 8ul) in
  let b7 = hload64_le (Buffer.sub b 49ul 8ul) in
  let b8 = hload64_le (Buffer.sub b 56ul 8ul) in
  
  let o0 = b0 &^ 0xffffffffffffffuL in
  let o1 = b1 &^ 0xffffffffffffffuL in
  let o2 = b2 &^ 0xffffffffffffffuL in
  let o3 = b3 &^ 0xffffffffffffffuL in
  let o4 = b4 &^ 0xffffffffffffffuL in
  let o5 = b5 &^ 0xffffffffffffffuL in
  let o6 = b6 &^ 0xffffffffffffffuL in
  let o7 = b7 &^ 0xffffffffffffffuL in
  let o8 = b8 &^ 0xffffffffffffffuL in
  let o9 = b8 >>^ 56ul in
  Hacl.Lib.Create64.make_h64_10 out o0 o1 o2 o3 o4 o5 o6 o7 o8 o9


val load_32_bytes:
  out:buffer h64{length out = 5} ->
  b:hint8_p{length b = 32} ->
  Stack unit
    (requires (fun h -> live h out /\ live h b))
    (ensures (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1
      (* /\ (let out = as_seq h1 out in *)
      (*    little_endian (as_seq h0 b) *)
      (*     == eval_q_10 out.[0] out.[1] out.[2] out.[3] out.[4] out.[5] out.[6] out.[7] out.[8] out.[9]) *)
    ))
let load_32_bytes out b =
  let b0 = hload64_le (Buffer.sub b 0ul 8ul) in
  let b1 = hload64_le (Buffer.sub b 7ul 8ul) in
  let b2 = hload64_le (Buffer.sub b 14ul 8ul) in
  let b3 = hload64_le (Buffer.sub b 21ul 8ul) in
  let b4 = hload32_le (Buffer.sub b 28ul 4ul) in
  let b4 = Hacl.Cast.sint32_to_sint64 b4 in
  let o0 = b0 &^ 0xffffffffffffffuL in
  let o1 = b1 &^ 0xffffffffffffffuL in
  let o2 = b2 &^ 0xffffffffffffffuL in
  let o3 = b3 &^ 0xffffffffffffffuL in
  let o4 = b4                       in
  Hacl.Lib.Create64.make_h64_5 out o0 o1 o2 o3 o4
