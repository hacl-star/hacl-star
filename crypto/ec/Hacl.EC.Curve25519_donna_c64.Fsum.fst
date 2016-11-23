module Hacl.EC.Curve25519_donna_c64.Fsum


open FStar.Mul
open FStar.HyperStack
open FStar.Buffer
open FStar.Int.Cast
open Hacl.UInt64
open Hacl.Cast

open Hacl.EC.Curve25519_donna_c64.Bigint


module U8 = FStar.UInt8
module U32 = FStar.UInt32

module H8 = Hacl.UInt8
module H64 = Hacl.UInt64
module H128 = Hacl.UInt128


inline_for_extraction let zero_8 = uint8_to_sint8 0uy
inline_for_extraction let zero_64 = uint64_to_sint64 0uL
inline_for_extraction let one_8 = uint8_to_sint8 1uy
inline_for_extraction let one_64 = uint64_to_sint64 1uL


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 100"

val fsum: output:felem -> input:felem -> Stack unit
  (requires (fun h -> bound h output 52 /\ bound h input 52))
  (ensures (fun h0 _ h1 -> bound h0 output 52 /\ bound h0 input 52
    /\ bound h1 output 53 /\ modifies_1 output h0 h1
    /\ eval h1 output = eval h0 output + eval h0 input))
let fsum output input =
  let input0 = input.(0ul) in let input1 = input.(1ul) in
  let input2 = input.(2ul) in let input3 = input.(3ul) in
  let input4 = input.(4ul) in let output0 = output.(0ul) in
  let output1 = output.(1ul) in let output2 = output.(2ul) in
  let output3 = output.(3ul) in let output4 = output.(4ul) in
  assert_norm (pow2 52 = 2 * pow2 51); assert_norm (pow2 53 = 2 * pow2 52);
  let o0 = output0 +^ input0 in
  let o1 = output1 +^ input1 in
  let o2 = output2 +^ input2 in
  let o3 = output3 +^ input3 in
  let o4 = output4 +^ input4 in
  output.(0ul) <- o0;
  output.(1ul) <- o1;
  output.(2ul) <- o2;
  output.(3ul) <- o3;
  output.(4ul) <- o4


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 100"

(* Output: x_i < 2^54 *)
val fdifference: output:felem -> input:felem -> Stack unit
  (requires (fun h -> bound h output 52 /\ bound h input 52))
  (ensures (fun h0 _ h1 -> bound h0 output 52 /\ bound h0 input 52
    /\ bound h1 output 55 /\ modifies_1 output h0 h1
    /\ eval h1 output = 8 * (pow2 255 - 19) + eval h0 input - eval h0 output))
let fdifference output input =
  let two54m152 = uint64_to_sint64 0x3fffffffffff68uL in
  let two54m8   = uint64_to_sint64 0x3ffffffffffff8uL   in
  assert_norm (v two54m152 = pow2 54 - 152); assert_norm (v two54m8 = pow2 54 - 8);
  assert_norm (pow2 54 = 2 * pow2 53); assert_norm (pow2 53 = 2 * pow2 52);
  assert_norm(pow2 52 = 2 * pow2 51); assert_norm (pow2 55 = 2 * pow2 54);
  assert_norm(v two54m152 + pow2 51 * v two54m8 + pow2 102 * v two54m8
    + pow2 153 * v two54m8 + pow2 204 * v two54m8 = 8 * (pow2 255 - 19));
  let input0 = input.(0ul) in let input1 = input.(1ul) in
  let input2 = input.(2ul) in let input3 = input.(3ul) in
  let input4 = input.(4ul) in let output0 = output.(0ul) in
  let output1 = output.(1ul) in let output2 = output.(2ul) in
  let output3 = output.(3ul) in let output4 = output.(4ul) in
  let o0 = input0 +^ two54m152 -^ output0 in
  let o1 = input1 +^ two54m8   -^ output1 in
  let o2 = input2 +^ two54m8   -^ output2 in
  let o3 = input3 +^ two54m8   -^ output3 in
  let o4 = input4 +^ two54m8   -^ output4 in
  output.(0ul) <- o0;
  output.(1ul) <- o1;
  output.(2ul) <- o2;
  output.(3ul) <- o3;
  output.(4ul) <- o4
