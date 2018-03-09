module Spec.Keccak.Test

#reset-options "--z3rlimit 100 --max_fuel 0"

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq

//
// Test 1
//

let test1_plaintext = create 32 (u8 0xFF)

let test1_expected = List.Tot.map u8_from_UInt8 [
  0xf5uy; 0x97uy; 0x7cuy; 0x82uy; 0x83uy; 0x54uy; 0x6auy; 0x63uy;
  0x72uy; 0x3buy; 0xc3uy; 0x1duy; 0x26uy; 0x19uy; 0x12uy; 0x4fuy;
  0x11uy; 0xdbuy; 0x46uy; 0x58uy; 0x64uy; 0x33uy; 0x36uy; 0x74uy;
  0x1duy; 0xf8uy; 0x17uy; 0x57uy; 0xd5uy; 0xaduy; 0x30uy; 0x62uy
]

//
// Main
//

let test () =

  IO.print_string "\nTEST 1\n";
  let test1_plaintext_len : size_nat = 32 in
  let test1_expected : lbytes 32 = createL test1_expected in
  let test1_result : lbytes 32 = Spec.Keccak.keccak Spec.Keccak.shake256_rate test1_plaintext_len test1_plaintext (u8 0x1F) 32 in
  let result1 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test1_expected test1_result in

  IO.print_string "\nResult   SHAKE 256: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string_hex (u8_to_UInt8 a))) (as_list test1_result);

  IO.print_string "\nExpected SHAKE 256: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string_hex (u8_to_UInt8 a))) (as_list test1_expected);

  if result1 then IO.print_string "\nSHAKE 256 Test1 : Success!\n"
  else IO.print_string "\nSHAKE 256 Test1: Failure :(\n"
