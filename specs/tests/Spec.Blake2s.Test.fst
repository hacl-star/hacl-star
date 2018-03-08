module Spec.Blake2s.Test

#reset-options "--z3rlimit 100 --max_fuel 0"

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq

//
// Test 1
//

let test1_plaintext_list  = List.Tot.map u8_from_UInt8 [
  0x00uy; 0x61uy; 0x62uy; 0x63uy
]
let test1_plaintext : lbytes 4 =
  assert_norm (List.Tot.length test1_plaintext_list = 4);createL test1_plaintext_list

let test1_expected_list = List.Tot.map u8_from_UInt8 [
  0x50uy; 0x8Cuy; 0x5Euy; 0x8Cuy; 0x32uy; 0x7Cuy; 0x14uy; 0xE2uy;
  0xE1uy; 0xA7uy; 0x2Buy; 0xA3uy; 0x4Euy; 0xEBuy; 0x45uy; 0x2Fuy;
  0x37uy; 0x45uy; 0x8Buy; 0x20uy; 0x9Euy; 0xD6uy; 0x3Auy; 0x29uy;
  0x4Duy; 0x99uy; 0x9Buy; 0x4Cuy; 0x86uy; 0x67uy; 0x59uy; 0x82uy;
]
let test1_expected : lbytes 32 = assert_norm (List.Tot.length test1_expected_list = 32); createL test1_expected_list

//
// Main
//

let test () =

  IO.print_string "\nTEST 1\n";
  let test1_plaintext_len : size_nat = 32 in
  let test1_result : lbytes 32 = 
    Spec.Blake2s.blake2s 4 test1_plaintext 0 (createL []) 32
  in
  let result1 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test1_expected test1_result in

  IO.print_string "\nResult   SHAKE 256: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string_hex (u8_to_UInt8 a))) (as_list test1_result);

  IO.print_string "\nExpected SHAKE 256: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string_hex (u8_to_UInt8 a))) (as_list test1_expected);

  if result1 then IO.print_string "\nSHAKE 256 Test1 : Success!\n"
  else IO.print_string "\nSHAKE 256 Test1: Failure :(\n"
