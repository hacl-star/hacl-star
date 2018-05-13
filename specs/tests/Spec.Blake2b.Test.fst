module Spec.Blake2b.Test

#reset-options "--z3rlimit 100 --max_fuel 0"

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq

//
// Test 1
//

let test1_plaintext_list  = List.Tot.map u8_from_UInt8 [
  0x61uy; 0x62uy; 0x63uy
]
let test1_plaintext : lbytes 3 =
  assert_norm (List.Tot.length test1_plaintext_list = 3);createL test1_plaintext_list

let test1_expected_list = List.Tot.map u8_from_UInt8 [
  0xBAuy; 0x80uy; 0xA5uy; 0x3Fuy; 0x98uy; 0x1Cuy; 0x4Duy; 0x0Duy; 0x6Auy; 0x27uy; 0x97uy; 0xB6uy; 0x9Fuy; 0x12uy; 0xF6uy; 0xE9uy;
  0x4Cuy; 0x21uy; 0x2Fuy; 0x14uy; 0x68uy; 0x5Auy; 0xC4uy; 0xB7uy; 0x4Buy; 0x12uy; 0xBBuy; 0x6Fuy; 0xDBuy; 0xFFuy; 0xA2uy; 0xD1uy;
  0x7Duy; 0x87uy; 0xC5uy; 0x39uy; 0x2Auy; 0xABuy; 0x79uy; 0x2Duy; 0xC2uy; 0x52uy; 0xD5uy; 0xDEuy; 0x45uy; 0x33uy; 0xCCuy; 0x95uy;
  0x18uy; 0xD3uy; 0x8Auy; 0xA8uy; 0xDBuy; 0xF1uy; 0x92uy; 0x5Auy; 0xB9uy; 0x23uy; 0x86uy; 0xEDuy; 0xD4uy; 0x00uy; 0x99uy; 0x23uy
]
let test1_expected : lbytes 64 = assert_norm (List.Tot.length test1_expected_list = 64); createL test1_expected_list

//
// Main
//

let test () =

  IO.print_string "\nTEST 1\n";
  let test1_plaintext_len : size_nat = 64 in
  let test1_result : lbytes 64 =
    Spec.Blake2b.blake2b 3 test1_plaintext 0 (createL []) 64
  in
  let result1 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test1_expected test1_result in

  IO.print_string "\nResult   BLAKE2B: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (as_list test1_result);

  IO.print_string "\nExpected BLAKE2B: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (as_list test1_expected);

  if result1 then IO.print_string "\nBLAKE2B Test1 : Success!\n"
  else IO.print_string "\nBLAKE2B Test1: Failure :(\n"
