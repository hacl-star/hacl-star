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
  0x61uy; 0x62uy; 0x63uy
]
let test1_plaintext : lbytes 3 =
  assert_norm (List.Tot.length test1_plaintext_list = 3);
  createL test1_plaintext_list

let test1_expected_list = List.Tot.map u8_from_UInt8 [
  0x50uy; 0x8Cuy; 0x5Euy; 0x8Cuy; 0x32uy; 0x7Cuy; 0x14uy; 0xE2uy;
  0xE1uy; 0xA7uy; 0x2Buy; 0xA3uy; 0x4Euy; 0xEBuy; 0x45uy; 0x2Fuy;
  0x37uy; 0x45uy; 0x8Buy; 0x20uy; 0x9Euy; 0xD6uy; 0x3Auy; 0x29uy;
  0x4Duy; 0x99uy; 0x9Buy; 0x4Cuy; 0x86uy; 0x67uy; 0x59uy; 0x82uy;
]
let test1_expected : lbytes 32 =
  assert_norm (List.Tot.length test1_expected_list = 32);
  createL test1_expected_list



let test2_plaintext_list = List.Tot.map u8_from_UInt8 [ 0x00uy ]
let test2_plaintext : lbytes 1 =
  assert_norm (List.Tot.length test2_plaintext_list = 1);
  createL test2_plaintext_list

let test2_key_list = List.Tot.map u8_from_UInt8 [
  0x00uy; 0x01uy; 0x02uy; 0x03uy; 0x04uy; 0x05uy; 0x06uy; 0x07uy;
  0x08uy; 0x09uy; 0x0auy; 0x0buy; 0x0cuy; 0x0duy; 0x0euy; 0x0fuy;
  0x10uy; 0x11uy; 0x12uy; 0x13uy; 0x14uy; 0x15uy; 0x16uy; 0x17uy;
  0x18uy; 0x19uy; 0x1auy; 0x1buy; 0x1cuy; 0x1duy; 0x1euy; 0x1fuy ]

let test2_key : lbytes 32 =
  assert_norm (List.Tot.length test2_key_list = 32);
  createL test2_key_list

let test2_expected_list = List.Tot.map u8_from_UInt8 [
  0x40uy; 0xd1uy; 0x5fuy; 0xeeuy; 0x7cuy; 0x32uy; 0x88uy; 0x30uy;
  0x16uy; 0x6auy; 0xc3uy; 0xf9uy; 0x18uy; 0x65uy; 0x0fuy; 0x80uy;
  0x7euy; 0x7euy; 0x01uy; 0xe1uy; 0x77uy; 0x25uy; 0x8cuy; 0xdcuy;
  0x0auy; 0x39uy; 0xb1uy; 0x1fuy; 0x59uy; 0x80uy; 0x66uy; 0xf1uy ]

let test2_expected : lbytes 32 =
  assert_norm (List.Tot.length test2_expected_list = 32);
  createL test2_expected_list

//
// Main
//

let test () =

  IO.print_string "\nTEST 1";
  let test1_plaintext_len : size_nat = 32 in
  let test1_result : lbytes 32 =
    Spec.Blake2s.blake2s 3 test1_plaintext 0 (createL []) 32
  in
  let result1 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test1_expected test1_result in

  IO.print_string "\n1. Result  : ";
  List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a)) (as_list test1_result);

  IO.print_string "\n1. Expected: ";
  List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a)) (as_list test1_expected);

  //
  // TEST 2
  //
  IO.print_string "\nTEST 2";

  let test2_result : lbytes 32 =
    Spec.Blake2s.blake2s 32 test2_key 1 test2_plaintext 32
  in
  let result2 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test2_expected test2_result in

  IO.print_string "\n2. Result  : ";
  List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a)) (as_list test2_result);

  IO.print_string "\n2. Expected: ";
  List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a)) (as_list test2_expected);

  if result1 && result2 then IO.print_string "\n\nSuccess !\n"
  else IO.print_string "\n\nFailed !\n"


