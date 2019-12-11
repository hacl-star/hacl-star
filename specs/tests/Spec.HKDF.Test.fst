module Spec.HKDF.Test

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0"

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

module HMAC = Spec.Agile.HMAC
module HKDF = Spec.Agile.HKDF


//
// Test 1
//

let test1_hash = Spec.Hash.Definitions.SHA2_256

let test1_ikm = List.Tot.map u8_from_UInt8 [
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy
]

let test1_salt = List.Tot.map u8_from_UInt8 [
  0x00uy; 0x01uy; 0x02uy; 0x03uy; 0x04uy; 0x05uy; 0x06uy; 0x07uy;
  0x08uy; 0x09uy; 0x0auy; 0x0buy; 0x0cuy
]

let test1_info = List.Tot.map u8_from_UInt8 [
  0xf0uy; 0xf1uy; 0xf2uy; 0xf3uy; 0xf4uy; 0xf5uy; 0xf6uy; 0xf7uy;
  0xf8uy; 0xf9uy
]

let test1_len = 42

let test1_expected_prk = List.Tot.map u8_from_UInt8 [
  0x07uy; 0x77uy; 0x09uy; 0x36uy; 0x2cuy; 0x2euy; 0x32uy; 0xdfuy;
  0x0duy; 0xdcuy; 0x3fuy; 0x0duy; 0xc4uy; 0x7buy; 0xbauy; 0x63uy;
  0x90uy; 0xb6uy; 0xc7uy; 0x3buy; 0xb5uy; 0x0fuy; 0x9cuy; 0x31uy;
  0x22uy; 0xecuy; 0x84uy; 0x4auy; 0xd7uy; 0xc2uy; 0xb3uy; 0xe5uy
]

let test1_expected_okm = List.Tot.map u8_from_UInt8 [
  0x3cuy; 0xb2uy; 0x5fuy; 0x25uy; 0xfauy; 0xacuy; 0xd5uy; 0x7auy;
  0x90uy; 0x43uy; 0x4fuy; 0x64uy; 0xd0uy; 0x36uy; 0x2fuy; 0x2auy;
  0x2duy; 0x2duy; 0x0auy; 0x90uy; 0xcfuy; 0x1auy; 0x5auy; 0x4cuy;
  0x5duy; 0xb0uy; 0x2duy; 0x56uy; 0xecuy; 0xc4uy; 0xc5uy; 0xbfuy;
  0x34uy; 0x00uy; 0x72uy; 0x08uy; 0xd5uy; 0xb8uy; 0x87uy; 0x18uy;
  0x58uy; 0x65uy
]

//
// Test 2
//

let test2_hash = Spec.Hash.Definitions.SHA2_256

let test2_ikm = List.Tot.map u8_from_UInt8 [
  0x00uy; 0x01uy; 0x02uy; 0x03uy; 0x04uy; 0x05uy; 0x06uy; 0x07uy;
  0x08uy; 0x09uy; 0x0auy; 0x0buy; 0x0cuy; 0x0duy; 0x0euy; 0x0fuy;
  0x10uy; 0x11uy; 0x12uy; 0x13uy; 0x14uy; 0x15uy; 0x16uy; 0x17uy;
  0x18uy; 0x19uy; 0x1auy; 0x1buy; 0x1cuy; 0x1duy; 0x1euy; 0x1fuy;
  0x20uy; 0x21uy; 0x22uy; 0x23uy; 0x24uy; 0x25uy; 0x26uy; 0x27uy;
  0x28uy; 0x29uy; 0x2auy; 0x2buy; 0x2cuy; 0x2duy; 0x2euy; 0x2fuy;
  0x30uy; 0x31uy; 0x32uy; 0x33uy; 0x34uy; 0x35uy; 0x36uy; 0x37uy;
  0x38uy; 0x39uy; 0x3auy; 0x3buy; 0x3cuy; 0x3duy; 0x3euy; 0x3fuy;
  0x40uy; 0x41uy; 0x42uy; 0x43uy; 0x44uy; 0x45uy; 0x46uy; 0x47uy;
  0x48uy; 0x49uy; 0x4auy; 0x4buy; 0x4cuy; 0x4duy; 0x4euy; 0x4fuy
]

let test2_salt = List.Tot.map u8_from_UInt8 [
  0x60uy; 0x61uy; 0x62uy; 0x63uy; 0x64uy; 0x65uy; 0x66uy; 0x67uy;
  0x68uy; 0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy; 0x6euy; 0x6fuy;
  0x70uy; 0x71uy; 0x72uy; 0x73uy; 0x74uy; 0x75uy; 0x76uy; 0x77uy;
  0x78uy; 0x79uy; 0x7auy; 0x7buy; 0x7cuy; 0x7duy; 0x7euy; 0x7fuy;
  0x80uy; 0x81uy; 0x82uy; 0x83uy; 0x84uy; 0x85uy; 0x86uy; 0x87uy;
  0x88uy; 0x89uy; 0x8auy; 0x8buy; 0x8cuy; 0x8duy; 0x8euy; 0x8fuy;
  0x90uy; 0x91uy; 0x92uy; 0x93uy; 0x94uy; 0x95uy; 0x96uy; 0x97uy;
  0x98uy; 0x99uy; 0x9auy; 0x9buy; 0x9cuy; 0x9duy; 0x9euy; 0x9fuy;
  0xa0uy; 0xa1uy; 0xa2uy; 0xa3uy; 0xa4uy; 0xa5uy; 0xa6uy; 0xa7uy;
  0xa8uy; 0xa9uy; 0xaauy; 0xabuy; 0xacuy; 0xaduy; 0xaeuy; 0xafuy
]

let test2_info = List.Tot.map u8_from_UInt8 [
  0xb0uy; 0xb1uy; 0xb2uy; 0xb3uy; 0xb4uy; 0xb5uy; 0xb6uy; 0xb7uy;
  0xb8uy; 0xb9uy; 0xbauy; 0xbbuy; 0xbcuy; 0xbduy; 0xbeuy; 0xbfuy;
  0xc0uy; 0xc1uy; 0xc2uy; 0xc3uy; 0xc4uy; 0xc5uy; 0xc6uy; 0xc7uy;
  0xc8uy; 0xc9uy; 0xcauy; 0xcbuy; 0xccuy; 0xcduy; 0xceuy; 0xcfuy;
  0xd0uy; 0xd1uy; 0xd2uy; 0xd3uy; 0xd4uy; 0xd5uy; 0xd6uy; 0xd7uy;
  0xd8uy; 0xd9uy; 0xdauy; 0xdbuy; 0xdcuy; 0xdduy; 0xdeuy; 0xdfuy;
  0xe0uy; 0xe1uy; 0xe2uy; 0xe3uy; 0xe4uy; 0xe5uy; 0xe6uy; 0xe7uy;
  0xe8uy; 0xe9uy; 0xeauy; 0xebuy; 0xecuy; 0xeduy; 0xeeuy; 0xefuy;
  0xf0uy; 0xf1uy; 0xf2uy; 0xf3uy; 0xf4uy; 0xf5uy; 0xf6uy; 0xf7uy;
  0xf8uy; 0xf9uy; 0xfauy; 0xfbuy; 0xfcuy; 0xfduy; 0xfeuy; 0xffuy
]

let test2_len = 82

let test2_expected_prk = List.Tot.map u8_from_UInt8 [
  0x06uy; 0xa6uy; 0xb8uy; 0x8cuy; 0x58uy; 0x53uy; 0x36uy; 0x1auy;
  0x06uy; 0x10uy; 0x4cuy; 0x9cuy; 0xebuy; 0x35uy; 0xb4uy; 0x5cuy;
  0xefuy; 0x76uy; 0x00uy; 0x14uy; 0x90uy; 0x46uy; 0x71uy; 0x01uy;
  0x4auy; 0x19uy; 0x3fuy; 0x40uy; 0xc1uy; 0x5fuy; 0xc2uy; 0x44uy
]

let test2_expected_okm = List.Tot.map u8_from_UInt8 [
  0xb1uy; 0x1euy; 0x39uy; 0x8duy; 0xc8uy; 0x03uy; 0x27uy; 0xa1uy;
  0xc8uy; 0xe7uy; 0xf7uy; 0x8cuy; 0x59uy; 0x6auy; 0x49uy; 0x34uy;
  0x4fuy; 0x01uy; 0x2euy; 0xdauy; 0x2duy; 0x4euy; 0xfauy; 0xd8uy;
  0xa0uy; 0x50uy; 0xccuy; 0x4cuy; 0x19uy; 0xafuy; 0xa9uy; 0x7cuy;
  0x59uy; 0x04uy; 0x5auy; 0x99uy; 0xcauy; 0xc7uy; 0x82uy; 0x72uy;
  0x71uy; 0xcbuy; 0x41uy; 0xc6uy; 0x5euy; 0x59uy; 0x0euy; 0x09uy;
  0xdauy; 0x32uy; 0x75uy; 0x60uy; 0x0cuy; 0x2fuy; 0x09uy; 0xb8uy;
  0x36uy; 0x77uy; 0x93uy; 0xa9uy; 0xacuy; 0xa3uy; 0xdbuy; 0x71uy;
  0xccuy; 0x30uy; 0xc5uy; 0x81uy; 0x79uy; 0xecuy; 0x3euy; 0x87uy;
  0xc1uy; 0x4cuy; 0x01uy; 0xd5uy; 0xc1uy; 0xf3uy; 0x43uy; 0x4fuy;
  0x1duy; 0x87uy
]


//
// Test 3
//

let test3_hash = Spec.Hash.Definitions.SHA2_256

let test3_ikm = List.Tot.map u8_from_UInt8 [
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy
]

let test3_salt = List.Tot.map u8_from_UInt8 []

let test3_info = List.Tot.map u8_from_UInt8 []

let test3_len = 42

let test3_expected_prk = List.Tot.map u8_from_UInt8 [
  0x19uy; 0xefuy; 0x24uy; 0xa3uy; 0x2cuy; 0x71uy; 0x7buy; 0x16uy;
  0x7fuy; 0x33uy; 0xa9uy; 0x1duy; 0x6fuy; 0x64uy; 0x8buy; 0xdfuy;
  0x96uy; 0x59uy; 0x67uy; 0x76uy; 0xafuy; 0xdbuy; 0x63uy; 0x77uy;
  0xacuy; 0x43uy; 0x4cuy; 0x1cuy; 0x29uy; 0x3cuy; 0xcbuy; 0x04uy
]

let test3_expected_okm = List.Tot.map u8_from_UInt8 [
  0x8duy; 0xa4uy; 0xe7uy; 0x75uy; 0xa5uy; 0x63uy; 0xc1uy; 0x8fuy;
  0x71uy; 0x5fuy; 0x80uy; 0x2auy; 0x06uy; 0x3cuy; 0x5auy; 0x31uy;
  0xb8uy; 0xa1uy; 0x1fuy; 0x5cuy; 0x5euy; 0xe1uy; 0x87uy; 0x9euy;
  0xc3uy; 0x45uy; 0x4euy; 0x5fuy; 0x3cuy; 0x73uy; 0x8duy; 0x2duy;
  0x9duy; 0x20uy; 0x13uy; 0x95uy; 0xfauy; 0xa4uy; 0xb6uy; 0x1auy;
  0x96uy; 0xc8uy
]

//
// Main
//

let test () =

  IO.print_string "\nTEST 1\n";
  let test1_ikm_len : size_nat = List.Tot.length test1_ikm in
  let test1_ikm : lbytes test1_ikm_len = of_list test1_ikm in
  let test1_salt_len :size_nat = List.Tot.length test1_salt in
  let test1_salt : lbytes test1_salt_len = of_list test1_salt in
  let test1_info_len : size_nat = List.Tot.length test1_info in
  let test1_info : lbytes test1_info_len = of_list test1_info in
  let test1_expected_prk_len : size_nat = List.Tot.length test1_expected_prk in
  let test1_expected_prk : lbytes test1_expected_prk_len = of_list test1_expected_prk in
  let test1_expected_okm_len : size_nat = List.Tot.length test1_expected_okm in
  let test1_expected_okm : lbytes test1_expected_okm_len = of_list test1_expected_okm in
  let test1_prk : lbytes test1_expected_prk_len =
    HKDF.extract test1_hash test1_salt test1_ikm in
  let test1_okm : lbytes test1_expected_okm_len =
    HKDF.expand test1_hash test1_expected_prk test1_info test1_len in
  let r1_a = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test1_expected_prk test1_prk in
  let r1_b = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test1_expected_okm test1_okm in
  IO.print_string "\nExpected PRK: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test1_expected_prk);
  IO.print_string "\nComputed PRK: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test1_prk);
  IO.print_string "\nExpected OKM: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test1_expected_okm);
  IO.print_string "\nComputed OKM: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test1_okm);

  if r1_a then IO.print_string "\nHKDF Extract: Success!\n"
  else IO.print_string "\nHKDF Extract: Failure :(\n";
  if r1_b then IO.print_string "HKDF Expand: Success!\n"
  else IO.print_string "HKDF Expand: Failure :(\n";

  IO.print_string "\nTEST 2\n";
  let test2_ikm_len : size_nat = List.Tot.length test2_ikm in
  let test2_ikm : lbytes test2_ikm_len = of_list test2_ikm in
  let test2_salt_len :size_nat = List.Tot.length test2_salt in
  let test2_salt : lbytes test2_salt_len = of_list test2_salt in
  let test2_info_len : size_nat = List.Tot.length test2_info in
  let test2_info : lbytes test2_info_len = of_list test2_info in
  let test2_expected_prk_len : size_nat = List.Tot.length test2_expected_prk in
  let test2_expected_prk : lbytes test2_expected_prk_len = of_list test2_expected_prk in
  let test2_expected_okm_len : size_nat = List.Tot.length test2_expected_okm in
  let test2_expected_okm : lbytes test2_expected_okm_len = of_list test2_expected_okm in
  let test2_prk : lbytes test2_expected_prk_len =
    HKDF.extract test2_hash test2_salt test2_ikm in
  let test2_okm : lbytes test2_expected_okm_len =
    HKDF.expand test2_hash test2_expected_prk test2_info test2_len in
  let r2_a = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test2_expected_prk test2_prk in
  let r2_b = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test2_expected_okm test2_okm in
  IO.print_string "\nExpected PRK: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test2_expected_prk);
  IO.print_string "\nComputed PRK: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test2_prk);
  IO.print_string "\nExpected OKM: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test2_expected_okm);
  IO.print_string "\nComputed OKM: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test2_okm);

  if r2_a then IO.print_string "\nHKDF Extract: Success!\n"
  else IO.print_string "\nHKDF Extract: Failure :(\n";
  if r2_b then IO.print_string "HKDF Expand: Success!\n"
  else IO.print_string "HKDF Expand: Failure :(\n";


  IO.print_string "\nTEST 3\n";
  let test3_ikm_len : size_nat = List.Tot.length test3_ikm in
  let test3_ikm : lbytes test3_ikm_len = of_list test3_ikm in
  let test3_salt_len :size_nat = List.Tot.length test3_salt in
  let test3_salt : lbytes test3_salt_len = of_list test3_salt in
  let test3_info_len : size_nat = List.Tot.length test3_info in
  let test3_info : lbytes test3_info_len = of_list test3_info in
  let test3_expected_prk_len : size_nat = List.Tot.length test3_expected_prk in
  let test3_expected_prk : lbytes test3_expected_prk_len = of_list test3_expected_prk in
  let test3_expected_okm_len : size_nat = List.Tot.length test3_expected_okm in
  let test3_expected_okm : lbytes test3_expected_okm_len = of_list test3_expected_okm in
  let test3_prk : lbytes test3_expected_prk_len =
    HKDF.extract test3_hash test3_salt test3_ikm in
  let test3_okm : lbytes test3_expected_okm_len =
    HKDF.expand test3_hash test3_expected_prk test3_info test3_len in
  let r3_a = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test3_expected_prk test3_prk in
  let r3_b = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test3_expected_okm test3_okm in
  IO.print_string "\nExpected PRK: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test3_expected_prk);
  IO.print_string "\nComputed PRK: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test3_prk);
  IO.print_string "\nExpected OKM: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test3_expected_okm);
  IO.print_string "\nComputed OKM: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test3_okm);

  if r3_a then IO.print_string "\nHKDF Extract: Success!\n"
  else IO.print_string "\nHKDF Extract: Failure :(\n";
  if r3_b then IO.print_string "HKDF Expand: Success!\n"
  else IO.print_string "HKDF Expand: Failure :(\n";

  // Composite result
  if r1_a && r1_b && r2_a && r2_b && r3_a && r3_b then begin IO.print_string "\nComposite result: Success!\n"; true end
  else begin IO.print_string "\nComposite result: Failure :(\n"; false end
