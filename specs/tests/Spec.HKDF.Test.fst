module Spec.HKDF.Test

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0"

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq
open Spec.Lib.Stateful

module Hash = Spec.SHA2
module HMAC = Spec.HMAC
module HKDF = Spec.HKDF


//
// Test 1
//

let test1_hash = Hash.parameters_sha2_256

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

//
// Main
//

let test () =
  let test1_ikm_len : size_t = List.Tot.length test1_ikm in
  let test1_ikm : lbytes test1_ikm_len = createL test1_ikm in
  let test1_salt_len :size_t = List.Tot.length test1_salt in
  let test1_salt : lbytes test1_salt_len = createL test1_salt in
  let test1_info_len : size_t = List.Tot.length test1_info in
  let test1_info : lbytes test1_info_len = createL test1_info in
  let test1_expected_prk_len : size_t = List.Tot.length test1_expected_prk in
  let test1_expected_prk : lbytes test1_expected_prk_len = createL test1_expected_prk in
  let test1_expected_okm_len : size_t = List.Tot.length test1_expected_okm in
  let test1_expected_okm : lbytes test1_expected_okm_len = createL test1_expected_okm in
  let test1_prk : lbytes test1_expected_prk_len =
    HKDF.hkdf_extract test1_hash test1_salt_len test1_salt test1_ikm_len test1_ikm in
  let test1_okm : lbytes test1_expected_okm_len =
    HKDF.hkdf_expand test1_hash test1_expected_prk_len test1_expected_prk test1_info_len test1_info test1_len in
  let r1_a = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test1_expected_prk test1_prk in
  let r1_b = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test1_expected_okm test1_okm in
  IO.print_string "\nExpected PRK: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (as_list test1_expected_prk);
  IO.print_string "\nComputed PRK: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (as_list test1_prk);
  IO.print_string "\nExpected OKM: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (as_list test1_expected_okm);
  IO.print_string "\nComputed OKM: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (as_list test1_okm);

  if r1_a then IO.print_string "\nHKDF Extract: Success!\n"
  else IO.print_string "\nHKDF Extract: Failure :(\n";
  if r1_b then IO.print_string "HKDF Expand: Success!\n"
  else IO.print_string "HKDF Expand: Failure :(\n"
