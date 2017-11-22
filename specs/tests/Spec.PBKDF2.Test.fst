module Spec.PBKDF2.Test

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0"

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq
open Spec.Lib.Stateful

module Hash = Spec.Hash
module HMAC = Spec.HMAC
module PBKDF2 = Spec.PBKDF2

//
// Test 1
//

let test1_pwd = List.Tot.map u8_from_UInt8 [
  0x70uy; 0x61uy; 0x73uy; 0x73uy; 0x77uy; 0x6fuy; 0x72uy; 0x64uy; 0x00uy
]

let test1_salt = List.Tot.map u8_from_UInt8 [
  0x73uy; 0x61uy; 0x6cuy; 0x74uy; 0x00uy
]

let test1_counter = 1
let dkLen = 20

let test1_expected = List.Tot.map u8_from_UInt8 [
  0x12uy; 0x0fuy; 0xb6uy; 0xcfuy; 0xfcuy; 0xf8uy; 0xb3uy; 0x2cuy;
  0x43uy; 0xe7uy; 0x22uy; 0x52uy; 0x56uy; 0xc4uy; 0xf8uy; 0x37uy;
  0xa8uy; 0x65uy; 0x48uy; 0xc9uy
]

// TODO: get correct size
let numbytes_size_t = 4

let test () =
  let p_len: size_t = 8 in
  let s_len: size_t = 4 in
  let x = s_len + numbytes_size_t + (Hash.size_block Hash.SHA2_256) in
  assert_norm(List.Tot.length test1_pwd = p_len);
  assert_norm(List.Tot.length test1_salt = s_len);
  assert_norm(List.Tot.length test1_expected = 20);
  assert_norm(dkLen = 20);
  assert_norm(x <= max_size_t);
  assert_norm(x < Hash.max_input Hash.SHA2_256);
  let test1_pwd : lbytes 8 = createL test1_pwd in
  let test1_salt : lbytes 4 = createL test1_salt in
  let test1_expected : lbytes 20 = createL test1_expected in
  let output : lbytes 20 = PBKDF2.pbkdf2 Hash.SHA2_256 p_len test1_pwd s_len test1_salt test1_counter dkLen in
  let result = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) output test1_expected in
  IO.print_string   "Expected key:";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (as_list test1_expected);
  IO.print_string "\nComputed key:";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (as_list output);
  if result then   IO.print_string "\nSuccess!\n"
  else IO.print_string "\nFailure :(\n"
