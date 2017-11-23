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

let test2_counter = 2
let test2_expected = List.Tot.map u8_from_UInt8 [
  0xaeuy; 0x4duy; 0x0cuy; 0x95uy; 0xafuy; 0x6buy; 0x46uy; 0xd3uy;
  0x2duy; 0x0auy; 0xdfuy; 0xf9uy; 0x28uy; 0xf0uy; 0x6duy; 0xd0uy;
  0x2auy; 0x30uy; 0x3fuy; 0x8euy
]

let test5_counter = 3
let test5_expected = List.Tot.map u8_from_UInt8 [
  0xaduy; 0x35uy; 0x24uy; 0x0auy; 0xc6uy; 0x83uy; 0xfeuy; 0xbfuy;
  0xafuy; 0x3cuy; 0xd4uy; 0x9duy; 0x84uy; 0x54uy; 0x73uy; 0xfbuy;
  0xbbuy; 0xaauy; 0x24uy; 0x37uy
]

let test6_counter = 100
let test6_expected = List.Tot.map u8_from_UInt8 [
  0x07uy; 0xe6uy; 0x99uy; 0x71uy; 0x80uy; 0xcfuy; 0x7fuy; 0x12uy;
  0x90uy; 0x4fuy; 0x04uy; 0x10uy; 0x0duy; 0x40uy; 0x5duy; 0x34uy;
  0x88uy; 0x8fuy; 0xdfuy; 0x62uy
]

let test3_counter = 4096
let test3_expected = List.Tot.map u8_from_UInt8 [
  0xc5uy; 0xe4uy; 0x78uy; 0xd5uy; 0x92uy; 0x88uy; 0xc8uy; 0x41uy;
  0xaauy; 0x53uy; 0x0duy; 0xb6uy; 0x84uy; 0x5cuy; 0x4cuy; 0x8duy;
  0x96uy; 0x28uy; 0x93uy; 0xa0uy
]

let test4_counter = 16777216
let test4_expected = List.Tot.map u8_from_UInt8 [
  0xcfuy; 0x81uy; 0xc6uy; 0x6fuy; 0xe8uy; 0xcfuy; 0xc0uy; 0x4duy;
  0x1fuy; 0x31uy; 0xecuy; 0xb6uy; 0x5duy; 0xabuy; 0x40uy; 0x89uy;
  0xf7uy; 0xf1uy; 0x79uy; 0xe8uy
]

let test7_counter = 100
let dkLen2 = 50
let test7_expected = List.Tot.map u8_from_UInt8 [
  0x07uy; 0xe6uy; 0x99uy; 0x71uy; 0x80uy; 0xcfuy; 0x7fuy; 0x12uy;
  0x90uy; 0x4fuy; 0x04uy; 0x10uy; 0x0duy; 0x40uy; 0x5duy; 0x34uy;
  0x88uy; 0x8fuy; 0xdfuy; 0x62uy; 0xafuy; 0x6duy; 0x50uy; 0x6auy;
  0x0euy; 0xccuy; 0x23uy; 0xb1uy; 0x96uy; 0xfeuy; 0x99uy; 0xd8uy;
  0x67uy; 0x52uy; 0x94uy; 0xecuy; 0x5auy; 0xa7uy; 0x94uy; 0x4buy;
  0x6auy; 0x86uy; 0xc5uy; 0x1fuy; 0xd9uy; 0x70uy; 0x51uy; 0xbbuy;
  0xefuy; 0xaduy
]

let test8_counter = 1000
let test8_expected = List.Tot.map u8_from_UInt8 [
  0x63uy; 0x2cuy; 0x28uy; 0x12uy; 0xe4uy; 0x6duy; 0x46uy; 0x04uy;
  0x10uy; 0x2buy; 0xa7uy; 0x61uy; 0x8euy; 0x9duy; 0x6duy; 0x7duy;
  0x2fuy; 0x81uy; 0x28uy; 0xf6uy; 0x26uy; 0x6buy; 0x4auy; 0x03uy;
  0x26uy; 0x4duy; 0x2auy; 0x04uy; 0x60uy; 0xb7uy; 0xdcuy; 0xb3uy;
  0x88uy; 0xb3uy; 0xb1uy; 0x13uy; 0x1fuy; 0x74uy; 0x1buy; 0xcbuy;
  0xebuy; 0x02uy; 0x54uy; 0x1cuy; 0x8cuy; 0x2euy; 0x97uy; 0xbduy;
  0x8buy; 0xeduy
]

// TODO: get correct size
let numbytes_size_t = 4

val test_c: expected:lbytes 20 -> counter:size_t -> FStar.All.ML unit
let test_c expected counter =
  let p_len: size_t = 8 in
  let s_len: size_t = 4 in
  let test_pwd : lbytes 8 = createL test1_pwd in
  let test_salt : lbytes 4 = createL test1_salt in
  let test_expected : lbytes 20 = createL expected in
  let output : lbytes 20 = PBKDF2.pbkdf2 Hash.SHA2_256 p_len test1_pwd s_len test1_salt counter dkLen in
  let result = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) output test_expected in
  IO.print_string   "Expected key:";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (as_list test_expected);
  IO.print_string "\nComputed key:";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (as_list output);
  if result then   IO.print_string "\nSuccess!\n"
  else IO.print_string "\nFailure :(\n"

val test_c2: expected:lbytes 50 -> counter:size_t -> FStar.All.ML unit
let test_c2 expected counter =
  let p_len: size_t = 8 in
  let s_len: size_t = 4 in
  let test_pwd : lbytes 8 = createL test1_pwd in
  let test_salt : lbytes 4 = createL test1_salt in
  let test_expected : lbytes 50 = createL expected in
  let output : lbytes 50 = PBKDF2.pbkdf2 Hash.SHA2_256 p_len test1_pwd s_len test1_salt counter dkLen2 in
  let result = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) output test_expected in
  IO.print_string   "Expected key:";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (as_list test_expected);
  IO.print_string "\nComputed key:";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (as_list output);
  if result then   IO.print_string "\nSuccess!\n"
  else IO.print_string "\nFailure :(\n"

let test () =
  let p_len: size_t = 8 in
  let s_len: size_t = 4 in
  let x = s_len + numbytes_size_t + (Hash.size_block Hash.SHA2_256) in
  assert_norm(List.Tot.length test1_pwd = p_len);
  assert_norm(List.Tot.length test1_salt = s_len);
  assert_norm(List.Tot.length test1_expected = 20);
  assert_norm(List.Tot.length test2_expected = 20);
  assert_norm(List.Tot.length test3_expected = 20);
  assert_norm(dkLen = 20);
  assert_norm(x <= max_size_t);
  assert_norm(x < Hash.max_input Hash.SHA2_256);

  test_c test1_expected test1_counter;
  test_c test2_expected test2_counter;
  (*test_c test3_expected test3_counter;
  test_c test4_expected test4_counter;*)
  test_c test5_expected test5_counter;
  test_c test6_expected test6_counter;
  test_c2 test7_expected test7_counter;
  test_c2 test8_expected test8_counter
