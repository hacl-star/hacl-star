module Spec.GCM.Test

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0"

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq
open Spec.Lib.Stateful

module GCM = Spec.GCM

let key_length = 16
let ghash_length = 16

(* Test 1 *)

let test1_hash_key = List.Tot.map u8_from_UInt8 [
  0x66uy; 0xe9uy; 0x4buy; 0xd4uy; 0xefuy; 0x8auy; 0x2cuy; 0x3buy; 0x88uy;
  0x4cuy; 0xfauy; 0x59uy; 0xcauy; 0x34uy; 0x2buy; 0x2euy
]

let test1_ciphertext = List.Tot.map u8_from_UInt8 [
  0x03uy; 0x88uy; 0xdauy; 0xceuy; 0x60uy; 0xb6uy; 0xa3uy; 0x92uy; 0xf3uy;
  0x28uy; 0xc2uy; 0xb9uy; 0x71uy; 0xb2uy; 0xfeuy; 0x78uy
]

let test1_aad = List.Tot.map u8_from_UInt8 []

let test1_expected = List.Tot.map u8_from_UInt8 [
  0xf3uy; 0x8cuy; 0xbbuy; 0x1auy; 0xd6uy; 0x92uy; 0x23uy; 0xdcuy; 0xc3uy;
  0x45uy; 0x7auy; 0xe5uy; 0xb6uy; 0xb0uy; 0xf8uy; 0x85uy
]

let test1_c_length: size_nat = 16
let test1_aad_length: size_nat = 0

(* Test 2 *)

let test2_hash_key = List.Tot.map u8_from_UInt8 [
  0xb8uy; 0x3buy; 0x53uy; 0x37uy; 0x08uy; 0xbfuy; 0x53uy; 0x5duy; 0x0auy;
  0xa6uy; 0xe5uy; 0x29uy; 0x80uy; 0xd5uy; 0x3buy; 0x78uy
]

let test2_ciphertext = List.Tot.map u8_from_UInt8 [
  0x42uy; 0x83uy; 0x1euy; 0xc2uy; 0x21uy; 0x77uy; 0x74uy; 0x24uy; 0x4buy;
  0x72uy; 0x21uy; 0xb7uy; 0x84uy; 0xd0uy; 0xd4uy; 0x9cuy; 0xe3uy; 0xaauy;
  0x21uy; 0x2fuy; 0x2cuy; 0x02uy; 0xa4uy; 0xe0uy; 0x35uy; 0xc1uy; 0x7euy;
  0x23uy; 0x29uy; 0xacuy; 0xa1uy; 0x2euy; 0x21uy; 0xd5uy; 0x14uy; 0xb2uy;
  0x54uy; 0x66uy; 0x93uy; 0x1cuy; 0x7duy; 0x8fuy; 0x6auy; 0x5auy; 0xacuy;
  0x84uy; 0xaauy; 0x05uy; 0x1buy; 0xa3uy; 0x0buy; 0x39uy; 0x6auy; 0x0auy;
  0xacuy; 0x97uy; 0x3duy; 0x58uy; 0xe0uy; 0x91uy; 0x47uy; 0x3fuy; 0x59uy;
  0x85uy
]

let test2_aad = List.Tot.map u8_from_UInt8 []

let test2_expected = List.Tot.map u8_from_UInt8 [
  0x7fuy; 0x1buy; 0x32uy; 0xb8uy; 0x1buy; 0x82uy; 0x0duy; 0x02uy; 0x61uy;
  0x4fuy; 0x88uy; 0x95uy; 0xacuy; 0x1duy; 0x4euy; 0xacuy
]

let test2_c_length: size_nat = 64
let test2_aad_length: size_nat = 0

(* Test 3 *)

let test3_hash_key = List.Tot.map u8_from_UInt8 [
  0xb8uy; 0x3buy; 0x53uy; 0x37uy; 0x08uy; 0xbfuy; 0x53uy; 0x5duy; 0x0auy;
  0xa6uy; 0xe5uy; 0x29uy; 0x80uy; 0xd5uy; 0x3buy; 0x78uy
]

let test3_ciphertext = List.Tot.map u8_from_UInt8 [
  0x42uy; 0x83uy; 0x1euy; 0xc2uy; 0x21uy; 0x77uy; 0x74uy; 0x24uy; 0x4buy;
  0x72uy; 0x21uy; 0xb7uy; 0x84uy; 0xd0uy; 0xd4uy; 0x9cuy; 0xe3uy; 0xaauy;
  0x21uy; 0x2fuy; 0x2cuy; 0x02uy; 0xa4uy; 0xe0uy; 0x35uy; 0xc1uy; 0x7euy;
  0x23uy; 0x29uy; 0xacuy; 0xa1uy; 0x2euy; 0x21uy; 0xd5uy; 0x14uy; 0xb2uy;
  0x54uy; 0x66uy; 0x93uy; 0x1cuy; 0x7duy; 0x8fuy; 0x6auy; 0x5auy; 0xacuy;
  0x84uy; 0xaauy; 0x05uy; 0x1buy; 0xa3uy; 0x0buy; 0x39uy; 0x6auy; 0x0auy;
  0xacuy; 0x97uy; 0x3duy; 0x58uy; 0xe0uy; 0x91uy
]

let test3_aad = List.Tot.map u8_from_UInt8 [
  0xfeuy; 0xeduy; 0xfauy; 0xceuy; 0xdeuy; 0xaduy; 0xbeuy; 0xefuy; 0xfeuy;
  0xeduy; 0xfauy; 0xceuy; 0xdeuy; 0xaduy; 0xbeuy; 0xefuy; 0xabuy; 0xaduy;
  0xdauy; 0xd2uy
]

let test3_expected = List.Tot.map u8_from_UInt8 [
  0x69uy; 0x8euy; 0x57uy; 0xf7uy; 0x0euy; 0x6euy; 0xccuy; 0x7fuy; 0xd9uy;
  0x46uy; 0x3buy; 0x72uy; 0x60uy; 0xa9uy; 0xaeuy; 0x5fuy
]

let test3_c_length: size_nat = 60
let test3_aad_length: size_nat = 20

let test () =
  let output = GCM.ghash test1_c_length test1_ciphertext test1_aad_length test1_aad test1_hash_key in
  let result = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) output test1_expected in
  IO.print_string   "Expected tag: ";
  let test_expected : lbytes key_length = createL test1_expected in
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a));  IO.print_string ":") (as_list test_expected);
  IO.print_string "\nComputed tag: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a));  IO.print_string ":") (as_list output);
  if result then IO.print_string "\nSuccess!\n"
  else IO.print_string "\nFailure :(\n";

  let output = GCM.ghash test2_c_length test2_ciphertext test2_aad_length test2_aad test2_hash_key in
  let result = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) output test2_expected in
  IO.print_string   "Expected tag: ";
  let test_expected : lbytes key_length = createL test2_expected in
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a));  IO.print_string ":") (as_list test_expected);
  IO.print_string "\nComputed tag: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a));  IO.print_string ":") (as_list output);
  if result then IO.print_string "\nSuccess!\n"
  else IO.print_string "\nFailure :(\n";

  let output = GCM.ghash test3_c_length test3_ciphertext test3_aad_length test3_aad test3_hash_key in
  let result = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) output test3_expected in
  IO.print_string   "Expected tag: ";
  let test_expected : lbytes key_length = createL test3_expected in
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a));  IO.print_string ":") (as_list test_expected);
  IO.print_string "\nComputed tag: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a));  IO.print_string ":") (as_list output);
  if result then IO.print_string "\nSuccess!\n"
  else IO.print_string "\nFailure :(\n"
