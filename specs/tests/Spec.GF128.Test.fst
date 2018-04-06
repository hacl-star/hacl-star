module Spec.GF128.Test

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0"

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq
open Spec.Lib.Stateful

module GaloisField = Spec.GaloisField
module GF = Spec.GF128

let key_length = 16
let ghash_length = 16

(* Empty ciphertext test *)

let test1_gmul_hash_key = List.Tot.map u8_from_UInt8 [
  0x66uy; 0xe9uy; 0x4buy; 0xd4uy; 0xefuy; 0x8auy; 0x2cuy; 0x3buy; 0x88uy;
  0x4cuy; 0xfauy; 0x59uy; 0xcauy; 0x34uy; 0x2buy; 0x2euy
]

let test1_gmul_ciphertext = List.Tot.map u8_from_UInt8 []

let test1_gmul_expected = List.Tot.map u8_from_UInt8 [
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy
]

let test1_gmul_c_length: size_nat = 0

(* Test 2 *)

let test2_gmul_hash_key = List.Tot.map u8_from_UInt8 [
  0x66uy; 0xe9uy; 0x4buy; 0xd4uy; 0xefuy; 0x8auy; 0x2cuy; 0x3buy; 0x88uy;
  0x4cuy; 0xfauy; 0x59uy; 0xcauy; 0x34uy; 0x2buy; 0x2euy
]

let test2_gmul_ciphertext = List.Tot.map u8_from_UInt8 [
  0x03uy; 0x88uy; 0xdauy; 0xceuy; 0x60uy; 0xb6uy; 0xa3uy; 0x92uy; 0xf3uy;
  0x28uy; 0xc2uy; 0xb9uy; 0x71uy; 0xb2uy; 0xfeuy; 0x78uy
]

let test2_gmul_expected = List.Tot.map u8_from_UInt8 [
  0x5euy; 0x2euy; 0xc7uy; 0x46uy; 0x91uy; 0x70uy; 0x62uy; 0x88uy; 0x2cuy;
  0x85uy; 0xb0uy; 0x68uy; 0x53uy; 0x53uy; 0xdeuy; 0xb7uy
]

let test2_gmul_c_length: size_nat = 16

(* Test 3 *)

let test3_gmul_hash_key = List.Tot.map u8_from_UInt8 [
  0x5euy; 0x2euy; 0xc7uy; 0x46uy; 0x91uy; 0x70uy; 0x62uy; 0x88uy; 0x2cuy;
  0x85uy; 0xb0uy; 0x68uy; 0x53uy; 0x53uy; 0xdeuy; 0x37uy
]

let test3_gmul_ciphertext = List.Tot.map u8_from_UInt8 [
  0x66uy; 0xe9uy; 0x4buy; 0xd4uy; 0xefuy; 0x8auy; 0x2cuy; 0x3buy; 0x88uy;
  0x4cuy; 0xfauy; 0x59uy; 0xcauy; 0x34uy; 0x2buy; 0x2euy
]

let test3_gmul_expected = List.Tot.map u8_from_UInt8 [
  0xf3uy; 0x8cuy; 0xbbuy; 0x1auy; 0xd6uy; 0x92uy; 0x23uy; 0xdcuy; 0xc3uy;
  0x45uy; 0x7auy; 0xe5uy; 0xb6uy; 0xb0uy; 0xf8uy; 0x85uy
]

let test3_gmul_c_length: size_nat = 16

(* Full GCM tests *)

let test () =
  let x : lbytes key_length = createL test2_gmul_hash_key in
  let x_int = nat_from_bytes_be x in
  let y : lbytes key_length = createL test2_gmul_ciphertext in
  let y_int = nat_from_bytes_be y in
  IO.print_string (Printf.sprintf "%d" x_int);
  IO.print_string " * ";
  IO.print_string (Printf.sprintf "%d" y_int);
  IO.print_string "\n";

  let a = GF.encode 16 test2_gmul_ciphertext in
  let b = GF.encode 16 test2_gmul_hash_key in
  let output = GaloisField.fmul_intel #GF.gf128 a b in
  let out = createL (GF.decode output) in
  let out_int = nat_from_bytes_be out in
  IO.print_string "Computed: ";
  IO.print_string (Printf.sprintf "%d" out_int);
  IO.print_string "\n";

  let output = GF.gmul test1_gmul_c_length test1_gmul_ciphertext test1_gmul_hash_key in
  let result = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) output test1_gmul_expected in
  IO.print_string   "Expected hash: ";
  let test_expected : lbytes key_length = createL test1_gmul_expected in
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a));  IO.print_string ":") (as_list test_expected);
  IO.print_string "\nComputed hash: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a));  IO.print_string ":") (as_list output);
  if result then IO.print_string "\nSuccess!\n"
  else IO.print_string "\nFailure :(\n";

  let output = GF.gmul test2_gmul_c_length test2_gmul_ciphertext test2_gmul_hash_key in
  let result = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) output test2_gmul_expected in
  IO.print_string   "Expected hash: ";
  let test_expected : lbytes key_length = createL test2_gmul_expected in
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a));  IO.print_string ":") (as_list test_expected);
  IO.print_string "\nComputed hash: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a));  IO.print_string ":") (as_list output);
  if result then IO.print_string "\nSuccess!\n"
  else IO.print_string "\nFailure :(\n";

  let output = GF.gmul test3_gmul_c_length test3_gmul_ciphertext test3_gmul_hash_key in
  let result = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) output test3_gmul_expected in
  IO.print_string   "Expected hash: ";
  let test_expected : lbytes key_length = createL test3_gmul_expected in
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a));  IO.print_string ":") (as_list test_expected);
  IO.print_string "\nComputed hash: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a));  IO.print_string ":") (as_list output);
  if result then IO.print_string "\nSuccess!\n"
  else IO.print_string "\nFailure :(\n";
  ()
