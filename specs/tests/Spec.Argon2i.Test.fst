module Spec.Argon2i.Test

#reset-options "--z3rlimit 100 --max_fuel 0"

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq

let password_list = List.Tot.map u8_from_UInt8 [
  0x01uy; 0x01uy; 0x01uy; 0x01uy; 0x01uy; 0x01uy; 0x01uy; 0x01uy;
  0x01uy; 0x01uy; 0x01uy; 0x01uy; 0x01uy; 0x01uy; 0x01uy; 0x01uy;
  0x01uy; 0x01uy; 0x01uy; 0x01uy; 0x01uy; 0x01uy; 0x01uy; 0x01uy;
  0x01uy; 0x01uy; 0x01uy; 0x01uy; 0x01uy; 0x01uy; 0x01uy; 0x01uy
]

let password : lbytes 32 = assert_norm (List.Tot.length password_list = 32);createL password_list

let nonce_list = List.Tot.map u8_from_UInt8 [
  0x02uy; 0x02uy; 0x02uy; 0x02uy; 0x02uy; 0x02uy; 0x02uy; 0x02uy;
  0x02uy; 0x02uy; 0x02uy; 0x02uy; 0x02uy; 0x02uy; 0x02uy; 0x02uy
]

let nonce : lbytes 16 = assert_norm (List.Tot.length nonce_list = 16);createL nonce_list

let key_list = List.Tot.map u8_from_UInt8 [
  0x03uy; 0x03uy; 0x03uy; 0x03uy; 0x03uy; 0x03uy; 0x03uy; 0x03uy
]

let key : lbytes 8 = assert_norm (List.Tot.length key_list = 8);createL key_list

let associated_data_list = List.Tot.map u8_from_UInt8 [
  0x04uy; 0x04uy; 0x04uy; 0x04uy; 0x04uy; 0x04uy; 0x04uy; 0x04uy;
  0x04uy; 0x04uy; 0x04uy; 0x04uy
]

let associated_data : lbytes 12 = assert_norm (List.Tot.length associated_data_list = 12);
  createL associated_data_list

let expected_list = List.Tot.map u8_from_UInt8 [
  0xc8uy; 0x14uy; 0xd9uy; 0xd1uy; 0xdcuy; 0x7fuy; 0x37uy; 0xaauy;
  0x13uy; 0xf0uy; 0xd7uy; 0x7fuy; 0x24uy; 0x94uy; 0xbduy; 0xa1uy;
  0xc8uy; 0xdeuy; 0x6buy; 0x01uy; 0x6duy; 0xd3uy; 0x88uy; 0xd2uy;
  0x99uy; 0x52uy; 0xa4uy; 0xc4uy; 0x67uy; 0x2buy; 0x6cuy; 0xe8uy
]

let expected : lbytes 32 = assert_norm (List.Tot.length expected_list = 32); createL expected_list

let test () =

  IO.print_string "\nTEST 1\n";
  let p_len = 32 in
  let p = password in
  let s_len = 16 in
  let s = nonce in
  let lanes = 4 in
  let t_len = 32 in
  let m = 32 in
  let iterations = 3 in
  let x_len = 12 in
  let x = associated_data in
  let k_len = 8 in
  let k = key in
  let output : lbytes 32 =
    Spec.Argon2i.argon2i p_len p s_len s lanes t_len m iterations x_len x k_len k
  in
  let result = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) expected output in
  IO.print_string "\nResult   ARGON2i: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string_hex (u8_to_UInt8 a))) (as_list output);

  IO.print_string "\nExpected ARGON2i: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string_hex (u8_to_UInt8 a))) (as_list expected);

  if result then IO.print_string "\nARGON2i Test1 : Success!\n"
  else IO.print_string "\nARGON2i Test1: Failure :(\n"
