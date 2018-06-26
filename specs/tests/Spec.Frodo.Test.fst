module Spec.Frodo.Test

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Frodo

let print_and_compare (len:size_nat) (test_expected:lbytes len) (test_result:lbytes len) =
  IO.print_string "\n\nResult:   ";
  List.iter (fun a -> IO.print_string (UInt8.to_string_hex (u8_to_UInt8 a))) (as_list test_result);
  IO.print_string "\nExpected: ";
  List.iter (fun a -> IO.print_string (UInt8.to_string_hex (u8_to_UInt8 a))) (as_list test_expected);
  for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test_expected test_result

let test_frodo keypair_len keypaircoins enc_len enccoins ss_len ss_expected =
  let keypaircoins:lbytes keypair_len = createL keypaircoins in
  let enccoins:lbytes enc_len = createL enccoins in
  let ss_expected:lbytes ss_len = createL ss_expected in

  let pk, sk = crypto_kem_keypair keypaircoins in
  let ct, ss1 = crypto_kem_enc enccoins pk in
  let ss2 = crypto_kem_dec ct sk in

  let r_ss = print_and_compare ss_len ss1 ss2 in
  let r_ss1 = print_and_compare ss_len ss_expected ss2 in
  r_ss && r_ss1

//
// Test1. FrodoKEM-640. CSHAKE128
//
let test1_keypaircoins = List.Tot.map u8_from_UInt8 [
  0x4buy; 0x62uy; 0x2duy; 0xe1uy; 0x35uy; 0x01uy; 0x19uy; 0xc4uy; 0x5auy; 0x9fuy; 0x2euy; 0x2euy; 0xf3uy; 0xdcuy; 0x5duy; 0xf5uy;
  0x0auy; 0x75uy; 0x9duy; 0x13uy; 0x8cuy; 0xdfuy; 0xbduy; 0x64uy; 0xc8uy; 0x1cuy; 0xc7uy; 0xccuy; 0x2fuy; 0x51uy; 0x33uy; 0x45uy;
  0xd5uy; 0xa4uy; 0x5auy; 0x4cuy; 0xeduy; 0x06uy; 0x40uy; 0x3cuy; 0x55uy; 0x57uy; 0xe8uy; 0x71uy; 0x13uy; 0xcbuy; 0x30uy; 0xeauy]
let test1_enccoins = List.Tot.map u8_from_UInt8 [
  0x08uy; 0xe2uy; 0x55uy; 0x38uy; 0x48uy; 0x4cuy; 0xd7uy; 0xf1uy; 0x61uy; 0x32uy; 0x48uy; 0xfeuy; 0x6cuy; 0x9fuy; 0x6buy; 0x4euy]
let test1_ss_expected = List.Tot.map u8_from_UInt8 [
  0xdauy; 0xa9uy; 0xb2uy; 0x2cuy; 0x55uy; 0xafuy; 0x73uy; 0xa3uy; 0xeauy; 0xa0uy; 0x6duy; 0x08uy; 0x1euy; 0x1auy; 0x56uy; 0x06uy]

let test () =
  let result = test_frodo 48 test1_keypaircoins 16 test1_enccoins 16 test1_ss_expected in
  if result then IO.print_string "\n\nFrodoKEM : Success!\n"
  else IO.print_string "\n\nFrodoKEM: Failure :(\n"
