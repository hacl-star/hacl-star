module Spec.AES256_CBC.Test

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Spec.AES256_CBC
open Lib.LoopCombinators

let test1_input_key = of_list (List.Tot.map u8 [
  0x60; 0x3d; 0xeb; 0x10; 0x15; 0xca; 0x71; 0xbe;
  0x2b; 0x73; 0xae; 0xf0; 0x85; 0x7d; 0x77; 0x81;
  0x1f; 0x35; 0x2c; 0x07; 0x3b; 0x61; 0x08; 0xd7;
  0x2d; 0x98; 0x10; 0xa3; 0x09; 0x14; 0xdf; 0xf4
])

let test1_input_iv = of_list (List.Tot.map u8 [
  0x00; 0x01; 0x02; 0x03; 0x04; 0x05; 0x06; 0x07;
  0x08; 0x09; 0x0A; 0x0B; 0x0C; 0x0D; 0x0E; 0x0F
])

let test1_input_plaintext = of_list (List.Tot.map u8 [
  0x6b; 0xc1; 0xbe; 0xe2; 0x2e; 0x40; 0x9f; 0x96;
  0xe9; 0x3d; 0x7e; 0x11; 0x73; 0x93; 0x17; 0x2a
])

let test1_output_ciphertext = of_list (List.Tot.map u8 [
  0xf5; 0x8c; 0x4c; 0x04; 0xd6; 0xe5; 0xf1; 0xba;
  0x77; 0x9e; 0xab; 0xfb; 0x5f; 0x7b; 0xfb; 0xd6;
  0x48; 0x5a; 0x5c; 0x81; 0x51; 0x9c; 0xf3; 0x78;
  0xfa; 0x36; 0xd4; 0x2b; 0x85; 0x47; 0xed; 0xc0
])

let test_compare_buffers (msg:string) (expected:seq uint8) (computed:seq uint8) =
  IO.print_string "\n";
  IO.print_string msg;
  IO.print_string "\nexpected (";
  IO.print_uint32_dec (UInt32.uint_to_t (length expected));
  IO.print_string "):\n";
  FStar.List.iter (fun a -> IO.print_uint8_hex_pad (u8_to_UInt8 a)) (to_list expected);
  IO.print_string "\n";
  IO.print_string "computed (";
  IO.print_uint32_dec (UInt32.uint_to_t (length computed));
  IO.print_string "):\n";
  FStar.List.iter (fun a -> IO.print_uint8_hex_pad (u8_to_UInt8 a)) (to_list computed);
  IO.print_string "\n";
  let result =
    if length computed <> length expected then false else
    for_all2 #uint8 #uint8 #(length computed) (fun x y -> uint_to_nat #U8 x = uint_to_nat #U8 y)
      computed expected
  in
  if result then IO.print_string "\nSuccess !\n"
  else IO.print_string "\nFailed !\n"

let test() : FStar.All.ML unit =
  let computed1 = aes256_cbc_encrypt test1_input_key test1_input_iv test1_input_plaintext (length test1_input_plaintext) in
  test_compare_buffers "TEST1: encryption of one block" test1_output_ciphertext computed1;
  let computed2 = aes256_cbc_decrypt test1_input_key test1_input_iv computed1 (length computed1) in
  match computed2 with
  | Some computed2 ->
    test_compare_buffers "TEST2: decryption of the previous block" test1_input_plaintext computed2
  | None -> IO.print_string "Failure"
