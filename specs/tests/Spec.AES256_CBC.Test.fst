module Spec.AES256_CBC.Test

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Spec.AES256_CBC
open Lib.LoopCombinators

let test1_input_key = of_list (List.Tot.map u8 [
  0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00;
  0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00;
  0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00;
  0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00
])

let test1_input_iv = of_list (List.Tot.map u8 [
  0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00;
  0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00
])

let test1_input_plaintext = of_list (List.Tot.map u8 [
  0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00;
  0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00
])

let test1_output_ciphertext = of_list (List.Tot.map u8 [
  0xFE; 0x3C; 0x53; 0x65; 0x3E; 0x2F; 0x45; 0xB5;
  0x6F; 0xCD; 0x88; 0xB2; 0xCC; 0x89; 0x8F; 0xF0
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
