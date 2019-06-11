module Spec.AES256_GCM.Test

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0"

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence


module AEAD = Spec.AES_GCM


let key_length = AEAD.size_key Spec.AES.AES256

let test1_key = List.Tot.map u8 [
0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00;
0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00
]

let test1_nonce = List.Tot.map u8 [
0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00
]

let test1_msg = List.Tot.map u8 [

]

let test1_aad = List.Tot.map u8 [

]

let test1_expected = List.Tot.map u8 [
0x53; 0xe20f; 0x8a; 0xfd; 0xc7; 0x45; 0x36; 0xb9; 0xa9; 0x63; 0xd4; 0xf1; 0xc4; 0xcd; 0x73; 0x8b
]

let test1_ciphertext = List.Tot.map u8 [

]


let test2_key = List.Tot.map u8 [
  0x84; 0x0f; 0x02; 0xff; 0x9b; 0xa0; 0xa8; 0x8a;
  0x8b; 0xde; 0x50; 0x66; 0xa6; 0x60; 0x89; 0x20;
  0xfd; 0x7a; 0xab; 0xa4; 0xed; 0xa1; 0x0e; 0x93;
  0x01; 0x68; 0x35; 0x7d; 0xca; 0x6a; 0xb9; 0x42
]

let test2_nonce = List.Tot.map u8 [
  0xad; 0x77; 0x02; 0xeb; 0xd4; 0x6f; 0xeb; 0x36;
  0xb0; 0x6a; 0xad; 0xb4
]

let test2_msg = List.Tot.map u8 [
  0x73; 0xf2; 0xd6; 0xda; 0x5f; 0x4e; 0x03; 0x28;
  0x6b; 0x05; 0x29; 0x66; 0xc3; 0xd6; 0xe8; 0xf6
]

let test2_aad = List.Tot.map u8 [
  0x2c; 0x3b; 0x09; 0x03; 0xe7; 0x7d; 0xc8; 0xa1;
  0xb3; 0x78; 0xf6; 0xd1; 0xb5; 0x6e; 0xbd; 0x8b;
  0xf5; 0x65; 0x57; 0xb3
]

let test2_expected = List.Tot.map u8 [
  0xc7; 0xf2; 0xe0; 0x47; 0x88; 0xad; 0xf6; 0x6e;
  0x66; 0x87; 0x19; 0x00; 0x2f; 0x59; 0xa9; 0x2e;
  0xf2; 0x76; 0x3a; 0xfe; 0xde; 0x44; 0x52; 0xbe;
  0x55; 0x93; 0x16; 0x9a; 0x13
]

let test2_tag = List.Tot.map u8 [
  0xc7; 0xf2; 0xe0; 0x47; 0x88; 0xad; 0xf6; 0x6e;
  0x66; 0x87; 0x19; 0x00; 0x2f; 0x59; 0xa9; 0x2e;
]

val test_aesgcm:
  text_len:size_nat ->
  text:lbytes text_len ->
  aad_len:size_nat ->
  aad:lbytes aad_len ->
  n_len:size_nat ->
  n:lbytes n_len ->
  k:lbytes key_length ->
  expected:lbytes (16 + text_len) ->
  i:size_nat ->
  FStar.All.ML unit

let test_aesgcm text_len text aad_len aad n_len n k expected i =
  IO.print_string " ================================ CIPHER ";
  IO.print_string (UInt8.to_string (u8_to_UInt8 (u8 i)));
  IO.print_string " ================================\n";
  let output = AEAD.aes256gcm_encrypt k n text aad in
  let ciphertext = sub (to_lseq output) 0 (length output - 16) in
  let mac = sub (to_lseq output) (length output - 16) 16 in
  let decrypted = AEAD.aes256gcm_decrypt k n aad ciphertext mac in
  let result0 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) ciphertext expected in
  let result1 =
    match decrypted with
    | Some dec ->
	   for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) dec text
    | None -> false in
  if result0 && result1 then (IO.print_string "Success!\n";
      IO.print_string  "\nExpected ciphertext: ";
    List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a);  IO.print_string ":") (to_list expected);
    IO.print_string "\nComputed ciphertext: ";
    List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a);  IO.print_string ":") (to_list ciphertext);
    IO.print_string "\nExpected tag: ";
    List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a);  IO.print_string ":") (to_list mac);
    IO.print_newline())
  else (IO.print_string "Failure!\n";
    IO.print_string  "\nExpected ciphertext: ";
    List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a);  IO.print_string ":") (to_list expected);
    IO.print_string "\nComputed ciphertext: ";
    List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a);  IO.print_string ":") (to_list ciphertext);
    IO.print_string "\nExpected plaintext: ";
    List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a);  IO.print_string ":") (to_list text);
    (match decrypted with
      | Some dec ->  IO.print_string "\nComputed plaintext: ";
		    List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a);
		    IO.print_string ":") (to_list dec);
		    IO.print_string "\n"
      | None -> IO.print_string "\n AEAD decryption failed!\n"))


let test () =
  test_aesgcm (List.Tot.length test1_msg) (of_list test1_msg) (List.Tot.length test1_aad) (of_list test1_aad) (List.Tot.length test1_nonce) (of_list test1_nonce) (of_list test1_key) (of_list test1_expected) 1;
  test_aesgcm (List.Tot.length test2_msg) (of_list test2_msg) (List.Tot.length test2_aad) (of_list test2_aad) (List.Tot.length test2_nonce) (of_list test2_nonce) (of_list test2_key) (of_list test2_expected) 2;
  ()
