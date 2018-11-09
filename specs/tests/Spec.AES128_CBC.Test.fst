module Spec.AES128_CBC.Test

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence


open Spec.AES128_CBC


let key : lbytes 16 = createL [u8 0x2b; u8 0x7e; u8 0x15; u8 0x16; u8 0x28; u8 0xae; u8 0xd2; u8 0xa6; u8 0xab; u8 0xf7; u8 0x15; u8 0x88; u8 0x09; u8 0xcf; u8 0x4f; u8 0x3c]

let iv : lbytes 16 = createL [u8 0x00; u8 0x01; u8 0x02; u8 0x03; u8 0x04; u8 0x05; u8 0x06; u8 0x07; u8 0x08; u8 0x09; u8 0x0a; u8 0x0b; u8 0x0c; u8 0x0d; u8 0x0e; u8 0x0f]



let test1_plaintext: lbytes 16 = createL [u8 0x6b; u8 0xc1; u8 0xbe; u8 0xe2; u8 0x2e; u8 0x40; u8 0x9f; u8 0x96; u8 0xe9; u8 0x3d; u8 0x7e; u8 0x11; u8 0x73; u8 0x93; u8 0x17; u8 0x2a]

let test1_input_block: lbytes 16 = createL [u8 0x6b; u8 0xc0; u8 0xbc; u8 0xe1; u8 0x2a; u8 0x45; u8 0x99; u8 0x91; u8 0xe1; u8 0x34; u8 0x74; u8 0x1a; u8 0x7f; u8 0x9e; u8 0x19; u8 0x25]

let test1_output: lbytes 16 = createL [u8 0x76; u8 0x49; u8 0xab; u8 0xac; u8 0x81; u8 0x19; u8 0xb2; u8 0x46; u8 0xce; u8 0xe9; u8 0x8e; u8 0x9b; u8 0x12; u8 0xe9; u8 0x19; u8 0x7d]

let test1_ciphertext: lbytes 16 = createL [u8 0x76; u8 0x49; u8 0xab; u8 0xac; u8 0x81; u8 0x19; u8 0xb2; u8 0x46; u8 0xce; u8 0xe9; u8 0x8e; u8 0x9b; u8 0x12; u8 0xe9; u8 0x19; u8 0x7d]



let test2_plaintext: lbytes 16 = createL [u8 0xae; u8 0x2d; u8 0x8a; u8 0x57; u8 0x1e; u8 0x03; u8 0xac; u8 0x9c; u8 0x9e; u8 0xb7; u8 0x6f; u8 0xac; u8 0x45; u8 0xaf; u8 0x8e; u8 0x51]

let test2_input_block: lbytes 16 = createL [u8 0xd8; u8 0x64; u8 0x21; u8 0xfb; u8 0x9f; u8 0x1a; u8 0x1e; u8 0xda; u8 0x50; u8 0x5e; u8 0xe1; u8 0x37; u8 0x57; u8 0x46; u8 0x97; u8 0x2c]

let test2_output: lbytes 16 = createL [u8 0x50; u8 0x86; u8 0xcb; u8 0x9b; u8 0x50; u8 0x72; u8 0x19; u8 0xee; u8 0x95; u8 0xdb; u8 0x11; u8 0x3a; u8 0x91; u8 0x76; u8 0x78; u8 0xb2]

let test2_ciphertext: lbytes 16 = createL [u8 0x50; u8 0x86; u8 0xcb; u8 0x9b; u8 0x50; u8 0x72; u8 0x19; u8 0xee; u8 0x95; u8 0xdb; u8 0x11; u8 0x3a; u8 0x91; u8 0x76; u8 0x78; u8 0xb2]


val test_aescbc:
    input: bytes
  -> key: lbytes size_block
  -> iv: lbytes size_block
  -> expected: lbytes size_block ->
  FStar.All.ML unit

let test_aescbc input key iv expected =
  let ilen = length input in

  let computed_encrypt = Spec.AES128_CBC.cbc_encrypt_block test1_plaintext key iv in
  let computed_decrypt = Spec.AES128_CBC.cbc_decrypt_block computed_encrypt key iv in
IO.print_string  "\nPlaintext: ";
  List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a);  IO.print_string ":") (to_list test1_plaintext);
  IO.print_string  "\nComputed Ciphertext: ";
  List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a);  IO.print_string ":") (to_list computed_encrypt);
  IO.print_string  "\nComputed Plaintext: ";
  List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a);  IO.print_string ":") (to_list computed_decrypt)


  (* IO.print_string  "\nPlaintext: "; *)
  (* List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a);  IO.print_string ":") (to_list input); *)
  (* let computed_encrypt = Spec.AES128_CBC.aes128_cbc_encrypt input key iv in *)
  (* let result0 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) computed_encrypt expected in *)
  (* IO.print_string  "\nExpected ciphertext: "; *)
  (* List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a);  IO.print_string ":") (to_list expected); *)
  (* IO.print_string  "\nComputed ciphertext: "; *)
  (* List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a);  IO.print_string ":") (to_list computed_encrypt); *)

  (* let ocomputed_decrypt = Spec.AES128_CBC.aes128_cbc_decrypt computed_encrypt key iv in *)
  (* let result1 = *)
  (*   match ocomputed_decrypt with *)
  (*   | None -> IO.print_string "\nCould not decrypt!\n"; false *)
  (*   | Some computed_decrypt -> begin *)
  (*     let result1 = for_all2 #uint8 #uint8 #ilen (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) computed_decrypt input in *)
  (*     IO.print_string  "\nComputed plaintext: "; *)
  (*     List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a);  IO.print_string ":") (to_list computed_decrypt); *)
  (*     result1 end in *)
  (* IO.print_string "\n"; *)
  (* if result0 && result1 then IO.print_string "Success!\n" *)
  (* else (IO.print_string "Failure!\n") *)


let _ =
  (* test_aescbc test1_plaintext key iv test1_output; *)
  test_aescbc (to_seq (test1_plaintext @| test2_plaintext)) key iv (test1_output @| test2_output)
