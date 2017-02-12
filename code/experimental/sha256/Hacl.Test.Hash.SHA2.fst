module Hacl.Test.Hash.SHA2

open FStar.Buffer

module SHA2 = Hacl.Hash.SHA2.L256


val test_1a: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_1a () =

  (* Push a new memory frame *)
  (**) push_frame();

  let output_len = 32ul in
  let output = FStar.Buffer.create 0uy output_len in

  let plaintext_len = 3ul in
  let plaintext = FStar.Buffer.createL [
      0x61uy; 0x62uy; 0x63uy;
    ] in

  let expected = FStar.Buffer.createL [
      0xBAuy; 0x78uy; 0x16uy; 0xBFuy; 0x8Fuy; 0x01uy; 0xCFuy; 0xEAuy;
      0x41uy; 0x41uy; 0x40uy; 0xDEuy; 0x5Duy; 0xAEuy; 0x22uy; 0x23uy;
      0xB0uy; 0x03uy; 0x61uy; 0xA3uy; 0x96uy; 0x17uy; 0x7Auy; 0x9Cuy;
      0xB4uy; 0x10uy; 0xFFuy; 0x61uy; 0xF2uy; 0x00uy; 0x15uy; 0xADuy
    ] in

  (* Allocate memory for state *)
  let ctx = FStar.Buffer.create 0ul 137ul in

  (* Call the hash function *)
  SHA2.init ctx;
  SHA2.update_last ctx plaintext plaintext_len;
  SHA2.finish ctx output;

  (* Display the result *)
  TestLib.compare_and_print (C.string_of_literal "Test 1a") expected output 32ul;

  (* Pop the memory frame *)
  (**) pop_frame()


val test_1b: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_1b () =

  (* Push a new memory frame *)
  (**) push_frame();

  let output_len = 32ul in
  let output = FStar.Buffer.create 0uy output_len in

  let plaintext_len = 3ul in
  let plaintext = FStar.Buffer.createL [
      0x61uy; 0x62uy; 0x63uy;
    ] in

  let expected = FStar.Buffer.createL [
      0xbauy; 0x78uy; 0x16uy; 0xbfuy; 0x8fuy; 0x01uy; 0xcfuy; 0xeauy;
      0x41uy; 0x41uy; 0x40uy; 0xdeuy; 0x5duy; 0xaeuy; 0x22uy; 0x23uy;
      0xb0uy; 0x03uy; 0x61uy; 0xa3uy; 0x96uy; 0x17uy; 0x7auy; 0x9cuy;
      0xb4uy; 0x10uy; 0xffuy; 0x61uy; 0xf2uy; 0x00uy; 0x15uy; 0xaduy
    ] in

  (* Allocate memory for state *)
  let ctx = FStar.Buffer.create 0ul 137ul in

  (* Call the hash function *)
  SHA2.sha256 output plaintext plaintext_len;

  (* Display the result *)
  TestLib.compare_and_print (C.string_of_literal "Test 1b") expected output 32ul;

  (* Pop the memory frame *)
  (**) pop_frame()



val main: unit -> ST FStar.Int32.t
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let main () =

  (* Run test vector 1 *)
  test_1a ();
  test_1b ();

  (* Exit the program *)
  C.exit_success
