module SampleProject

(* This file is provided for test purposes only. It can be built in a single
 * invocation of KreMLin:

  krml -ldopt -levercrypt SampleProject.fst -no-prefix SampleProject -I
    ../multiplexer/ -add-include '"kremstr.h"' KRML_HOME/kremlib/testlib.c
    -add-include '"testlib.h"' -ldopt -L.. -o sample-project.exe

 * Then, it can be run with:
 * - LD_LIBRARY_PATH=.. ./sample-project.exe (Linux)
 * - DYLD_LIBRARY_PATH=.. ./sample-project.exe (OSX)
 * - PATH=.. ./sample-project.exe (Windows)
 *)

module B = FStar.Buffer
module U32 = FStar.UInt32

open FStar.HyperStack.ST
open EverCrypt.Helpers

val test1: unit -> St unit
let test1 () =
  push_frame();

  let output_len = 32ul in
  let output = B.create 0uy output_len in

  let plaintext_len = 3ul in
  let plaintext = B.createL [
      0x61uy; 0x62uy; 0x63uy;
    ] in

  let expected = B.createL [
      0xBAuy; 0x78uy; 0x16uy; 0xBFuy; 0x8Fuy; 0x01uy; 0xCFuy; 0xEAuy;
      0x41uy; 0x41uy; 0x40uy; 0xDEuy; 0x5Duy; 0xAEuy; 0x22uy; 0x23uy;
      0xB0uy; 0x03uy; 0x61uy; 0xA3uy; 0x96uy; 0x17uy; 0x7Auy; 0x9Cuy;
      0xB4uy; 0x10uy; 0xFFuy; 0x61uy; 0xF2uy; 0x00uy; 0x15uy; 0xADuy
    ] in

  (* Allocate memory for state *)
  let ctx = B.create 0ul U32.(64ul +^ 64ul +^ 8ul +^ 1ul) in

  (* Call the hash function *)
  EverCrypt.sha256_init ctx;
  EverCrypt.sha256_update_last ctx plaintext plaintext_len;
  EverCrypt.sha256_finish ctx output;

  (* Display the result *)
  TestLib.compare_and_print !$"Test 1a" expected output 32ul;

  pop_frame()

let main (): St C.exit_code =
  push_frame ();
  test1 ();
  EverCrypt.(init (Some Vale));
  test1 ();
  EverCrypt.(init (Some Hacl));
  pop_frame ();
  C.EXIT_SUCCESS
