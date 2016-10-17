module Hacl.Test.SHA2.L256

val main: unit -> ST FStar.Int32.t
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))

let main () =
  push_frame();

  (* Define various sizes *)
  let size_hash = 32ul in
  let size_state = 256ul in
  let size_input = 3ul in

  (* Create state and output spaces *)
  let state  = FStar.Buffer.create 0uy size_state in
  let output = FStar.Buffer.create 0uy size_hash in

  (* Define input and expected output *)
  let input    = FStar.Buffer.createL [0x6auy; 0x6buy; 0x6cuy] in
  let expected = FStar.Buffer.createL [
    0xbauy; 0x78uy; 0x16uy; 0xbfuy; 0x8fuy; 0x01uy;
    0xcfuy; 0xeauy; 0x41uy; 0x41uy; 0x40uy; 0xdeuy;
    0x5duy; 0xaeuy; 0x22uy; 0x23uy; 0xb0uy; 0x03uy;
    0x61uy; 0xa3uy; 0x96uy; 0x17uy; 0x7auy; 0x9cuy;
    0xb4uy; 0x10uy; 0xffuy; 0x61uy; 0xf2uy; 0x00uy;
    0x15ad ] in

  (* Call the function *)
  Hacl.Hash.SHA2.L256.sha256 output plaintext size_input;

  (* Compare the expected result with output *)
  C.compare_and_print2 expected output len;
  pop_frame();

  (* Exit *)
  C.exit_success
