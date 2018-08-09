module Hacl.Test.SHA2_256

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Buffer
open FStar.UInt32

module Hash = Hacl.SHA2_256

val test_1a: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_1a () =

  (* Push a new memory frame *)
  (**) push_frame();

  [@inline_let]
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
  let ctx = FStar.Buffer.create 0ul Hash.size_state in

  (* Call the hash function *)
  Hash.init ctx;
  Hash.update_last ctx plaintext plaintext_len;
  Hash.finish ctx output;

  (* Display the result *)
  TestLib.compare_and_print (C.String.of_literal "Test 1a") expected output 32ul;

  (* Pop the memory frame *)
  (**) pop_frame()


val test_1b: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_1b () =

  (* Push a new memory frame *)
  (**) push_frame();

  [@inline_let]
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
  let ctx = FStar.Buffer.create 0ul Hash.size_state in

  (* Call the hash function *)
  Hash.hash output plaintext plaintext_len;

  (* Display the result *)
  TestLib.compare_and_print (C.String.of_literal "Test 1b") expected output 32ul;

  (* Pop the memory frame *)
  (**) pop_frame()



val test_2a: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_2a () =

  (* Push a new memory frame *)
  (**) push_frame();

  [@inline_let]
  let output_len = 32ul in
  let output = FStar.Buffer.create 0uy output_len in

  let plaintext_len = 0ul in
  let plaintext = FStar.Buffer.createL [] in

  let expected = FStar.Buffer.createL [
      0xe3uy; 0xb0uy; 0xc4uy; 0x42uy; 0x98uy; 0xfcuy; 0x1cuy; 0x14uy;
      0x9auy; 0xfbuy; 0xf4uy; 0xc8uy; 0x99uy; 0x6fuy; 0xb9uy; 0x24uy;
      0x27uy; 0xaeuy; 0x41uy; 0xe4uy; 0x64uy; 0x9buy; 0x93uy; 0x4cuy;
      0xa4uy; 0x95uy; 0x99uy; 0x1buy; 0x78uy; 0x52uy; 0xb8uy; 0x55uy
    ] in

  (* Allocate memory for state *)
  let ctx = FStar.Buffer.create 0ul Hash.size_state in

  (* Call the hash function *)
  Hash.init ctx;
  Hash.update_last ctx plaintext plaintext_len;
  Hash.finish ctx output;

  (* Display the result *)
  TestLib.compare_and_print (C.String.of_literal "Test 2a") expected output 32ul;

  (* Pop the memory frame *)
  (**) pop_frame()


val test_2b: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_2b () =

  (* Push a new memory frame *)
  (**) push_frame();

  [@inline_let]
  let output_len = 32ul in
  let output = FStar.Buffer.create 0uy output_len in

  let plaintext_len = 0ul in
  let plaintext = FStar.Buffer.createL [] in

  let expected = FStar.Buffer.createL [
      0xe3uy; 0xb0uy; 0xc4uy; 0x42uy; 0x98uy; 0xfcuy; 0x1cuy; 0x14uy;
      0x9auy; 0xfbuy; 0xf4uy; 0xc8uy; 0x99uy; 0x6fuy; 0xb9uy; 0x24uy;
      0x27uy; 0xaeuy; 0x41uy; 0xe4uy; 0x64uy; 0x9buy; 0x93uy; 0x4cuy;
      0xa4uy; 0x95uy; 0x99uy; 0x1buy; 0x78uy; 0x52uy; 0xb8uy; 0x55uy
    ] in

  (* Allocate memory for state *)
  let ctx = FStar.Buffer.create 0ul Hash.size_state in

  (* Call the hash function *)
  Hash.hash output plaintext plaintext_len;

  (* Display the result *)
  TestLib.compare_and_print (C.String.of_literal "Test 2b") expected output 32ul;

  (* Pop the memory frame *)
  (**) pop_frame()



val test_3a: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_3a () =

  (* Push a new memory frame *)
  (**) push_frame();

  [@inline_let]
  let output_len = 32ul in
  let output = FStar.Buffer.create 0uy output_len in

  let plaintext_len = 56ul in
  let plaintext = FStar.Buffer.createL [
    0x61uy; 0x62uy; 0x63uy; 0x64uy; 0x62uy; 0x63uy; 0x64uy; 0x65uy;
    0x63uy; 0x64uy; 0x65uy; 0x66uy; 0x64uy; 0x65uy; 0x66uy; 0x67uy;
    0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy;
    0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x68uy; 0x69uy; 0x6auy; 0x6buy;
    0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy;
    0x6buy; 0x6cuy; 0x6duy; 0x6euy; 0x6cuy; 0x6duy; 0x6euy; 0x6fuy;
    0x6duy; 0x6euy; 0x6fuy; 0x70uy; 0x6euy; 0x6fuy; 0x70uy; 0x71uy
  ] in

  let expected = FStar.Buffer.createL [
      0x24uy; 0x8duy; 0x6auy; 0x61uy; 0xd2uy; 0x06uy; 0x38uy; 0xb8uy;
      0xe5uy; 0xc0uy; 0x26uy; 0x93uy; 0x0cuy; 0x3euy; 0x60uy; 0x39uy;
      0xa3uy; 0x3cuy; 0xe4uy; 0x59uy; 0x64uy; 0xffuy; 0x21uy; 0x67uy;
      0xf6uy; 0xecuy; 0xeduy; 0xd4uy; 0x19uy; 0xdbuy; 0x06uy; 0xc1uy
  ] in

  (* Allocate memory for state *)
  let ctx = FStar.Buffer.create 0ul Hash.size_state in

  (* Call the hash function *)
  Hash.init ctx;
  Hash.update_last ctx plaintext plaintext_len;
  Hash.finish ctx output;

  (* Display the result *)
  TestLib.compare_and_print (C.String.of_literal "Test 3a") expected output 32ul;

  (* Pop the memory frame *)
  (**) pop_frame()


val test_3b: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_3b () =

  (* Push a new memory frame *)
  (**) push_frame();

  [@inline_let]
  let output_len = 32ul in
  let output = FStar.Buffer.create 0uy output_len in

  let plaintext_len = 56ul in
  let plaintext = FStar.Buffer.createL [
    0x61uy; 0x62uy; 0x63uy; 0x64uy; 0x62uy; 0x63uy; 0x64uy; 0x65uy;
    0x63uy; 0x64uy; 0x65uy; 0x66uy; 0x64uy; 0x65uy; 0x66uy; 0x67uy;
    0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy;
    0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x68uy; 0x69uy; 0x6auy; 0x6buy;
    0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy;
    0x6buy; 0x6cuy; 0x6duy; 0x6euy; 0x6cuy; 0x6duy; 0x6euy; 0x6fuy;
    0x6duy; 0x6euy; 0x6fuy; 0x70uy; 0x6euy; 0x6fuy; 0x70uy; 0x71uy
  ] in

  let expected = FStar.Buffer.createL [
      0x24uy; 0x8duy; 0x6auy; 0x61uy; 0xd2uy; 0x06uy; 0x38uy; 0xb8uy;
      0xe5uy; 0xc0uy; 0x26uy; 0x93uy; 0x0cuy; 0x3euy; 0x60uy; 0x39uy;
      0xa3uy; 0x3cuy; 0xe4uy; 0x59uy; 0x64uy; 0xffuy; 0x21uy; 0x67uy;
      0xf6uy; 0xecuy; 0xeduy; 0xd4uy; 0x19uy; 0xdbuy; 0x06uy; 0xc1uy
  ] in

  (* Allocate memory for state *)
  let ctx = FStar.Buffer.create 0ul Hash.size_state in

  (* Call the hash function *)
  Hash.hash output plaintext plaintext_len;

  (* Display the result *)
  TestLib.compare_and_print (C.String.of_literal "Test 3b") expected output 32ul;

  (* Pop the memory frame *)
  (**) pop_frame()



val test_4a: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_4a () =

  (* Push a new memory frame *)
  (**) push_frame();

  [@inline_let]
  let output_len = 32ul in
  let output = FStar.Buffer.create 0uy output_len in

  let plaintext_len = 112ul in
  let plaintext = FStar.Buffer.createL [
      0x61uy; 0x62uy; 0x63uy; 0x64uy; 0x65uy; 0x66uy; 0x67uy; 0x68uy;
      0x62uy; 0x63uy; 0x64uy; 0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy;
      0x63uy; 0x64uy; 0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy; 0x6auy;
      0x64uy; 0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x6buy;
      0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x6buy; 0x6cuy;
      0x66uy; 0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy;
      0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy; 0x6euy;
      0x68uy; 0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy; 0x6euy; 0x6fuy;
      0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy; 0x6euy; 0x6fuy; 0x70uy;
      0x6auy; 0x6buy; 0x6cuy; 0x6duy; 0x6euy; 0x6fuy; 0x70uy; 0x71uy;
      0x6buy; 0x6cuy; 0x6duy; 0x6euy; 0x6fuy; 0x70uy; 0x71uy; 0x72uy;
      0x6cuy; 0x6duy; 0x6euy; 0x6fuy; 0x70uy; 0x71uy; 0x72uy; 0x73uy;
      0x6duy; 0x6euy; 0x6fuy; 0x70uy; 0x71uy; 0x72uy; 0x73uy; 0x74uy;
      0x6euy; 0x6fuy; 0x70uy; 0x71uy; 0x72uy; 0x73uy; 0x74uy; 0x75uy
    ] in

  let expected = FStar.Buffer.createL [
      0xcfuy; 0x5buy; 0x16uy; 0xa7uy; 0x78uy; 0xafuy; 0x83uy; 0x80uy;
      0x03uy; 0x6cuy; 0xe5uy; 0x9euy; 0x7buy; 0x04uy; 0x92uy; 0x37uy;
      0x0buy; 0x24uy; 0x9buy; 0x11uy; 0xe8uy; 0xf0uy; 0x7auy; 0x51uy;
      0xafuy; 0xacuy; 0x45uy; 0x03uy; 0x7auy; 0xfeuy; 0xe9uy; 0xd1uy
    ] in

  (* Allocate memory for state *)
  let ctx = FStar.Buffer.create 0ul Hash.size_state in

  (* Call the hash function *)
  Hash.init ctx;
  Hash.update_last ctx plaintext plaintext_len;
  Hash.finish ctx output;

  (* Display the result *)
  TestLib.compare_and_print (C.String.of_literal "Test 4a") expected output 32ul;

  (* Pop the memory frame *)
  (**) pop_frame()


val test_4b: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_4b () =

  (* Push a new memory frame *)
  (**) push_frame();

  [@inline_let]
  let output_len = 32ul in
  let output = FStar.Buffer.create 0uy output_len in

  let plaintext_len = 112ul in
  let plaintext = FStar.Buffer.createL [
      0x61uy; 0x62uy; 0x63uy; 0x64uy; 0x65uy; 0x66uy; 0x67uy; 0x68uy;
      0x62uy; 0x63uy; 0x64uy; 0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy;
      0x63uy; 0x64uy; 0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy; 0x6auy;
      0x64uy; 0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x6buy;
      0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x6buy; 0x6cuy;
      0x66uy; 0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy;
      0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy; 0x6euy;
      0x68uy; 0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy; 0x6euy; 0x6fuy;
      0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy; 0x6euy; 0x6fuy; 0x70uy;
      0x6auy; 0x6buy; 0x6cuy; 0x6duy; 0x6euy; 0x6fuy; 0x70uy; 0x71uy;
      0x6buy; 0x6cuy; 0x6duy; 0x6euy; 0x6fuy; 0x70uy; 0x71uy; 0x72uy;
      0x6cuy; 0x6duy; 0x6euy; 0x6fuy; 0x70uy; 0x71uy; 0x72uy; 0x73uy;
      0x6duy; 0x6euy; 0x6fuy; 0x70uy; 0x71uy; 0x72uy; 0x73uy; 0x74uy;
      0x6euy; 0x6fuy; 0x70uy; 0x71uy; 0x72uy; 0x73uy; 0x74uy; 0x75uy
    ] in

  let expected = FStar.Buffer.createL [
      0xcfuy; 0x5buy; 0x16uy; 0xa7uy; 0x78uy; 0xafuy; 0x83uy; 0x80uy;
      0x03uy; 0x6cuy; 0xe5uy; 0x9euy; 0x7buy; 0x04uy; 0x92uy; 0x37uy;
      0x0buy; 0x24uy; 0x9buy; 0x11uy; 0xe8uy; 0xf0uy; 0x7auy; 0x51uy;
      0xafuy; 0xacuy; 0x45uy; 0x03uy; 0x7auy; 0xfeuy; 0xe9uy; 0xd1uy
    ] in

  (* Allocate memory for state *)
  let ctx = FStar.Buffer.create 0ul Hash.size_state in

  (* Call the hash function *)
  Hash.hash output plaintext plaintext_len;

  (* Display the result *)
  TestLib.compare_and_print (C.String.of_literal "Test 4b") expected output 32ul;

  (* Pop the memory frame *)
  (**) pop_frame()



val test_5: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_5 () =

  (* Push a new memory frame *)
  (**) push_frame();

  [@inline_let]
  let output_len = 32ul in
  let output = FStar.Buffer.create 0uy output_len in

  [@inline_let]
  let plaintext_len = 1000000ul in
  let plaintext = FStar.Buffer.create 0x61uy plaintext_len in

  let expected = FStar.Buffer.createL [
      0xcduy; 0xc7uy; 0x6euy; 0x5cuy; 0x99uy; 0x14uy; 0xfbuy; 0x92uy;
      0x81uy; 0xa1uy; 0xc7uy; 0xe2uy; 0x84uy; 0xd7uy; 0x3euy; 0x67uy;
      0xf1uy; 0x80uy; 0x9auy; 0x48uy; 0xa4uy; 0x97uy; 0x20uy; 0x0euy;
      0x04uy; 0x6duy; 0x39uy; 0xccuy; 0xc7uy; 0x11uy; 0x2cuy; 0xd0uy
    ] in

  (* Allocate memory for state *)
  let ctx = FStar.Buffer.create 0ul Hash.size_state in

  (* Call the hash function *)
  Hash.hash output plaintext plaintext_len;

  (* Display the result *)
  TestLib.compare_and_print (C.String.of_literal "Test 5") expected output 32ul;

  (* Pop the memory frame *)
  (**) pop_frame()



val test_6_loop:
  state:FStar.Buffer.buffer FStar.UInt32.t ->
  plaintext:FStar.Buffer.buffer FStar.UInt8.t ->
  ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_6_loop state plaintext =
  let inv (h1: HyperStack.mem) (i: nat) : Type0 =
    live h1 state /\ i <= v 16777215ul
  in
  let f' (t:FStar.UInt32.t) :
    Stack unit
      (requires (fun h -> True))
      (ensures (fun h_1 _ h_2 -> True))
    =
    Hash.update state plaintext
  in
  C.Loops.for 0ul 16777215ul inv f'


val test_6: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_6 () =

  (* Push a new memory frame *)
  (**) push_frame();

  [@inline_let]
  let output_len = 32ul in
  let output = FStar.Buffer.create 0uy output_len in

  [@inline_let]
  let plaintext_len = 64ul in
  let plaintext = FStar.Buffer.createL [
      0x61uy; 0x62uy; 0x63uy; 0x64uy; 0x65uy; 0x66uy; 0x67uy; 0x68uy;
      0x62uy; 0x63uy; 0x64uy; 0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy;
      0x63uy; 0x64uy; 0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy; 0x6auy;
      0x64uy; 0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x6buy;
      0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x6buy; 0x6cuy;
      0x66uy; 0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy;
      0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy; 0x6euy;
      0x68uy; 0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy; 0x6euy; 0x6fuy
  ] in

  let expected = FStar.Buffer.createL [
      0x50uy; 0xe7uy; 0x2auy; 0x0euy; 0x26uy; 0x44uy; 0x2fuy; 0xe2uy;
      0x55uy; 0x2duy; 0xc3uy; 0x93uy; 0x8auy; 0xc5uy; 0x86uy; 0x58uy;
      0x22uy; 0x8cuy; 0x0cuy; 0xbfuy; 0xb1uy; 0xd2uy; 0xcauy; 0x87uy;
      0x2auy; 0xe4uy; 0x35uy; 0x26uy; 0x6fuy; 0xcduy; 0x05uy; 0x5euy
    ] in

  (* Allocate memory for state *)
  let ctx = FStar.Buffer.create 0ul Hash.size_state in

  (* initialize the hash state *)
  Hash.init ctx;

  test_6_loop ctx plaintext;

  Hash.update_last ctx plaintext plaintext_len;
  Hash.finish ctx output;

  (* Display the result *)
  TestLib.compare_and_print (C.String.of_literal "Test 6") expected output 32ul;

  (* Pop the memory frame *)
  (**) pop_frame()



val main: unit -> ST C.exit_code
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let main () =

  (* Run test vector 1 *)
  test_1a ();
  test_1b ();

  (* Run test vector 2 *)
  test_2a ();
  test_2b ();

  (* Run test vector 3 *)
  test_3a ();
  test_3b ();

  (* Run test vector 4 *)
  test_4a ();
  test_4b ();

  (* Run test vector 5 *)
  test_5 ();

  (* Run test vector 6 *)
  test_6();

  (* Exit the program *)
  C.EXIT_SUCCESS
