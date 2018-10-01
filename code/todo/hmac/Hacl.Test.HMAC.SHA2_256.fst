module Hacl.Test.HMAC.SHA2_256

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Buffer

module Hash = Hacl.Impl.SHA2_256
module HMAC = Hacl.HMAC.SHA2_256


val test_1: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_1 () =

  (* Push a new memory frame *)
  (**) push_frame();

  [@inline_let] let output_len = Hash.size_hash in
  let output = FStar.Buffer.create 0uy output_len in

  [@inline_let] let key_len = 3ul in
  let key = FStar.Buffer.createL [
      0x61uy; 0x62uy; 0x63uy;
    ] in

  [@inline_let] let key_len = 20ul in
  let key = FStar.Buffer.create 0x0buy key_len in

  [@inline_let] let data_len = 8ul in
  let data = FStar.Buffer.createL [
      0x48uy; 0x69uy; 0x20uy; 0x54uy; 0x68uy; 0x65uy; 0x72uy; 0x65uy
    ] in

  let expected = FStar.Buffer.createL [
      0xb0uy; 0x34uy; 0x4cuy; 0x61uy; 0xd8uy; 0xdbuy; 0x38uy; 0x53uy;
      0x5cuy; 0xa8uy; 0xafuy; 0xceuy; 0xafuy; 0x0buy; 0xf1uy; 0x2buy;
      0x88uy; 0x1duy; 0xc2uy; 0x00uy; 0xc9uy; 0x83uy; 0x3duy; 0xa7uy;
      0x26uy; 0xe9uy; 0x37uy; 0x6cuy; 0x2euy; 0x32uy; 0xcfuy; 0xf7uy
    ] in

  (* Call the hash function *)
  HMAC.hmac output key key_len data data_len;

  (* Display the result *)
  TestLib.compare_and_print (C.String.of_literal "Test 1") expected output Hash.size_hash;

  (* Pop the memory frame *)
  (**) pop_frame()



val test_2: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_2 () =

  (* Push a new memory frame *)
  (**) push_frame();

  [@inline_let] let output_len = Hash.size_hash in
  let output = FStar.Buffer.create 0uy output_len in

  [@inline_let] let key_len = 3ul in
  let key = FStar.Buffer.createL [
      0x61uy; 0x62uy; 0x63uy;
    ] in

  [@inline_let] let key_len = 4ul in
  let key = FStar.Buffer.createL [
      0x4auy; 0x65uy; 0x66uy; 0x65uy
    ] in

  [@inline_let] let data_len = 28ul in
  let data = FStar.Buffer.createL [
      0x77uy; 0x68uy; 0x61uy; 0x74uy; 0x20uy; 0x64uy; 0x6fuy; 0x20uy;
      0x79uy; 0x61uy; 0x20uy; 0x77uy; 0x61uy; 0x6euy; 0x74uy; 0x20uy;
      0x66uy; 0x6fuy; 0x72uy; 0x20uy; 0x6euy; 0x6fuy; 0x74uy; 0x68uy;
      0x69uy; 0x6euy; 0x67uy; 0x3fuy
    ] in

  let expected = FStar.Buffer.createL [
      0x5buy; 0xdcuy; 0xc1uy; 0x46uy; 0xbfuy; 0x60uy; 0x75uy; 0x4euy;
      0x6auy; 0x04uy; 0x24uy; 0x26uy; 0x08uy; 0x95uy; 0x75uy; 0xc7uy;
      0x5auy; 0x00uy; 0x3fuy; 0x08uy; 0x9duy; 0x27uy; 0x39uy; 0x83uy;
      0x9duy; 0xecuy; 0x58uy; 0xb9uy; 0x64uy; 0xecuy; 0x38uy; 0x43uy
    ] in

  (* Call the hash function *)
  HMAC.hmac output key key_len data data_len;

  (* Display the result *)
  TestLib.compare_and_print (C.String.of_literal "Test 2") expected output Hash.size_hash;

  (* Pop the memory frame *)
  (**) pop_frame()



val test_3: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_3 () =

  (* Push a new memory frame *)
  (**) push_frame();

  [@inline_let] let output_len = Hash.size_hash in
  let output = FStar.Buffer.create 0uy output_len in

  [@inline_let] let key_len = 3ul in
  let key = FStar.Buffer.createL [
      0x61uy; 0x62uy; 0x63uy;
    ] in

  [@inline_let] let key_len = 20ul in
  let key = FStar.Buffer.create 0xaauy key_len in

  [@inline_let] let data_len = 50ul in
  let data = FStar.Buffer.create 0xdduy data_len in

  let expected = FStar.Buffer.createL [
      0x77uy; 0x3euy; 0xa9uy; 0x1euy; 0x36uy; 0x80uy; 0x0euy; 0x46uy;
      0x85uy; 0x4duy; 0xb8uy; 0xebuy; 0xd0uy; 0x91uy; 0x81uy; 0xa7uy;
      0x29uy; 0x59uy; 0x09uy; 0x8buy; 0x3euy; 0xf8uy; 0xc1uy; 0x22uy;
      0xd9uy; 0x63uy; 0x55uy; 0x14uy; 0xceuy; 0xd5uy; 0x65uy; 0xfeuy
    ] in

  (* Call the hash function *)
  HMAC.hmac output key key_len data data_len;

  (* Display the result *)
  TestLib.compare_and_print (C.String.of_literal "Test 3") expected output Hash.size_hash;

  (* Pop the memory frame *)
  (**) pop_frame()



val test_4: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_4 () =

  (* Push a new memory frame *)
  (**) push_frame();

  [@inline_let] let output_len = Hash.size_hash in
  let output = FStar.Buffer.create 0uy output_len in

  [@inline_let] let key_len = 3ul in
  let key = FStar.Buffer.createL [
      0x61uy; 0x62uy; 0x63uy;
    ] in

  [@inline_let] let key_len = 25ul in
  let key = FStar.Buffer.createL [
    0x01uy; 0x02uy; 0x03uy; 0x04uy; 0x05uy; 0x06uy; 0x07uy; 0x08uy;
    0x09uy; 0x0auy; 0x0buy; 0x0cuy; 0x0duy; 0x0euy; 0x0fuy; 0x10uy;
    0x11uy; 0x12uy; 0x13uy; 0x14uy; 0x15uy; 0x16uy; 0x17uy; 0x18uy;
    0x19uy
  ] in

  [@inline_let] let data_len = 50ul in
  let data = FStar.Buffer.create 0xcduy data_len in

  let expected = FStar.Buffer.createL [
      0x82uy; 0x55uy; 0x8auy; 0x38uy; 0x9auy; 0x44uy; 0x3cuy; 0x0euy;
      0xa4uy; 0xccuy; 0x81uy; 0x98uy; 0x99uy; 0xf2uy; 0x08uy; 0x3auy;
      0x85uy; 0xf0uy; 0xfauy; 0xa3uy; 0xe5uy; 0x78uy; 0xf8uy; 0x07uy;
      0x7auy; 0x2euy; 0x3fuy; 0xf4uy; 0x67uy; 0x29uy; 0x66uy; 0x5buy
    ] in

  (* Call the hash function *)
  HMAC.hmac output key key_len data data_len;

  (* Display the result *)
  TestLib.compare_and_print (C.String.of_literal "Test 4") expected output Hash.size_hash;

  (* Pop the memory frame *)
  (**) pop_frame()



val test_5: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_5 () =

  (* Push a new memory frame *)
  (**) push_frame();

  [@inline_let] let output_len = Hash.size_hash in
  let output = FStar.Buffer.create 0x00uy output_len in

  [@inline_let] let key_len = 20ul in
  let key = FStar.Buffer.create 0x0cuy key_len in

  [@inline_let] let data_len = 20ul in
  let data = FStar.Buffer.createL [
      0x54uy; 0x65uy; 0x73uy; 0x74uy; 0x20uy; 0x57uy; 0x69uy; 0x74uy;
      0x68uy; 0x20uy; 0x54uy; 0x72uy; 0x75uy; 0x6euy; 0x63uy; 0x61uy;
      0x74uy; 0x69uy; 0x6fuy; 0x6euy
  ] in

  let expected = FStar.Buffer.createL [
      0xa3uy; 0xb6uy; 0x16uy; 0x74uy; 0x73uy; 0x10uy; 0x0euy; 0xe0uy;
      0x6euy; 0x0cuy; 0x79uy; 0x6cuy; 0x29uy; 0x55uy; 0x55uy; 0x2buy
    ] in

  (* Call the hash function *)
  HMAC.hmac output key key_len data data_len;

  (* Display the result *)
  TestLib.compare_and_print (C.String.of_literal "Test 5") expected output 16ul;

  (* Pop the memory frame *)
  (**) pop_frame()



val test_6: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_6 () =

  (* Push a new memory frame *)
  (**) push_frame();

  [@inline_let] let output_len = Hash.size_hash in
  let output = FStar.Buffer.create 0uy output_len in

  [@inline_let] let key_len = 131ul in
  let key = FStar.Buffer.create 0xaauy key_len in

  [@inline_let] let data_len = 54ul in
  let data = FStar.Buffer.createL [
      0x54uy; 0x65uy; 0x73uy; 0x74uy; 0x20uy; 0x55uy; 0x73uy; 0x69uy;
      0x6euy; 0x67uy; 0x20uy; 0x4cuy; 0x61uy; 0x72uy; 0x67uy; 0x65uy;
      0x72uy; 0x20uy; 0x54uy; 0x68uy; 0x61uy; 0x6euy; 0x20uy; 0x42uy;
      0x6cuy; 0x6fuy; 0x63uy; 0x6buy; 0x2duy; 0x53uy; 0x69uy; 0x7auy;
      0x65uy; 0x20uy; 0x4buy; 0x65uy; 0x79uy; 0x20uy; 0x2duy; 0x20uy;
      0x48uy; 0x61uy; 0x73uy; 0x68uy; 0x20uy; 0x4buy; 0x65uy; 0x79uy;
      0x20uy; 0x46uy; 0x69uy; 0x72uy; 0x73uy; 0x74uy
  ] in

  let expected = FStar.Buffer.createL [
      0x60uy; 0xe4uy; 0x31uy; 0x59uy; 0x1euy; 0xe0uy; 0xb6uy; 0x7fuy;
      0x0duy; 0x8auy; 0x26uy; 0xaauy; 0xcbuy; 0xf5uy; 0xb7uy; 0x7fuy;
      0x8euy; 0x0buy; 0xc6uy; 0x21uy; 0x37uy; 0x28uy; 0xc5uy; 0x14uy;
      0x05uy; 0x46uy; 0x04uy; 0x0fuy; 0x0euy; 0xe3uy; 0x7fuy; 0x54uy
    ] in

  (* Call the hash function *)
  HMAC.hmac output key key_len data data_len;

  (* Display the result *)
  TestLib.compare_and_print (C.String.of_literal "Test 6") expected output Hash.size_hash;

  (* Pop the memory frame *)
  (**) pop_frame()



val test_7: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_7 () =

  (* Push a new memory frame *)
  (**) push_frame();

  [@inline_let] let output_len = Hash.size_hash in
  let output = FStar.Buffer.create 0uy output_len in

  [@inline_let] let key_len = 131ul in
  let key = FStar.Buffer.create 0xaauy key_len in

  [@inline_let] let data_len = 152ul in
  let data = FStar.Buffer.createL [
      0x54uy; 0x68uy; 0x69uy; 0x73uy; 0x20uy; 0x69uy; 0x73uy; 0x20uy;
      0x61uy; 0x20uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x20uy; 0x75uy;
      0x73uy; 0x69uy; 0x6euy; 0x67uy; 0x20uy; 0x61uy; 0x20uy; 0x6cuy;
      0x61uy; 0x72uy; 0x67uy; 0x65uy; 0x72uy; 0x20uy; 0x74uy; 0x68uy;
      0x61uy; 0x6euy; 0x20uy; 0x62uy; 0x6cuy; 0x6fuy; 0x63uy; 0x6buy;
      0x2duy; 0x73uy; 0x69uy; 0x7auy; 0x65uy; 0x20uy; 0x6buy; 0x65uy;
      0x79uy; 0x20uy; 0x61uy; 0x6euy; 0x64uy; 0x20uy; 0x61uy; 0x20uy;
      0x6cuy; 0x61uy; 0x72uy; 0x67uy; 0x65uy; 0x72uy; 0x20uy; 0x74uy;
      0x68uy; 0x61uy; 0x6euy; 0x20uy; 0x62uy; 0x6cuy; 0x6fuy; 0x63uy;
      0x6buy; 0x2duy; 0x73uy; 0x69uy; 0x7auy; 0x65uy; 0x20uy; 0x64uy;
      0x61uy; 0x74uy; 0x61uy; 0x2euy; 0x20uy; 0x54uy; 0x68uy; 0x65uy;
      0x20uy; 0x6buy; 0x65uy; 0x79uy; 0x20uy; 0x6euy; 0x65uy; 0x65uy;
      0x64uy; 0x73uy; 0x20uy; 0x74uy; 0x6fuy; 0x20uy; 0x62uy; 0x65uy;
      0x20uy; 0x68uy; 0x61uy; 0x73uy; 0x68uy; 0x65uy; 0x64uy; 0x20uy;
      0x62uy; 0x65uy; 0x66uy; 0x6fuy; 0x72uy; 0x65uy; 0x20uy; 0x62uy;
      0x65uy; 0x69uy; 0x6euy; 0x67uy; 0x20uy; 0x75uy; 0x73uy; 0x65uy;
      0x64uy; 0x20uy; 0x62uy; 0x79uy; 0x20uy; 0x74uy; 0x68uy; 0x65uy;
      0x20uy; 0x48uy; 0x4duy; 0x41uy; 0x43uy; 0x20uy; 0x61uy; 0x6cuy;
      0x67uy; 0x6fuy; 0x72uy; 0x69uy; 0x74uy; 0x68uy; 0x6duy; 0x2euy
  ] in

  let expected = FStar.Buffer.createL [
      0x9buy; 0x09uy; 0xffuy; 0xa7uy; 0x1buy; 0x94uy; 0x2fuy; 0xcbuy;
      0x27uy; 0x63uy; 0x5fuy; 0xbcuy; 0xd5uy; 0xb0uy; 0xe9uy; 0x44uy;
      0xbfuy; 0xdcuy; 0x63uy; 0x64uy; 0x4fuy; 0x07uy; 0x13uy; 0x93uy;
      0x8auy; 0x7fuy; 0x51uy; 0x53uy; 0x5cuy; 0x3auy; 0x35uy; 0xe2uy
    ] in

  (* Call the hash function *)
  HMAC.hmac output key key_len data data_len;

  (* Display the result *)
  TestLib.compare_and_print (C.String.of_literal "Test 7") expected output Hash.size_hash;

  (* Pop the memory frame *)
  (**) pop_frame()



val main: unit -> ST C.exit_code
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let main () =

  (* Run test vectors *)
  test_1 ();
  test_2 ();
  test_3 ();
  test_4 ();
  test_5 ();
  test_6 ();
  test_7 ();

  (* Exit the program *)
  C.EXIT_SUCCESS
