open Char
open Hacl_SBuffer
open Hash_Sha256
open Hacl_Cast

let from_string s l =
  let b = create (Hacl_UInt8.of_string "0") l in
  for i = 0 to (String.length s - 1) do
    upd b i (uint8_to_sint8 (code (String.get s i)))
  done;
  b

let from_bytestring s =
  let b = create (Hacl_UInt8.of_string "0") ((String.length s) / 2) in
  for i = 0 to ((String.length s / 2) - 1) do
    upd b i (uint8_to_sint8 (int_of_string ("0x" ^ (String.sub s (2*i) 2))))
  done;
  b

let print_bytes (s:Hacl_UInt8.uint8 Hacl_SBuffer.buffer) : unit =
  for i = 0 to Array.length s.content - 1 do
    print_string (Hacl_UInt8.to_string_hex (Hacl_SBuffer.index s i))
  done;
  print_string "\n"

let print_uint32s (s:Hacl_UInt32.uint32 Hacl_SBuffer.buffer) : unit =
  for i = 0 to Array.length s.content - 1 do
    print_string (Hacl_UInt32.to_string_hex (index s i))
  done;
  print_string "\n"

let print_l_bytes (s:Hacl_UInt8.uint8 Hacl_SBuffer.buffer) l : unit =
  for i = 0 to l - 1 do
    print_string (Hacl_UInt8.to_string_hex (Hacl_SBuffer.index s i))
  done;
  print_string "\n"

let print_l_uint32s (s:Hacl_UInt32.uint32 Hacl_SBuffer.buffer) l : unit =
  for i = 0 to l - 1 do
    print_string (Hacl_UInt32.to_string_hex (index s i))
  done;
  print_string "\n"



let blocksize = 64
let wblocksize = 16


let test_result () =

  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input = "" in
  let expected = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" in
  Printf.printf "Input    : %s\n" input;
  sha256 hash (from_string input blocksize) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;


  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input = "abc" in
  let expected = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" in
  Printf.printf "Input    : %s\n" input;
  sha256 hash (from_string input blocksize) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;


  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input = "abcabc" in
  let expected = "bbb59da3af939f7af5f360f2ceb80a496e3bae1cd87dde426db0ae40677e1c2c" in
  Printf.printf "Input    : %s\n" input;
  sha256 hash (from_string input blocksize) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;


  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input = "abcdefghijklmnopqrstuvwxyz" in
  let expected = "71c480df93d6ae2f1efad1447c66c9525e316218cf51fc8d9ed832f2daf18b73" in
  Printf.printf "Input    : %s\n" input;
  sha256 hash (from_string input blocksize) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" in
  let expected = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" in
  Printf.printf "Input    : %s\n" input;
  sha256 hash (from_string input (2 * blocksize)) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopqabcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" in
  let expected = "59f109d9533b2b70e7c3b814a2bd218f78ea5d3714455bc67987cf0d664399cf" in
  Printf.printf "Input    : %s\n" input;
  sha256 hash (from_string input (2 * blocksize)) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu" in
  let expected = "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1" in
  Printf.printf "Input    : %s\n" input;
  sha256 hash (from_string input (2 * blocksize)) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input_txt = "1M 'a'" in
  let input = Bytes.make 1000000 '\x61' in
  let expected = "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0" in
  Printf.printf "Input    : %s\n" input_txt;
  sha256 hash (from_string input (15700 * blocksize)) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected

let _ =  test_result ()
