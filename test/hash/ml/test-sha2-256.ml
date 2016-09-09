open Char
open Hacl_SBuffer
open Hacl_Cast
open Hacl_Utils


   
let _ =

  (* Printf.printf "##############################\n"; *)
  (* Printf.printf "   Hacl.Operations.copymask   \n"; *)
  (* Printf.printf "##############################\n"; *)

  (* let test_in = create (uint8_to_sint8 17) 64 in *)
  (* let test_out = create (uint8_to_sint8 34) 64 in *)
  (* print_bytes test_in; *)
  (* Hacl_Operations.copymask test_in (uint32_to_sint32 0) (uint32_to_sint32 0) test_out 64; *)
  (* print_bytes test_out; *)

  (* let test_in = create (uint8_to_sint8 17) 64 in *)
  (* let test_out = create (uint8_to_sint8 34) 64 in *)
  (* print_bytes test_in; *)
  (* Hacl_Operations.copymask test_in (uint32_to_sint32 0) (uint32_to_sint32 32) test_out 64; *)
  (* print_bytes test_out; *)

  (* let test_in = create (uint8_to_sint8 17) 64 in *)
  (* let test_out = create (uint8_to_sint8 34) 64 in *)
  (* print_bytes test_in; *)
  (* Hacl_Operations.copymask test_in (uint32_to_sint32 32) (uint32_to_sint32 64) test_out 64; *)
  (* print_bytes test_out; *)
  
  (* let test_in = create (uint8_to_sint8 17) 64 in *)
  (* let test_out = create (uint8_to_sint8 34) 64 in *)
  (* print_bytes test_in; *)
  (* Hacl_Operations.copymask test_in (uint32_to_sint32 0) (uint32_to_sint32 64) test_out 64; *)
  (* print_bytes test_out; *)

  
  Printf.printf "#####################################################\n";
  Printf.printf "   Hash.Sha256: Incremental & Partial block hidding  \n";
  Printf.printf "#####################################################\n";
  
  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input = "" in
  let expected = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" in
  Printf.printf "Input    : %s\n" input;
  Hash_SHA2_L256.sha256 hash (from_string_block input Hash_SHA2_L256.blocksize) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;


  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input = "abc" in
  let expected = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" in
  Printf.printf "Input    : %s\n" input;
  Hash_SHA2_L256.sha256 hash (from_string_block input Hash_SHA2_L256.blocksize) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input = "abcabc" in
  let expected = "bbb59da3af939f7af5f360f2ceb80a496e3bae1cd87dde426db0ae40677e1c2c" in
  Printf.printf "Input    : %s\n" input;
  Hash_SHA2_L256.sha256 hash (from_string_block input Hash_SHA2_L256.blocksize) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;


  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input = "abcdefghijklmnopqrstuvwxyz" in
  let expected = "71c480df93d6ae2f1efad1447c66c9525e316218cf51fc8d9ed832f2daf18b73" in
  Printf.printf "Input    : %s\n" input;
  Hash_SHA2_L256.sha256 hash (from_string_block input Hash_SHA2_L256.blocksize) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" in
  let expected = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" in
  Printf.printf "Input    : %s\n" input;
  Hash_SHA2_L256.sha256 hash (from_string_block input (2 * Hash_SHA2_L256.blocksize)) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopqabcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" in
  let expected = "59f109d9533b2b70e7c3b814a2bd218f78ea5d3714455bc67987cf0d664399cf" in
  Printf.printf "Input    : %s\n" input;
  Hash_SHA2_L256.sha256 hash (from_string_block input (2 * Hash_SHA2_L256.blocksize)) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu" in
  let expected = "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1" in
  Printf.printf "Input    : %s\n" input;
  Hash_SHA2_L256.sha256 hash (from_string_block input (2 * Hash_SHA2_L256.blocksize)) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected

  (* let hash = create (uint8_to_sint8 0) 32 in *)
  (* let state = create (uint32_to_sint32 0) 256 in *)
  (* let output = create (uint8_to_sint8 0) 64 in *)
  (* let input_txt = "1M 'a'" in *)
  (* let input = Bytes.make 1000000 '\x61' in *)
  (* let expected = "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0" in *)
  (* Printf.printf "Input    : %s\n" input_txt; *)
  (* Hash_SHA2_L256.sha256 hash (from_string_block input (15700 * Hash_SHA2_L256.blocksize)) (String.length input); *)
  (* Printf.printf "Result   :"; *)
  (* print_bytes hash; *)
  (* Printf.printf "Expected :%s\n\n" expected; *)


  (* Printf.printf "#########################################################\n"; *)
  (* Printf.printf "  Hash.Sha256_LH: Incremental & Length hidding via mask  \n"; *)
  (* Printf.printf "#########################################################\n"; *)
  
  (* let hash = create (uint8_to_sint8 0) 32 in *)
  (* let state = create (uint32_to_sint32 0) 256 in *)
  (* let output = create (uint8_to_sint8 0) 64 in *)
  (* let rounds_mask = 2 in *)
  (* let masklen = rounds_mask * Hash_Sha256_LH.blocksize in *)
  (* let mask = create (uint8_to_sint8 0) masklen in *)
  (* let input = "" in *)
  (* let expected = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" in *)
  (* Printf.printf "Input    : %s\n" input; *)
  (* Hash_Sha256_LH.sha256 hash (from_string_block input masklen) (String.length input) mask rounds_mask; *)
  (* Printf.printf "Result   :"; *)
  (* print_bytes hash; *)
  (* Printf.printf "Expected :%s\n\n" expected; *)

  
  (* let hash = create (uint8_to_sint8 0) 32 in *)
  (* let state = create (uint32_to_sint32 0) 256 in *)
  (* let output = create (uint8_to_sint8 0) 64 in *)
  (* let rounds_mask = 2 in *)
  (* let masklen = rounds_mask * Hash_Sha256_LH.blocksize in *)
  (* let mask = create (uint8_to_sint8 0) masklen in *)
  (* let input = "abc" in *)
  (* let expected = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" in *)
  (* Printf.printf "Input    : %s\n" input; *)
  (* Hash_Sha256_LH.sha256 hash (from_string_block input masklen) (String.length input) mask rounds_mask; *)
  (* Printf.printf "Result   :"; *)
  (* print_bytes hash; *)
  (* Printf.printf "Expected :%s\n\n" expected *)


  (*;
  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input = "abcabc" in
  let expected = "bbb59da3af939f7af5f360f2ceb80a496e3bae1cd87dde426db0ae40677e1c2c" in
  Printf.printf "Input    : %s\n" input;
  Hash_Sha256_LH.sha256 hash (from_string_block input Hash_Sha256_LH.blocksize) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;


  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input = "abcdefghijklmnopqrstuvwxyz" in
  let expected = "71c480df93d6ae2f1efad1447c66c9525e316218cf51fc8d9ed832f2daf18b73" in
  Printf.printf "Input    : %s\n" input;
  Hash_Sha256_LH.sha256 hash (from_string_block input Hash_Sha256_LH.blocksize) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" in
  let expected = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" in
  Printf.printf "Input    : %s\n" input;
  Hash_Sha256_LH.sha256 hash (from_string_block input (2 * Hash_Sha256_LH.blocksize)) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopqabcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" in
  let expected = "59f109d9533b2b70e7c3b814a2bd218f78ea5d3714455bc67987cf0d664399cf" in
  Printf.printf "Input    : %s\n" input;
  Hash_Sha256_LH.sha256 hash (from_string_block input (2 * Hash_Sha256_LH.blocksize)) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let hash = create (uint8_to_sint8 0) 32 in
  let state = create (uint32_to_sint32 0) 256 in
  let output = create (uint8_to_sint8 0) 64 in
  let input = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu" in
  let expected = "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1" in
  Printf.printf "Input    : %s\n" input;
  Hash_Sha256_LH.sha256 hash (from_string_block input (2 * Hash_Sha256_LH.blocksize)) (String.length input);
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
  Hash_Sha256_LH.sha256 hash (from_string_block input (15700 * Hash_Sha256_LH.blocksize)) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected

   *)
