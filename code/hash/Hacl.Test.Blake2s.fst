module Hacl.Test.Blake2s

#reset-options "--z3rlimit 100 --max_fuel 0 --lax"

open FStar.HyperStack.All
open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntBuf

//
// Test 1
//

// inline_for_extraction let test1_plaintext_len = size 3
// inline_for_extraction let test1_plaintext : list uint8 = [
//   u8 0x61; u8 0x62; u8 0x63
// ]

// inline_for_extraction let test1_expected_len = size 32
// inline_for_extraction let test1_expected :  list uint8 = [
//   u8 0x50; u8 0x8C; u8 0x5E; u8 0x8C; u8 0x32; u8 0x7C; u8 0x14; u8 0xE2;
//   u8 0xE1; u8 0xA7; u8 0x2B; u8 0xA3; u8 0x4E; u8 0xEB; u8 0x45; u8 0x2F;
//   u8 0x37; u8 0x45; u8 0x8B; u8 0x20; u8 0x9E; u8 0xD6; u8 0x3A; u8 0x29;
//   u8 0x4D; u8 0x99; u8 0x9B; u8 0x4C; u8 0x86; u8 0x67; u8 0x59; u8 0x82
// ]

// inline_for_extraction let empty : list uint8 = []

//
// Main
//

val main: unit -> Stack C.exit_code (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let main () =

  let test1_plaintext_len = size 3 in
  let test1_expected_len = size 32 in
  let test1_empty_len = size 0 in

  let test1_plaintext : lbuffer uint8 (size_v test1_plaintext_len) =
    createL [
      u8 0x61; u8 0x62; u8 0x63
    ] in
  let test1_expected : lbuffer uint8 (size_v test1_expected_len) =
    createL [
      u8 0x50; u8 0x8C; u8 0x5E; u8 0x8C; u8 0x32; u8 0x7C; u8 0x14; u8 0xE2;
      u8 0xE1; u8 0xA7; u8 0x2B; u8 0xA3; u8 0x4E; u8 0xEB; u8 0x45; u8 0x2F;
      u8 0x37; u8 0x45; u8 0x8B; u8 0x20; u8 0x9E; u8 0xD6; u8 0x3A; u8 0x29;
      u8 0x4D; u8 0x99; u8 0x9B; u8 0x4C; u8 0x86; u8 0x67; u8 0x59; u8 0x82
    ] in
  let empty : lbuffer uint8 (size_v test1_empty_len) = createL [] in
  C.String.print (C.String.of_literal "\nTEST 1\n");
  let test1_result : lbuffer uint8 (size_v test1_expected_len) = create #uint8 (size 32) (u8 0) in
  Hacl.Impl.Blake2s.blake2s test1_plaintext_len test1_plaintext test1_empty_len empty test1_expected_len test1_result;

  Spec.Lib.Print.print_compare_display test1_expected_len test1_result test1_expected;

  let test2_plaintext_len = size 1 in
  let test2_key_len = size 32 in
  let test2_expected_len = size 32 in

  let test2_plaintext : lbuffer uint8 (size_v test2_plaintext_len) =
    createL [ u8 0x00 ] in
  let test2_key : lbuffer uint8 (size_v test2_expected_len) =
    createL [
      u8 0x00; u8 0x01; u8 0x02; u8 0x03; u8 0x04; u8 0x05; u8 0x06; u8 0x07;
      u8 0x08; u8 0x09; u8 0x0a; u8 0x0b; u8 0x0c; u8 0x0d; u8 0x0e; u8 0x0f;
      u8 0x10; u8 0x11; u8 0x12; u8 0x13; u8 0x14; u8 0x15; u8 0x16; u8 0x17;
      u8 0x18; u8 0x19; u8 0x1a; u8 0x1b; u8 0x1c; u8 0x1d; u8 0x1e; u8 0x1f
    ] in
  let test2_expected : lbuffer uint8 (size_v test2_key_len) =
    createL [
      u8 0x40; u8 0xd1; u8 0x5f; u8 0xee; u8 0x7c; u8 0x32; u8 0x88; u8 0x30;
      u8 0x16; u8 0x6a; u8 0xc3; u8 0xf9; u8 0x18; u8 0x65; u8 0x0f; u8 0x80;
      u8 0x7e; u8 0x7e; u8 0x01; u8 0xe1; u8 0x77; u8 0x25; u8 0x8c; u8 0xdc;
      u8 0x0a; u8 0x39; u8 0xb1; u8 0x1f; u8 0x59; u8 0x80; u8 0x66; u8 0xf1
    ] in

  C.String.print (C.String.of_literal "\nTEST 2\n");
  let test2_result : lbuffer uint8 (size_v test2_expected_len) = create #uint8 (size 32) (u8 0) in
  Hacl.Impl.Blake2s.blake2s test2_plaintext_len test2_plaintext test2_key_len test2_key test2_expected_len test2_result;

  (* Display the result *)
  Spec.Lib.Print.print_compare_display test2_expected_len test2_result test2_expected;

  C.EXIT_SUCCESS
