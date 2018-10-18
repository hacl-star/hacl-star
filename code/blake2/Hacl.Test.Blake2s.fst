module Hacl.Test.Blake2s

open FStar.HyperStack.All
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.Print
open Hacl.Blake2s


val test_blake2s:
    msg_len:size_t
  -> msg:lbytes (size_v msg_len)
  -> key_len:size_t{v key_len <= 32 /\ (if v key_len = 0 then v msg_len < pow2 64 else v msg_len + 64 < pow2 64)}
  -> key:lbytes (size_v key_len)
  -> expected_len:size_t{1 <= v expected_len /\ v expected_len <= 32}
  -> expected:lbytes (size_v expected_len)
  -> Stack unit
    (requires fun h ->
      live h msg /\ live h expected /\ live h key)
    (ensures  fun h0 r h1 -> True)

let test_blake2s msg_len msg key_len key expected_len expected =
  push_frame();
  let result = create #_ #(v expected_len) expected_len (u8 0) in
  blake2s result msg msg_len key key_len expected_len;
  print_compare_display expected_len result expected;
  pop_frame()


///
/// Test 1
///

inline_for_extraction let test1_size_plaintext = 3
let test1_plaintext: b:lbytes test1_size_plaintext{ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x61; 0x62; 0x63])
  in
  assert_norm (List.Tot.length l == 3);
  createL_global l

inline_for_extraction let test1_size_key = 0
let test1_key: b:lbytes test1_size_key{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 []) in
  assert_norm (List.Tot.length l == 0); admit();
  createL_global l

inline_for_extraction let test1_size_expected = 32
let test1_expected: b:lbytes test1_size_expected{ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [ 0x50; 0x8C; 0x5E; 0x8C; 0x32; 0x7C; 0x14; 0xE2;
      0xE1; 0xA7; 0x2B; 0xA3; 0x4E; 0xEB; 0x45; 0x2F;
      0x37; 0x45; 0x8B; 0x20; 0x9E; 0xD6; 0x3A; 0x29;
      0x4D; 0x99; 0x9B; 0x4C; 0x86; 0x67; 0x59; 0x82])
  in
  assert_norm (List.Tot.length l == 32);
  createL_global l

//
// Main
//

val main: unit -> St C.exit_code
let main () =
  C.String.print (C.String.of_literal "\nTEST 1. \n");
  recall test1_plaintext;
  recall test1_key;
  recall test1_expected;
  test_blake2s test1_size_plaintext test1_plaintext test1_size_key test1_key test1_size_expected test1_expected;
  C.EXIT_SUCCESS
