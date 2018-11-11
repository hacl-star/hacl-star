module Test.Impl.HMAC_SHA2_256

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators
open Lib.Print


module Spec = Spec.SHA2

module Hash = Hacl.SHA2_256

inline_for_extraction let size_hash: size_nat= 32

///
/// Testing function
///

val test_hmac_sha2_256:
    key_len: size_t
  -> key: lbytes (size_v key_len)
  -> msg_len: size_t
  -> msg: lbytes (size_v msg_len)
  -> expected: lbytes size_hash ->
  Stack unit
    (requires fun h -> live h msg /\ live h expected)
    (ensures  fun h0 r h1 -> True)

let test_hmac_sha2_256 key_len key msg_len msg expected =
  push_frame();
  let result = create #_ #size_hash (size size_hash) (u8 0xFF) in
  Hacl.HMAC_SHA2_256.hmac result key key_len msg msg_len;
  print_compare_display (size size_hash) result expected;
  pop_frame()

///
/// Test 1
///

inline_for_extraction let test1_size_plaintext = 8ul
let test1_plaintext: b:lbytes (v test1_size_plaintext){ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x48; 0x69; 0x20; 0x54; 0x68; 0x65; 0x72; 0x65
    ])
  in
  assert_norm (List.Tot.length l == 8);
  createL_global l


let test1_expected: b:lbytes size_hash =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0xb0; 0x34; 0x4c; 0x61; 0xd8; 0xdb; 0x38; 0x53;
      0x5c; 0xa8; 0xaf; 0xce; 0xaf; 0x0b; 0xf1; 0x2b;
      0x88; 0x1d; 0xc2; 0x00; 0xc9; 0x83; 0x3d; 0xa7;
      0x26; 0xe9; 0x37; 0x6c; 0x2e; 0x32; 0xcf; 0xf7
    ])
  in
  assert_norm (List.Tot.length l == 32);
  createL_global l


///
/// Main
///

val main: unit -> St C.exit_code
let main () =

  C.String.print (C.String.of_literal "\nTEST 1. \n");
  let test1_result = create #_ #size_hash (size size_hash) (u8 0x00) in
  let test1_key = create #uint8 #20 (size 20) (u8 0x0b) in
  Hacl.HMAC_SHA2_256.hmac test1_result test1_key (size 20) test1_plaintext test1_size_plaintext;
  print_compare_display (size size_hash) test1_result test1_expected;

  C.EXIT_SUCCESS
