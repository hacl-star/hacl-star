module Test.Impl.SHA2_256

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


val test_sha2_256:
    msg_len: size_t
  -> msg: lbytes (size_v msg_len)
  -> expected: lbytes size_hash ->
  Stack unit
    (requires fun h -> live h msg /\ live h expected)
    (ensures  fun h0 r h1 -> True)

let test_sha2_256 msg_len msg expected =
  push_frame();
  let result = create #_ #size_hash (size size_hash) (u8 0xFF) in
  Hacl.SHA2_256.hash result msg msg_len;
  print_compare_display (size size_hash) result expected;
  pop_frame()


inline_for_extraction let test1_size_plaintext = 3ul
let test1_plaintext: b:lbytes (v test1_size_plaintext){ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [ 0x61; 0x62; 0x63 ])
  in
  assert_norm (List.Tot.length l == 3);
  createL_global l


let test1_expected: b:lbytes size_hash =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0xba; 0x78; 0x16; 0xbf; 0x8f; 0x01; 0xcf; 0xea;
      0x41; 0x41; 0x40; 0xde; 0x5d; 0xae; 0x22; 0x23;
      0xb0; 0x03; 0x61; 0xa3; 0x96; 0x17; 0x7a; 0x9c;
      0xb4; 0x10; 0xff; 0x61; 0xf2; 0x00; 0x15; 0xad
    ])
  in
  assert_norm (List.Tot.length l == 32);
  createL_global l


//
// Main
//

val main: unit -> St C.exit_code
let main () =
  C.String.print (C.String.of_literal "\nTEST 1. \n");
  test_sha2_256 test1_size_plaintext test1_plaintext test1_expected;

  C.EXIT_SUCCESS
