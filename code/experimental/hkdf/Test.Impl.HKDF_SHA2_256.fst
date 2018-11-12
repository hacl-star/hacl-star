module Test.Impl.HKDF_SHA2_256

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
/// Test 1
///

inline_for_extraction let test1_size_ikm = 22ul
let test1_ikm: b:lbytes (v test1_size_ikm){ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x0b; 0x0b; 0x0b; 0x0b; 0x0b; 0x0b; 0x0b; 0x0b;
      0x0b; 0x0b; 0x0b; 0x0b; 0x0b; 0x0b; 0x0b; 0x0b;
      0x0b; 0x0b; 0x0b; 0x0b; 0x0b; 0x0b
    ])
  in
  assert_norm (List.Tot.length l == 22);
  createL_global l


inline_for_extraction let test1_size_salt = 13ul
let test1_salt: b:lbytes (v test1_size_salt){ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x00; 0x01; 0x02; 0x03; 0x04; 0x05; 0x06; 0x07;
      0x08; 0x09; 0x0a; 0x0b; 0x0c
    ])
  in
  assert_norm (List.Tot.length l == 13);
  createL_global l


inline_for_extraction let test1_size_info = 10ul
let test1_info: b:lbytes (v test1_size_info){ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0xf0; 0xf1; 0xf2; 0xf3; 0xf4; 0xf5; 0xf6; 0xf7;
      0xf8; 0xf9
    ])
  in
  assert_norm (List.Tot.length l == 10);
  createL_global l


inline_for_extraction let test1_size_expected_prk = 32
let test1_expected_prk: b:lbytes test1_size_expected_prk =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x07; 0x77; 0x09; 0x36; 0x2c; 0x2e; 0x32; 0xdf;
      0x0d; 0xdc; 0x3f; 0x0d; 0xc4; 0x7b; 0xba; 0x63;
      0x90; 0xb6; 0xc7; 0x3b; 0xb5; 0x0f; 0x9c; 0x31;
      0x22; 0xec; 0x84; 0x4a; 0xd7; 0xc2; 0xb3; 0xe5
    ])
  in
  assert_norm (List.Tot.length l == 32);
  createL_global l


inline_for_extraction let test1_size_expected_okm = 42
let test1_expected_okm: b:lbytes test1_size_expected_okm =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x3c; 0xb2; 0x5f; 0x25; 0xfa; 0xac; 0xd5; 0x7a;
      0x90; 0x43; 0x4f; 0x64; 0xd0; 0x36; 0x2f; 0x2a;
      0x2d; 0x2d; 0x0a; 0x90; 0xcf; 0x1a; 0x5a; 0x4c;
      0x5d; 0xb0; 0x2d; 0x56; 0xec; 0xc4; 0xc5; 0xbf;
      0x34; 0x00; 0x72; 0x08; 0xd5; 0xb8; 0x87; 0x18;
      0x58; 0x65
    ])
  in
  assert_norm (List.Tot.length l == 42);
  createL_global l


///
/// Main
///

val main: unit -> St C.exit_code
let main () =

  C.String.print (C.String.of_literal "TEST 1. \n");
  let test1_result_prk = create #_ #size_hash (size size_hash) (u8 0x00) in
  let test1_result_okm = create #_ #size_hash (size test1_size_expected_okm) (u8 0x00) in

  Hacl.HKDF_SHA2_256.hkdf_extract test1_result_prk test1_salt test1_size_salt test1_ikm test1_size_ikm;
  let r1a = result_compare_display (size size_hash) test1_result_prk test1_expected_prk in

  Hacl.HKDF_SHA2_256.hkdf_expand test1_result_okm test1_result_prk (size size_hash) test1_info test1_size_info test1_size_expected_okm;
  let r1b = result_compare_display test1_size_expected_okm test1_result_okm test1_expected_okm in


  if r1a && r1b then begin
    C.String.print (C.String.of_literal "Composite Result: Success !\n");
    C.EXIT_SUCCESS end
  else begin
    C.String.print (C.String.of_literal "Composite Result: Failure !\n");
    C.EXIT_FAILURE end
