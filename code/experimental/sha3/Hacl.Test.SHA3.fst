module Hacl.Test.SHA3

open FStar.HyperStack.All
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.PQ.Buffer
open Hacl.SHA3

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let lbytes len = lbuffer uint8 len

val test_sha3:
     msg_len:size_t
  -> msg:lbytes (size_v msg_len)
  -> expected224:lbytes 28
  -> expected256:lbytes 32
  -> expected384:lbytes 48
  -> expected512:lbytes 64
  -> Stack unit
    (requires fun h ->
      live h msg /\ live h expected224 /\ live h expected256 /\
      live h expected384 /\ live h expected512)
    (ensures  fun h0 r h1 -> True)
let test_sha3 msg_len msg expected224 expected256 expected384 expected512 =
  push_frame();
  let test224 = create #_ #28 (size 28) (u8 0) in
  let test256 = create #_ #32 (size 32) (u8 0) in
  let test384 = create #_ #48 (size 48) (u8 0) in
  let test512 = create #_ #64 (size 64) (u8 0) in
  sha3_224 msg_len msg test224;
  sha3_256 msg_len msg test256;
  sha3_384 msg_len msg test384;
  sha3_512 msg_len msg test512;

  print_compare_display (size 28) test224 expected224;
  print_compare_display (size 32) test256 expected256;
  print_compare_display (size 48) test384 expected384;
  print_compare_display (size 64) test512 expected512;
  pop_frame()


/// Test2.
///
val u8: n:nat{n < 0x100} -> uint8
let u8 n = u8 n

let test2_plaintext: b:lbytes 3{ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x61; 0x62; 0x63])
  in
  assert_norm (List.Tot.length l == 3);
  createL_global l

let test2_expected_sha3_224: b:lbytes 28{ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xe6; 0x42; 0x82; 0x4c; 0x3f; 0x8c; 0xf2; 0x4a; 0xd0; 0x92; 0x34; 0xee; 0x7d; 0x3c; 0x76; 0x6f;
     0xc9; 0xa3; 0xa5; 0x16; 0x8d; 0x0c; 0x94; 0xad; 0x73; 0xb4; 0x6f; 0xdf])
  in
  assert_norm (List.Tot.length l == 28);
  createL_global l

let test2_expected_sha3_256: b:lbytes 32{ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x3a; 0x98; 0x5d; 0xa7; 0x4f; 0xe2; 0x25; 0xb2; 0x04; 0x5c; 0x17; 0x2d; 0x6b; 0xd3; 0x90; 0xbd;
     0x85; 0x5f; 0x08; 0x6e; 0x3e; 0x9d; 0x52; 0x5b; 0x46; 0xbf; 0xe2; 0x45; 0x11; 0x43; 0x15; 0x32])
  in
  assert_norm (List.Tot.length l == 32);
  createL_global l

let test2_expected_sha3_384: b:lbytes 48{ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xec; 0x01; 0x49; 0x82; 0x88; 0x51; 0x6f; 0xc9; 0x26; 0x45; 0x9f; 0x58; 0xe2; 0xc6; 0xad; 0x8d;
     0xf9; 0xb4; 0x73; 0xcb; 0x0f; 0xc0; 0x8c; 0x25; 0x96; 0xda; 0x7c; 0xf0; 0xe4; 0x9b; 0xe4; 0xb2;
     0x98; 0xd8; 0x8c; 0xea; 0x92; 0x7a; 0xc7; 0xf5; 0x39; 0xf1; 0xed; 0xf2; 0x28; 0x37; 0x6d; 0x25])
  in
  assert_norm (List.Tot.length l == 48);
  createL_global l

let test2_expected_sha3_512: b:lbytes 64{ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0xb7; 0x51; 0x85; 0x0b; 0x1a; 0x57; 0x16; 0x8a; 0x56; 0x93; 0xcd; 0x92; 0x4b; 0x6b; 0x09; 0x6e;
     0x08; 0xf6; 0x21; 0x82; 0x74; 0x44; 0xf7; 0x0d; 0x88; 0x4f; 0x5d; 0x02; 0x40; 0xd2; 0x71; 0x2e;
     0x10; 0xe1; 0x16; 0xe9; 0x19; 0x2a; 0xf3; 0xc9; 0x1a; 0x7e; 0xc5; 0x76; 0x47; 0xe3; 0x93; 0x40;
     0x57; 0x34; 0x0b; 0x4c; 0xf4; 0x08; 0xd5; 0xa5; 0x65; 0x92; 0xf8; 0x27; 0x4e; 0xec; 0x53; 0xf0])
  in
  assert_norm (List.Tot.length l == 64);
  createL_global l

val main: unit -> St C.exit_code
let main () =
  recall test2_expected_sha3_224;
  recall test2_expected_sha3_256;
  recall test2_expected_sha3_384;
  recall test2_expected_sha3_512;
  recall test2_plaintext;
  test_sha3 (size 3) test2_plaintext test2_expected_sha3_224 test2_expected_sha3_256 test2_expected_sha3_384 test2_expected_sha3_512;
  C.EXIT_SUCCESS
