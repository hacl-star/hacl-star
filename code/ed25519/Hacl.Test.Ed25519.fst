module Hacl.Test.Ed25519

open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.PrintBuffer

module Ed25519 = Hacl.Ed25519

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val u8: n:nat{n < 0x100} -> uint8
let u8 n = u8 n

//
// Test1
//
let msg1: b:lbuffer uint8 0ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 []) in
  assert_norm (List.Tot.length l == 0);
  createL_mglobal l

let sk1: b:lbuffer uint8 32ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x9d; 0x61; 0xb1; 0x9d; 0xef; 0xfd; 0x5a; 0x60; 0xba; 0x84; 0x4a; 0xf4; 0x92; 0xec; 0x2c; 0xc4;
      0x44; 0x49; 0xc5; 0x69; 0x7b; 0x32; 0x69; 0x19; 0x70; 0x3b; 0xac; 0x03; 0x1c; 0xae; 0x7f; 0x60
    ]) in
  assert_norm (List.Tot.length l == 32);
  createL_mglobal l

let pk1: b:lbuffer uint8 32ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0xd7; 0x5a; 0x98; 0x01; 0x82; 0xb1; 0x0a; 0xb7; 0xd5; 0x4b; 0xfe; 0xd3; 0xc9; 0x64; 0x07; 0x3a;
      0x0e; 0xe1; 0x72; 0xf3; 0xda; 0xa6; 0x23; 0x25; 0xaf; 0x02; 0x1a; 0x68; 0xf7; 0x07; 0x51; 0x1a
    ]) in
  assert_norm (List.Tot.length l == 32);
  createL_mglobal l

let sig1: b:lbuffer uint8 64ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0xe5; 0x56; 0x43; 0x00; 0xc3; 0x60; 0xac; 0x72; 0x90; 0x86; 0xe2; 0xcc; 0x80; 0x6e; 0x82; 0x8a;
      0x84; 0x87; 0x7f; 0x1e; 0xb8; 0xe5; 0xd9; 0x74; 0xd8; 0x73; 0xe0; 0x65; 0x22; 0x49; 0x01; 0x55;
      0x5f; 0xb8; 0x82; 0x15; 0x90; 0xa3; 0x3b; 0xac; 0xc6; 0x1e; 0x39; 0x70; 0x1c; 0xf9; 0xb4; 0x6b;
      0xd2; 0x5b; 0xf5; 0xf0; 0x59; 0x5b; 0xbe; 0x24; 0x65; 0x51; 0x41; 0x43; 0x8e; 0x7a; 0x10; 0x0b
    ]) in
  assert_norm (List.Tot.length l == 64);
  createL_mglobal l


//
// Test2
//
let msg2: b:lbuffer uint8 1ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [ 0x72]) in
  assert_norm (List.Tot.length l == 1);
  createL_mglobal l

let sk2: b:lbuffer uint8 32ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x4c; 0xcd; 0x08; 0x9b; 0x28; 0xff; 0x96; 0xda; 0x9d; 0xb6; 0xc3; 0x46; 0xec; 0x11; 0x4e; 0x0f;
      0x5b; 0x8a; 0x31; 0x9f; 0x35; 0xab; 0xa6; 0x24; 0xda; 0x8c; 0xf6; 0xed; 0x4f; 0xb8; 0xa6; 0xfb
    ]) in
  assert_norm (List.Tot.length l == 32);
  createL_mglobal l

let pk2: b:lbuffer uint8 32ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x3d; 0x40; 0x17; 0xc3; 0xe8; 0x43; 0x89; 0x5a; 0x92; 0xb7; 0x0a; 0xa7; 0x4d; 0x1b; 0x7e; 0xbc;
      0x9c; 0x98; 0x2c; 0xcf; 0x2e; 0xc4; 0x96; 0x8c; 0xc0; 0xcd; 0x55; 0xf1; 0x2a; 0xf4; 0x66; 0x0c
    ]) in
  assert_norm (List.Tot.length l == 32);
  createL_mglobal l

let sig2: b:lbuffer uint8 64ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x92; 0xa0; 0x09; 0xa9; 0xf0; 0xd4; 0xca; 0xb8; 0x72; 0x0e; 0x82; 0x0b; 0x5f; 0x64; 0x25; 0x40;
      0xa2; 0xb2; 0x7b; 0x54; 0x16; 0x50; 0x3f; 0x8f; 0xb3; 0x76; 0x22; 0x23; 0xeb; 0xdb; 0x69; 0xda;
      0x08; 0x5a; 0xc1; 0xe4; 0x3e; 0x15; 0x99; 0x6e; 0x45; 0x8f; 0x36; 0x13; 0xd0; 0xf1; 0x1d; 0x8c;
      0x38; 0x7b; 0x2e; 0xae; 0xb4; 0x30; 0x2a; 0xee; 0xb0; 0x0d; 0x29; 0x16; 0x12; 0xbb; 0x0c; 0x00
    ]) in
  assert_norm (List.Tot.length l == 64);
  createL_mglobal l


//
// Test3
//
let msg3: b:lbuffer uint8 2ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [0xaf; 0x82]) in
  assert_norm (List.Tot.length l == 2);
  createL_mglobal l

let sk3: b:lbuffer uint8 32ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0xc5; 0xaa; 0x8d; 0xf4; 0x3f; 0x9f; 0x83; 0x7b; 0xed; 0xb7; 0x44; 0x2f; 0x31; 0xdc; 0xb7; 0xb1;
      0x66; 0xd3; 0x85; 0x35; 0x07; 0x6f; 0x09; 0x4b; 0x85; 0xce; 0x3a; 0x2e; 0x0b; 0x44; 0x58; 0xf7
    ]) in
  assert_norm (List.Tot.length l == 32);
  createL_mglobal l

let pk3: b:lbuffer uint8 32ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0xfc; 0x51; 0xcd; 0x8e; 0x62; 0x18; 0xa1; 0xa3; 0x8d; 0xa4; 0x7e; 0xd0; 0x02; 0x30; 0xf0; 0x58;
      0x08; 0x16; 0xed; 0x13; 0xba; 0x33; 0x03; 0xac; 0x5d; 0xeb; 0x91; 0x15; 0x48; 0x90; 0x80; 0x25
    ]) in
  assert_norm (List.Tot.length l == 32);
  createL_mglobal l

let sig3: b:lbuffer uint8 64ul{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x62; 0x91; 0xd6; 0x57; 0xde; 0xec; 0x24; 0x02; 0x48; 0x27; 0xe6; 0x9c; 0x3a; 0xbe; 0x01; 0xa3;
      0x0c; 0xe5; 0x48; 0xa2; 0x84; 0x74; 0x3a; 0x44; 0x5e; 0x36; 0x80; 0xd7; 0xdb; 0x5a; 0xc3; 0xac;
      0x18; 0xff; 0x9b; 0x53; 0x8d; 0x16; 0xf2; 0x90; 0xae; 0x67; 0xf7; 0x60; 0x98; 0x4d; 0xc6; 0x59;
      0x4a; 0x7c; 0x15; 0xe9; 0x71; 0x6e; 0xd2; 0x8d; 0xc0; 0x27; 0xbe; 0xce; 0xea; 0x1e; 0xc4; 0x0a
    ]) in
  assert_norm (List.Tot.length l == 64);
  createL_mglobal l


val test_verify:
     msg_len:size_t
  -> msg:lbuffer uint8 msg_len
  -> pk:lbuffer uint8 32ul
  -> sig:lbuffer uint8 64ul
  -> Stack unit
    (requires fun h ->
      live h msg /\ live h pk /\ live h sig)
    (ensures  fun h0 r h1 -> modifies0 h0 h1)

let test_verify msg_len msg pk sig =
  let res = Ed25519.verify pk msg_len msg sig in

  C.String.print (C.String.of_literal "Test Ed25519 Verify:\n");
  if res then C.String.print (C.String.of_literal "Success!\n")
  else (C.String.print (C.String.of_literal "Failure :(\n"); C.exit 255l)


val test_sign:
     msg_len:size_t
  -> msg:lbuffer uint8 msg_len
  -> sk:lbuffer uint8 32ul
  -> expected_sig:lbuffer uint8 64ul
  -> Stack unit
    (requires fun h ->
      live h msg /\ live h sk /\ live h expected_sig)
    (ensures  fun h0 r h1 -> modifies0 h0 h1)

let test_sign msg_len msg sk expected_sig =
  push_frame ();
  let test_sig = create 64ul (u8 0) in
  Ed25519.sign test_sig sk msg_len msg;

  C.String.print (C.String.of_literal "\nTest Ed25519 Sign:\n");
  if not (result_compare_display 64ul (to_const test_sig) (to_const expected_sig)) then C.exit 255l;
  pop_frame ()


val test_secret_to_public:
    sk:lbuffer uint8 32ul
  -> expected_pk:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h -> live h sk /\ live h expected_pk)
    (ensures  fun h0 r h1 -> modifies0 h0 h1)

let test_secret_to_public sk expected_pk =
  push_frame ();
  let pk = create 32ul (u8 0) in
  Ed25519.secret_to_public pk sk;

  C.String.print (C.String.of_literal "Test Ed25519 Secret_to_public:\n");
  if not (result_compare_display 32ul (to_const pk) (to_const expected_pk)) then C.exit 255l;
  pop_frame ()


val test:
     msg_len:size_t
  -> msg:lbuffer uint8 msg_len
  -> pk:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul
  -> expected_sig:lbuffer uint8 64ul
  -> Stack unit
    (requires fun h ->
      live h msg /\ live h expected_sig /\ live h pk /\ live h sk)
    (ensures  fun h0 r h1 -> modifies0 h0 h1)

let test msg_len msg pk sk expected_sig =
  test_verify msg_len msg pk expected_sig;
  test_sign msg_len msg sk expected_sig;
  test_secret_to_public sk pk


val main: unit -> St C.exit_code
let main () =
  C.String.print (C.String.of_literal "\nTEST 1. Ed25519\n");
  recall msg1;
  recall sk1;
  recall pk1;
  recall sig1;
  test 0ul msg1 pk1 sk1 sig1;

  C.String.print (C.String.of_literal "\nTEST 2. Ed25519\n");
  recall msg2;
  recall sk2;
  recall pk2;
  recall sig2;
  test 1ul msg2 pk2 sk2 sig2;

  C.String.print (C.String.of_literal "\nTEST 3. Ed25519\n");
  recall msg3;
  recall sk3;
  recall pk3;
  recall sig3;
  test 2ul msg3 pk3 sk3 sig3;

  C.EXIT_SUCCESS
