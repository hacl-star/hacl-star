module Hacl.Test.Blake2b.Incremental

open FStar.HyperStack.All
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.PrintBuffer
open Hacl.Blake2b
open Hacl.Impl.Blake2b.Incremental

#reset-options "--admit_smt_queries true"

val test_blake2b:
    msg_len:size_t
  -> msg:ilbuffer uint8 msg_len
  -> key_len:size_t{v key_len <= 32 /\ (if v key_len = 0 then v msg_len < pow2 64 else v msg_len + 64 < pow2 64)}
  -> key:ilbuffer uint8 key_len
  -> expected_len:size_t{1 <= v expected_len /\ v expected_len <= 32}
  -> expected:ilbuffer uint8 expected_len
  -> Stack bool
    (requires fun h ->
      live h msg /\ live h expected /\ live h key)
    (ensures  fun h0 r h1 -> True)

let test_blake2b ll d kk k nn expected =
  push_frame();
  let tmsg = create ll (u8 0) in
  mapT ll tmsg secret d;
  let tkey = create kk (u8 0) in
  mapT kk tkey secret k;
  let output = create nn (u8 0) in
  let state = {
    hash = create (size 8) (u64 0);
    n = create (size 1) (size 0);
    pl = create (size 1) (size 0);
    block = create Hacl.Impl.Blake2b.size_block (u8 0);
  } in
  blake2b_incremental_init state kk k nn;
  let res = blake2b_incremental_update state ll d in
  blake2b_incremental_finish nn output state;
  print_compare_display nn output expected;
  pop_frame();
  res


///
/// Test 1
///

inline_for_extraction let test1_size_plaintext = 44ul
let test1_plaintext: b:ilbuffer uint8 test1_size_plaintext{ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x00; 0x01; 0x02; 0x03; 0x04; 0x05; 0x06; 0x07;
      0x08; 0x09; 0x0a; 0x0b; 0x0c; 0x0d; 0x0e; 0x0f;
      0x10; 0x11; 0x12; 0x13; 0x14; 0x15; 0x16; 0x17;
      0x18; 0x19; 0x1a; 0x1b; 0x1c; 0x1d; 0x1e; 0x1f;
      0x20; 0x21; 0x22; 0x23; 0x24; 0x25; 0x26; 0x27;
      0x28; 0x29; 0x2a; 0x2b])
  in
  assert_norm (List.Tot.length l == 44);
  createL_global l


inline_for_extraction let test1_size_key = size 64
let test1_key: b:ilbuffer uint8 test1_size_key{ recallable b } =
  let open Lib.RawIntTypes in
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x00; 0x01; 0x02; 0x03; 0x04; 0x05; 0x06; 0x07;
      0x08; 0x09; 0x0a; 0x0b; 0x0c; 0x0d; 0x0e; 0x0f;
      0x10; 0x11; 0x12; 0x13; 0x14; 0x15; 0x16; 0x17;
      0x18; 0x19; 0x1a; 0x1b; 0x1c; 0x1d; 0x1e; 0x1f;
      0x20; 0x21; 0x22; 0x23; 0x24; 0x25; 0x26; 0x27;
      0x28; 0x29; 0x2a; 0x2b; 0x2c; 0x2d; 0x2e; 0x2f;
      0x30; 0x31; 0x32; 0x33; 0x34; 0x35; 0x36; 0x37;
      0x38; 0x39; 0x3a; 0x3b; 0x3c; 0x3d; 0x3e; 0x3f])
  in
  assert_norm (List.Tot.length l == 64); admit();
  createL_global l


inline_for_extraction let test1_size_expected = size 64
let test1_expected: b:ilbuffer uint8 test1_size_expected{ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0xc8; 0xf6; 0x8e; 0x69; 0x6e; 0xd2; 0x82; 0x42;
      0xbf; 0x99; 0x7f; 0x5b; 0x3b; 0x34; 0x95; 0x95;
      0x08; 0xe4; 0x2d; 0x61; 0x38; 0x10; 0xf1; 0xe2;
      0xa4; 0x35; 0xc9; 0x6e; 0xd2; 0xff; 0x56; 0x0c;
      0x70; 0x22; 0xf3; 0x61; 0xa9; 0x23; 0x4b; 0x98;
      0x37; 0xfe; 0xee; 0x90; 0xbf; 0x47; 0x92; 0x2e;
      0xe0; 0xfd; 0x5f; 0x8d; 0xdf; 0x82; 0x37; 0x18;
      0xd8; 0x6d; 0x1e; 0x16; 0xc6; 0x09; 0x00; 0x71 ])
  in
  assert_norm (List.Tot.length l == 64);
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
  let res = test_blake2b test1_size_plaintext test1_plaintext test1_size_key test1_key test1_size_expected test1_expected in
  if res then () else (C.String.print (C.String.of_literal "\nFAILED in blake2b_incremental_update !!!\n"));
  C.EXIT_SUCCESS
