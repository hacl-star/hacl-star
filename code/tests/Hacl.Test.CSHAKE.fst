module Hacl.Test.CSHAKE

open FStar.HyperStack.All
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.PrintBuffer
open Hacl.SHA3

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val test_cshake128:
     msg_len:size_t{v msg_len > 0}
  -> msg:ilbuffer uint8 msg_len
  -> ctr:uint16
  -> out_len:size_t{size_v out_len > 0}
  -> expected:ilbuffer uint8 out_len
  -> Stack unit
    (requires fun h -> live h msg /\ live h expected)
    (ensures  fun h0 r h1 -> True)
let test_cshake128 msg_len msg ctr out_len expected =
  push_frame ();
  let test = create out_len (u8 0) in
  let msg' = create msg_len (u8 0) in
  copy msg' msg;
  cshake128_frodo msg_len msg' ctr out_len test;
  if not (result_compare_display out_len test expected) then C.exit 255l;
  pop_frame ()

inline_for_extraction noextract
val u8: n:nat{n < 0x100} -> uint8
let u8 n = u8 n

//
// Test1_cSHAKE128
//
let test1_plaintext: b:ilbuffer uint8 16ul{ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x61; 0x62; 0x63; 0x64; 0x65; 0x66; 0x67; 0x68; 0x62; 0x63; 0x64; 0x65; 0x66; 0x67; 0x68; 0x69])
  in
  assert_norm (List.Tot.length l == 16);
  createL_global l

let test1_expected: b:ilbuffer uint8 64ul{ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [0x89; 0x2e; 0xd8; 0xb5; 0x1a; 0xec; 0x70; 0x3f; 0xda; 0x4b; 0x40; 0x0e; 0x93; 0xa4; 0x94; 0x56;
     0xd3; 0x28; 0xdf; 0x46; 0x0d; 0x35; 0x80; 0x2a; 0x01; 0xbf; 0xcf; 0xa7; 0x3d; 0xa3; 0xd0; 0xb1;
     0xb4; 0x87; 0x94; 0x2d; 0xe9; 0x34; 0x8b; 0x9f; 0xa0; 0xbe; 0xb0; 0xed; 0x09; 0x29; 0x5b; 0x96;
     0x9b; 0x2f; 0x14; 0x24; 0xf8; 0x6a; 0x4a; 0x39; 0xc5; 0x2e; 0xb3; 0xc5; 0xe2; 0xb2; 0x23; 0x6f])
  in
  assert_norm (List.Tot.length l == 64);
  createL_global l

val main: unit -> St C.exit_code
let main () =
  C.String.print (C.String.of_literal "\nTEST 1. SHA3\n");
  recall test1_expected;
  recall test1_plaintext;
  test_cshake128 16ul test1_plaintext (u16 2) 64ul test1_expected;

  C.EXIT_SUCCESS
