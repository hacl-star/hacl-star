module Hacl.Test.K256

open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.PrintBuffer

module K256 = Hacl.K256.ECDSA

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val u8: n:nat{n < 0x100} -> uint8
let u8 n = u8 n

///  Test1

let pk1: b:lbuffer uint8 64ul{ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0xb8; 0x38; 0xff; 0x44; 0xe5; 0xbc; 0x17; 0x7b; 0xf2; 0x11; 0x89; 0xd0; 0x76; 0x60; 0x82; 0xfc;
      0x9d; 0x84; 0x32; 0x26; 0x88; 0x7f; 0xc9; 0x76; 0x03; 0x71; 0x10; 0x0b; 0x7e; 0xe2; 0x0a; 0x6f;
      0xf0; 0xc9; 0xd7; 0x5b; 0xfb; 0xa7; 0xb3; 0x1a; 0x6b; 0xca; 0x19; 0x74; 0x49; 0x6e; 0xeb; 0x56;
      0xde; 0x35; 0x70; 0x71; 0x95; 0x5d; 0x83; 0xc4; 0xb1; 0xba; 0xda; 0xa0; 0xb2; 0x18; 0x32; 0xe9 ]) in
  assert_norm (List.Tot.length l == 64);
  createL_mglobal l


let msg1: b:lbuffer uint8 6ul{ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [ 0x31; 0x32; 0x33; 0x34; 0x30; 0x30]) in
  assert_norm (List.Tot.length l == 6);
  createL_mglobal l


let sgnt1: b:lbuffer uint8 64ul{ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x81; 0x3e; 0xf7; 0x9c; 0xce; 0xfa; 0x9a; 0x56; 0xf7; 0xba; 0x80; 0x5f; 0x0e; 0x47; 0x85; 0x84;
      0xfe; 0x5f; 0x0d; 0xd5; 0xf5; 0x67; 0xbc; 0x09; 0xb5; 0x12; 0x3c; 0xcb; 0xc9; 0x83; 0x23; 0x65;
      0x6f; 0xf1; 0x8a; 0x52; 0xdc; 0xc0; 0x33; 0x6f; 0x7a; 0xf6; 0x24; 0x00; 0xa6; 0xdd; 0x9b; 0x81;
      0x07; 0x32; 0xba; 0xf1; 0xff; 0x75; 0x80; 0x00; 0xd6; 0xf6; 0x13; 0xa5; 0x56; 0xeb; 0x31; 0xba ]) in
  assert_norm (List.Tot.length l == 64);
  createL_mglobal l


///  Test2

let sk2: b:lbuffer uint8 32ul{ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0xeb; 0xb2; 0xc0; 0x82; 0xfd; 0x77; 0x27; 0x89; 0x0a; 0x28; 0xac; 0x82; 0xf6; 0xbd; 0xf9; 0x7b;
      0xad; 0x8d; 0xe9; 0xf5; 0xd7; 0xc9; 0x02; 0x86; 0x92; 0xde; 0x1a; 0x25; 0x5c; 0xad; 0x3e; 0x0f ]) in
  assert_norm (List.Tot.length l == 32);
  createL_mglobal l


let pk2: b:lbuffer uint8 64ul{ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x77; 0x9d; 0xd1; 0x97; 0xa5; 0xdf; 0x97; 0x7e; 0xd2; 0xcf; 0x6c; 0xb3; 0x1d; 0x82; 0xd4; 0x33;
      0x28; 0xb7; 0x90; 0xdc; 0x6b; 0x3b; 0x7d; 0x44; 0x37; 0xa4; 0x27; 0xbd; 0x58; 0x47; 0xdf; 0xcd;
      0xe9; 0x4b; 0x72; 0x4a; 0x55; 0x5b; 0x6d; 0x01; 0x7b; 0xb7; 0x60; 0x7c; 0x3e; 0x32; 0x81; 0xda;
      0xf5; 0xb1; 0x69; 0x9d; 0x6e; 0xf4; 0x12; 0x49; 0x75; 0xc9; 0x23; 0x7b; 0x91; 0x7d; 0x42; 0x6f ]) in
  assert_norm (List.Tot.length l == 64);
  createL_mglobal l


let nonce2: b:lbuffer uint8 32ul{ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x49; 0xa0; 0xd7; 0xb7; 0x86; 0xec; 0x9c; 0xde; 0x0d; 0x07; 0x21; 0xd7; 0x28; 0x04; 0xbe; 0xfd;
      0x06; 0x57; 0x1c; 0x97; 0x4b; 0x19; 0x1e; 0xfb; 0x42; 0xec; 0xf3; 0x22; 0xba; 0x9d; 0xdd; 0x9a ]) in
  assert_norm (List.Tot.length l == 32);
  createL_mglobal l


let msgHash2: b:lbuffer uint8 32ul{ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x4b; 0x68; 0x8d; 0xf4; 0x0b; 0xce; 0xdb; 0xe6; 0x41; 0xdd; 0xb1; 0x6f; 0xf0; 0xa1; 0x84; 0x2d;
      0x9c; 0x67; 0xea; 0x1c; 0x3b; 0xf6; 0x3f; 0x3e; 0x04; 0x71; 0xba; 0xa6; 0x64; 0x53; 0x1d; 0x1a ]) in
  assert_norm (List.Tot.length l == 32);
  createL_mglobal l


let sgnt2: b:lbuffer uint8 64ul{ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x24; 0x10; 0x97; 0xef; 0xbf; 0x8b; 0x63; 0xbf; 0x14; 0x5c; 0x89; 0x61; 0xdb; 0xdf; 0x10; 0xc3;
      0x10; 0xef; 0xbb; 0x3b; 0x26; 0x76; 0xbb; 0xc0; 0xf8; 0xb0; 0x85; 0x05; 0xc9; 0xe2; 0xf7; 0x95;
      0x02; 0x10; 0x06; 0xb7; 0x83; 0x86; 0x09; 0x33; 0x9e; 0x8b; 0x41; 0x5a; 0x7f; 0x9a; 0xcb; 0x1b;
      0x66; 0x18; 0x28; 0x13; 0x1a; 0xef; 0x1e; 0xcb; 0xc7; 0x95; 0x5d; 0xfb; 0x01; 0xf3; 0xca; 0x0e ]) in
  assert_norm (List.Tot.length l == 64);
  createL_mglobal l


val test_secret_to_public:
    sk:lbuffer uint8 32ul
  -> pk:lbuffer uint8 64ul
  -> Stack unit
  (requires fun h -> live h sk /\ live h pk)
  (ensures  fun h0 _ h1 -> modifies0 h0 h1)

let test_secret_to_public sk pk =
  push_frame ();
  let pk_comp = create 64ul (u8 0) in
  let b = K256.secret_to_public pk_comp sk in

  C.String.print (C.String.of_literal "\n Test K256 secret_to_public: ");
  let is_eq = result_compare_display 64ul (to_const pk) (to_const pk_comp) in
  if (is_eq && b) then C.String.print (C.String.of_literal "Success!\n")
  else (C.String.print (C.String.of_literal "Failure :(\n"); C.exit 255l);
  pop_frame ()


val test_verify_sha256:
    msg_len:size_t
  -> msg:lbuffer uint8 msg_len
  -> pk:lbuffer uint8 64ul
  -> sgnt:lbuffer uint8 64ul
  -> Stack unit
    (requires fun h -> live h msg /\ live h pk /\ live h sgnt)
    (ensures  fun h0 r h1 -> modifies0 h0 h1)

let test_verify_sha256 msg_len msg pk sgnt =
  let b = K256.ecdsa_verify_sha256 msg_len msg pk sgnt in

  C.String.print (C.String.of_literal "\n Test K256 ecdsa verification: ");
  if b then C.String.print (C.String.of_literal "Success!\n")
  else (C.String.print (C.String.of_literal "Failure :(\n"); C.exit 255l)


val test_verify_hashed:
    msgHash:lbuffer uint8 32ul
  -> pk:lbuffer uint8 64ul
  -> sgnt:lbuffer uint8 64ul
  -> Stack unit
    (requires fun h -> live h msgHash /\ live h pk /\ live h sgnt)
    (ensures  fun h0 r h1 -> modifies0 h0 h1)

let test_verify_hashed msgHash pk sgnt =
  let b = K256.ecdsa_verify_hashed_msg msgHash pk sgnt in

  C.String.print (C.String.of_literal "\n Test K256 ecdsa verification: ");
  if b then C.String.print (C.String.of_literal "Success!\n")
  else (C.String.print (C.String.of_literal "Failure :(\n"); C.exit 255l)


val test_sign_hashed:
    msgHash:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul
  -> nonce:lbuffer uint8 32ul
  -> expected_sgnt:lbuffer uint8 64ul
  -> Stack unit
    (requires fun h ->
      live h msgHash /\ live h sk /\ live h nonce /\ live h expected_sgnt)
    (ensures  fun h0 r h1 -> modifies0 h0 h1)

let test_sign_hashed msgHash sk nonce expected_sgnt =
  push_frame ();
  let sgnt = create 64ul (u8 0) in
  let _ = K256.ecdsa_sign_hashed_msg sgnt msgHash sk nonce in

  C.String.print (C.String.of_literal "\n Test K256 ecdsa signing:\n");
  if not (result_compare_display 64ul (to_const sgnt) (to_const expected_sgnt)) then C.exit 255l;
  pop_frame ()


val test_sign_and_verify_hashed:
    msgHash:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul
  -> nonce:lbuffer uint8 32ul
  -> pk:lbuffer uint8 64ul
  -> expected_sgnt:lbuffer uint8 64ul
  -> Stack unit
    (requires fun h ->
      live h msgHash /\ live h sk /\ live h nonce /\
      live h pk /\ live h expected_sgnt)
    (ensures  fun h0 r h1 -> modifies0 h0 h1)

let test_sign_and_verify_hashed msgHash sk nonce pk expected_sgnt =
  test_verify_hashed msgHash pk expected_sgnt;
  test_sign_hashed msgHash sk nonce expected_sgnt


val test_public_key_compressed: pk:lbuffer uint8 64ul -> Stack unit
  (requires fun h -> live h pk)
  (ensures  fun h0 _ h1 -> modifies0 h0 h1)

let test_public_key_compressed pk =
  push_frame ();
  let pk_c = create 33ul (u8 0) in
  let pk_raw_c = create 64ul (u8 0) in

  K256.public_key_compressed_from_raw pk_c pk;
  let b = K256.public_key_compressed_to_raw pk_raw_c pk_c in

  C.String.print (C.String.of_literal "\n Test K256 pk_compressed:\n");
  if b
  then (if not (result_compare_display 64ul (to_const pk) (to_const pk_raw_c)) then C.exit 255l)
  else (C.String.print (C.String.of_literal "Failure :(\n"); C.exit 255l);
  pop_frame ()


val test_public_key_uncompressed: pk:lbuffer uint8 64ul -> Stack unit
  (requires fun h -> live h pk)
  (ensures  fun h0 _ h1 -> modifies0 h0 h1)

let test_public_key_uncompressed pk =
  push_frame ();
  let pk_u = create 65ul (u8 0) in
  let pk_raw_u = create 64ul (u8 0) in

  K256.public_key_uncompressed_from_raw pk_u pk;
  let b = K256.public_key_uncompressed_to_raw pk_raw_u pk_u in

  C.String.print (C.String.of_literal "\n Test K256 pk_uncompressed:\n");
  if b
  then (if not (result_compare_display 64ul (to_const pk) (to_const pk_raw_u)) then C.exit 255l)
  else (C.String.print (C.String.of_literal "Failure :(\n"); C.exit 255l);
  pop_frame ()


val main: unit -> St C.exit_code
let main () =
  C.String.print (C.String.of_literal "\nTEST 1. K256\n");
  recall msg1;
  recall pk1;
  recall sgnt1;
  test_verify_sha256 6ul msg1 pk1 sgnt1;

  C.String.print (C.String.of_literal "\nTEST 2. K256\n");
  recall msgHash2;
  recall sk2;
  recall nonce2;
  recall pk2;
  recall sgnt2;
  test_sign_and_verify_hashed msgHash2 sk2 nonce2 pk2 sgnt2;

  C.String.print (C.String.of_literal "\nTEST 3. K256\n");
  test_public_key_compressed pk1;

  C.String.print (C.String.of_literal "\nTEST 4. K256\n");
  test_public_key_uncompressed pk1;

  C.String.print (C.String.of_literal "\nTEST 5. K256\n");
  test_secret_to_public sk2 pk2;

  C.EXIT_SUCCESS
