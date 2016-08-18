open Char
open Hacl_SBuffer
open Hacl_Cast
open Hacl_Utils





(* Tests from RFC 4231 *)
let _ =

  Printf.printf "#####################################################\n";
  Printf.printf "    HMAC.B: Non-incremental & Non-length hidding     \n";
  Printf.printf "#####################################################\n";
  let mac = create (uint8_to_sint8 0) 32 in

  (* Test 1 *)

  let key = Bytes.make 20 '\x0b' in
  let data = "Hi There" in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7" in

  HMAC_B.hmac_sha256 mac (from_string_block key HMAC_B.blocksize) keylen (from_string_block data HMAC_B.blocksize) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 2 *)

  let key = "Jefe" in
  let data = "what do ya want for nothing?" in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843" in

  HMAC_B.hmac_sha256 mac (from_string_block key HMAC_B.blocksize) keylen (from_string_block data HMAC_B.blocksize) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 3 *)

  let key = Bytes.make 20 '\xaa' in
  let data = Bytes.make 50 '\xdd' in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe" in

  HMAC_B.hmac_sha256 mac (from_string_block key HMAC_B.blocksize) keylen (from_string_block data HMAC_B.blocksize) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 4 *)

  let key = Bytes.make 25 '\x00' in
  Bytes.set key 0 '\x01';
  Bytes.set key 1 '\x02';
  Bytes.set key 2 '\x03';
  Bytes.set key 3 '\x04';
  Bytes.set key 4 '\x05';
  Bytes.set key 5 '\x06';
  Bytes.set key 6 '\x07';
  Bytes.set key 7 '\x08';
  Bytes.set key 8 '\x09';
  Bytes.set key 9 '\x0a';
  Bytes.set key 10 '\x0b';
  Bytes.set key 11 '\x0c';
  Bytes.set key 12 '\x0d';
  Bytes.set key 13 '\x0e';
  Bytes.set key 14 '\x0f';
  Bytes.set key 15 '\x10';
  Bytes.set key 16 '\x11';
  Bytes.set key 17 '\x12';
  Bytes.set key 18 '\x13';
  Bytes.set key 19 '\x14';
  Bytes.set key 20 '\x15';
  Bytes.set key 21 '\x16';
  Bytes.set key 22 '\x17';
  Bytes.set key 23 '\x18';
  Bytes.set key 24 '\x19';
  let data = Bytes.make 50 '\xcd' in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b" in

  HMAC_B.hmac_sha256 mac (from_string_block key HMAC_B.blocksize) keylen (from_string_block data HMAC_B.blocksize) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 5 *)

  let key = Bytes.make 20 '\x0c' in
  let data = "Test With Truncation" in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "a3b6167473100ee06e0c796c2955552b" in

  HMAC_B.hmac_sha256 mac (from_string_block key HMAC_B.blocksize) keylen (from_string_block data HMAC_B.blocksize) datalen;
  let res = sub mac 0 16 in
  Printf.printf "Result (truncation at 128) :";
  print_l_bytes res 16;
  Printf.printf "Expected                   :%s\n\n" expected;


  (* Test 6 *)

  let key = Bytes.make 131 '\xaa' in
  let data = "Test Using Larger Than Block-Size Key - Hash Key First" in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54" in

  HMAC_B.hmac_sha256 mac (from_string_block key (10 * HMAC_B.blocksize)) keylen (from_string_block data (3 * HMAC_B.blocksize)) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 7 *)

  let key = Bytes.make 131 '\xaa' in
  let data = "This is a test using a larger than block-size key and a larger than block-size data. The key needs to be hashed before being used by the HMAC algorithm." in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2" in

  HMAC_B.hmac_sha256 mac (from_string_block key (10 * HMAC_B.blocksize)) keylen (from_string_block data (3 * HMAC_B.blocksize)) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected
