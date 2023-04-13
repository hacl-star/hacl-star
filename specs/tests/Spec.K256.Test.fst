module Spec.K256.Test

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.K256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Test 1

let test1_pk : lbytes 64 =
  let l = List.Tot.map u8_from_UInt8 [
    0xb8uy; 0x38uy; 0xffuy; 0x44uy; 0xe5uy; 0xbcuy; 0x17uy; 0x7buy;
    0xf2uy; 0x11uy; 0x89uy; 0xd0uy; 0x76uy; 0x60uy; 0x82uy; 0xfcuy;
    0x9duy; 0x84uy; 0x32uy; 0x26uy; 0x88uy; 0x7fuy; 0xc9uy; 0x76uy;
    0x03uy; 0x71uy; 0x10uy; 0x0buy; 0x7euy; 0xe2uy; 0x0auy; 0x6fuy;
    0xf0uy; 0xc9uy; 0xd7uy; 0x5buy; 0xfbuy; 0xa7uy; 0xb3uy; 0x1auy;
    0x6buy; 0xcauy; 0x19uy; 0x74uy; 0x49uy; 0x6euy; 0xebuy; 0x56uy;
    0xdeuy; 0x35uy; 0x70uy; 0x71uy; 0x95uy; 0x5duy; 0x83uy; 0xc4uy;
    0xb1uy; 0xbauy; 0xdauy; 0xa0uy; 0xb2uy; 0x18uy; 0x32uy; 0xe9uy
  ] in
  assert_norm (List.Tot.length l == 64);
  of_list l


let test1_msg : lbytes 6 =
  let l = List.Tot.map u8_from_UInt8 [
    0x31uy; 0x32uy; 0x33uy; 0x34uy; 0x30uy; 0x30uy
  ] in
  assert_norm (List.Tot.length l == 6);
  of_list l


let test1_sgnt : lbytes 64 =
  let l = List.Tot.map u8_from_UInt8 [
    0x81uy; 0x3euy; 0xf7uy; 0x9cuy; 0xceuy; 0xfauy; 0x9auy; 0x56uy;
    0xf7uy; 0xbauy; 0x80uy; 0x5fuy; 0x0euy; 0x47uy; 0x85uy; 0x84uy;
    0xfeuy; 0x5fuy; 0x0duy; 0xd5uy; 0xf5uy; 0x67uy; 0xbcuy; 0x09uy;
    0xb5uy; 0x12uy; 0x3cuy; 0xcbuy; 0xc9uy; 0x83uy; 0x23uy; 0x65uy;
    0x6fuy; 0xf1uy; 0x8auy; 0x52uy; 0xdcuy; 0xc0uy; 0x33uy; 0x6fuy;
    0x7auy; 0xf6uy; 0x24uy; 0x00uy; 0xa6uy; 0xdduy; 0x9buy; 0x81uy;
    0x07uy; 0x32uy; 0xbauy; 0xf1uy; 0xffuy; 0x75uy; 0x80uy; 0x00uy;
    0xd6uy; 0xf6uy; 0x13uy; 0xa5uy; 0x56uy; 0xebuy; 0x31uy; 0xbauy
  ] in
  assert_norm (List.Tot.length l == 64);
  of_list l


///  Test 2

let test2_sk : lbytes 32 =
  let l = List.Tot.map u8_from_UInt8 [
    0xebuy; 0xb2uy; 0xc0uy; 0x82uy; 0xfduy; 0x77uy; 0x27uy; 0x89uy;
    0x0auy; 0x28uy; 0xacuy; 0x82uy; 0xf6uy; 0xbduy; 0xf9uy; 0x7buy;
    0xaduy; 0x8duy; 0xe9uy; 0xf5uy; 0xd7uy; 0xc9uy; 0x02uy; 0x86uy;
    0x92uy; 0xdeuy; 0x1auy; 0x25uy; 0x5cuy; 0xaduy; 0x3euy; 0x0fuy
  ] in
  assert_norm (List.Tot.length l == 32);
  of_list l


let test2_pk : lbytes 64 =
  let l = List.Tot.map u8_from_UInt8 [
    0x77uy; 0x9duy; 0xd1uy; 0x97uy; 0xa5uy; 0xdfuy; 0x97uy; 0x7euy;
    0xd2uy; 0xcfuy; 0x6cuy; 0xb3uy; 0x1duy; 0x82uy; 0xd4uy; 0x33uy;
    0x28uy; 0xb7uy; 0x90uy; 0xdcuy; 0x6buy; 0x3buy; 0x7duy; 0x44uy;
    0x37uy; 0xa4uy; 0x27uy; 0xbduy; 0x58uy; 0x47uy; 0xdfuy; 0xcduy;
    0xe9uy; 0x4buy; 0x72uy; 0x4auy; 0x55uy; 0x5buy; 0x6duy; 0x01uy;
    0x7buy; 0xb7uy; 0x60uy; 0x7cuy; 0x3euy; 0x32uy; 0x81uy; 0xdauy;
    0xf5uy; 0xb1uy; 0x69uy; 0x9duy; 0x6euy; 0xf4uy; 0x12uy; 0x49uy;
    0x75uy; 0xc9uy; 0x23uy; 0x7buy; 0x91uy; 0x7duy; 0x42uy; 0x6fuy
  ] in
  assert_norm (List.Tot.length l == 64);
  of_list l


let test2_nonce : lbytes 32 =
  let l = List.Tot.map u8_from_UInt8 [
    0x49uy; 0xa0uy; 0xd7uy; 0xb7uy; 0x86uy; 0xecuy; 0x9cuy; 0xdeuy;
    0x0duy; 0x07uy; 0x21uy; 0xd7uy; 0x28uy; 0x04uy; 0xbeuy; 0xfduy;
    0x06uy; 0x57uy; 0x1cuy; 0x97uy; 0x4buy; 0x19uy; 0x1euy; 0xfbuy;
    0x42uy; 0xecuy; 0xf3uy; 0x22uy; 0xbauy; 0x9duy; 0xdduy; 0x9auy
  ] in
  assert_norm (List.Tot.length l == 32);
  of_list l


let test2_msgHash : lbytes 32 =
  let l = List.Tot.map u8_from_UInt8 [
    0x4buy; 0x68uy; 0x8duy; 0xf4uy; 0x0buy; 0xceuy; 0xdbuy; 0xe6uy;
    0x41uy; 0xdduy; 0xb1uy; 0x6fuy; 0xf0uy; 0xa1uy; 0x84uy; 0x2duy;
    0x9cuy; 0x67uy; 0xeauy; 0x1cuy; 0x3buy; 0xf6uy; 0x3fuy; 0x3euy;
    0x04uy; 0x71uy; 0xbauy; 0xa6uy; 0x64uy; 0x53uy; 0x1duy; 0x1auy
  ] in
  assert_norm (List.Tot.length l == 32);
  of_list l


let test2_sgnt : lbytes 64 =
  let l = List.Tot.map u8_from_UInt8 [
    0x24uy; 0x10uy; 0x97uy; 0xefuy; 0xbfuy; 0x8buy; 0x63uy; 0xbfuy;
    0x14uy; 0x5cuy; 0x89uy; 0x61uy; 0xdbuy; 0xdfuy; 0x10uy; 0xc3uy;
    0x10uy; 0xefuy; 0xbbuy; 0x3buy; 0x26uy; 0x76uy; 0xbbuy; 0xc0uy;
    0xf8uy; 0xb0uy; 0x85uy; 0x05uy; 0xc9uy; 0xe2uy; 0xf7uy; 0x95uy;
    0x02uy; 0x10uy; 0x06uy; 0xb7uy; 0x83uy; 0x86uy; 0x09uy; 0x33uy;
    0x9euy; 0x8buy; 0x41uy; 0x5auy; 0x7fuy; 0x9auy; 0xcbuy; 0x1buy;
    0x66uy; 0x18uy; 0x28uy; 0x13uy; 0x1auy; 0xefuy; 0x1euy; 0xcbuy;
    0xc7uy; 0x95uy; 0x5duy; 0xfbuy; 0x01uy; 0xf3uy; 0xcauy; 0x0euy
  ] in
  assert_norm (List.Tot.length l == 64);
  of_list l


let test_secret_to_public (sk:lbytes 32) (pk_expected:lbytes 64) : FStar.All.ML bool =
  let pk = secret_to_public sk in

  let is_pk_valid =
    match pk with
    | Some pk -> for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) pk_expected pk
    | None -> false in

  if is_pk_valid then IO.print_string "Test K256 secret_to_public: Success!\n"
  else IO.print_string "Test K256 secret_to_public: Failure :(\n";
  is_pk_valid


val test_verify:
    pk:lbytes 64
  -> msg:bytes{length msg <= max_size_t}
  -> sgnt:lbytes 64 ->
  FStar.All.ML bool

let test_verify pk msg sgnt =
  let verify : bool = ecdsa_verify_sha256 (length msg) msg pk sgnt in
  if verify
  then begin IO.print_string "Test K256 ecdsa verification: Success!\n"; true end
  else begin IO.print_string "Test K256 ecdsa verification: Failure :(\n"; false end


val test_sign_and_verify:
    sk:lbytes 32
  -> pk:lbytes 64
  -> nonce:lbytes 32
  -> msgHash:lbytes 32
  -> sgnt:lbytes 64 ->
  FStar.All.ML bool

let test_sign_and_verify sk pk nonce msgHash sgnt =
  let signature = ecdsa_sign_hashed_msg msgHash sk nonce in

  let is_sgnt_valid =
    match signature with
    | Some x -> for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) sgnt x
    | None -> false in

  let verify_sgnt = ecdsa_verify_hashed_msg msgHash pk sgnt in

  if verify_sgnt && is_sgnt_valid
  then begin IO.print_string "Test K256 ecdsa signature and verification: Success!\n"; true end
  else begin IO.print_string "Test K256 ecdsa signature and verification: Failure :(\n"; false end


let test_public_key_compressed (pk_raw:lbytes 64) : FStar.All.ML bool =
  let pk_c = pk_compressed_from_raw pk_raw in
  let pk_raw_c = pk_compressed_to_raw pk_c in

  match pk_raw_c with
  | Some pk_raw_c ->
    let is_pk_c_valid =
      for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) pk_raw_c pk_raw in
    if not is_pk_c_valid then IO.print_string "Test K256 pk_compressed (Some): Failure :(\n"
    else IO.print_string "Test K256 pk_compressed: Success!\n";
    is_pk_c_valid
  | None ->
    begin IO.print_string "Test K256 pk_compressed (None): Failure :(\n"; false end


let test_public_key_uncompressed (pk_raw:lbytes 64) : FStar.All.ML bool =
  let pk_u = pk_uncompressed_from_raw pk_raw in
  let pk_raw_u = pk_uncompressed_to_raw pk_u in

  match pk_raw_u with
  | Some pk_raw_u ->
    let is_pk_u_valid =
      for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) pk_raw_u pk_raw in
    if not is_pk_u_valid then IO.print_string "Test K256 pk_uncompressed (Some): Failure :(\n"
    else IO.print_string "Test K256 pk_uncompressed: Success!\n";
    is_pk_u_valid
  | None ->
    begin IO.print_string "Test K256 pk_uncompressed (None): Failure :(\n"; false end

#set-options "--ifuel 2"

let test () : FStar.All.ML bool  =
  let t0 : bool = test_secret_to_public test2_sk test2_pk in
  let t1 : bool = test_verify test1_pk test1_msg test1_sgnt in
  let t2 : bool = test_sign_and_verify test2_sk test2_pk test2_nonce test2_msgHash test2_sgnt in
  let t3 : bool = test_public_key_compressed test2_pk in
  let t4 : bool = test_public_key_uncompressed test2_pk in

  if t0 && t1 && t2 && t3 && t4
  then begin IO.print_string "Test K256 ecdsa: Success!\n"; true end
  else begin IO.print_string "Test K256 ecdsa: Failure :(\n"; false end
