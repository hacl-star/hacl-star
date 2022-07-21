module Spec.K256.Test

#reset-options "--z3rlimit 100 --fuel 0 --ifuel 0"

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.K256

//
// Test 1
//

let test1_pk = List.Tot.map u8_from_UInt8 [
  0xb8uy; 0x38uy; 0xffuy; 0x44uy; 0xe5uy; 0xbcuy; 0x17uy; 0x7buy;
  0xf2uy; 0x11uy; 0x89uy; 0xd0uy; 0x76uy; 0x60uy; 0x82uy; 0xfcuy;
  0x9duy; 0x84uy; 0x32uy; 0x26uy; 0x88uy; 0x7fuy; 0xc9uy; 0x76uy;
  0x03uy; 0x71uy; 0x10uy; 0x0buy; 0x7euy; 0xe2uy; 0x0auy; 0x6fuy;
  0xf0uy; 0xc9uy; 0xd7uy; 0x5buy; 0xfbuy; 0xa7uy; 0xb3uy; 0x1auy;
  0x6buy; 0xcauy; 0x19uy; 0x74uy; 0x49uy; 0x6euy; 0xebuy; 0x56uy;
  0xdeuy; 0x35uy; 0x70uy; 0x71uy; 0x95uy; 0x5duy; 0x83uy; 0xc4uy;
  0xb1uy; 0xbauy; 0xdauy; 0xa0uy; 0xb2uy; 0x18uy; 0x32uy; 0xe9uy
]

let test1_msg = List.Tot.map u8_from_UInt8 [
  0x31uy; 0x32uy; 0x33uy; 0x34uy; 0x30uy; 0x30uy
]

let test1_sgnt = List.Tot.map u8_from_UInt8 [
  0x81uy; 0x3euy; 0xf7uy; 0x9cuy; 0xceuy; 0xfauy; 0x9auy; 0x56uy;
  0xf7uy; 0xbauy; 0x80uy; 0x5fuy; 0x0euy; 0x47uy; 0x85uy; 0x84uy;
  0xfeuy; 0x5fuy; 0x0duy; 0xd5uy; 0xf5uy; 0x67uy; 0xbcuy; 0x09uy;
  0xb5uy; 0x12uy; 0x3cuy; 0xcbuy; 0xc9uy; 0x83uy; 0x23uy; 0x65uy;
  0x6fuy; 0xf1uy; 0x8auy; 0x52uy; 0xdcuy; 0xc0uy; 0x33uy; 0x6fuy;
  0x7auy; 0xf6uy; 0x24uy; 0x00uy; 0xa6uy; 0xdduy; 0x9buy; 0x81uy;
  0x07uy; 0x32uy; 0xbauy; 0xf1uy; 0xffuy; 0x75uy; 0x80uy; 0x00uy;
  0xd6uy; 0xf6uy; 0x13uy; 0xa5uy; 0x56uy; 0xebuy; 0x31uy; 0xbauy
]

//
// Test 2
//

let test2_sk = List.Tot.map u8_from_UInt8 [
  0xebuy; 0xb2uy; 0xc0uy; 0x82uy; 0xfduy; 0x77uy; 0x27uy; 0x89uy;
  0x0auy; 0x28uy; 0xacuy; 0x82uy; 0xf6uy; 0xbduy; 0xf9uy; 0x7buy;
  0xaduy; 0x8duy; 0xe9uy; 0xf5uy; 0xd7uy; 0xc9uy; 0x02uy; 0x86uy;
  0x92uy; 0xdeuy; 0x1auy; 0x25uy; 0x5cuy; 0xaduy; 0x3euy; 0x0fuy
]

let test2_pk = List.Tot.map u8_from_UInt8 [
  0x77uy; 0x9duy; 0xd1uy; 0x97uy; 0xa5uy; 0xdfuy; 0x97uy; 0x7euy;
  0xd2uy; 0xcfuy; 0x6cuy; 0xb3uy; 0x1duy; 0x82uy; 0xd4uy; 0x33uy;
  0x28uy; 0xb7uy; 0x90uy; 0xdcuy; 0x6buy; 0x3buy; 0x7duy; 0x44uy;
  0x37uy; 0xa4uy; 0x27uy; 0xbduy; 0x58uy; 0x47uy; 0xdfuy; 0xcduy;
  0xe9uy; 0x4buy; 0x72uy; 0x4auy; 0x55uy; 0x5buy; 0x6duy; 0x01uy;
  0x7buy; 0xb7uy; 0x60uy; 0x7cuy; 0x3euy; 0x32uy; 0x81uy; 0xdauy;
  0xf5uy; 0xb1uy; 0x69uy; 0x9duy; 0x6euy; 0xf4uy; 0x12uy; 0x49uy;
  0x75uy; 0xc9uy; 0x23uy; 0x7buy; 0x91uy; 0x7duy; 0x42uy; 0x6fuy
]

let test2_nonce = List.Tot.map u8_from_UInt8 [
  0x49uy; 0xa0uy; 0xd7uy; 0xb7uy; 0x86uy; 0xecuy; 0x9cuy; 0xdeuy;
  0x0duy; 0x07uy; 0x21uy; 0xd7uy; 0x28uy; 0x04uy; 0xbeuy; 0xfduy;
  0x06uy; 0x57uy; 0x1cuy; 0x97uy; 0x4buy; 0x19uy; 0x1euy; 0xfbuy;
  0x42uy; 0xecuy; 0xf3uy; 0x22uy; 0xbauy; 0x9duy; 0xdduy; 0x9auy
]

let test2_msgHash = List.Tot.map u8_from_UInt8 [
  0x4buy; 0x68uy; 0x8duy; 0xf4uy; 0x0buy; 0xceuy; 0xdbuy; 0xe6uy;
  0x41uy; 0xdduy; 0xb1uy; 0x6fuy; 0xf0uy; 0xa1uy; 0x84uy; 0x2duy;
  0x9cuy; 0x67uy; 0xeauy; 0x1cuy; 0x3buy; 0xf6uy; 0x3fuy; 0x3euy;
  0x04uy; 0x71uy; 0xbauy; 0xa6uy; 0x64uy; 0x53uy; 0x1duy; 0x1auy
]

let test2_sgnt = List.Tot.map u8_from_UInt8 [
  0x24uy; 0x10uy; 0x97uy; 0xefuy; 0xbfuy; 0x8buy; 0x63uy; 0xbfuy;
  0x14uy; 0x5cuy; 0x89uy; 0x61uy; 0xdbuy; 0xdfuy; 0x10uy; 0xc3uy;
  0x10uy; 0xefuy; 0xbbuy; 0x3buy; 0x26uy; 0x76uy; 0xbbuy; 0xc0uy;
  0xf8uy; 0xb0uy; 0x85uy; 0x05uy; 0xc9uy; 0xe2uy; 0xf7uy; 0x95uy;
  0x02uy; 0x10uy; 0x06uy; 0xb7uy; 0x83uy; 0x86uy; 0x09uy; 0x33uy;
  0x9euy; 0x8buy; 0x41uy; 0x5auy; 0x7fuy; 0x9auy; 0xcbuy; 0x1buy;
  0x66uy; 0x18uy; 0x28uy; 0x13uy; 0x1auy; 0xefuy; 0x1euy; 0xcbuy;
  0xc7uy; 0x95uy; 0x5duy; 0xfbuy; 0x01uy; 0xf3uy; 0xcauy; 0x0euy
]


let test_verify () : FStar.All.ML bool =
  assert_norm (List.Tot.length test1_pk = 64);
  assert_norm (List.Tot.length test1_msg = 6);
  assert_norm (List.Tot.length test1_sgnt = 64);

  let pk_raw : lbytes 64 = of_list test1_pk in
  let msg : lbytes 6 = of_list test1_msg in
  let sgnt : lbytes 64 = of_list test1_sgnt in

  let verify : bool = ecdsa_verify_sha256 6 msg pk_raw sgnt in
  if verify
  then begin IO.print_string "Test K256 ecdsa verification: Success!\n"; true end
  else begin IO.print_string "Test K256 ecdsa verification: Failure :(\n"; false end


let test_sign_and_verify () : FStar.All.ML bool =
  assert_norm (List.Tot.length test2_sk = 32);
  assert_norm (List.Tot.length test2_pk = 64);
  assert_norm (List.Tot.length test2_nonce = 32);
  assert_norm (List.Tot.length test2_msgHash = 32);
  assert_norm (List.Tot.length test2_sgnt = 64);

  let sk : lbytes 32 = of_list test2_sk in
  let nonce : lbytes 32 = of_list test2_nonce in
  let pk_raw : lbytes 64 = of_list test2_pk in

  let msgHash : lbytes 32 = of_list test2_msgHash in
  let sgnt : lbytes 64 = of_list test2_sgnt in

  let signature = ecdsa_sign_hashed_msg msgHash sk nonce in

  let is_sgnt_valid =
    match signature with
    | Some x -> for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) sgnt x
    | None -> false in

  let verify_sgnt = ecdsa_verify_hashed_msg msgHash pk_raw sgnt in

  if verify_sgnt && is_sgnt_valid
  then begin IO.print_string "Test K256 ecdsa signature and verification: Success!\n"; true end
  else begin IO.print_string "Test K256 ecdsa signature and verification: Failure :(\n"; false end


let test_public_key_compressed () : FStar.All.ML bool =
  assert_norm (List.Tot.length test1_pk = 64);

  let pk_raw : lbytes 64 = of_list test1_pk in
  let pk_c = pk_compressed_from_raw pk_raw in
  let pk_raw_c = pk_compressed_to_raw pk_c in

  match pk_raw_c with
  | Some pk_raw_c ->
    let is_pk_c_valid = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) pk_raw_c pk_raw in
    if not is_pk_c_valid then IO.print_string "Test K256 pk_compressed (Some): Failure :(\n"
    else IO.print_string "Test K256 pk_compressed: Success!\n";
    is_pk_c_valid
  | None ->
    begin IO.print_string "Test K256 pk_compressed (None): Failure :(\n"; false end


let test_public_key_uncompressed () : FStar.All.ML bool =
  assert_norm (List.Tot.length test1_pk = 64);

  let pk_raw : lbytes 64 = of_list test1_pk in
  let pk_u = pk_uncompressed_from_raw pk_raw in
  let pk_raw_u = pk_uncompressed_to_raw pk_u in

  match pk_raw_u with
  | Some pk_raw_u ->
    let is_pk_u_valid = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) pk_raw_u pk_raw in
    if not is_pk_u_valid then IO.print_string "Test K256 pk_uncompressed (Some): Failure :(\n"
    else IO.print_string "Test K256 pk_uncompressed: Success!\n";
    is_pk_u_valid
  | None ->
    begin IO.print_string "Test K256 pk_uncompressed (None): Failure :(\n"; false end

(*
let print_bytes str len (b:lbytes len) =
  IO.print_string str;
  FStar.List.iter (fun b_i -> IO.print_uint8_hex_pad (u8_to_UInt8 b_i)) (to_list b)

(*
 Projective coordinates
 X = 0xb557707daa602223c86676d1c5bb40ec5a72b1cae4dac112fd9f9bac02f0f927
 Y = 0x3ea9b711a4fb06e03eadf27281d55bd2f37d2760dfc33085dec6f65cea720fa2
 Z = 0x86d3d793c74502a81743dd5581e1f94773a8d97c603ce3bdbe00c4009bb8800f

 Affine coordinates
 x = 0xbcace2e99da01887ab0102b696902325872844067f15e98da7bba04400b88fcb
 y = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8

 Expected beta * gx
 beta * gx = 0xbcace2e99da01887ab0102b696902325872844067f15e98da7bba04400b88fcb
 gy = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
*)
let print_glv_for_base_point () : FStar.All.ML unit =
  let lambda : qelem = 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72 in
  let r_X, r_Y, r_Z = point_mul_g lambda in
  let r_x, r_y = to_aff_point (r_X, r_Y, r_Z) in
  let r_Xb : lbytes 32 = nat_to_bytes_be #SEC 32 r_X in
  let r_Yb : lbytes 32 = nat_to_bytes_be #SEC 32 r_Y in
  let r_Zb : lbytes 32 = nat_to_bytes_be #SEC 32 r_Z in

  let r_xb : lbytes 32 = nat_to_bytes_be #SEC 32 r_x in
  let r_yb : lbytes 32 = nat_to_bytes_be #SEC 32 r_y in

  let beta : felem = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee in
  let beta_gx = beta *% g_x in
  let beta_gxb : lbytes 32 = nat_to_bytes_be #SEC 32 beta_gx in
  let gyb : lbytes 32 = nat_to_bytes_be #SEC 32 g_y in

  IO.print_string "\n Projective coordinates \n";
  print_bytes "\n X = " 32 r_Xb;
  print_bytes "\n Y = " 32 r_Yb;
  print_bytes "\n Z = " 32 r_Zb;

  IO.print_string "\n Affine coordinates \n";
  print_bytes "\n x = " 32 r_xb;
  print_bytes "\n y = " 32 r_yb;

  IO.print_string "\n Expected beta * gx \n";
  print_bytes "\n beta * gx = " 32 beta_gxb;
  print_bytes "\n gy = " 32 gyb;
  IO.print_string "\n End of print \n"
*)

let test () : FStar.All.ML bool  =
  // print_glv_for_base_point ();
  let t1 : bool = test_verify () in
  let t2 : bool = test_sign_and_verify () in
  let t3 : bool = test_public_key_compressed () in
  let t4 : bool = test_public_key_uncompressed () in

  if t1 && t2 && t3 && t4
  then begin IO.print_string "Test K256 ecdsa: Success!\n"; true end
  else begin IO.print_string "Test K256 ecdsa: Failure :(\n"; false end
