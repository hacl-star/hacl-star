module Spec.Poly1305.Test

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Spec.Poly1305

(* ********************* *)
(* RFC 7539 Test Vectors *)
(* ********************* *)

let msg = List.Tot.map u8_from_UInt8 [
  0x43uy; 0x72uy; 0x79uy; 0x70uy; 0x74uy; 0x6fuy; 0x67uy; 0x72uy;
  0x61uy; 0x70uy; 0x68uy; 0x69uy; 0x63uy; 0x20uy; 0x46uy; 0x6fuy;
  0x72uy; 0x75uy; 0x6duy; 0x20uy; 0x52uy; 0x65uy; 0x73uy; 0x65uy;
  0x61uy; 0x72uy; 0x63uy; 0x68uy; 0x20uy; 0x47uy; 0x72uy; 0x6fuy;
  0x75uy; 0x70uy]

let k = List.Tot.map u8_from_UInt8 [
  0x85uy; 0xd6uy; 0xbeuy; 0x78uy; 0x57uy; 0x55uy; 0x6duy; 0x33uy;
  0x7fuy; 0x44uy; 0x52uy; 0xfeuy; 0x42uy; 0xd5uy; 0x06uy; 0xa8uy;
  0x01uy; 0x03uy; 0x80uy; 0x8auy; 0xfbuy; 0x0duy; 0xb2uy; 0xfduy;
  0x4auy; 0xbfuy; 0xf6uy; 0xafuy; 0x41uy; 0x49uy; 0xf5uy; 0x1buy]

let expected = List.Tot.map u8_from_UInt8 [
  0xa8uy; 0x06uy; 0x1duy; 0xc1uy; 0x30uy; 0x51uy; 0x36uy; 0xc6uy;
  0xc2uy; 0x2buy; 0x8buy; 0xafuy; 0x0cuy; 0x01uy; 0x27uy; 0xa9uy]

let test () =
  assert_norm(List.Tot.length msg      = 34);
  assert_norm(List.Tot.length k        = 32);
  assert_norm(List.Tot.length expected = 16);
  let msg      : lseq uint8 34  = of_list #uint8 msg in
  let k        : lseq uint8 size_key  = of_list #uint8 k   in
  let expected : lseq uint8 size_block = of_list #uint8 expected in
  let mac      : lseq uint8 size_block = poly1305_mac msg k in
  let result : bool = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) mac expected in
  IO.print_string   "Expected MAC:";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list expected);
  IO.print_string "\nComputed MAC:";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list mac);
  if result then begin  IO.print_string "\nSuccess!\n"; true end
  else begin IO.print_string "\nFailure :(\n"; false end
