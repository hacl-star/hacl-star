module Lib.PrintSequence

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators


let print_lbytes #len b =
  let n = len / 32 in
  let r = len % 32 in
  if n = 0 then (
    List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a)) (to_list b))
  else (
  repeat_range_all_ml 0 n (fun i _ ->
    let sb = sub #uint8 #len b (i * 32) 32 in
    List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a)) (to_list sb);
    IO.print_string "\n") ();
  let sb = sub #uint8 #len b (n * 32) r in
  List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a)) (to_list sb))


let print_hex_uint8 x =
  IO.print_uint8 (u8_to_UInt8 x)

let print_hex_uint32 x =
  IO.print_uint32 (u32_to_UInt32 x)

let print_hex_uint64 x =
  IO.print_uint64 (u64_to_UInt64 x)


let print_dec_uint8 x =
  IO.print_uint8_dec (u8_to_UInt8 x)

let print_dec_uint32 x =
  IO.print_uint32_dec (u32_to_UInt32 x)

let print_dec_uint64 x =
  IO.print_uint64_dec (u64_to_UInt64 x)


let print_hex_nat8 x =
  IO.print_uint8 (u8_to_UInt8 (u8 x))

let print_hex_nat32 x =
  IO.print_uint32 (u32_to_UInt32 (u32 x))

let print_hex_nat64 x =
  IO.print_uint64 (u64_to_UInt64 (u64 x))


let print_dec_nat8 x =
  IO.print_uint8_dec (u8_to_UInt8 (u8 x))

let print_dec_nat32 x =
  IO.print_uint32_dec (u32_to_UInt32 (u32 x))

let print_dec_nat64 x =
  IO.print_uint64_dec (u64_to_UInt64 (u64 x))


let print_label_hex_uint8 s x =
  IO.print_string s;
  IO.print_string ": ";
  print_hex_uint8 x;
  IO.print_string "\n"

let print_label_hex_uint32 s x =
  IO.print_string s;
  IO.print_string ": ";
  print_hex_uint32 x;
  IO.print_string "\n"

let print_label_hex_uint64 s x =
  IO.print_string s;
  IO.print_string ": ";
  print_hex_uint64 x;
  IO.print_string "\n"

let print_label_dec_nat8 s x =
  IO.print_string s;
  IO.print_string ": ";
  print_dec_nat8 x;
  IO.print_string "\n"

let print_label_dec_nat32 s x =
  IO.print_string s;
  IO.print_string ": ";
  print_dec_nat32 x;
  IO.print_string "\n"

let print_label_dec_nat64 s x =
  IO.print_string s;
  IO.print_string ": ";
  print_dec_nat64 x;
  IO.print_string "\n"

let print_compare len expected result =
  IO.print_string "\n\nResult:   ";
  List.iter (fun a -> print_hex_uint8 a) (to_list result);
  IO.print_string "\nExpected: ";
  List.iter (fun a -> print_hex_uint8 a) (to_list expected);
  for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) expected result
