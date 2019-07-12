module Lib.PrintSequence

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators



let print_nat8_hex x =
  IO.print_uint8 (u8_to_UInt8 (u8 x))

let print_nat8_hex_pad x =
  IO.print_uint8_hex_pad (u8_to_UInt8 (u8 x))

let print_nat8_dec x =
  IO.print_uint8_dec (u8_to_UInt8 (u8 x))

let print_nat8_dec_pad x =
  IO.print_uint8_dec_pad (u8_to_UInt8 (u8 x))


let print_nat32_hex x =
  IO.print_uint32 (u32_to_UInt32 (u32 x))

let print_nat32_hex_pad x =
  IO.print_uint32_hex_pad (u32_to_UInt32 (u32 x))

let print_nat32_dec x =
  IO.print_uint32_dec (u32_to_UInt32 (u32 x))

let print_nat32_dec_pad x =
  IO.print_uint32_dec_pad (u32_to_UInt32 (u32 x))


let print_nat64_hex x =
  IO.print_uint64 (u64_to_UInt64 (u64 x))

let print_nat64_hex_pad x =
  IO.print_uint64_hex_pad (u64_to_UInt64 (u64 x))

let print_nat64_dec x =
  IO.print_uint64_dec (u64_to_UInt64 (u64 x))

let print_nat64_dec_pad x =
  IO.print_uint64_dec_pad (u64_to_UInt64 (u64 x))


let print_uint8_hex x =
  IO.print_uint8 (u8_to_UInt8 x)

let print_uint8_hex_pad x =
  IO.print_uint8_hex_pad (u8_to_UInt8 x)

let print_uint8_dec x =
  IO.print_uint8_dec (u8_to_UInt8 x)

let print_uint8_dec_pad x =
  IO.print_uint8_dec_pad (u8_to_UInt8 x)


let print_uint32_hex x =
  IO.print_uint32 (u32_to_UInt32 x)

let print_uint32_hex_pad x =
  IO.print_uint32_hex_pad (u32_to_UInt32 x)

let print_uint32_dec x =
  IO.print_uint32_dec (u32_to_UInt32 x)

let print_uint32_dec_pad x =
  IO.print_uint32_dec_pad (u32_to_UInt32 x)


let print_uint64_hex x =
  IO.print_uint64 (u64_to_UInt64 x)

let print_uint64_hex_pad x =
  IO.print_uint64_hex_pad (u64_to_UInt64 x)

let print_uint64_dec x =
  IO.print_uint64_dec (u64_to_UInt64 x)

let print_uint64_dec_pad x =
  IO.print_uint64_dec_pad (u64_to_UInt64 x)


let print_label_nat64 s x =
  IO.print_string s;
  IO.print_string ": ";
  print_nat64_dec x;
  IO.print_string "\n"

let print_label_uint8 s x =
  IO.print_string s;
  IO.print_string ": ";
  print_uint8_hex_pad x;
  IO.print_string "\n"

let print_label_uint32 s x =
  IO.print_string s;
  IO.print_string ": ";
  print_uint32_hex_pad x;
  IO.print_string "\n"

let print_label_uint64 s x =
  IO.print_string s;
  IO.print_string ": ";
  print_uint64_hex_pad x;
  IO.print_string "\n"


let print_list_nat64 l =
  repeat_range_all_ml 0 (List.Tot.length l) (fun i _ ->
    print_nat64_dec (List.Tot.index l i);
    IO.print_string " "
) ()



let print_lbytes #len b =
  let q = 32 in
  let n = len / q in
  let r = len % q in
  if n = 0 then (
    List.iter (fun a -> print_uint8_hex_pad a) (to_list b))
  else (
  repeat_range_all_ml 0 n (fun i _ ->
    let sb = sub #uint8 #len b (i * q) q in
    List.iter (fun a -> print_uint8_hex_pad a) (to_list sb);
    (if i < n - 1 then IO.print_string "\n" else ())) ();
  (if r <> 0 then IO.print_newline ());
  let sb = sub #uint8 #len b (n * q) r in
  List.iter (fun a -> print_uint8_hex_pad a) (to_list sb))

let print_label_lbytes #len label b =
  IO.print_string label;
  IO.print_string ": \n";
  print_lbytes #len b;
  IO.print_newline ()

let print_compare len expected result =
  IO.print_string "\nResult:   ";
  List.iter (fun a -> print_uint8_hex_pad a) (to_list result);
  IO.print_string "\nExpected: ";
  List.iter (fun a -> print_uint8_hex_pad a) (to_list expected);
  for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) expected result
