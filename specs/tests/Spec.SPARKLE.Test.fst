module Spec.SPARKLE.Test
#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0"

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.SPARKLE


let dflag: bool = true

inline_for_extraction
let vsize_plaintext1: size_nat = 3

inline_for_extraction
let plaintext1_list: l:List.Tot.llist uint8 vsize_plaintext1 =
  [@inline_let]
  let l = List.Tot.map u8 [0x4c; 0x61; 0x64] in
  assert_norm(List.Tot.length l == vsize_plaintext1);
  l

let plaintext1: lbytes vsize_plaintext1  = createL plaintext1_list

let expected1: lbytes 32 = create 32 (u8 0)


let test () =

  IO.print_string "\n\nTEST 1\n\n";
  let computed1 = create 32 (u8 0) in
  let flag1 = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) expected1 computed1 in
  Lib.PrintSequence.print_label_lbytes dflag "1. Result" (length computed1) computed1;
  Lib.PrintSequence.print_label_lbytes dflag "1. Expected" (length expected1) expected1;
  if flag1 then IO.print_string "\nSuccess !\n"
  else IO.print_string "\nFailure !\n"
