module Lib.StringSequence

open Lib.IntTypes
open Lib.Sequence

#push-options "--z3rlimit 50"

private
let uint32_pow21 = u:uint32{v u < pow2 21}

private
let uint8_to_uint32_pow21 (u : uint8) : uint32_pow21 = to_u32 u

private
let uint32_pow21_to_char_code (u : uint32_pow21) : Char.char_code =
  Lib.RawIntTypes.u32_to_UInt32 u

private
val list_u8_to_list_char_code: l:list uint8
  -> Tot (l':list Char.char_code{List.length l' = List.length l})
let list_u8_to_list_char_code l =
  let lu32: list uint32_pow21 = List.Tot.map uint8_to_uint32_pow21 l in
  let plu32: l:list Char.char_code = List.Tot.map uint32_pow21_to_char_code lu32 in
  plu32

#pop-options

val from_string: s:string -> Tot (b:seq uint8{length b = FStar.String.strlen s})
let from_string s =
  let lc = FStar.String.list_of_string s in
  let lu32 = List.Tot.map FStar.Char.u32_of_char lc in
  let lu8 = List.Tot.map to_u8 lu32 in
  FStar.Seq.seq_of_list lu8

val to_string: seq uint8 -> Tot string
let to_string b =
  assert_norm(forall i. v (Seq.index b i) < pow2 21);
  let lu8: list uint8 = to_list b in
  let lu32 = list_u8_to_list_char_code lu8 in
  let lc: list String.char = List.Tot.map FStar.Char.char_of_u32 lu32 in
  FStar.String.string_of_list lc
