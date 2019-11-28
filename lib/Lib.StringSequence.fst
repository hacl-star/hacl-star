module Lib.StringSequence

open Lib.IntTypes
open Lib.Sequence


#push-options "--z3rlimit 50"

private
val list_u8_to_list_char_code: list uint8 -> Tot (list Char.char_code)
let list_u8_to_list_char_code l =
  assert(forall i. v (List.Tot.Base.index l i) < pow2 21);
  let lu32: list uint32 = List.Tot.map (to_u32) l in
  let plu32: l:list FStar.UInt32.t = List.Tot.map Lib.RawIntTypes.u32_to_UInt32 lu32 in
  admit();
  assert(forall i. v (List.Tot.Base.index plu32 i) < pow2 21);
  let plu32': l:list Char.char_code = plu32 in
  plu32'

#pop-options


val from_string: string -> Tot (seq uint8)
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
