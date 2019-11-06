module Lib.Meta

open Lib.IntTypes

/// Helpers used in tests and tactics (see e.g. Test.LowStarize)

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

noextract
val is_hex_digit: Char.char -> bool
let is_hex_digit = function
  | '0'
  | '1'
  | '2'
  | '3'
  | '4'
  | '5'
  | '6'
  | '7'
  | '8'
  | '9'
  | 'a' | 'A'
  | 'b' | 'B'
  | 'c' | 'C'
  | 'd' | 'D'
  | 'e' | 'E'
  | 'f' | 'F' -> true
  | _ -> false

noextract
type hex_digit = c:Char.char{is_hex_digit c}

noextract
val int_of_hex: c:hex_digit -> int
let int_of_hex = function
  | '0' -> 0
  | '1' -> 1
  | '2' -> 2
  | '3' -> 3
  | '4' -> 4
  | '5' -> 5
  | '6' -> 6
  | '7' -> 7
  | '8' -> 8
  | '9' -> 9
  | 'a' | 'A' -> 10
  | 'b' | 'B' -> 11
  | 'c' | 'C' -> 12
  | 'd' | 'D' -> 13
  | 'e' | 'E' -> 14
  | 'f' | 'F' -> 15

noextract
val byte_of_hex: a:hex_digit -> b:hex_digit -> int
let byte_of_hex a b =
  FStar.Mul.(int_of_hex a * 16 + int_of_hex b)

noextract unfold
type hex_string =
  s:string{normalize (String.strlen s % 2 = 0) /\
           normalize (List.Tot.for_all is_hex_digit (String.list_of_string s))}

#push-options "--fuel 2"

let rec as_uint8s acc
  (cs:list Char.char{normalize (List.length cs % 2 = 0) /\
                     normalize (List.Tot.for_all is_hex_digit cs)}):
  Tot (l:list uint8{List.length l = List.length acc + List.length cs / 2}) (decreases (List.length cs))
=
  match cs with
  | c1 :: c2 :: cs' -> as_uint8s (u8 (byte_of_hex c1 c2) :: acc) cs'
  | _ -> List.rev_length acc; List.rev acc

let from_hex (s:hex_string) : Seq.lseq uint8 (String.strlen s / 2) =
  Seq.seq_of_list (as_uint8s [] (String.list_of_string s))
