(**

   This is a convenience module for making it easier to debug
   transformations by overriding some printers. You probably do not want
   to use this module unless you know exactly what you're doing.

*)
module Vale.Transformers.DebugPrint

open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.Def.PossiblyMonad
open Vale.X64.Decls
open Vale.X64.Print_s
open FStar.String

let rec get_non_space (x:list char) : string =
  match x with
  | [] -> "."
  | x :: xs ->
    if x = ' ' then get_non_space xs else string_of_list [x]

let print_ins i _ =
  get_non_space (list_of_string (print_ins i gcc))

let rec aux_print_code (c:code) : string =
  match c with
  | Ins i -> print_ins i gcc
  | Block l -> "(" ^ aux_print_codes l ^ ")"
  | IfElse _ t f -> "I" ^ aux_print_code t ^ aux_print_code f
  | While _ b -> "W" ^ aux_print_code b

and aux_print_codes (c:codes) : string =
  match c with
  | [] -> ""
  | x :: xs -> aux_print_code x ^ aux_print_codes xs

let print_code c _ _ = ("<" ^ aux_print_code c ^ ">\n"), 0
