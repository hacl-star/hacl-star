module Spec.Dilithium.Debug

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators

open Spec.Dilithium.Params
open Spec.Dilithium.Poly

open FStar.List.Tot
open FStar.Char
open FStar.String
module VanillaU32 = FStar.UInt32


let tab = "    "
let tab3 = tab ^ tab ^ tab
let tab4 = tab3 ^ tab
let ntabs n = repeat n (fun s -> tab ^ s) ""

let format_args argnames args =
  match argnames with
  | [] -> ""
  | h::t_names -> tab ^ tab ^ tab ^ h ^ " = " ^
      (match args with
      | [] -> "[BAD: more argnames than args]\n"
      | h::t_args -> h ^ "\n")


let to_file () = IO.debug_print_string "echo to file:\n"

val string_of_seq': #t:inttype -> #l:secrecy_level -> n:size_nat -> s: lseq (int_t t l) n -> i:nat{i <= n}
  -> Tot string (decreases (n-i))

let rec string_of_seq' #t #l n s i =
  if i = n then "" else
  (string_of_int (v s.[i])) ^ " " ^ (string_of_seq' #t #l n s (i+1))

let string_of_seq #t #l n s = string_of_seq' #t #l n s 0

(* This checks correctly, but extraction to ocaml fails. *)

// let hex_digit (x:nat{x < 16}) =
//   string_of_char
//     (if x < 10
//       then char_of_int (x + 48) // ord('0') = 48
//       else char_of_int (x - 10 + 97)) // ord('a') = 97

let hex_digits_inorder = "0123456789ABCDEF"

let hex_digit (x:nat{x < 16}) =
  assert_norm (FStar.String.length hex_digits_inorder = 16);
  index "0123456789ABCDEF" x


let strbytes (n:size_nat) (b:lbytes n) =
  "<binary>" ^ string_of_list
    (repeati n (fun i s -> hex_digit (v b.[n - i - 1] / 16) :: hex_digit (v b.[n - i - 1] % 16) :: s) [])
  ^ "</binary>\n"

let strpoly (p:poly) = "<poly>" ^ string_of_seq #U32 #SEC param_n p ^ "</poly>\n"

let strpolyveck (vec:polyveck) tabs =
  let s = repeati param_k (fun i s -> s ^ tabs ^ tab ^ strpoly vec.[i]) "" in
  "<polyveck>\n" ^ s ^ tabs ^ "</polyveck>\n"

let strpolyvecl (vec:polyvecl) tabs =
  let s = repeati param_l (fun i s -> s ^ tabs ^ tab ^ strpoly vec.[i]) "" in
  "<polyvecl>\n" ^ s ^ tabs ^ "</polyvecl>\n"

let strmat (mat:lseq polyvecl param_k) tabs =
  let s = repeati param_k (fun i s -> s ^ tabs ^ tab ^ (strpolyvecl mat.[i] (tab ^ tabs))) "" in
  "<matrix>\n" ^ s ^ tabs ^ "</matrix>\n"


let debug_print = IO.debug_print_string

let print_polyvecl vec = debug_print (strpolyvecl vec tab3)
let print_polyveck vec = debug_print (strpolyveck vec tab3)
let print_poly vec = debug_print (strpoly vec)
let print_hex n b = debug_print (strbytes n b)
let print_mat mat = debug_print (strmat mat tab3)

