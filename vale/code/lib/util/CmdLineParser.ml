type platform = Win | Linux | MacOS
type asm = GCC | MASM
(*
let print_header = function
  | GCC -> print_endline "GCC HEADER HERE"
  | MASM -> print_endline "MASM HEADER HERE"

let is_it_win b =
  if b
  then print_endline "Yep, we have a win here"
  else print_endline "Nope, not a win"
*)

let proc_name : string -> platform -> string =
  fun name plat ->
    let prefix =
      match plat with
        | MacOS -> "_"
        | _ -> ""
    in
    prefix ^ name

let parse_cmdline :
  (string * (Prims.bool ->
    (X64_Vale_Decls.ins,X64_Vale_Decls.ocmp) X64_Machine_s.precode)) list -> unit
  =
  fun l  ->
  let argc = Array.length Sys.argv in
  if argc < 3
  then
    raise (Invalid_argument
             "Expected usage: ./[executable].exe [GCC|MASM] [Win|Linux|MacOS]\n")
  else
    let asm_choice_name = Sys.argv.(1) in
    let platform_choice_name = Sys.argv.(2) in
    let platform_choice =
      match platform_choice_name with
      | "Win" -> Win
      | "Linux" -> Linux
      | "MacOS" -> MacOS
      | _ ->
        raise (Invalid_argument
                 "Please choose a correct assembler option: Win or Linux or MacOS\n")
    in
    let asm_choice =
      match asm_choice_name with
      | "GCC" -> GCC
      | "MASM" -> MASM
      | _ ->
        raise (Invalid_argument
                 "Please choose a correct assembler option: GCC or MASM\n")
    in
    let printer =
      match asm_choice with
      | GCC -> X64_Vale_Decls.gcc
      | MASM -> X64_Vale_Decls.masm
    in
    let windows = platform_choice = Win in
    X64_Vale_Decls.print_header printer;
    let _ = List.fold_left (fun label_count (name, code) ->
                           X64_Vale_Decls.print_proc (proc_name name platform_choice)
                                                       (code windows)
                                                       label_count printer)
                           (Prims.parse_int "0") l in
    X64_Vale_Decls.print_footer printer
