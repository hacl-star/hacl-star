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
    (Vale_X64_Decls.ins,Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode * Vale_X64_Decls.va_pbool) * int * bool) list -> unit
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
      | GCC -> Vale_X64_Decls.gcc
      | MASM -> Vale_X64_Decls.masm
    in
    let windows = platform_choice = Win in

    (* Ensure that we've actually got all the codes *)
    let l = List.map (fun (name, code_and_gen, nbr_args, return_public) ->
        let c, p = code_and_gen windows in
        match Vale_X64_Decls.get_reason p with
        | None -> (name, (fun _ -> c), nbr_args, return_public)
        | Some reason ->
          failwith ("method " ^ name ^ " cannot be safely generated. Reason: " ^ reason)) l in

    (* Run taint analysis *)
    let _ = List.iter (fun (name, code, nbr_args, return_public) ->
      if Vale_X64_Leakage.check_if_code_is_leakage_free (code windows) (Vale_X64_Leakage.mk_analysis_taints windows (Prims.parse_int (string_of_int nbr_args))) return_public then ()
      else failwith ("method " ^ name ^ " does not satisfy taint analysis on" ^ if windows then "Windows" else "Linux")
    ) l in

    (* Extract and print assembly code *)
    Vale_X64_Decls.print_header printer;
    let _ = List.fold_left (fun label_count (name, code, _, _) ->
                           Vale_X64_Decls.print_proc (proc_name name platform_choice)
                                                       (code windows)
                                                       label_count printer)
                           (Prims.parse_int "0") l in
    Vale_X64_Decls.print_footer printer
