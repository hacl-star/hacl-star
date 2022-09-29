let parse_cmdline :
  (string * (unit -> (Vale_PPC64LE_Decls.ins,Vale_PPC64LE_Decls.ocmp) Vale_PPC64LE_Machine_s.precode) * int * bool) list -> unit
  =
  fun l  ->
  let printer = Vale_PPC64LE_Decls.gcc in
  (* Extract and print assembly code *)
  Vale_PPC64LE_Decls.print_header printer;
  let _ = List.fold_left (fun label_count (name, code, _, _) ->
                          Vale_PPC64LE_Decls.print_proc name
                                                      (code ())
                                                      label_count printer)
                          (Prims.parse_int "0") l in
  Vale_PPC64LE_Decls.print_footer printer

let _ =
  parse_cmdline [
    ("sha256_update", Vale_SHA_PPC64LE.va_code_Sha_update_bytes_main, 4, false);
  ]
