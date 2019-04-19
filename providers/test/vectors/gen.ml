(* This minimalist script reads JSON test vectors from HACSpec, tries to make
 * sense of them, and to generate decent F* syntax to be used in EverCrypt
 * tests. No Makefile, since this is truly a one-time thing.

ocamlfind ocamlopt -package yojson gen.ml -linkpkg -o gen.exe && \
  ./gen.exe -module Test.Vectors.Poly1305 poly1305_test_vectors.json && \
  ./gen.exe -module Test.Vectors.Curve25519 curve25519_test_vectors.json && \
  ./gen.exe -module Test.Vectors.Chacha20Poly1305 aead_chacha20poly1305_test_vectors.json && \
  ./gen.exe -module Test.Vectors.Aes128Gcm aead_aes128gcm_test_vectors.json && \
  ./gen.exe -module Test.Vectors.Aes128 aes128_test_vectors.json

*)

let problematic_fstar_keywords = [ "private" ]

let avoid f =
  if List.mem f problematic_fstar_keywords then
    f ^ "_"
  else
    f

let generate_hex_field oc i f hex has_aad =
  let l = String.length hex / 2 in
  let disj, disj_recall  =
    if f = "input" && has_aad
    then Printf.sprintf " /\\ B.disjoint b aad%d" i, Printf.sprintf "   B.recall aad%d;"  i
    else "", ""
  in
  Printf.fprintf oc
    "let %s%d: (b: B.buffer UInt8.t { B.length b = %d /\\ B.recallable b%s }) =\n  \
       %s[@inline_let] let l = [ " f i l disj disj_recall;
  if String.length hex mod 2 <> 0 then
    failwith (Printf.sprintf "data in entry %d field %s end on a half-byte boundary" i f);
  for i = 0 to l - 1 do
    Printf.fprintf oc "0x%c%cuy; " hex.[2*i] hex.[2*i+1];
  done;
  Printf.fprintf oc "] in\n  \
    assert_norm (List.Tot.length l = %d);\n  \
    B.gcmalloc_of_list HyperStack.root l\n\n" l;

  Printf.fprintf oc
    "inline_for_extraction let %s%d_len: (x:UInt32.t { UInt32.v x = B.length %s%d }) =\n  \
       %dul\n\n" f i f i l

let generate_bool_field oc i f b =
  Printf.fprintf oc "inline_for_extraction let %s%d = %b\n\n" f i b

let syntax_of_json module_ json =
  let oc = open_out_bin (module_ ^ ".fst") in
  Printf.fprintf oc "module %s\n\n" module_;

  Printf.fprintf oc "module B = LowStar.Buffer\n\n";

  Printf.fprintf oc "#set-options \"--max_fuel 0 --max_ifuel 0\"\n\n";

  let vectors = match json with
    | `List vectors -> vectors
    | _ -> failwith "JSON does not start with a list"
  in
  let hex_fields = ref [] in
  let bool_fields = ref [] in

  (* if there is a field called aad, then we should add a
       disjointness postcondition to any field called input that would
       follow aad *)
  let has_aad = ref false in

  List.iteri (fun i vec ->
    let fields = match vec with
      | `Assoc fields -> fields
      | _ -> failwith "JSON list entries are not associative objects"
    in
    List.iter (fun (f, hex) ->
      let f = avoid f in
      if String.length f < 4 || String.sub f (String.length f - 4) 4 <> "_len" then
        match hex with
        | `String hex ->
            (* Just trusting the first entry to have the right fields. *)
            if i = 0 then begin
                hex_fields := f :: !hex_fields;
                if f = "aad" then has_aad := true;
              end;
            generate_hex_field oc i f hex !has_aad

        | `Bool b ->
            if i = 0 then
              bool_fields := f :: !bool_fields;
            generate_bool_field oc i f b

        | _ -> failwith "JSON list entry has a field that is not a string or a bool"
    ) fields
  ) vectors;

  let has_aad = !has_aad in
  
  Printf.fprintf oc "noeq\ntype vector = | Vector:\n";
  List.iter (fun f ->
    let disj =
      if f = "aad" && has_aad (* the list of fields got reversed, so aad will now appear after input *)
      then " /\\ B.disjoint input aad"
      else ""
    in
    let f = avoid f in
    Printf.fprintf oc "  %s: B.buffer UInt8.t { B.recallable %s%s } ->\n" f f disj;
    Printf.fprintf oc "  %s_len: UInt32.t { B.length %s = UInt32.v %s_len } ->\n" f f f
  ) !hex_fields;
  List.iter (fun f ->
    let f = avoid f in
    Printf.fprintf oc "  %s: bool ->\n" f
  ) !bool_fields;
  Printf.fprintf oc "  vector\n\n";

  let l = List.length vectors in
  Printf.fprintf oc
    "let vectors: (b: B.buffer vector { B.length b = %d /\\ B.recallable b }) =\n  \
       [@inline_let] let l = [ \n" l;
  for i = 0 to l - 1 do
    Printf.fprintf oc "    Vector ";
    List.iter (fun f ->
      let f = avoid f in
      Printf.fprintf oc "%s%d " f i;
      Printf.fprintf oc "%s%d_len " f i
    ) !hex_fields;
    List.iter (fun f ->
      let f = avoid f in
      Printf.fprintf oc "%s%d" f i
    ) !bool_fields;
    Printf.fprintf oc ";\n";
  done;
  Printf.fprintf oc "  ] in\n  \
    assert_norm (List.Tot.length l = %d);\n  \
    B.gcmalloc_of_list HyperStack.root l\n\n" l;
  Printf.fprintf oc
    "let vectors_len: (x:UInt32.t { UInt32.v x = B.length vectors }) =\n  \
       %dul\n" l

let _ =
  let help = Printf.sprintf "Usage: %s FILE.json" Sys.argv.(0) in
  let file = ref "" in
  let module_ = ref "" in
  let spec = [
    "-module", Arg.Set_string module_, "  F* module to generate"
  ] in
  let spec = Arg.align spec in
  let found = ref false in
  Arg.parse spec (fun f ->
    if !found then
      failwith "Only one file on the command-line";
    file := f;
    found := true
  ) help;
  if not !found then begin
    print_endline (Arg.usage_string spec help);
    exit 1
  end;
  if !module_ = "" then begin
    print_endline "ERROR: no module specified";
    print_endline (Arg.usage_string spec help);
    exit 1
  end;

  let json = Yojson.Safe.from_channel (open_in !file) in
  syntax_of_json !module_ json
