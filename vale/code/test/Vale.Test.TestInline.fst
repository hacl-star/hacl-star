module Vale.Test.TestInline
open FStar.Mul
open FStar.IO
open Vale.Arch.HeapTypes_s
open Vale.X64.Machine_s
open Vale.X64.Instructions_s
open Vale.X64.Bytes_Code_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.InsLemmas
open Vale.Interop.Base
open Vale.Interop.X64
open Vale.X64.Print_Inline_s

let print_function
    (name:string)
    (ret_val:option string)
    (args:list (string & td & reg_64))
    (regs_mod:reg_64 -> bool)
    (c:code)
  : FStar.All.ML unit
  =
  let len = List.length args in
  let arg_names n = match List.Tot.nth args n with None -> "" | Some (x, _, _) -> x in
  let arg_types = List.Tot.map (fun (_, t, _) -> t) args in
  let arg_regs (n:reg_nat len) : reg_64 =
    match List.Tot.nth args n with None -> 0 | Some (_, _, r) -> r
    in
  let _ = print_inline name 0 ret_val len arg_types arg_names c arg_regs regs_mod [] in
  ()

let test_inline_mov_input () : FStar.All.ML unit =
  let args = [
    ("first_arg", TD_Base TUInt64, rR15);
    ] in
  let regs_mod r = (r = rRax || r = rRdx) in
  let c = Block [
    Ins (make_instr ins_Mov64 (OReg rRax) (OReg rR15));
    ] in
  print_function "test_inline_mov_input" (Some "result") args regs_mod c

let test_inline_mov_add_input () : FStar.All.ML unit =
  let args = [
    ("first_arg", TD_Base TUInt64, rR15);
    ] in
  let regs_mod r = (r = rRax || r = rRdx) in
  let c = Block [
    Ins (make_instr ins_Mov64 (OReg rRax) (OReg rR15));
    Ins (make_instr ins_Add64 (OReg rRax) (OConst 1));
    ] in
  print_function "test_inline_mov_add_input" (Some "result") args regs_mod c

let test_inline_mul_inputs () : FStar.All.ML unit =
  let args = [
    ("first_arg", TD_Base TUInt64, rRbx);
    ("second_arg", TD_Base TUInt64, rR15);
    ] in
  let regs_mod r = (r = rRax || r = rRdx) in
  let c = Block [
    Ins (make_instr ins_Mov64 (OReg rRax) (OReg rRbx));
    Ins (make_instr ins_IMul64 (OReg rRax) (OReg rR15));
    ] in
  print_function "test_inline_mul_inputs" (Some "result") args regs_mod c

let test_inline_mov_mul_rax_100 () : FStar.All.ML unit =
  let args = [
    ("first_arg", TD_Base TUInt64, rRbx);
    ] in
  let regs_mod r = (r = rRax || r = rRcx || r = rRdx) in
  let c = Block [
    Ins (make_instr ins_Mov64 (OReg rRax) (OReg rRbx));
    Ins (make_instr ins_Mov64 (OReg rRcx) (OConst 100));
    Ins (make_instr ins_IMul64 (OReg rRax) (OReg rRcx));
    ] in
  print_function "test_inline_mov_mul_rax_100" (Some "result") args regs_mod c

let test_inline_mov_mul_inputs () : FStar.All.ML unit =
  let args = [
    ("first_arg", TD_Base TUInt64, rRbx);
    ("second_arg", TD_Base TUInt64, rR15);
    ] in
  let regs_mod r = (r = rRax || r = rRcx || r = rRdx) in
  let c = Block [
    Ins (make_instr ins_Mov64 (OReg rRax) (OReg rRbx));
    Ins (make_instr ins_Mov64 (OReg rRcx) (OReg rR15));
    Ins (make_instr ins_IMul64 (OReg rRax) (OReg rRcx));
    ] in
  print_function "test_inline_mov_mul_inputs" (Some "result") args regs_mod c

// This test generates the correct inline assembly code, but only works with gcc >= 9
// On prior versions, gcc ignores the register asm("rax") annotation, and does not correctly
// allocate the output "result" into register rax
(*
let test_inline_mov_add_input_dummy_mul () : FStar.All.ML unit =
  let args = [
    ("first_arg", TD_Base TUInt64, rR15);
    ] in
  let regs_mod r = (r = rRax || r = rRdx) in
  let c = Block [
    Ins (make_instr ins_Mov64 (OReg rRax) (OReg rR15));
    Ins (make_instr ins_Mul64 (OReg rR15));
    Ins (make_instr ins_Mov64 (OReg rRax) (OReg rR15));
    Ins (make_instr ins_Add64 (OReg rRax) (OConst 1));
    ] in
  print_function "test_inline_mov_add_input_dummy_mul" (Some "result") args regs_mod c
*)

let test_inline_comment_add () : FStar.All.ML unit =
  let args = [
    ("first_arg", TD_Base TUInt64, rR15);
  ] in
  let regs_mod r = (r = rR15 || r = rRax) in
  let s = "This is a comment" in
  let c = Block [
    Ins (make_instr_annotate (ins_Comment s) (AnnotateComment s));
    Ins (make_instr ins_Add64 (OReg rR15) (OReg rR15));
    Ins (make_instr ins_Mov64 (OReg rRax) (OReg rR15));
  ] in
  print_function "test_inline_comment_add" (Some "result") args regs_mod c

let test_inline_same_line () : FStar.All.ML unit =
  let args = [
    ("first_arg", TD_Base TUInt64, rR15);
  ] in
  let regs_mod r = (r = rR15 || r = rRax) in
  let c = Block [
    Ins (make_instr_annotate (ins_Space 0) (AnnotateSpace 0));
    Ins (make_instr ins_Add64 (OReg rR15) (OReg rR15));
    Ins (make_instr ins_Mov64 (OReg rRax) (OReg rR15));
  ] in
  print_function "test_inline_same_line" (Some "result") args regs_mod c

let test_inline_same_line_newline () : FStar.All.ML unit =
  let args = [
    ("first_arg", TD_Base TUInt64, rR15);
  ] in
  let regs_mod r = (r = rR15 || r = rRax) in
  let c = Block [
    Ins (make_instr_annotate (ins_Space 4) (AnnotateSpace 4));
    Ins (make_instr ins_Mov64 (OReg rRax) (OReg rR15));
    Ins (make_instr ins_Add64 (OReg rR15) (OReg rR15));
    Ins (make_instr_annotate ins_Newline (AnnotateNewline ()));
    Ins (make_instr_annotate (ins_Space 4) (AnnotateSpace 4));
    Ins (make_instr ins_Add64 (OReg rR15) (OReg rRax));
    Ins (make_instr ins_Mov64 (OReg rRax) (OReg rR15));
  ] in
  print_function "test_inline_same_line_newline" (Some "result") args regs_mod c


let test_inline () : FStar.All.ML unit =
  test_inline_mov_input ();
  test_inline_mov_add_input ();
  test_inline_mul_inputs ();
  test_inline_mov_mul_rax_100 ();
  test_inline_mov_mul_inputs ();
// This test leads (rightfully) to a failure in the printer due to a gcc bug
//  test_inline_mov_add_input_dummy_mul ();
  test_inline_comment_add ();
  test_inline_same_line ();
  test_inline_same_line_newline ();
  ()
