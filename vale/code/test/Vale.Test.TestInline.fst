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

let test_inline () : FStar.All.ML unit =
  let len = 1 in
  let args = [
    ("first_arg", TD_Base TUInt64, 0);
    ] in
  let regs_mod r = r = 2 in
  let c = Block [
    Ins (make_instr ins_Mov64 (OReg 2) (OConst 100));
    Ins (make_instr ins_Mul64 (OReg 2));
    ] in
  print_function "test_inline1" (Some "result") args regs_mod c

