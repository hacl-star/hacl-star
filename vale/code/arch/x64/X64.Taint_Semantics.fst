module X64.Taint_Semantics

open X64.Taint_Semantics_s
open X64.Vale.Decls
open X64.Machine_s
open X64.Instruction_s
module S = X64.Bytes_Semantics_s
module L = FStar.List.Tot


let mk_ins (i:S.ins) (t:taint) : Pure tainted_code
  (requires True)
  (ensures fun c ->
    c == Ins (TaintedIns i t) /\
    i == normal i /\
    S.eval_ins i == normal (S.eval_ins i)
  )
  =
  Ins (TaintedIns i t)

let mk_taint_ins1 (i:operand->S.ins)
                  (o:va_operand)
                  : tainted_code
  =
  let o_basic = t_op_to_op o in
  Ins (TaintedIns (i o_basic) (get_taint o))

let mk_taint_ins2 (i:operand->operand->S.ins)
                  (o1 o2:va_operand)
                  : tainted_code
  =
  let o1_basic = t_op_to_op o1 in
  let o2_basic = t_op_to_op o2 in
  Ins (TaintedIns (i o1_basic o2_basic)
                  (extract_taint o1 o2))

let mk_taint_ins3 (i:operand->operand->operand->S.ins)
                  (o1 o2 o3:va_operand)
                  : tainted_code
  =
  let o1_basic = t_op_to_op o1 in
  let o2_basic = t_op_to_op o2 in
  let o3_basic = t_op_to_op o3 in
  Ins (TaintedIns (i o1_basic o2_basic o3_basic)
                  (extract_taint3 o1 o2 o3))

