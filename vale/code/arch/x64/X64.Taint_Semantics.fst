module X64.Taint_Semantics

open X64.Taint_Semantics_s
open X64.Vale.Decls
open X64.Machine_s
module S = X64.Semantics_s
module L = FStar.List.Tot

let mk_taint_ins1 (i:operand->S.ins)
                  (o:va_operand)
                  (dsts:list va_operand)
                  (srcs:list va_operand
                        { extract_operands (i (t_op_to_op o)) ==
                          (L.map t_op_to_op dsts,
                           L.map t_op_to_op srcs) } ) : tainted_code
  =
  let o_basic = t_op_to_op o in
  let dsts_basic = L.map t_op_to_op dsts in
  let srcs_basic = L.map t_op_to_op srcs in
  Ins (TaintedIns (i o_basic, dsts_basic, srcs_basic) (get_taint o))

let mk_taint_ins2 (i:operand->operand->S.ins)
                  (o1 o2:va_operand)
                  (dsts:list va_operand)
                  (srcs:list va_operand
                        { extract_operands (i (t_op_to_op o1) (t_op_to_op o2)) ==
                          (L.map t_op_to_op dsts,
                           L.map t_op_to_op srcs) } ) : tainted_code
  =
  let o1_basic = t_op_to_op o1 in
  let o2_basic = t_op_to_op o2 in
  let dsts_basic = L.map t_op_to_op dsts in
  let srcs_basic = L.map t_op_to_op srcs in
  Ins (TaintedIns (i o1_basic o2_basic, dsts_basic, srcs_basic)
                  (extract_taint o1 o2))

let mk_taint_ins3 (i:operand->operand->operand->S.ins)
                  (o1 o2 o3:va_operand)
                  (dsts:list va_operand)
                  (srcs:list va_operand
                        { extract_operands (i (t_op_to_op o1)
                                              (t_op_to_op o2)
                                              (t_op_to_op o3)) ==
                          (L.map t_op_to_op dsts,
                           L.map t_op_to_op srcs) } ) : tainted_code
  =
  let o1_basic = t_op_to_op o1 in
  let o2_basic = t_op_to_op o2 in
  let o3_basic = t_op_to_op o3 in
  let dsts_basic = L.map t_op_to_op dsts in
  let srcs_basic = L.map t_op_to_op srcs in
  Ins (TaintedIns (i o1_basic o2_basic o3_basic, dsts_basic, srcs_basic)
                  (extract_taint3 o1 o2 o3))

