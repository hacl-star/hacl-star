module X64.Vale.InsLemmas

open X64.Machine_s
open X64.Instruction_s
open X64.Vale.State
open X64.Vale.Decls
module S = X64.Bytes_Semantics_s

val lemma_valid_taint64_operand (m:maddr) (t:taint) (s:va_state) : Lemma
  (requires valid_operand (TMem m t) s)
  (ensures taint_at s.memTaint (eval_maddr m s) == t)
  [SMTPat (eval_maddr m s); SMTPat (TMem m t)]

[@instr_attr]
let rec make_instr_t_args (args:list instr_operand) : Type0 =
  match normal args with
  | [] -> S.ins
  | (IOpEx i)::args -> arrow (instr_operand_t i) (make_instr_t_args args)
  | (IOpIm _)::args -> make_instr_t_args args

[@instr_attr]
let rec make_instr_t (outs:list instr_out) (args:list instr_operand) : Type0 =
  match normal outs with
  | [] -> make_instr_t_args args
  | (_, IOpEx i)::outs -> arrow (instr_operand_t i) (make_instr_t outs args)
  | (_, IOpIm _)::outs -> make_instr_t outs args

[@instr_attr]
let rec make_instr_args
    (args:list instr_operand) (k:arrow (instr_operands_t_args args) S.ins)
  : make_instr_t_args args =
  match args with
  | [] -> k ()
  | (IOpEx i)::args -> fun (o:instr_operand_t i) ->
      let k = coerce #(arrow (instr_operand_t i & instr_operands_t_args args) S.ins) k in // REVIEW: workaround for F* -> OCaml bug
      let k (oprs:instr_operands_t_args args) : S.ins = k (o, oprs) in
      make_instr_args args k
  | (IOpIm i)::args -> coerce (make_instr_args args (coerce #(arrow (instr_operands_t_args args) S.ins) k))

[@instr_attr]
let rec make_instr_outs
    (outs:list instr_out) (args:list instr_operand) (k:arrow (instr_operands_t outs args) S.ins)
  : make_instr_t outs args =
  match outs with
  | [] -> make_instr_args args k
  | (b, IOpEx i)::outs -> fun (o:instr_operand_t i) ->
      let k = coerce #(arrow (instr_operand_t i & instr_operands_t outs args) S.ins) k in // REVIEW: workaround for F* -> OCaml bug
      let k (oprs:instr_operands_t outs args) = k (o, oprs) in
      make_instr_outs outs args k
  | (_, IOpIm i)::outs -> coerce (make_instr_outs outs args (coerce #(arrow (instr_operands_t outs args) S.ins) k))

[@instr_attr]
let make_instr
    (#outs:list instr_out) (#args:list instr_operand) (#havoc_flags:flag_havoc)
    (i:instr_t outs args havoc_flags)
  : make_instr_t outs args =
  make_instr_outs outs args (fun oprs -> S.Instr outs args havoc_flags i oprs)

