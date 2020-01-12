module Vale.X64.InsLemmas

open FStar.Mul
open Vale.Arch.HeapImpl
open Vale.X64.Machine_s
open Vale.X64.Instruction_s
open Vale.X64.State
open Vale.X64.StateLemmas
open Vale.X64.Decls
open Vale.X64.Memory
module BC = Vale.X64.Bytes_Code_s
module S = Vale.X64.Machine_Semantics_s
let has_taint128 (o:operand128) (t:taint) : bool =
  match o with
  | OMem (_, t') | OStack (_, t') -> t = t'
  | _ -> true

val lemma_valid_src_operand64_and_taint (o:operand64) (s:vale_state) : Lemma
  (requires valid_operand o s)
  (ensures S.valid_src_operand64_and_taint o (state_to_S s))
  [SMTPat (S.valid_src_operand64_and_taint o (state_to_S s))]

val lemma_valid_src_operand128_and_taint (o:operand128) (s:vale_state) : Lemma
  (requires valid_operand128 o s)
  (ensures S.valid_src_operand128_and_taint o (state_to_S s))
  [SMTPat (S.valid_src_operand128_and_taint o (state_to_S s))]

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
  make_instr_outs outs args (fun oprs -> BC.Instr (InstrTypeRecord i) oprs S.AnnotateNone)

[@instr_attr]
let make_instr_annotate
    (#outs:list instr_out) (#args:list instr_operand) (#havoc_flags:flag_havoc)
    (i:instr_t outs args havoc_flags) (ann:S.instr_annotation (InstrTypeRecord i))
  : make_instr_t outs args =
  make_instr_outs outs args (fun oprs -> BC.Instr (InstrTypeRecord i) oprs ann)

