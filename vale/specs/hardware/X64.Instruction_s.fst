module X64.Instruction_s
// only trusted specification files should friend this module

[@instr_attr]
let rec instr_print_t_args (args:list instr_operand) : Type0 =
  match args with
  | [] -> instr_print
  | (IOpEx i)::args -> arrow (instr_operand_t i) (instr_print_t_args args)
  | (IOpIm _)::args -> instr_print_t_args args

[@instr_attr]
let rec instr_print_t (outs:list instr_out) (args:list instr_operand) : Type0 =
  match outs with
  | [] -> instr_print_t_args args
  | (_, IOpEx i)::outs -> arrow (instr_operand_t i) (instr_print_t outs args)
  | (_, IOpIm _)::outs -> instr_print_t outs args

noeq type instr_t (outs:list instr_out) (args:list instr_operand) (havoc_flags:flag_havoc) = {
  i_eval:instr_eval_t outs args;
  i_printer:instr_print_t outs args;
  // havoc_flags isn't used here, but we still need it in the type to track the semantics of each instr_t
}

let instr_eval #_ #_ #_ ins = ins.i_eval

let rec instr_printer_args
    (args:list instr_operand)
    (f:instr_print_t_args args) (oprs:instr_operands_t_args args)
  : instr_print =
  match args with
  | [] -> f
  | i::args ->
    (
      match i with
      | IOpEx i ->
// REVIEW: triggers F* -> OCaml bug:          let f:arrow (instr_operand_t i) (instr_print_t_args args) = coerce f in
          let (o, oprs) = coerce oprs in instr_printer_args args
            (coerce #(arrow (instr_operand_t i) (instr_print_t_args args)) #(instr_print_t_args ((IOpEx i)::args)) f o)
            oprs
      | IOpIm _ -> instr_printer_args args (coerce f) (coerce #(instr_operands_t_args args) oprs)
    )

let rec instr_printer_outs
    (outs:list instr_out) (args:list instr_operand)
    (f:instr_print_t outs args) (oprs:instr_operands_t outs args)
  : instr_print =
  match outs with
  | [] -> instr_printer_args args f oprs
//  | (_, i)::outs ->
  | (b, i)::outs ->
    (
      match i with
      | IOpEx i ->
//          let f:arrow (instr_operand_t i) (instr_print_t outs args) = coerce f in
          let (o, oprs) = coerce oprs in instr_printer_outs outs args
            (coerce #(arrow (instr_operand_t i) (instr_print_t outs args)) #(instr_print_t ((b, (IOpEx i))::outs) args) f o)
            oprs
      | IOpIm _ -> instr_printer_outs outs args (coerce f) (coerce #(instr_operands_t outs args) oprs)
    )

let instr_printer #outs #args #_ ins oprs =
  instr_printer_outs outs args ins.i_printer oprs

let make_ins
    (#outs:list instr_out) (#args:list instr_operand) (#havoc_flags:flag_havoc)
    (#f:normal (instr_eval_t outs args))
    (print:normal (instr_print_t outs args))
  : instr_dep outs args havoc_flags f =
  {i_printer = print; i_eval = f}

let print (name:string) (oprs:list instr_print_operand) : instr_print = Print name POpcode oprs
let print_s (name:string) (oprs:list instr_print_operand) : instr_print = Print name PSuffix oprs

