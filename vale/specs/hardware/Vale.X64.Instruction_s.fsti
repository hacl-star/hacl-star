module Vale.X64.Instruction_s
open FStar.Mul
open Vale.Def.Words_s
open Vale.Def.Types_s
open Vale.X64.Machine_s

(*
An generic instruction has:
- zero or more input operands
- zero or more output operands or input/output operands
- a possible effect on the status flags
Some of the operands may be hard-coded to a particular register; other operands are flexible.
For example, the Intel 64-bit MUL instruction, which executes "(RDX:RAX) := RAX * src" has:
- one hard-coded input/output operand, the flags
  - note: the instruction can havoc the flags in addition to or instead of specifying a flags operand
- one hard-coded output operand, RDX
- one hard-coded input/output operand, RAX
- one flexible input operand (src)
*)
type instr_operand_inout = | InOut | Out
type instr_operand_explicit = // flexible operand
  | IOp64 : instr_operand_explicit
  | IOpXmm : instr_operand_explicit
type instr_operand_implicit = // hard-coded operand
  | IOp64One : o:operand64 -> instr_operand_implicit
  | IOpXmmOne : o:operand128 -> instr_operand_implicit
  | IOpFlagsCf : instr_operand_implicit
  | IOpFlagsOf : instr_operand_implicit
type instr_operand =
  | IOpEx : instr_operand_explicit -> instr_operand
  | IOpIm : instr_operand_implicit -> instr_operand
let instr_out = instr_operand_inout & instr_operand

irreducible let instr_attr = ()
unfold let normal (#a:Type) (x:a) : a = norm [zeta; iota; delta_attr [`%instr_attr]] x

let arrow (a b:Type) = a -> b
[@instr_attr] unfold let coerce (#b #a:Type) (x:a{a == b}) : b = x

[@instr_attr] unfold let inOut (o:instr_operand) = (InOut, o)
[@instr_attr] unfold let out (o:instr_operand) = (Out, o)
[@instr_attr] unfold let op64 = IOpEx IOp64
[@instr_attr] unfold let opXmm = IOpEx IOpXmm
[@instr_attr] unfold let one64 (o:operand64) = IOpIm (IOp64One o)
[@instr_attr] unfold let one64Reg (r:reg_64) = IOpIm (IOp64One (OReg r))
[@instr_attr] unfold let oneXmm (o:operand128) = IOpIm (IOpXmmOne o)
[@instr_attr] unfold let opFlagsCf = IOpIm IOpFlagsCf
[@instr_attr] unfold let opFlagsOf = IOpIm IOpFlagsOf

[@instr_attr]
let instr_val_t (o:instr_operand) : Type0 =
  match o with
  | IOpEx IOp64 | IOpIm (IOp64One _) -> nat64
  | IOpEx IOpXmm | IOpIm (IOpXmmOne _) -> quad32
  | IOpIm IOpFlagsCf -> bool
  | IOpIm IOpFlagsOf -> bool

[@instr_attr]
let rec instr_ret_t (outs:list instr_out) : Type0 =
  match outs with
  | [] -> unit
  | [(_, o)] -> instr_val_t o
  | (_, o)::outs -> instr_val_t o & instr_ret_t outs

[@instr_attr]
let rec instr_args_t (outs:list instr_out) (args:list instr_operand) : Type0 =
  match args with
  | [] -> option (instr_ret_t outs)
  | i::args -> arrow (instr_val_t i) (instr_args_t outs args)

[@instr_attr]
let rec instr_inouts_t (outs inouts:list instr_out) (args:list instr_operand) : Type0 =
  match inouts with
  | [] -> instr_args_t outs args
  | (Out, _)::inouts -> instr_inouts_t outs inouts args
  | (InOut, i)::inouts -> arrow (instr_val_t i) (instr_inouts_t outs inouts args)

(*
An instr evaluator is a function of type:
  in_outs1 ... ->  in_outsi -> args1 -> ...> argsj -> (outs1 & (... & outsk) ...)
where in_outs = [(b, o) in outs | b = InOut]
*)
[@instr_attr]
let instr_eval_t (outs:list instr_out) (args:list instr_operand) : Type0 =
  instr_inouts_t outs outs args

[@instr_attr]
let instr_operand_t (arg:instr_operand_explicit) : Type0 =
  match arg with
  | IOp64 -> operand64
  | IOpXmm -> operand128

[@instr_attr]
let rec instr_operands_t_args (args:list instr_operand) : Type0 =
  match args with
  | [] -> unit
  | (IOpEx i)::args -> instr_operand_t i & instr_operands_t_args args
  | (IOpIm _)::args -> instr_operands_t_args args

[@instr_attr]
let rec instr_operands_t (outs:list instr_out) (args:list instr_operand) : Type0 =
  match outs with
  | [] -> instr_operands_t_args args
  | (_, IOpEx i)::outs -> instr_operand_t i & instr_operands_t outs args
  | (_, IOpIm _)::outs -> instr_operands_t outs args

(*
The printed syntax may be different from the underlying semantics,
so we have a separate data type to represent operand syntax.
The print operands are listed in Intel/MASM order (destination operand listed first).
*)
type instr_print_operand =
  | P8 : operand64 -> instr_print_operand
  | P16 : operand64 -> instr_print_operand
  | P32 : operand64 -> instr_print_operand
  | P64 : operand64 -> instr_print_operand
  | PXmm : operand128 -> instr_print_operand
  | PImm : int -> instr_print_operand
  | PShift : operand64 -> instr_print_operand
type instr_print_kind =
  | POpcode
  | PSuffix // add suffix character to opcode for GCC/ATT syntax
  | PrintPSha256rnds2
type instr_print =
  | Print : string -> instr_print_kind -> list instr_print_operand -> instr_print

type flag_havoc = | HavocFlags | PreserveFlags

(*
This type is abstract so that untrusted code can't invent nonexistent instruction semantics
out of thin air.  (Only trusted instruction definitions can create new values of this type.)
The arguments (outs, args, havoc_flags), together with a function instr_eval,
determine the semantics.
*)
val instr_t (outs:list instr_out) (args:list instr_operand) (havoc_flags:flag_havoc) : Type0

noeq type instr_t_record =
  | InstrTypeRecord :
      #outs:list instr_out ->
      #args:list instr_operand ->
      #havoc_flags:flag_havoc ->
      i:instr_t outs args havoc_flags ->
      instr_t_record

val instr_eval
    (#outs:list instr_out) (#args:list instr_operand) (#havoc_flags:flag_havoc)
    (i:instr_t outs args havoc_flags)
//  : normal (instr_eval_t outs args)
  : norm [zeta; iota; delta_attr [`%instr_attr]] (instr_eval_t outs args)

val instr_printer
    (#outs:list instr_out) (#args:list instr_operand) (#havoc_flags:flag_havoc)
    (i:instr_t outs args havoc_flags) (oprs:normal (instr_operands_t outs args))
  : instr_print

let instr_dep
    (outs:list instr_out) (args:list instr_operand) (havoc_flags:flag_havoc)
    (f:normal (instr_eval_t outs args))
  : Type0 =
  i:(instr_t outs args havoc_flags){instr_eval i == f}

