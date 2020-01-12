module Vale.X64.Machine_s
open FStar.Mul
include Vale.Arch.HeapTypes_s

irreducible let va_qattr = ()
unfold let pow2_32 = Vale.Def.Words_s.pow2_32
unfold let pow2_64 = Vale.Def.Words_s.pow2_64
unfold let pow2_128 = Vale.Def.Words_s.pow2_128

unfold let nat64 = Vale.Def.Types_s.nat64
let int_to_nat64 (i:int) : n:nat64{0 <= i && i < pow2_64 ==> i == n} =
  Vale.Def.Words_s.int_to_natN pow2_64 i
unfold let nat128 = Vale.Def.Words_s.nat128
unfold let quad32 = Vale.Def.Types_s.quad32

type flag:eqtype = i:int{0 <= i /\ i < 16}

[@va_qattr] unfold let fCarry    : flag = 0
[@va_qattr] unfold let fOverflow : flag = 11

let n_reg_files = 2
let reg_file_id = rf:nat{rf < n_reg_files}
let n_regs (rf:reg_file_id) : nat =
  match rf with
  | 0 -> 16
  | 1 -> 16
let t_reg_file (rf:reg_file_id) : Type0 =
  match rf with
  | 0 -> nat64
  | 1 -> quad32

let reg_id (rf:reg_file_id) : Type0 = r:nat{r < n_regs rf}

[@va_qattr]
type reg =
  | Reg: rf:reg_file_id -> r:reg_id rf -> reg

let t_reg (r:reg) : Type0 = t_reg_file r.rf

// Some register files can be used as integers (for addresses); others arbitrarily return 0
let t_reg_to_int (rf:reg_file_id) (v:t_reg_file rf) : int =
  match rf with
  | 0 -> v
  | 1 -> 0

type maddr:eqtype =
  | MConst: n:int -> maddr
  | MReg: r:reg -> offset:int -> maddr
  | MIndex: base:reg -> scale:int -> index:reg -> offset:int -> maddr

type tmaddr:eqtype = maddr & taint

[@va_qattr]
type operand (tc tr:eqtype) : eqtype =
  | OConst: n:tc -> operand tc tr
  | OReg: r:tr -> operand tc tr
  | OMem: m:tmaddr -> operand tc tr
  | OStack: m:tmaddr -> operand tc tr

[@va_qattr]
let operand_rf (rf:reg_file_id) : eqtype =
  operand (t_reg_file rf) (reg_id rf)

[@va_qattr]
unfold let oreg (r:reg) : operand_rf r.rf =
  OReg r.r

let reg_64 : Type0 = r:nat{r < 16}
let reg_xmm : Type0 = r:nat{r < 16}

[@va_qattr] unfold let rRax : reg_64 = 0
[@va_qattr] unfold let rRbx : reg_64 = 1
[@va_qattr] unfold let rRcx : reg_64 = 2
[@va_qattr] unfold let rRdx : reg_64 = 3
[@va_qattr] unfold let rRsi : reg_64 = 4
[@va_qattr] unfold let rRdi : reg_64 = 5
[@va_qattr] unfold let rRbp : reg_64 = 6
[@va_qattr] unfold let rRsp : reg_64 = 7
[@va_qattr] unfold let rR8  : reg_64 = 8
[@va_qattr] unfold let rR9  : reg_64 = 9
[@va_qattr] unfold let rR10 : reg_64 = 10
[@va_qattr] unfold let rR11 : reg_64 = 11
[@va_qattr] unfold let rR12 : reg_64 = 12
[@va_qattr] unfold let rR13 : reg_64 = 13
[@va_qattr] unfold let rR14 : reg_64 = 14
[@va_qattr] unfold let rR15 : reg_64 = 15

[@va_qattr] unfold let reg_Rax : reg = Reg 0 0
[@va_qattr] unfold let reg_Rbx : reg = Reg 0 1
[@va_qattr] unfold let reg_Rcx : reg = Reg 0 2
[@va_qattr] unfold let reg_Rdx : reg = Reg 0 3
[@va_qattr] unfold let reg_Rsi : reg = Reg 0 4
[@va_qattr] unfold let reg_Rdi : reg = Reg 0 5
[@va_qattr] unfold let reg_Rbp : reg = Reg 0 6
[@va_qattr] unfold let reg_Rsp : reg = Reg 0 7
[@va_qattr] unfold let reg_R8  : reg = Reg 0 8
[@va_qattr] unfold let reg_R9  : reg = Reg 0 9
[@va_qattr] unfold let reg_R10 : reg = Reg 0 10
[@va_qattr] unfold let reg_R11 : reg = Reg 0 11
[@va_qattr] unfold let reg_R12 : reg = Reg 0 12
[@va_qattr] unfold let reg_R13 : reg = Reg 0 13
[@va_qattr] unfold let reg_R14 : reg = Reg 0 14
[@va_qattr] unfold let reg_R15 : reg = Reg 0 15

[@va_qattr]
let operand64:eqtype = operand nat64 reg_64

[@va_qattr]
let operand128:eqtype = operand quad32 reg_xmm

noeq
type precode (t_ins:Type0) (t_ocmp:eqtype) : Type0 =
  | Ins: ins:t_ins -> precode t_ins t_ocmp
  | Block: block:list (precode t_ins t_ocmp) -> precode t_ins t_ocmp
  | IfElse: ifCond:t_ocmp -> ifTrue:precode t_ins t_ocmp -> ifFalse:precode t_ins t_ocmp -> precode t_ins t_ocmp
  | While: whileCond:t_ocmp -> whileBody:precode t_ins t_ocmp -> precode t_ins t_ocmp

type observation:eqtype =
  | BranchPredicate: pred:bool -> observation
  | MemAccess: addr:int -> observation

