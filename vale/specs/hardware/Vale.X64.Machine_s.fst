module Vale.X64.Machine_s

irreducible let va_qattr = ()
unfold let pow2_32 = Vale.Def.Words_s.pow2_32
unfold let pow2_64 = Vale.Def.Words_s.pow2_64
unfold let pow2_128 = Vale.Def.Words_s.pow2_128

unfold let nat64 = Vale.Def.Types_s.nat64
let int_to_nat64 (i:int) : n:nat64{0 <= i && i < pow2_64 ==> i == n} =
  Vale.Def.Words_s.int_to_natN pow2_64 i
unfold let nat128 = Vale.Def.Words_s.nat128
unfold let quad32 = Vale.Def.Types_s.quad32

type reg:eqtype = i:int{0 <= i /\ i < 16}
type xmm:eqtype = i:int{0 <= i /\ i < 16}
type imm8:eqtype = i:int{0 <= i && i < 256}

[@va_qattr] unfold let rRax : reg = 0
[@va_qattr] unfold let rRbx : reg = 1
[@va_qattr] unfold let rRcx : reg = 2
[@va_qattr] unfold let rRdx : reg = 3
[@va_qattr] unfold let rRsi : reg = 4
[@va_qattr] unfold let rRdi : reg = 5
[@va_qattr] unfold let rRbp : reg = 6
[@va_qattr] unfold let rRsp : reg = 7
[@va_qattr] unfold let rR8  : reg = 8
[@va_qattr] unfold let rR9  : reg = 9
[@va_qattr] unfold let rR10 : reg = 10
[@va_qattr] unfold let rR11 : reg = 11
[@va_qattr] unfold let rR12 : reg = 12
[@va_qattr] unfold let rR13 : reg = 13
[@va_qattr] unfold let rR14 : reg = 14
[@va_qattr] unfold let rR15 : reg = 15

type maddr:eqtype =
  | MConst: n:int -> maddr
  | MReg: r:reg -> offset:int -> maddr
  | MIndex: base:reg -> scale:int -> index:reg -> offset:int -> maddr

type taint:eqtype =
  | Public
  | Secret

type tmaddr:eqtype = maddr & taint

[@va_qattr]
type operand:eqtype =
  | OConst: n:int -> operand
  | OReg: r:reg -> operand
  | OMem: m:tmaddr -> operand
  | OStack: m:tmaddr -> operand

[@va_qattr]
type operand128:eqtype =
  | OReg128: x:xmm -> operand128
  | OMem128: m:tmaddr -> operand128
  | OStack128: m:tmaddr -> operand128

noeq
type precode (t_ins:Type0) (t_ocmp:eqtype) : Type0 =
  | Ins: ins:t_ins -> precode t_ins t_ocmp
  | Block: block:list (precode t_ins t_ocmp) -> precode t_ins t_ocmp
  | IfElse: ifCond:t_ocmp -> ifTrue:precode t_ins t_ocmp -> ifFalse:precode t_ins t_ocmp -> precode t_ins t_ocmp
  | While: whileCond:t_ocmp -> whileBody:precode t_ins t_ocmp -> precode t_ins t_ocmp

type observation:eqtype =
  | BranchPredicate: pred:bool -> observation
  | MemAccess: addr:nat64 -> observation
  | MemAccessOffset: base:nat64 -> index:nat64 -> observation

type memTaint_t = (m:Map.t int taint{Set.equal (Map.domain m) (Set.complement Set.empty)})
