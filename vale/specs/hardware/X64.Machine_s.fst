module X64.Machine_s

irreducible let va_qattr = ()
unfold let pow2_32 = Words_s.pow2_32
unfold let pow2_64 = Words_s.pow2_64
unfold let pow2_128 = Words_s.pow2_128

unfold let nat64 = Types_s.nat64
let int_to_nat64 (i:int) : n:nat64{0 <= i && i < pow2_64 ==> i == n} =
  Words_s.int_to_natN pow2_64 i
unfold let nat128 = Words_s.nat128
unfold let quad32 = Types_s.quad32

type reg =
  | Rax
  | Rbx
  | Rcx
  | Rdx
  | Rsi
  | Rdi
  | Rbp
  | Rsp
  | R8
  | R9
  | R10
  | R11
  | R12
  | R13
  | R14
  | R15

type maddr =
  | MConst: n:int -> maddr
  | MReg: r:reg -> offset:int -> maddr
  | MIndex: base:reg -> scale:int -> index:reg -> offset:int -> maddr

[@va_qattr]
type operand =
  | OConst: n:int -> operand
  | OReg: r:reg -> operand
  | OMem: m:maddr -> operand

type imm8 = i:int { 0 <= i && i < 256}
type xmm = i:int{ 0 <= i /\ i < 16 }

type mov128_op =
  | Mov128Xmm: x:xmm -> mov128_op
  | Mov128Mem: m:maddr -> mov128_op

type precode (t_ins:Type0) (t_ocmp:Type0) =
  | Ins: ins:t_ins -> precode t_ins t_ocmp
  | Block: block:list (precode t_ins t_ocmp) -> precode t_ins t_ocmp
  | IfElse: ifCond:t_ocmp -> ifTrue:precode t_ins t_ocmp -> ifFalse:precode t_ins t_ocmp -> precode t_ins t_ocmp
  | While: whileCond:t_ocmp -> whileBody:precode t_ins t_ocmp -> precode t_ins t_ocmp

let valid_dst (o:operand) : bool =
  not(OConst? o || (OReg? o && Rsp? (OReg?.r o)))

type taint =
  | Public
  | Secret

type observation =
  | BranchPredicate: pred:bool -> observation
  | MemAccess: addr:nat64 -> observation
  | MemAccessOffset: base:nat64 -> index:nat64 -> observation

type memTaint_t = (m:Map.t int taint{Map.domain m == Set.complement Set.empty})
