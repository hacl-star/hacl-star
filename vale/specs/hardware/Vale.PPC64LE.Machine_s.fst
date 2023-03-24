module Vale.PPC64LE.Machine_s
open Vale.Arch.Heap
include Vale.Arch.HeapTypes_s

irreducible let va_qattr = ()
unfold let pow2_8 = Vale.Def.Words_s.pow2_8
unfold let pow2_32 = Vale.Def.Words_s.pow2_32
unfold let pow2_64 = Vale.Def.Words_s.pow2_64

unfold let nat8 = Vale.Def.Words_s.nat8
unfold let nat16 = Vale.Def.Words_s.nat16
unfold let nat32 = Vale.Def.Words_s.nat32
let int_to_nat8 (i:int) : n:nat8{0 <= i && i < pow2_8 ==> i == n} =
  Vale.Def.Words_s.int_to_natN pow2_8 i
let int_to_nat32 (i:int) : n:nat32{0 <= i && i < pow2_32 ==> i == n} =
  Vale.Def.Words_s.int_to_natN pow2_32 i
unfold let nat64 = Vale.Def.Words_s.nat64
let int_to_nat64 (i:int) : n:nat64{0 <= i && i < pow2_64 ==> i == n} =
  Vale.Def.Words_s.int_to_natN pow2_64 i
unfold let quad32 = Vale.Def.Types_s.quad32

type reg = i:int{0 <= i /\ i < 32}
type vec = i:int{0 <= i /\ i < 32}

// Immediate operand of logical compare, and, or, and xor instructions
type imm16 = i:int{0 <= i && i <= 65535}
// Immediate operand of compare, add (with signed immediate) instructions
type simm16 = i:int{-32768 <= i && i <= 32767}
// Immediate operand of sub (with negative signed immediate) instruction
type nsimm16 = i:int{-32767 <= i && i <= 32768}
// Immediate operand of rotate, shift, and clear for 64-bit instructions
type bits64 = i:int{0 <= i && i < 64}
// Immediate operand of rotate, shift, and clear for 32-bit instructions
type bits32 = i:int{0 <= i && i < 32}
// Immediate operand of vector shift left double by octet
type quad32bytes = i:int{0 <= i && i < 16}
// Immediate operand of vector splat
type sim = i:int{-16 <= i && i < 15}

let regs_t = FStar.FunctionalExtensionality.restricted_t reg (fun _ -> nat64)
let vecs_t = FStar.FunctionalExtensionality.restricted_t vec (fun _ -> quad32)
[@va_qattr] unfold let regs_make (f:reg -> nat64) : regs_t = FStar.FunctionalExtensionality.on_dom reg f
[@va_qattr] unfold let vecs_make (f:vec -> quad32) : vecs_t = FStar.FunctionalExtensionality.on_dom vec f

// Condition Register (CR) Field 0 is interpreted as individual 4-bits that can be set as the implicit
// results of certain fixed-point instructions.
// Fixed-point compare instructions in which CR field operand is default or 0 and fixed-point arithmetic
// instructions that have "." suffix in the instruction mnemonic (Rc=1) alter the CR Field 0 (CR0) fields.
// The fourth bit of CR0 reflects the Summary Overflow (SO) field of Fixed-Point Exception Register (XER).
type cr0_t = {
  lt:bool;      // negative result
  gt:bool;      // positive result
  eq:bool;      // zero result
}

// Fixed-Point Exception Register (XER) stores the status of overflow and carry occurrences of
// instructions that can overflow with OE=1 and carry. Compare instructions don't alter XER.
type xer_t = {
  ov:bool;     // Overflow
  ca:bool;     // Carry
}

noeq
type machine_stack =
  | Machine_stack:
    initial_r1:nat64{initial_r1 >= 65536} ->  // Initial rsp pointer when entering the function
    stack_mem:Map.t int nat8 ->                // Stack contents
    machine_stack

noeq type state = {
  ok: bool;
  regs: regs_t;
  vecs: vecs_t;
  cr0: cr0_t;
  xer: xer_t;
  ms_heap: heap_impl;
  ms_stack: machine_stack;
  ms_stackTaint: memTaint_t;
}

let get_cr0 (r:nat64) =
  { lt = r >= 0x8000000000000000; gt = r < 0x8000000000000000; eq = r = 0 }

type maddr = {
  address: reg;
  offset: int
}

type tmaddr:eqtype = maddr & taint

// Memory offset bound of 32-bit, 16-bit, and 8-bit load/store instructions
let valid_maddr_offset (n:int) : bool =
  n >= -32768 && n <= 32767

// Memory offset bound of 64-bit load/store instructions
let valid_maddr_offset64 (n:int) : bool =
  n >= -32768 && n <= 32764 && n % 4 = 0

// Memory offset bound of 128-bit load/store instructions
let valid_maddr_offset128 (n:int) : bool =
  n >= -32768 && n <= 32752 && n % 16 = 0

type cmp_opr =
  | CReg: r:reg -> cmp_opr
  | CImm: n:imm16 -> cmp_opr

let valid_first_cmp_opr (o:cmp_opr) : bool =
  CReg? o

type precode (t_ins:Type0) (t_ocmp:Type0) =
  | Ins: ins:t_ins -> precode t_ins t_ocmp
  | Block: block:list (precode t_ins t_ocmp) -> precode t_ins t_ocmp
  | IfElse: ifCond:t_ocmp -> ifTrue:precode t_ins t_ocmp -> ifFalse:precode t_ins t_ocmp -> precode t_ins t_ocmp
  | While: whileCond:t_ocmp -> whileBody:precode t_ins t_ocmp -> precode t_ins t_ocmp
