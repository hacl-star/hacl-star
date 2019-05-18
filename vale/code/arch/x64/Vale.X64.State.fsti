module Vale.X64.State
// This interface should not refer to Semantics_s

open Vale.Def.Prop_s
open Vale.X64.Machine_s
open Vale.X64.Memory
open Vale.X64.Stack_i
module Regs = Vale.X64.Regs
module Xmms = Vale.X64.Xmms

noeq type state = {
  ok: bool;
  regs: Regs.t;
  xmms: Xmms.t;
  flags: nat64;
  mem: mem;
  stack:stack;
  memTaint: memtaint;
  stackTaint: memtaint;
}

[@va_qattr]
unfold let eval_reg (r:reg) (s:state) : nat64 = Regs.sel r s.regs
[@va_qattr]
unfold let eval_xmm (x:xmm) (s:state) : Vale.Def.Types_s.quad32 = Xmms.sel x s.xmms
[@va_qattr]
unfold let eval_mem (ptr:int) (s:state) : GTot nat64 = load_mem64 ptr s.mem
[@va_qattr]
unfold let eval_mem128 (ptr:int) (s:state) : GTot Vale.Def.Types_s.quad32 = load_mem128 ptr s.mem
[@va_qattr]
unfold let eval_stack (ptr:int) (s:state) : GTot nat64 = load_stack64 ptr s.stack
[@va_qattr]
unfold let eval_stack128 (ptr:int) (s:state) : GTot quad32 = load_stack128 ptr s.stack

[@va_qattr]
let eval_maddr (m:maddr) (s:state) : int =
  let open FStar.Mul in
    match m with
    | MConst n -> n
    | MReg reg offset -> eval_reg reg s + offset
    | MIndex base scale index offset -> eval_reg base s + scale * (eval_reg index s) + offset

[@va_qattr]
let to_nat64 (i:int) : nat64 =
  if 0 <= i && i < 0x10000000000000000 then i else int_to_nat64 i

[@va_qattr]
let eval_operand (o:operand) (s:state) : GTot nat64 =
  match o with
  | OConst n -> to_nat64 n
  | OReg r -> eval_reg r s
  | OMem (m, _) -> eval_mem (eval_maddr m s) s
  | OStack (m, _) -> eval_stack (eval_maddr m s) s

[@va_qattr]
let eval_operand128 (o:operand128) (s:state) : GTot Vale.Def.Types_s.quad32 =
  match o with
  | OReg128 x -> eval_xmm x s
  | OMem128 (m, _) -> eval_mem128 (eval_maddr m s) s
  | OStack128 (m, _) -> eval_stack128 (eval_maddr m s) s

[@va_qattr]
let update_reg (r:reg) (v:nat64) (s:state) : state =
  {s with regs = Regs.upd r v s.regs}

[@va_qattr]
let update_xmm (x:xmm) (v:Vale.Def.Types_s.quad32) (s:state) : state =
  {s with xmms = Xmms.upd x v s.xmms}

[@va_qattr]
let update_mem (ptr:int) (v:nat64) (s:state) : GTot state = {s with mem = store_mem64 ptr v s.mem}

[@va_qattr]
let update_stack (ptr:int) (v:nat64) (s:state) : GTot state = {s with stack = store_stack64 ptr v s.stack}

[@va_qattr]
let update_operand (o:operand) (v:nat64) (sM:state) : GTot state =
  match o with
  | OConst n -> sM
  | OReg r -> update_reg r v sM
  | OMem (m, _) -> update_mem (eval_maddr m sM) v sM
  | OStack (m, _) -> update_stack (eval_maddr m sM) v sM

[@va_qattr]
let valid_maddr (m:maddr) (s:state) : prop0 = valid_mem64 (eval_maddr m s) s.mem

[@va_qattr]
let valid_maddr128 (m:maddr) (s:state) : prop0 = valid_mem128 (eval_maddr m s) s.mem

[@va_qattr]
let valid_src_operand (o:operand) (s:state) : prop0 =
  match o with
  | OConst n -> 0 <= n /\ n < pow2_64
  | OReg r -> True
  | OMem (m, _) -> valid_mem64 (eval_maddr m s) s.mem
  | OStack (m, _) -> valid_src_stack64 (eval_maddr m s) s.stack

[@va_qattr]
let valid_src_operand128 (o:operand128) (s:state) : prop0 =
  match o with
  | OReg128 _ -> True
  | OMem128 (m, _) -> valid_maddr128 m s
  | OStack128 (m, _) -> valid_src_stack128 (eval_maddr m s) s.stack

[@va_qattr]
let state_eta (s:state) : state =
  {s with regs = Regs.eta s.regs; xmms = Xmms.eta s.xmms}

[@va_qattr]
let state_eq (s0:state) (s1:state) : prop0 =
  s0.ok == s1.ok /\
  Regs.equal s0.regs s1.regs /\
  Xmms.equal s0.xmms s1.xmms /\
  s0.flags == s1.flags /\
  s0.mem == s1.mem /\
  s0.stack == s1.stack /\
  s0.memTaint == s1.memTaint /\
  s0.stackTaint == s1.stackTaint
