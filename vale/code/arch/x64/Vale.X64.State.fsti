module Vale.X64.State
open FStar.Mul
// This interface should not refer to Machine_Semantics_s

open Vale.Def.Prop_s
open Vale.Arch.HeapImpl
open Vale.X64.Machine_s
open Vale.X64.Memory
open Vale.X64.Stack_i
module Flags = Vale.X64.Flags
module Regs = Vale.X64.Regs
module Map16 = Vale.Lib.Map16

noeq type vale_state = {
  vs_ok: bool;
  vs_regs: Regs.t;
  vs_flags: Flags.t;
  vs_heap: vale_full_heap;
  vs_stack: vale_stack;
  vs_stackTaint: memtaint;
}

unfold let vs_get_vale_heap (s:vale_state) : vale_heap = get_vale_heap s.vs_heap

[@va_qattr]
unfold let eval_reg (r:reg) (s:vale_state) : t_reg r = Regs.sel r s.vs_regs
[@va_qattr]
unfold let eval_reg_int (r:reg) (s:vale_state) : int = t_reg_to_int r.rf (eval_reg r s)
[@va_qattr]
unfold let eval_flag (f:flag) (s:vale_state) : Flags.flag_val_t = Flags.sel f s.vs_flags
[@va_qattr]
unfold let eval_mem (ptr:int) (s:vale_state) : GTot nat64 = load_mem64 ptr (get_vale_heap s.vs_heap)
[@va_qattr]
unfold let eval_mem128 (ptr:int) (s:vale_state) : GTot Vale.Def.Types_s.quad32 = load_mem128 ptr (get_vale_heap s.vs_heap)
[@va_qattr]
unfold let eval_stack (ptr:int) (s:vale_state) : GTot nat64 = load_stack64 ptr s.vs_stack
[@va_qattr]
unfold let eval_stack128 (ptr:int) (s:vale_state) : GTot quad32 = load_stack128 ptr s.vs_stack

[@va_qattr]
unfold let eval_reg_64 (r:reg_64) (s:vale_state) : nat64 = eval_reg (Reg 0 r) s

[@va_qattr]
unfold let eval_reg_xmm (r:reg_xmm) (s:vale_state) : quad32 = eval_reg (Reg 1 r) s

[@va_qattr]
let eval_maddr (m:maddr) (s:vale_state) : int =
  match m with
  | MConst n -> n
  | MReg r offset -> eval_reg_int r s + offset
  | MIndex base scale index offset -> eval_reg_int base s + scale * (eval_reg_int index s) + offset

[@va_qattr]
let eval_operand (o:operand64) (s:vale_state) : GTot nat64 =
  match o with
  | OConst n -> n
  | OReg r -> eval_reg_64 r s
  | OMem (m, _) -> eval_mem (eval_maddr m s) s
  | OStack (m, _) -> eval_stack (eval_maddr m s) s

[@va_qattr]
let eval_operand128 (o:operand128) (s:vale_state) : GTot Vale.Def.Types_s.quad32 =
  match o with
  | OConst c -> c
  | OReg r -> eval_reg_xmm r s
  | OMem (m, _) -> eval_mem128 (eval_maddr m s) s
  | OStack (m, _) -> eval_stack128 (eval_maddr m s) s

[@va_qattr]
let update_reg (r:reg) (v:t_reg r) (s:vale_state) : vale_state =
  {s with vs_regs = Regs.upd r v s.vs_regs}

[@va_qattr]
let update_reg_64 (r:reg_64) (v:nat64) (s:vale_state) : vale_state =
  update_reg (Reg 0 r) v s

[@va_qattr]
let update_flag (f:flag) (v:Flags.flag_val_t) (s:vale_state) : vale_state =
  {s with vs_flags = Flags.upd f v s.vs_flags}

[@va_qattr]
let update_reg_xmm (r:reg_xmm) (v:quad32) (s:vale_state) : vale_state =
  update_reg (Reg 1 r) v s

//[@va_qattr]
//let update_mem (ptr:int) (v:nat64) (s:vale_state) : GTot vale_state =
//  {s with vs_heap = set_vale_heap s.vs_heap (store_mem64 ptr v (get_vale_heap s.vs_heap))}

[@va_qattr]
let update_stack64 (ptr:int) (v:nat64) (s:vale_state) : GTot vale_state =
  {s with vs_stack = store_stack64 ptr v s.vs_stack}

//[@va_qattr]
//let update_operand64 (o:operand64) (v:nat64) (sM:vale_state) : GTot vale_state =
//  match o with
//  | OConst n -> sM
//  | OReg r -> update_reg (Reg 0 r) v sM
//  | OMem (m, _) -> update_mem (eval_maddr m sM) v sM
//  | OStack (m, _) -> update_stack64 (eval_maddr m sM) v sM

[@va_qattr]
let valid_maddr (m:maddr) (s:vale_state) : prop0 =
  valid_mem64 (eval_maddr m s) (get_vale_heap s.vs_heap)

[@va_qattr]
let valid_maddr128 (m:maddr) (s:vale_state) : prop0 =
  valid_mem128 (eval_maddr m s) (get_vale_heap s.vs_heap)

[@va_qattr]
let valid_src_operand (o:operand64) (s:vale_state) : prop0 =
  match o with
  | OConst c -> True
  | OReg r -> True
  | OMem (m, _) -> valid_maddr m s
  | OStack (m, _) -> valid_src_stack64 (eval_maddr m s) s.vs_stack

[@va_qattr]
let valid_src_operand128 (o:operand128) (s:vale_state) : prop0 =
  match o with
  | OConst _ -> False
  | OReg _ -> True
  | OMem (m, _) -> valid_maddr128 m s
  | OStack (m, _) -> valid_src_stack128 (eval_maddr m s) s.vs_stack

[@va_qattr]
let state_eta (s:vale_state) : vale_state =
  {s with
    vs_regs = Regs.eta s.vs_regs;
    vs_heap = {s.vs_heap with vf_heaplets = Map16.eta s.vs_heap.vf_heaplets};
  }

[@va_qattr]
let state_eq (s0:vale_state) (s1:vale_state) : prop0 =
  s0.vs_ok == s1.vs_ok /\
  Regs.equal s0.vs_regs s1.vs_regs /\
  Flags.equal s0.vs_flags s1.vs_flags /\
  vale_full_heap_equal s0.vs_heap s1.vs_heap /\
  s0.vs_stack == s1.vs_stack /\
  s0.vs_stackTaint == s1.vs_stackTaint
