module Vale.X64.State
// This interface should not refer to Semantics_s

open Vale.Def.Prop_s
open Vale.X64.Machine_s
open Vale.X64.Memory
open Vale.X64.Stack_i
module Flags = Vale.X64.Flags
module Regs = Vale.X64.Regs
module Xmms = Vale.X64.Xmms

noeq type vale_state = {
  vs_ok: bool;
  vs_regs: Regs.t;
  vs_xmms: Xmms.t;
  vs_flags: Flags.t;
  vs_mem: mem;
  vs_stack: stack;
  vs_memTaint: memtaint;
  vs_stackTaint: memtaint;
}

[@va_qattr]
unfold let eval_reg (r:reg) (s:vale_state) : nat64 = Regs.sel r s.vs_regs
[@va_qattr]
unfold let eval_xmm (x:xmm) (s:vale_state) : Vale.Def.Types_s.quad32 = Xmms.sel x s.vs_xmms
[@va_qattr]
unfold let eval_flag (f:flag) (s:vale_state) : Flags.flag_val_t = Flags.sel f s.vs_flags
[@va_qattr]
unfold let eval_mem (ptr:int) (s:vale_state) : GTot nat64 = load_mem64 ptr s.vs_mem
[@va_qattr]
unfold let eval_mem128 (ptr:int) (s:vale_state) : GTot Vale.Def.Types_s.quad32 = load_mem128 ptr s.vs_mem
[@va_qattr]
unfold let eval_stack (ptr:int) (s:vale_state) : GTot nat64 = load_stack64 ptr s.vs_stack
[@va_qattr]
unfold let eval_stack128 (ptr:int) (s:vale_state) : GTot quad32 = load_stack128 ptr s.vs_stack

[@va_qattr]
let eval_maddr (m:maddr) (s:vale_state) : int =
  let open FStar.Mul in
    match m with
    | MConst n -> n
    | MReg reg offset -> eval_reg reg s + offset
    | MIndex base scale index offset -> eval_reg base s + scale * (eval_reg index s) + offset

[@va_qattr]
let to_nat64 (i:int) : nat64 =
  if 0 <= i && i < 0x10000000000000000 then i else int_to_nat64 i

[@va_qattr]
let eval_operand (o:operand64) (s:vale_state) : GTot nat64 =
  match o with
  | OConst n -> to_nat64 n
  | OReg r -> eval_reg r s
  | OMem (m, _) -> eval_mem (eval_maddr m s) s
  | OStack (m, _) -> eval_stack (eval_maddr m s) s

[@va_qattr]
let eval_operand128 (o:operand128) (s:vale_state) : GTot Vale.Def.Types_s.quad32 =
  match o with
  | OConst c -> c
  | OReg x -> eval_xmm x s
  | OMem (m, _) -> eval_mem128 (eval_maddr m s) s
  | OStack (m, _) -> eval_stack128 (eval_maddr m s) s

[@va_qattr]
let update_reg (r:reg) (v:nat64) (s:vale_state) : vale_state =
  {s with vs_regs = Regs.upd r v s.vs_regs}

[@va_qattr]
let update_xmm (x:xmm) (v:Vale.Def.Types_s.quad32) (s:vale_state) : vale_state =
  {s with vs_xmms = Xmms.upd x v s.vs_xmms}

[@va_qattr]
let update_flag (f:flag) (v:Flags.flag_val_t) (s:vale_state) : vale_state =
  {s with vs_flags = Flags.upd f v s.vs_flags}

[@va_qattr]
let update_mem (ptr:int) (v:nat64) (s:vale_state) : GTot vale_state = {s with vs_mem = store_mem64 ptr v s.vs_mem}

[@va_qattr]
let update_stack64 (ptr:int) (v:nat64) (s:vale_state) : GTot vale_state = {s with vs_stack = store_stack64 ptr v s.vs_stack}

[@va_qattr]
let update_operand64 (o:operand64) (v:nat64) (sM:vale_state) : GTot vale_state =
  match o with
  | OConst n -> sM
  | OReg r -> update_reg r v sM
  | OMem (m, _) -> update_mem (eval_maddr m sM) v sM
  | OStack (m, _) -> update_stack64 (eval_maddr m sM) v sM

[@va_qattr]
let valid_maddr (m:maddr) (s:vale_state) : prop0 = valid_mem64 (eval_maddr m s) s.vs_mem

[@va_qattr]
let valid_maddr128 (m:maddr) (s:vale_state) : prop0 = valid_mem128 (eval_maddr m s) s.vs_mem

[@va_qattr]
let valid_src_operand (o:operand64) (s:vale_state) : prop0 =
  match o with
  | OConst n -> 0 <= n /\ n < pow2_64
  | OReg r -> True
  | OMem (m, _) -> valid_mem64 (eval_maddr m s) s.vs_mem
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
  {s with vs_regs = Regs.eta s.vs_regs; vs_xmms = Xmms.eta s.vs_xmms; vs_flags = Flags.eta s.vs_flags}

[@va_qattr]
let state_eq (s0:vale_state) (s1:vale_state) : prop0 =
  s0.vs_ok == s1.vs_ok /\
  Regs.equal s0.vs_regs s1.vs_regs /\
  Xmms.equal s0.vs_xmms s1.vs_xmms /\
  Flags.equal s0.vs_flags s1.vs_flags /\
  s0.vs_mem == s1.vs_mem /\
  s0.vs_stack == s1.vs_stack /\
  s0.vs_memTaint == s1.vs_memTaint /\
  s0.vs_stackTaint == s1.vs_stackTaint
