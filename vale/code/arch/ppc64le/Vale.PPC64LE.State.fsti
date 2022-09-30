module Vale.PPC64LE.State
// This interface should not refer to Semantics_s

open Vale.Def.Prop_s
open Vale.PPC64LE.Machine_s
module M = Vale.PPC64LE.Memory
open Vale.Arch.HeapImpl
open Vale.Arch.Heap
open Vale.PPC64LE.Stack_i
module Map16 = Vale.Lib.Map16
module VSS = Vale.PPC64LE.Stack_Sems

val same_heap_types : squash (vale_full_heap == heap_impl)
unfold let coerce (#b #a:Type) (x:a{a == b}) : b = x

unfold let state = Vale.PPC64LE.Machine_s.state

[@va_qattr]
unfold let eval_reg (r:reg) (s:state) : nat64 = s.regs r
[@va_qattr]
unfold let eval_vec (v:vec) (s:state) : quad32 = s.vecs v
[@va_qattr]
unfold let eval_mem (ptr:int) (s:state) : GTot nat64 = M.load_mem64 ptr (M.get_vale_heap (coerce s.ms_heap))

[@va_qattr]
let eval_maddr (m:maddr) (s:state) : int =
  eval_reg m.address s + m.offset

[@va_qattr]
let eval_cmp_opr (o:cmp_opr) (s:state) : nat64 =
  match o with
  | CReg r -> eval_reg r s
  | CImm n -> int_to_nat64 n

[@va_qattr]
unfold let eval_stack (ptr:int) (s:state) : GTot nat64 = load_stack64 ptr (VSS.stack_from_s s.ms_stack)
[@va_qattr]
unfold let eval_stack128 (ptr:int) (s:state) : GTot quad32 = load_stack128 ptr (VSS.stack_from_s s.ms_stack)

[@va_qattr]
let update_reg (r:reg) (v:nat64) (s:state) : state =
  { s with regs = regs_make (fun (r':reg) -> if r = r' then v else s.regs r') }

[@va_qattr]
let update_vec (vr:vec) (v:quad32) (s:state) : state =
  { s with vecs = vecs_make (fun (vr':vec) -> if vr' = vr then v else s.vecs vr') }

[@va_qattr]
let update_stack64 (ptr:int) (v:nat64) (s:state) : GTot state =
  {s with ms_stack = VSS.stack_to_s (store_stack64 ptr v (VSS.stack_from_s s.ms_stack))}

[@va_qattr]
let valid_maddr (m:maddr) (s:state) : prop0 =
  M.valid_mem64 (eval_maddr m s) (M.get_vale_heap (coerce s.ms_heap))

[@va_qattr]
let valid_mem (m:maddr) (s:state) : prop0 =
  valid_maddr_offset64 m.offset /\ valid_maddr m s

[@va_qattr]
let valid_mem128 (r:reg) (i:reg) (s:state) : prop0 =
  M.valid_mem128 (eval_reg r s + eval_reg i s) (M.get_vale_heap (coerce s.ms_heap))

[@va_qattr]
let state_eta (s:state) : state =
  {s with
    ms_heap = coerce ({ (coerce s.ms_heap) with vf_heaplets = Map16.eta (coerce s.ms_heap).vf_heaplets });
  }

[@va_qattr]
let state_eq (s0:state) (s1:state) : prop0 =
  s0.ok == s1.ok /\
  Regs.equal s0.regs s1.regs /\
  Vecs.equal s0.vecs s1.vecs /\
  s0.cr0 == s1.cr0 /\
  s0.xer == s1.xer /\
  M.vale_full_heap_equal (coerce s0.ms_heap) (coerce s1.ms_heap) /\
  s0.ms_stack == s1.ms_stack /\
  s0.ms_stackTaint == s1.ms_stackTaint

let machine_state_eq (s1 s2:state) =
  s1 == s2

let machine_state_equal (s1 s2:state) =
  s1.ok == s2.ok /\
  Regs.equal s1.regs s2.regs /\
  Vecs.equal s1.vecs s2.vecs /\
  s1.cr0 == s2.cr0 /\
  s1.xer == s2.xer /\
  s1.ms_heap == s2.ms_heap /\
  s1.ms_stack == s2.ms_stack /\
  s1.ms_stackTaint == s2.ms_stackTaint /\
  True

val use_machine_state_equal (_:unit) : Lemma
  (requires True)
  (ensures forall (s1 s2:state).{:pattern machine_state_eq s1 s2}
    machine_state_equal s1 s2 ==> machine_state_eq s1 s2)
