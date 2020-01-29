module Vale.X64.StateLemmas
open Vale.X64.Machine_s
open Vale.Arch.Heap
open Vale.X64.State
open FStar.FunctionalExtensionality
module Ms = Vale.X64.Machine_Semantics_s
//open Vale.X64.Machine_Semantics_s
//module ME = Vale.X64.Memory
open Vale.X64.Memory
open Vale.Arch.MachineHeap_s
//module MS = Vale.X64.Memory_Sems
module VSS = Vale.X64.Stack_Sems
module F = FStar.FunctionalExtensionality
open Vale.Def.Prop_s
open FStar.Mul

unfold let machine_state = Ms.machine_state
unfold let code = Ms.code
unfold let machine_eval_code = Ms.machine_eval_code
val same_heap_types : squash (vale_full_heap == heap_impl)
unfold let coerce (#b #a:Type) (x:a{a == b}) : b = x

let machine_state_eq (s1 s2:machine_state) =
  s1 == s2

let machine_state_equal (s1 s2:machine_state) =
  let open Vale.X64.Machine_Semantics_s in
  s1.ms_ok == s2.ms_ok /\
  F.feq s1.ms_regs s2.ms_regs /\
  F.feq s1.ms_flags s2.ms_flags /\
  s1.ms_heap == s2.ms_heap /\
  s1.ms_stack == s2.ms_stack /\
  s1.ms_stackTaint == s2.ms_stackTaint /\
  s1.ms_trace == s2.ms_trace /\
  True

val use_machine_state_equal (_:unit) : Lemma
  (requires True)
  (ensures forall (s1 s2:machine_state).{:pattern machine_state_eq s1 s2}
    machine_state_equal s1 s2 ==> machine_state_eq s1 s2)

let state_to_S (s:vale_state) : GTot machine_state =
  let open Ms in
  {
    ms_ok = s.vs_ok;
    ms_regs = F.on_dom reg (fun r -> Regs.sel r s.vs_regs);
    ms_flags = F.on_dom flag (fun f -> Flags.sel f s.vs_flags);
    ms_heap = coerce s.vs_heap;
    ms_stack = VSS.stack_to_s s.vs_stack;
    ms_stackTaint = s.vs_stackTaint;
    ms_trace = [];
  }

let state_of_S (s:machine_state) : GTot vale_state =
  let open Ms in
  {
    vs_ok = s.ms_ok;
    vs_regs = Regs.of_fun s.ms_regs;
    vs_flags = Flags.of_fun s.ms_flags;
    vs_heap = coerce s.ms_heap;
    vs_stack = VSS.stack_from_s s.ms_stack;
    vs_stackTaint = s.ms_stackTaint;
  }

val lemma_valid_mem_addr64 (h:vale_full_heap) (ptr:int) : Lemma
  (requires valid_mem64 ptr (get_vale_heap h))
  (ensures valid_addr64 ptr (heap_get (coerce h)))
  [SMTPat (valid_mem64 ptr (get_vale_heap h))]

val lemma_valid_mem_addr128 (h:vale_full_heap) (ptr:int) : Lemma
  (requires valid_mem128 ptr (get_vale_heap h))
  (ensures valid_addr128 ptr (heap_get (coerce h)))
  [SMTPat (valid_mem128 ptr (get_vale_heap h))]

val lemma_load_mem_get64 (h:vale_full_heap) (ptr:int) : Lemma
  (requires valid_mem64 ptr (get_vale_heap h))
  (ensures load_mem64 ptr (get_vale_heap h) == get_heap_val64 ptr (heap_get (coerce h)))
  [SMTPat (load_mem64 ptr (get_vale_heap h))]

val lemma_load_mem_get128 (h:vale_full_heap) (ptr:int) : Lemma
  (requires valid_mem128 ptr (get_vale_heap h))
  (ensures load_mem128 ptr (get_vale_heap h) == get_heap_val128 ptr (heap_get (coerce h)))
  [SMTPat (load_mem128 ptr (get_vale_heap h))]

//val lemma_valid_buffer_read64 (h:vale_heap) (b:buffer64) (i:int) : Lemma
//  (requires valid_buffer_read h b i)
//  (ensures valid_mem64 (buffer_addr b h + 8 * i) h)
//  [SMTPat (valid_buffer_read h b i)]

//val lemma_valid_buffer_read128 (h:vale_heap) (b:buffer128) (i:int) : Lemma
//  (requires valid_buffer_read h b i)
//  (ensures valid_mem128 (buffer_addr b h + 16 * i) h)
//  [SMTPat (valid_buffer_read h b i)]

val lemma_load_buffer_read64 (h:vale_heap) (b:buffer64) (i:int) : Lemma
  (requires valid_buffer_read h b i)
  (ensures buffer_read b i h == load_mem64 (buffer_addr b h + 8 * i) h)
  [SMTPat (buffer_read b i h)]

val lemma_load_buffer_read128 (h:vale_heap) (b:buffer128) (i:int) : Lemma
  (requires valid_buffer_read h b i)
  (ensures buffer_read b i h == load_mem128 (buffer_addr b h + 16 * i) h)
  [SMTPat (buffer_read b i h)]

// REVIEW: should this lemma be needed, since it is provable from the lemmas above?
val lemma_to_eval_operand (s:vale_state) (o:operand64) : Lemma
  (requires valid_src_operand o s)
  (ensures eval_operand o s == Ms.eval_operand o (state_to_S s))
  [SMTPat (eval_operand o s)]

//val lemma_to_eval_xmm (s:vale_state) (x:reg_xmm) : Lemma
//  (ensures eval_reg_xmm x s == Ms.eval_reg_xmm x (state_to_S s))
//  [SMTPat (eval_reg_xmm x s)]
//
//val lemma_to_eval_operand128 (s:vale_state) (o:operand128) : Lemma
//  (requires valid_src_operand128 o s)
//  (ensures eval_operand128 o s == Ms.eval_mov128_op o (state_to_S s))
//  [SMTPat (eval_operand128 o s)]
//
//val lemma_to_valid_operand (s:vale_state) (o:operand64) : Lemma
//  (ensures valid_src_operand o s ==> Ms.valid_src_operand o (state_to_S s))
//  [SMTPat (valid_src_operand o s)]

val lemma_to_of (s:machine_state) : Lemma
  (ensures state_to_S (state_of_S s) == {s with Ms.ms_trace = []})

