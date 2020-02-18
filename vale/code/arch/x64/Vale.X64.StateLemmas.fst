module Vale.X64.StateLemmas
open FStar.Mul
open Vale.Arch.HeapImpl
open Vale.X64.Machine_s
open Vale.X64.State
module BS = Vale.X64.Machine_Semantics_s
module MS = Vale.X64.Memory_Sems
module ME = Vale.X64.Memory
module VST = Vale.X64.Stack_i
module VSS = Vale.X64.Stack_Sems
module F = FStar.FunctionalExtensionality
friend Vale.X64.Memory

let same_heap_types = ()

let use_machine_state_equal () = ()

#set-options "--max_ifuel 2 --initial_ifuel 2"
let lemma_valid_mem_addr64 h ptr =
  MS.bytes_valid64 ptr (get_vale_heap h);
  MS.lemma_heap_get_heap h;
  ()

let lemma_valid_mem_addr128 h ptr =
  MS.bytes_valid128 ptr (get_vale_heap h);
  MS.lemma_heap_get_heap h;
  ()

let lemma_load_mem_get64 h ptr =
  MS.equiv_load_mem64 ptr (get_vale_heap h);
  MS.lemma_heap_get_heap h;
  ()

let lemma_load_mem_get128 h ptr =
  MS.equiv_load_mem128 ptr (get_vale_heap h);
  MS.lemma_heap_get_heap h;
  ()

//let lemma_valid_buffer_read64 h b i =
//  lemma_valid_mem64 b i h

//let lemma_valid_buffer_read128 h b i =
//  lemma_valid_mem128 b i h

let lemma_load_buffer_read64 h b i =
  lemma_load_mem64 b i h

let lemma_load_buffer_read128 h b i =
  lemma_load_mem128 b i h

#reset-options "--z3rlimit 50"
#restart-solver
let lemma_to_eval_operand s o =
  allow_inversion tmaddr;
  allow_inversion maddr

#reset-options "--initial_fuel 2 --max_fuel 2"

//let lemma_to_eval_xmm s x = ()

//#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 50"
//#restart-solver
//let lemma_to_eval_operand128 s o =
//  allow_inversion tmaddr;
//  allow_inversion maddr
//
//#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 50"
//#restart-solver
//let lemma_to_valid_operand s o =
//  allow_inversion tmaddr;
//  allow_inversion maddr

let lemma_to_of s =
  let open Ms in
  let s' = state_of_S s in
  let s'' = state_to_S s' in
  assert (feq s.ms_regs s''.ms_regs);
  assert (feq s.ms_flags s''.ms_flags);
  VSS.lemma_stack_to_from s.ms_stack;
  ()

