module Vale.PPC64LE.StateLemmas
open Vale.PPC64LE.Memory_Sems
open Vale.PPC64LE.Memory

#reset-options "--initial_fuel 2 --max_fuel 2"

let lemma_to_eval_reg s r = ()
let lemma_to_eval_vec s v = ()
let lemma_to_eval_maddr s m = ()
let lemma_to_eval_cmp_opr s o = ()
let lemma_to_valid_maddr64 s m = ()

let lemma_valid_mem_addr64 h ptr =
  bytes_valid64 ptr (get_vale_heap h);
  lemma_heap_get_heap h;
  ()

let lemma_valid_mem_addr128 h ptr =
  bytes_valid128 ptr (get_vale_heap h);
  lemma_heap_get_heap h;
  ()

let lemma_load_mem_get64 h ptr =
  equiv_load_mem64 ptr (get_vale_heap h);
  lemma_heap_get_heap h;
  ()

let lemma_load_mem_get128 h ptr =
  equiv_load_mem128 ptr (get_vale_heap h);
  lemma_heap_get_heap h;
  ()

let lemma_load_buffer_read64 h b i =
  lemma_load_mem64 b i h

let lemma_load_buffer_read128 h b i =
  lemma_load_mem128 b i h
