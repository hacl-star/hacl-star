module Vale.X64.Stack_Sems
open FStar.Mul

friend Vale.X64.Stack_i

let stack_to_s s = s
let stack_from_s s = s

let lemma_stack_from_to s = ()
let lemma_stack_to_from s = ()

let equiv_valid_src_stack64 ptr h = ()

let equiv_load_stack64 ptr h = ()

let free_stack_same_load start finish ptr h =
  reveal_opaque (`%S.valid_addr64) S.valid_addr64;
  let S.Machine_stack _ mem = h in
  let S.Machine_stack _ mem' = S.free_stack' start finish h in
  Classical.forall_intro (Vale.Lib.Set.remove_between_reveal (Map.domain mem) start finish);
  S.get_heap_val64_reveal ()

let equiv_store_stack64 ptr v h = ()

let store64_same_init_rsp ptr v h = ()

let equiv_init_rsp h = ()

let equiv_free_stack start finish h = ()

let equiv_valid_src_stack128 ptr h = ()

let equiv_load_stack128 ptr h = ()

let free_stack_same_load128 start finish ptr h =
  reveal_opaque (`%S.valid_addr128) S.valid_addr128;
  let S.Machine_stack _ mem = h in
  let S.Machine_stack _ mem' = S.free_stack' start finish h in
  Classical.forall_intro (Vale.Lib.Set.remove_between_reveal (Map.domain mem) start finish);
  S.get_heap_val128_reveal ();
  S.get_heap_val32_reveal ()

let equiv_store_stack128 ptr v h = ()
