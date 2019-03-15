module X64.Stack_Sems

friend X64.Stack_i

let stack_to_s s = s
let stack_from_s s = s

let lemma_stack_from_to s = ()
let lemma_stack_to_from s = ()

let equiv_valid_src_stack64 ptr h = admit()

let equiv_load_stack64 ptr h = admit()

let free_stack_same_load start finish ptr h =
  let S.Vale_stack _ mem = h in
  let S.Vale_stack _ mem' = S.free_stack' start finish h in
  Classical.forall_intro (Vale.Set.remove_between_reveal (Map.domain mem) start finish);
  Opaque_s.reveal_opaque S.get_heap_val64_def

let equiv_store_stack64 ptr v h = admit()

let store64_same_init_rsp ptr v h = admit()

let equiv_init_rsp h = admit()

let equiv_free_stack start finish h = admit()
