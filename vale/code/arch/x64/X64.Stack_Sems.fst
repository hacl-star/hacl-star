module X64.Stack_Sems

let stack_to_s s = admit()
let stack_from_s s = admit()

let lemma_stack_from_to s = admit()
let lemma_stack_to_from s = admit()

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
