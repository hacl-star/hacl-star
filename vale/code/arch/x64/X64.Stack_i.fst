module X64.Stack_i

module BS = X64.Bytes_Semantics_s

let stack = BS.stack

let valid_src_stack64 i st = admit()
let load_stack64 i st = admit()
let store_stack64 i v h = admit()
let free_stack64 start finish h = admit()

let init_rsp h = admit()

(* Lemmas *)
let lemma_store_stack_same_valid64 ptr v h i = admit()

let lemma_free_stack_same_valid64 start finish ptr h = admit()

let lemma_store_new_valid64 ptr v h = admit()

let lemma_correct_store_load_stack64 ptr v h = admit()

let lemma_frame_store_load_stack64 ptr v h i = admit()

let lemma_free_stack_same_load64 start finish ptr h = admit()

let lemma_compose_free_stack64 start inter finish h = admit()

let lemma_same_init_rsp_free_stack64 start finish h = admit()

let lemma_same_init_rsp_store_stack64 ptr v h = admit()
