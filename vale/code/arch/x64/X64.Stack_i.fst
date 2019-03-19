module X64.Stack_i

module BS = X64.Bytes_Semantics_s
open X64.Bytes_Semantics

let stack = BS.stack

let valid_src_stack64 i st = BS.valid_src_stack64 i st
let load_stack64 i st = BS.eval_stack i st
let store_stack64 i v h = BS.update_stack' i v h
let free_stack64 start finish h = BS.free_stack' start finish h

let valid_src_stack128 i st = BS.valid_src_stack128 i st
let load_stack128 i st = BS.eval_stack128 i st
let store_stack128 i v h = BS.update_stack128' i v h

let init_rsp h = h.BS.initial_rsp

(* Lemmas *)
let lemma_store_stack_same_valid64 ptr v h i = Opaque_s.reveal_opaque BS.update_heap64_def

let lemma_free_stack_same_valid64 start finish ptr h =
  let BS.Vale_stack _ mem = h in
  let domain = Map.domain mem in
  Classical.forall_intro (Vale.Set.remove_between_reveal domain start finish)

let lemma_store_new_valid64 ptr v h = Opaque_s.reveal_opaque BS.update_heap64_def

let lemma_correct_store_load_stack64 ptr v h =
  let BS.Vale_stack _ mem = h in
  correct_update_get ptr v mem

let lemma_frame_store_load_stack64 ptr v h i =
  let BS.Vale_stack _ mem = h in
  frame_update_heap ptr v mem;
  Opaque_s.reveal_opaque BS.get_heap_val64_def
  
let lemma_free_stack_same_load64 start finish ptr h =
  let BS.Vale_stack _ mem = h in
  let domain = Map.domain mem in
  Classical.forall_intro (Vale.Set.remove_between_reveal domain start finish);
  Opaque_s.reveal_opaque BS.get_heap_val64_def

let lemma_compose_free_stack64 start inter finish h =
  let BS.Vale_stack _ mem = h in
  let domain = Map.domain mem in
  let map_restr = Map.restrict (Vale.Set.remove_between domain start inter) mem in
  let restrict = Map.domain map_restr in
  let BS.Vale_stack _ mem1 = free_stack64 inter finish (free_stack64 start inter h) in
  let BS.Vale_stack _ mem2 = free_stack64 start finish h in
  let aux (i:int) : Lemma (Map.contains mem1 i = Map.contains mem2 i /\ Map.sel mem1 i = Map.sel mem2 i)
    = Vale.Set.remove_between_reveal domain start inter i;
      Vale.Set.remove_between_reveal restrict inter finish i;
      Vale.Set.remove_between_reveal domain start finish i;
      Vale.Set.lemma_sel_restrict (Vale.Set.remove_between domain start inter) mem i;
      Vale.Set.lemma_sel_restrict (Vale.Set.remove_between restrict inter finish) map_restr i;
      Vale.Set.lemma_sel_restrict (Vale.Set.remove_between domain start finish) mem i
  in Classical.forall_intro aux;
  assert (Map.equal mem1 mem2)
                    
let lemma_same_init_rsp_free_stack64 start finish h = ()

let lemma_same_init_rsp_store_stack64 ptr v h = ()
