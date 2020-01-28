module Vale.X64.InsLemmas

open FStar.Mul
open Vale.Arch.HeapTypes_s
open Vale.Arch.HeapImpl
open Vale.X64.StateLemmas
open Vale.X64.Taint_Semantics
open Vale.X64.Memory
open Vale.X64.Stack_i
open Vale.X64.Memory_Sems

friend Vale.X64.Decls

let lemma_valid_src_operand64_and_taint o s =
  let h = get_vale_heap s.vs_heap in
  match o with
  | OMem (m, t) ->
    let addr = eval_maddr m s in
    let aux (b:buffer64) (i:int) : Lemma
      (requires valid_buf_maddr64 addr h s.vs_heap.vf_layout b i t)
      (ensures S.valid_src_operand64_and_taint o (state_to_S s))
      =
      lemma_heap_get_heap s.vs_heap;
      lemma_valid_taint64 b (full_heap_taint s.vs_heap) h i t
      in
    Classical.forall_intro_2 (fun b i -> (fun b -> Classical.move_requires (aux b)) b i)
  | OStack (m, t) -> lemma_valid_taint_stack64 (eval_maddr m s) t s.vs_stackTaint
  | _ -> ()

let lemma_valid_src_operand128_and_taint o s =
  let h = get_vale_heap s.vs_heap in
  match o with
  | OMem (m, t) ->
    let addr = eval_maddr m s in
    let aux (b:buffer128) (i:int) : Lemma
      (requires valid_buf_maddr128 addr h s.vs_heap.vf_layout b i t)
      (ensures S.valid_src_operand128_and_taint o (state_to_S s))
      =
      lemma_heap_get_heap s.vs_heap;
      lemma_valid_taint128 b (full_heap_taint s.vs_heap) h i t
      in
    Classical.forall_intro_2 (fun b i -> (fun b -> Classical.move_requires (aux b)) b i)
  | OStack (m, t) -> lemma_valid_taint_stack128 (eval_maddr m s) t s.vs_stackTaint
  | _ -> ()

let instr_norm_lemma (#a:Type) (x:a) : Lemma
  (x == norm [zeta; iota; delta_attr [`%instr_attr]] x)
  =
  ()

