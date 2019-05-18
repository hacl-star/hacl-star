module Vale.X64.InsLemmas

open Vale.X64.StateLemmas
open Vale.X64.Taint_Semantics
open Vale.X64.Memory
open Vale.X64.Stack_i

friend Vale.X64.StateLemmas
friend Vale.X64.Decls

let lemma_valid_taint64_operand m t s =
  let tainted_mem:Vale.X64.Memory.memtaint = (state_to_S s).S.ms_memTaint in
  let real_mem:Vale.X64.Memory.mem = s.mem in
  Vale.Lib.Meta.exists_elim2
    (Map.sel tainted_mem (eval_maddr m s) == t)
    ()
    (fun (b:Vale.X64.Memory.buffer64) (index:nat{valid_maddr (eval_maddr m s) real_mem tainted_mem b index t}) ->
      lemma_valid_taint64 b tainted_mem real_mem index t)

let lemma_valid_taint_match64 o s =
  match o with
  | OMem (m, t) ->
    let addr = eval_maddr m s in
    let aux (b:buffer64) (i:int) : Lemma
      (requires valid_maddr addr s.mem s.memTaint b i t)
      (ensures S.taint_match o s.memTaint s.stackTaint (state_to_S s))
      =
      Vale.X64.Memory.lemma_valid_taint64 b s.memTaint s.mem i t
      in
    Classical.forall_intro_2 (fun b i -> (fun b -> Classical.move_requires (aux b)) b i)
  | OStack (m, t) -> lemma_valid_taint_stack64 (eval_maddr m s) t s.stackTaint
  | _ -> ()

let lemma_valid_taint_match128 o s =
  match o with
  | OMem128 (m, t) ->
    let addr = eval_maddr m s in
    let aux (b:buffer128) (i:int) : Lemma
      (requires valid_maddr128 addr s.mem s.memTaint b i t)
      (ensures S.taint_match128 o s.memTaint s.stackTaint (state_to_S s))
      =
      Vale.X64.Memory.lemma_valid_taint128 b s.memTaint s.mem i t
      in
    Classical.forall_intro_2 (fun b i -> (fun b -> Classical.move_requires (aux b)) b i)
  | OStack128 (m, t) -> lemma_valid_taint_stack128 (eval_maddr m s) t s.stackTaint
  | _ -> ()

let instr_norm_lemma (#a:Type) (x:a) : Lemma
  (x == norm [zeta; iota; delta_attr [`%instr_attr]] x)
  =
  ()

