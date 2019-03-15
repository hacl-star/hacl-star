module X64.Stack_Sems

open X64.Machine_s
open X64.Stack_i
module S = X64.Bytes_Semantics_s

val stack_to_s: (s:stack) -> Tot S.stack
val stack_from_s: (s:S.stack) -> Tot stack

val lemma_stack_from_to (s:stack) : Lemma 
  (stack_from_s (stack_to_s s) == s)
  [SMTPat (stack_from_s (stack_to_s s))]

val lemma_stack_to_from (s:S.stack) : Lemma 
  (stack_to_s (stack_from_s s) == s)

val equiv_valid_src_stack64: (ptr:int) -> (h:stack) -> Lemma
  (valid_src_stack64 ptr h == S.valid_src_stack64 ptr (stack_to_s h))
  [SMTPat (valid_src_stack64 ptr h)]

val equiv_load_stack64: (ptr:int) -> (h:stack) -> Lemma
  (S.eval_stack ptr (stack_to_s h) == load_stack64 ptr h)
  [SMTPat (load_stack64 ptr h)]

val free_stack_same_load: (start:int) -> (finish:int) -> (ptr:int) -> (h:S.stack) -> Lemma
  (requires S.valid_src_stack64 ptr h /\
    (ptr >= finish \/ ptr + 8 <= start))
  (ensures S.eval_stack ptr h == S.eval_stack ptr (S.free_stack' start finish h))
  [SMTPat (S.eval_stack ptr (S.free_stack' start finish h))]

val equiv_store_stack64: (ptr:int) -> (v:nat64) -> (h:stack) -> Lemma
  (stack_from_s (S.update_stack' ptr v (stack_to_s h)) == store_stack64 ptr v h)
  [SMTPat (store_stack64 ptr v h)]

val equiv_init_rsp: (h:stack) -> Lemma
  (init_rsp h == (stack_to_s h).S.initial_rsp)
  [SMTPat (init_rsp h)]

val equiv_free_stack: (start:int) -> (finish:int) -> (h:stack) -> Lemma
  (free_stack64 start finish h == stack_from_s (S.free_stack' start finish (stack_to_s h)))
  [SMTPat (free_stack64 start finish h)]

val equiv_valid_src_stack128: (ptr:int) -> (h:stack) -> Lemma
  (valid_src_stack128 ptr h == S.valid_src_stack128 ptr (stack_to_s h))
  [SMTPat (valid_src_stack128 ptr h)]

val equiv_load_stack128: (ptr:int) -> (h:stack) -> Lemma
  (S.eval_stack128 ptr (stack_to_s h) == load_stack128 ptr h)
  [SMTPat (load_stack128 ptr h)]

val free_stack_same_load128: (start:int) -> (finish:int) -> (ptr:int) -> (h:S.stack) -> Lemma
  (requires S.valid_src_stack128 ptr h /\
    (ptr >= finish \/ ptr + 16 <= start))
  (ensures S.eval_stack128 ptr h == S.eval_stack128 ptr (S.free_stack' start finish h))
  [SMTPat (S.eval_stack128 ptr (S.free_stack' start finish h))]

val equiv_store_stack128: (ptr:int) -> (v:quad32) -> (h:stack) -> Lemma
  (stack_from_s (S.update_stack128' ptr v (stack_to_s h)) == store_stack128 ptr v h)
  [SMTPat (store_stack128 ptr v h)]
