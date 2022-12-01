module Vale.PPC64LE.StateLemmas
open FStar.Mul
open Vale.PPC64LE.Machine_s
open Vale.PPC64LE.State
open Vale.PPC64LE.Memory
open Vale.Arch.HeapImpl
open Vale.Arch.Heap
module S = Vale.PPC64LE.Semantics_s

val lemma_to_eval_reg : s:state -> r:reg -> Lemma
  (ensures eval_reg r s == S.eval_reg r s)
  [SMTPat (eval_reg r s)]

val lemma_to_eval_vec : s:state -> v:vec -> Lemma
  (ensures eval_vec v s == S.eval_vec v s)
  [SMTPat (eval_vec v s)]

val lemma_to_eval_maddr : s:state -> m:maddr -> Lemma
  (ensures eval_maddr m s == S.eval_maddr m s)
  [SMTPat (eval_maddr m s)]

val lemma_to_eval_cmp_opr : s:state -> o:cmp_opr -> Lemma
  (ensures eval_cmp_opr o s == S.eval_cmp_opr o s)
  [SMTPat (eval_cmp_opr o s)]

val lemma_valid_mem_addr64 (h:vale_full_heap) (ptr:int) : Lemma
  (requires valid_mem64 ptr (get_vale_heap h))
  (ensures S.valid_addr64 ptr (heap_get (coerce h)))
  [SMTPat (valid_mem64 ptr (get_vale_heap h))]

val lemma_valid_mem_addr128 (h:vale_full_heap) (ptr:int) : Lemma
  (requires valid_mem128 ptr (get_vale_heap h))
  (ensures S.valid_addr128 ptr (heap_get (coerce h)))
  [SMTPat (valid_mem128 ptr (get_vale_heap h))]

val lemma_load_mem_get64 (h:vale_full_heap) (ptr:int) : Lemma
  (requires valid_mem64 ptr (get_vale_heap h))
  (ensures load_mem64 ptr (get_vale_heap h) == S.get_heap_val64 ptr (heap_get (coerce h)))
  [SMTPat (load_mem64 ptr (get_vale_heap h))]

val lemma_load_mem_get128 (h:vale_full_heap) (ptr:int) : Lemma
  (requires valid_mem128 ptr (get_vale_heap h))
  (ensures load_mem128 ptr (get_vale_heap h) == S.get_heap_val128 ptr (heap_get (coerce h)))
  [SMTPat (load_mem128 ptr (get_vale_heap h))]

val lemma_load_buffer_read64 (h:vale_heap) (b:buffer64) (i:int) : Lemma
  (requires valid_buffer_read h b i)
  (ensures buffer_read b i h == load_mem64 (buffer_addr b h + 8 * i) h)
  [SMTPat (buffer_read b i h)]

val lemma_load_buffer_read128 (h:vale_heap) (b:buffer128) (i:int) : Lemma
  (requires valid_buffer_read h b i)
  (ensures buffer_read b i h == load_mem128 (buffer_addr b h + 16 * i) h)
  [SMTPat (buffer_read b i h)]
