module X64.Memory_Sems

open Prop_s
open X64.Machine_s
open X64.Memory
module S = X64.Bytes_Semantics_s

val same_domain: (h:mem) -> (m:S.heap) -> prop0

val lemma_same_domains: (h:mem) -> (m1:S.heap) -> (m2:S.heap) -> Lemma
  (requires same_domain h m1 /\ Set.equal (Map.domain m1) (Map.domain m2))
  (ensures same_domain h m2)

val get_heap: (h:mem) -> GTot (m:S.heap{same_domain h m})

val get_hs: (h:mem) -> (m:S.heap{same_domain h m}) -> GTot (h':mem)

val get_hs_heap: (h:mem) -> Lemma (get_hs h (get_heap h) == h)
  [SMTPat (get_hs h (get_heap h))]

val get_heap_hs: (m:S.heap) -> (h:mem{same_domain h m}) -> Lemma
  (requires (forall x. not (Map.contains m x) ==> Map.sel m x == Map.sel (get_heap h) x))
  (ensures get_heap (get_hs h m) == m)

val bytes_valid (i:int) (m:mem) : Lemma
  (requires valid_mem64 i m)
  (ensures S.valid_addr64 i (get_heap m))
  [SMTPat (S.valid_addr64 i (get_heap m))]

val bytes_valid128 (i:int) (m:mem) : Lemma
  (requires valid_mem128 i m)
  (ensures S.valid_addr128 i (get_heap m))
  [SMTPat (S.valid_addr128 i (get_heap m))]

val equiv_load_mem: ptr:int -> m:mem -> Lemma
  (requires valid_mem64 ptr m)
  (ensures load_mem64 ptr m == S.get_heap_val64 ptr (get_heap m))

val low_lemma_valid_mem64: b:buffer64 -> i:nat -> h:mem -> Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    S.valid_addr64 (buffer_addr b h + 8 `op_Multiply` i) (get_heap h)
  )

val low_lemma_load_mem64 : b:buffer64 -> i:nat -> h:mem -> Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    S.get_heap_val64 (buffer_addr b h + 8 `op_Multiply` i) (get_heap h) == buffer_read b i h
  )

val same_domain_update64: b:buffer64 -> i:nat -> v:nat64 -> h:mem -> Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures same_domain h (S.update_heap64 (buffer_addr b h + 8 `op_Multiply` i) v (get_heap h)))

val low_lemma_store_mem64 : b:buffer64 -> i:nat-> v:nat64 -> h:mem -> Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b
  )
  (ensures (
    same_domain_update64 b i v h;
    get_hs h (S.update_heap64 (buffer_addr b h + 8 `op_Multiply` i) v (get_heap h)) == buffer_write b i v h)
  )

val low_lemma_valid_mem128: b:buffer128 -> i:nat -> h:mem -> Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    S.valid_addr128 (buffer_addr b h + 16 `op_Multiply` i) (get_heap h)
  )

val equiv_load_mem128: ptr:int -> m:mem -> Lemma
  (requires valid_mem128 ptr m)
  (ensures load_mem128 ptr m == S.get_heap_val128 ptr (get_heap m))

val low_lemma_load_mem128 : b:buffer128 -> i:nat -> h:mem -> Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    S.get_heap_val128 (buffer_addr b h + 16 `op_Multiply` i) (get_heap h) == buffer_read b i h
  )

val same_domain_update128: b:buffer128 -> i:nat -> v:quad32 -> h:mem -> Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures same_domain h (S.update_heap128 (buffer_addr b h + 16 `op_Multiply` i) v (get_heap h)))

val low_lemma_store_mem128 : b:buffer128 -> i:nat-> v:quad32 -> h:mem -> Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b
  )
  (ensures (
    same_domain_update128 b i v h;
    get_hs h (S.update_heap128 (buffer_addr b h + 16 `op_Multiply` i) v (get_heap h)) == buffer_write b i v h)
  )

val low_lemma_valid_mem128_64: b:buffer128 -> i:nat -> h:mem -> Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    S.valid_addr64 (buffer_addr b h + 16 `op_Multiply` i) (get_heap h) /\
    S.valid_addr64 (buffer_addr b h + 16 `op_Multiply` i + 8) (get_heap h)    
  )

open Arch.Types

val low_lemma_load_mem128_lo64 : b:buffer128 -> i:nat -> h:mem -> Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    S.get_heap_val64 (buffer_addr b h + 16 `op_Multiply` i) (get_heap h) == 
      lo64 (buffer_read b i h)
  )

val low_lemma_load_mem128_hi64 : b:buffer128 -> i:nat -> h:mem -> Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    S.get_heap_val64 (buffer_addr b h + 16 `op_Multiply` i + 8) (get_heap h) == 
      hi64 (buffer_read b i h)
  )

val same_domain_update128_64: b:buffer128 -> i:nat -> v:nat64 -> h:mem -> Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures 
    same_domain h (S.update_heap64 (buffer_addr b h + 16 `op_Multiply` i) v (get_heap h)) /\
    same_domain h (S.update_heap64 (buffer_addr b h + 16 `op_Multiply` i + 8) v (get_heap h))    
  )


val low_lemma_store_mem128_lo64 : b:buffer128 -> i:nat-> v:nat64 -> h:mem -> Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b
  )
  (ensures (
    let v' = insert_nat64_opaque (buffer_read b i h) v 0 in
    same_domain_update128_64 b i v h;
    get_hs h (S.update_heap64 (buffer_addr b h + 16 `op_Multiply` i) v (get_heap h)) == buffer_write b i v' h)
  )

val low_lemma_store_mem128_hi64 : b:buffer128 -> i:nat-> v:nat64 -> h:mem -> Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b
  )
  (ensures (
    let v' = insert_nat64_opaque (buffer_read b i h) v 1 in
    same_domain_update128_64 b i v h;
    get_hs h (S.update_heap64 (buffer_addr b h + 16 `op_Multiply` i + 8) v (get_heap h)) == buffer_write b i v' h)
  )
