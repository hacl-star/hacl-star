module Spec.Lib.IntSeq.Lemmas

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

val create_index: #a:Type -> len:size_t -> init:a -> i:size_t{i < len} -> Lemma
		  (requires True)
		  (ensures (index (create len init) i == init))
		  [SMTPat (index (create len init) i)]


val createL_index: #a:Type -> l:list a{List.Tot.length l <= maxint U32} -> i:size_t{i < List.Tot.length l} -> Lemma
		  (requires True)
		  (ensures (index (createL l) i) == List.Tot.index l i)
		  [SMTPat (index (createL l) i)]

val upd_index: #a:Type -> #len:size_t -> s:lseq a len -> i:size_t{i < len /\ len > 0} -> x:a -> j:size_t{j < len} -> Lemma
		  (requires True)
		  (ensures (index (upd s i x) j == (if i = j then x else index s j)))
		  [SMTPat (index (upd s i x) j)]

val sub_index: #a:Type -> #len:size_t -> s:lseq a len -> start:size_t -> n:size_t{start + n <= len} -> i:size_t{i < n} -> Lemma
		  (requires True)
		  (ensures (index (sub s start n) i == index s (start + i)))
		  [SMTPat (index (sub s start n) i)]

val slice_index: #a:Type -> #len:size_t -> s:lseq a len -> start:size_t -> fin:size_t{start <= fin /\ fin <= len} -> i:size_t{i < fin - start} -> Lemma
		  (requires True)
		  (ensures (index (slice s start fin) i == index s (start + i)))
		  [SMTPat (index (slice s start fin) i)]

val update_sub_index: #a:Type -> #len:size_t -> s:lseq a len -> start:size_t -> n:size_t{start + n <= len} -> x:lseq a n -> i:size_t{i < n} -> Lemma
		  (requires True)
		  (ensures (index (update_sub s start n x) i == 
			    (if i < start then index s i else
			     if i >= start + n then index s i else
			     index x (i - start))))
		  [SMTPat (index (update_sub s start n x) i )]

val update_slice_index: #a:Type -> #len:size_t -> s:lseq a len -> start:size_t -> fin:size_t{start <= fin /\ fin <= len} -> x:lseq a (fin - start) -> i:size_t{i < fin - start} -> Lemma
		  (requires True)
		  (ensures (index (update_slice s start fin x) i == 
			    (if i < start then index s i else
			     if i >= fin then index s i else
			     index x (i - start))))
		  [SMTPat (index (update_slice s start fin x) i )]

val map_index: #a:Type -> #b:Type -> #len:size_t -> f:(a -> Tot b) -> s:lseq a len -> i:size_t{i < len} -> Lemma 
		  (requires True)
		  (ensures (index (map f s) i == f (index s i)))
		  [SMTPat (index (map f s) i)]

val map2_index: #a:Type -> #b:Type -> #c:Type -> #len:size_t -> f:(a -> b ->  Tot c) -> s1:lseq a len -> s2:lseq b len -> i:size_t{i < len} -> Lemma 
		  (requires True)
		  (ensures (index (map2 f s1 s2) i == f (index s1 i) (index s2 i)))
		  [SMTPat (index (map2 f s1 s2) i)]



