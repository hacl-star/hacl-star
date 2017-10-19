module Spec.Lib.IntSeq

open Spec.Lib.IntTypes

val lseq: a:Type0 -> len:size_t -> t:Type0

val create: #a:Type -> len:size_t -> init:a -> lseq a len 
val createL: #a:Type -> l:list a{List.Tot.length l <= maxint U32} -> lseq a (List.Tot.length l)

val repeat: #a:Type -> n:size_t -> (a -> Tot a) -> a -> Tot (a) 
val repeati: #a:Type -> n:size_t -> (i:size_t{i < n}  -> a -> Tot a) -> a -> Tot (a) 
val fold_left: #a:Type -> #b:Type -> #len:size_t -> (a -> b -> Tot b) -> lseq a len -> b -> Tot (b) 
val fold_lefti: #a:Type -> #b:Type -> #len:size_t -> (size_t -> a -> b -> Tot b) -> lseq a len -> b -> Tot (b) 

val map: #a:Type -> #b:Type -> #len:size_t -> (a -> Tot b) -> lseq a len -> lseq b len
val for_all: #a:Type -> #len:size_t -> (a -> Tot bool) -> lseq a len -> bool


val ghost_map: #a:Type -> #b:Type -> #len:size_t -> (a -> GTot b) -> lseq a len -> GTot (lseq b len)

val map2: #a:Type -> #b:Type -> #c:Type -> #len:size_t -> (a -> b -> Tot c) -> lseq a len -> lseq b len -> lseq c len

val for_all2: #a:Type -> #b:Type -> #len:size_t -> (a -> b -> Tot bool) -> lseq a len -> lseq b len -> bool

val index: #a:Type -> #len:size_t{len > 0} -> lseq a len -> n:size_t{n < len} -> a

val upd: #a:Type -> #len:size_t -> lseq a len -> n:size_t{n < len /\ len > 0} -> x:a -> lseq a len

val sub: #a:Type -> #len:size_t -> lseq a len -> start:size_t -> n:size_t{start + n <= len} -> lseq a n

val slice: #a:Type -> #len:size_t -> lseq a len -> start:size_t -> fin:size_t{start <= fin /\ fin <= len} -> lseq a (fin - start)

val update_sub: #a:Type -> #len:size_t -> lseq a len -> start:size_t -> n:size_t{start + n <= len} -> lseq a n -> lseq a len

val update_slice: #a:Type -> #len:size_t -> lseq a len -> start:size_t -> fin:size_t{start <= fin /\ fin <= len} -> lseq a (fin - start) -> lseq a len

type intseq (t:inttype) (len:size_t) = lseq (uint_t t) len

val nat_from_intseq_be:#t:inttype -> #len:size_t -> b:intseq t len -> Tot (n:nat{n < pow2 (len `op_Multiply` bits t)})
val nat_from_intseq_le:#t:inttype -> #len:size_t -> b:intseq t len -> Tot (n:nat{n < pow2 (len `op_Multiply` bits t)})
val nat_to_bytes_le:
  len:size_t -> n:nat{n < pow2 (8 `op_Multiply` len)} ->  Tot (b:intseq U8 len {n == nat_from_intseq_le #U8 #len b})

val uint_to_bytes_le: #t:inttype -> u:uint_t t -> intseq U8 (numbytes t)

val uint_to_bytes_be: #t:inttype -> u:uint_t t -> intseq U8 (numbytes t)

val uint_from_bytes_le: #t:inttype -> intseq U8 (numbytes t) -> u:uint_t t 
val uint_from_bytes_be: #t:inttype -> intseq U8 (numbytes t) -> u:uint_t t 
