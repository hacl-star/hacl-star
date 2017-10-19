module Spec.Lib.IntSeq

open Spec.Lib.IntTypes

val lseq: a:Type0 -> len:size_t -> Type0
val create: #a:Type -> len:size_t -> init:a -> lseq a len 
val createL: #a:Type -> l:list a{List.Tot.length l <= maxint U32} -> lseq a (nat_to_size (List.Tot.length l))
val map: #a:Type -> #b:Type -> #len:size_t -> (a -> Tot b) -> lseq a len -> lseq b len

val ghost_map: #a:Type -> #b:Type -> #len:size_t -> (a -> GTot b) -> lseq a len -> GTot (lseq b len)

val map2: #a:Type -> #b:Type -> #c:Type -> #len:size_t -> (a -> b -> Tot c) -> lseq a len -> lseq b len -> lseq c len

val index: #a:Type -> #len:size_t{size_to_nat len > 0} -> lseq a len -> n:size_t{size_to_nat n < size_to_nat len} -> a

val upd: #a:Type -> #len:size_t -> lseq a len -> n:size_t{size_to_nat n < size_to_nat len /\ size_to_nat len > 0} -> x:a -> lseq a len

val slice: #a:Type -> #len:size_t -> lseq a len -> start:size_t -> n:size_t{size_to_nat start + size_to_nat n <= size_to_nat len} -> lseq a n

val update_slice: #a:Type -> #len:size_t -> lseq a len -> start:size_t -> n:size_t{size_to_nat start + size_to_nat n <= size_to_nat len} -> lseq a n -> lseq a len

type intseq (t:inttype) (len:size_t) = lseq (uint_t t) len

val uint_to_bytes_le: #t:inttype -> u:uint_t t -> intseq U8 (nat_to_size (size t))

val uint_to_bytes_be: #t:inttype -> u:uint_t t -> intseq U8 (nat_to_size (size t))

val uint_from_bytes_le: #t:inttype -> intseq U8 (nat_to_size (size t)) -> u:uint_t t 
val uint_from_bytes_be: #t:inttype -> intseq U8 (nat_to_size (size t)) -> u:uint_t t 
