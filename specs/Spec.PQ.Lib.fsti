module Spec.PQ.Lib

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

let size_pos = x:size_nat{x > 0}

val zqelem_t:q:size_pos -> Type0
val zqvector_t:q:size_pos -> n:size_pos -> Type0
val zqmatrix_t:q:size_pos -> n:size_pos -> m:size_pos -> Type0

val zqelem:#q:size_pos -> x:nat -> zqelem_t q
val zqadd:#q:size_pos -> a:zqelem_t q -> b:zqelem_t q -> zqelem_t q
val zqsub:#q:size_pos -> a:zqelem_t q -> b:zqelem_t q -> zqelem_t q
val zqmul:#q:size_pos -> a:zqelem_t q -> b:zqelem_t q -> zqelem_t q

val zqvector_add:#q:size_pos -> #n:size_pos -> a:zqvector_t q n -> b:zqvector_t q n -> c:zqvector_t q n
val zqvector_sub:#q:size_pos -> #n:size_pos -> a:zqvector_t q n -> b:zqvector_t q n -> c:zqvector_t q n

val zqmatrix_add:#q:size_pos -> #n:size_pos -> #m:size_pos -> a:zqmatrix_t q n m -> b:zqmatrix_t q n m -> c:zqmatrix_t q n m
val zqmatrix_sub:#q:size_pos -> #n:size_pos -> #m:size_pos -> a:zqmatrix_t q n m -> b:zqmatrix_t q n m -> c:zqmatrix_t q n m
val zqmatrix_mul:#q:size_pos -> #n:size_pos -> #m:size_pos -> #k:size_pos -> a:zqmatrix_t q n m -> b:zqmatrix_t q m k -> c:zqmatrix_t q n k
