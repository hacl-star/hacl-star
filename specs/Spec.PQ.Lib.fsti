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

val zqmatrix_zero:#q:size_pos -> #n:size_pos -> #m:size_pos -> zqmatrix_t q n m
val zqmatrix_add:#q:size_pos -> #n:size_pos -> #m:size_pos -> a:zqmatrix_t q n m -> b:zqmatrix_t q n m -> c:zqmatrix_t q n m
val zqmatrix_sub:#q:size_pos -> #n:size_pos -> #m:size_pos -> a:zqmatrix_t q n m -> b:zqmatrix_t q n m -> c:zqmatrix_t q n m
val zqmatrix_mul:#q:size_pos -> #n:size_pos -> #m:size_pos -> #k:size_pos -> a:zqmatrix_t q n m -> b:zqmatrix_t q m k -> c:zqmatrix_t q n k

(* Lemmas *)
val matrix_distributivity_add_right:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> #n3:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n1 n2 -> c:zqmatrix_t q n2 n3 -> Lemma
  (zqmatrix_mul (zqmatrix_add a b) c == zqmatrix_add (zqmatrix_mul a c) (zqmatrix_mul b c))

val matrix_distributivity_add_left:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> #n3:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n1 n2 -> c:zqmatrix_t q n3 n1 -> Lemma
  (zqmatrix_mul c (zqmatrix_add a b) == zqmatrix_add (zqmatrix_mul c a) (zqmatrix_mul c b))

val matrix_associativity_mul:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> #n3:size_pos -> #n4:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n2 n3 -> c:zqmatrix_t q n3 n4 -> Lemma
  (zqmatrix_mul (zqmatrix_mul a b) c == zqmatrix_mul a (zqmatrix_mul b c))

val matrix_associativity_add:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n1 n2 -> c:zqmatrix_t q n1 n2 -> Lemma
  (zqmatrix_add (zqmatrix_add a b) c == zqmatrix_add a (zqmatrix_add b c))

val matrix_commutativity_add:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n1 n2 -> Lemma
  (zqmatrix_add a b == zqmatrix_add b a)

val matrix_sub_zero:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos ->
  a:zqmatrix_t q n1 n2 -> Lemma
  (zqmatrix_sub a a == zqmatrix_zero)

val matrix_add_zero:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos ->
  a:zqmatrix_t q n1 n2 -> Lemma
  (zqmatrix_add a zqmatrix_zero == a)
