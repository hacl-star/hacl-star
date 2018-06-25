module Spec.PQ.Lib

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

let size_pos = x:size_nat{x > 0}

val zqelem_t:q:size_pos -> Type0
val zqelem:#q:size_pos -> x:nat -> zqelem_t q
val zqelem_v:#q:size_pos -> x:zqelem_t q -> GTot nat
val zqadd:#q:size_pos -> a:zqelem_t q -> b:zqelem_t q -> (r:zqelem_t q{zqelem_v r = (zqelem_v a + zqelem_v b) % q})
val zqsub:#q:size_pos -> a:zqelem_t q -> b:zqelem_t q -> (r:zqelem_t q{zqelem_v r = (zqelem_v a + q - zqelem_v b) % q})
val zqmul:#q:size_pos -> a:zqelem_t q -> b:zqelem_t q -> (r:zqelem_t q{zqelem_v r = (zqelem_v a * zqelem_v b) % q})

val zqvector_t:q:size_pos -> n:size_pos -> Type0
val zqvector_add:#q:size_pos -> #n:size_pos -> a:zqvector_t q n -> b:zqvector_t q n -> c:zqvector_t q n
val zqvector_sub:#q:size_pos -> #n:size_pos -> a:zqvector_t q n -> b:zqvector_t q n -> c:zqvector_t q n

val zqmatrix_t:q:size_pos -> n:size_pos -> m:size_pos -> Type0
val zqmatrix_create:q:size_pos -> n:size_pos -> m:size_pos -> zqmatrix_t q n m
val get:#q:size_pos -> #n1:size_pos -> #n2:size_pos -> m:zqmatrix_t q n1 n2 -> i:size_nat{i < n1} -> j:size_nat{j < n2} -> zqelem_t q
val set:#q:size_pos -> #n1:size_pos -> #n2:size_pos -> m:zqmatrix_t q n1 n2 -> i:size_nat{i < n1} -> j:size_nat{j < n2} -> v:zqelem_t q -> (res:zqmatrix_t q n1 n2{get res i j == v})

val sum:q:size_pos -> n:size_nat -> f:(i:size_nat{i < n} -> zqelem_t q) -> tmp0:zqelem_t q -> zqelem_t q

val zqmatrix_zero:#q:size_pos -> #n1:size_pos -> #n2:size_pos -> Pure (zqmatrix_t q n1 n2)
  (requires True)
  (ensures (fun res -> forall (i:size_nat{i < n1}) (j:size_nat{j < n2}).{:pattern get res i j} get res i j == zqelem #q 0))

val zqmatrix_add:#q:size_pos -> #n1:size_pos -> #n2:size_pos -> a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n1 n2 -> Pure (zqmatrix_t q n1 n2)
  (requires True)
  (ensures (fun res -> forall (i:size_nat{i < n1}) (j:size_nat{j < n2}).{:pattern get res i j} get res i j == zqadd (get a i j) (get b i j)))

val zqmatrix_sub:#q:size_pos -> #n1:size_pos -> #n2:size_pos -> a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n1 n2 -> Pure (zqmatrix_t q n1 n2)
  (requires True)
  (ensures (fun res -> forall (i:size_nat{i < n1}) (j:size_nat{j < n2}).{:pattern get res i j} get res i j == zqsub (get a i j) (get b i j)))

val zqmatrix_mul:#q:size_pos -> #n1:size_pos -> #n2:size_pos -> #n3:size_pos -> a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n2 n3 -> Pure (zqmatrix_t q n1 n3)
  (requires True)
  (ensures (fun res -> forall (i:size_nat{i < n1}) (k:size_nat{k < n3}).{:pattern get res i k} get res i k == sum q n2 (fun j -> zqmul (get a i j) (get b j k)) (zqelem #q 0)))

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
  (zqmatrix_sub a a == zqmatrix_zero #q #n1 #n2)

val matrix_add_zero:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos ->
  a:zqmatrix_t q n1 n2 -> Lemma
  (zqmatrix_add a (zqmatrix_zero #q #n1 #n2) == a)
