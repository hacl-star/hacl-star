module Spec.Frodo.Matrix.LL

open FStar.Mul
open FStar.Math.Lemmas

open Lib.IntTypes
open Lib.Sequence

type numeric_t = uint16

type matrix_t (n1:size_nat) (n2:size_nat{n1 * n2 < max_size_t}) = lseq uint16 (n1 * n2)

val matrix_create:
  n1:size_nat -> n2:size_nat{n1 * n2 < max_size_t} -> matrix_t n1 n2
let matrix_create n1 n2 = create (n1 * n2) (u16 0)

val mget:
  #n1:size_nat ->
  #n2:size_nat{n1 * n2 < max_size_t} ->
  a:matrix_t n1 n2 ->
  i:size_nat{i < n1} ->
  j:size_nat{j < n2} -> uint16
let mget #n1 #n2 a i j =
  Spec.Frodo.Lemmas.lemma_matrix_index n1 n2 i j;
  a.[i * n2 + j]

val mset:
  #n1:size_nat ->
  #n2:size_nat{n1 * n2 < max_size_t} ->
  a:matrix_t n1 n2 ->
  i:size_nat{i < n1} ->
  j:size_nat{j < n2} ->
  v:uint16 ->
  Pure (matrix_t n1 n2)
    (requires True)
    (ensures (fun res -> mget res i j == v /\ (forall (i1:size_nat{i1 < n1}) (j1:size_nat{j1 < n2}). (i1, j1) <> (i, j) ==> mget res i1 j1 == mget a i1 j1)))
let mset #n1 #n2 a i j v =
  Spec.Frodo.Lemmas.lemma_matrix_index n1 n2 i j;
  Classical.forall_intro_2 (Spec.Frodo.Lemmas.index_neq #n1 #n2 i j);
  a.[i * n2 + j] <- v

let op_Array_Access (#n1:size_nat) (#n2:size_nat{n1 * n2 < max_size_t}) (m:matrix_t n1 n2) (i,j) = mget m i j
let op_Array_Assignment (#n1:size_nat) (#n2:size_nat{n1 * n2 < max_size_t}) (m:matrix_t n1 n2) (i,j) x = mset m i j x

val matrix_map2:
  #n1:size_nat ->
  #n2:size_nat{n1 * n2 < max_size_t} ->
  f:(numeric_t -> numeric_t -> numeric_t) ->
  a:matrix_t n1 n2 ->
  b:matrix_t n1 n2 ->
  c:matrix_t n1 n2{ forall i j. c.(i,j) == f a.(i,j) b.(i,j) }
let matrix_map2 #n1 #n2 f a b =
  let c = matrix_create n1 n2 in
  repeati_inductive n1
  (fun i c -> forall (i0:size_nat{i0 < i}) (j:size_nat{j < n2}). c.(i0, j) == f a.(i0, j) b.(i0, j))
  (fun i c ->
    repeati_inductive n2
    (fun j c0 -> (forall (i0:size_nat{i0 < i}) (j:size_nat{j < n2}). c0.(i0, j) == c.(i0, j)) /\
	       (forall (j0:size_nat{j0 < j}). c0.(i, j0) == f a.(i, j0) b.(i, j0)))
    (fun j c0 -> c0.(i,j) <- f a.(i,j) b.(i,j)
    ) c
  ) c

val matrix_add:
  #n1:size_nat ->
  #n2:size_nat{n1 * n2 < max_size_t} ->
  a:matrix_t n1 n2 ->
  b:matrix_t n1 n2 ->
  Tot (c:matrix_t n1 n2{ forall i j. c.(i,j) == a.(i,j) +. b.(i,j) })
let matrix_add #n1 #n2 a b =
  matrix_map2 (add_mod) a b

val matrix_sub:
  #n1:size_nat ->
  #n2:size_nat{n1 * n2 < max_size_t} ->
  a:matrix_t n1 n2 ->
  b:matrix_t n1 n2 ->
  Tot (c:matrix_t n1 n2{ forall i j. c.(i,j) == a.(i,j) -. b.(i,j) })
let matrix_sub #n1 #n2 a b =
  matrix_map2 (sub_mod) a b

(*
val matrix_mul:
  #n1:size_nat ->
  #n2:size_nat{n1 * n2 < max_size_t} ->
  #n3:size_nat{n1 * n3 < max_size_t /\ n2 * n3 < max_size_t} ->
  a:matrix_t n1 n2 ->
  b:matrix_t n2 n3 ->
  Tot (matrix_t n1 n3)
let matrix_mul #n1 #n2 #n3 a b =
  let c = matrix_create n1 n3 in
  repeati n1
  (fun i c ->
    repeati n3
    (fun k c ->
      repeati n2
      (fun j c ->
	mset c i k (add_mod (mget c i k) (mul_mod (mget a i j) (mget b j k)))
      ) c
    ) c
  ) c
*)

val sum_:
  n:size_nat -> f:(j:size_nat{j < n} -> uint16) ->
  tmp0:uint16 -> i:size_nat{i <= n} -> Tot uint16
  (decreases (n - i))
let rec sum_ n f tmp0 i =
  if (i < n) then
    sum_ n f (tmp0 +. f i) (i + 1)
  else tmp0

let sum n f tmp0 = sum_ n f tmp0 0

val matrix_mul:
  #n1:size_nat ->
  #n2:size_nat{n1 * n2 < max_size_t} ->
  #n3:size_nat{n1 * n3 < max_size_t /\ n2 * n3 < max_size_t} ->
  a:matrix_t n1 n2 ->
  b:matrix_t n2 n3 ->
  Tot (c:matrix_t n1 n3{ forall i k. c.(i, k) == sum n2 (fun j -> a.(i, j) *. b.(j, k)) (u16 0) })
let matrix_mul #n1 #n2 #n3 a b =
  let c = matrix_create n1 n3 in
  repeati_inductive n1
  (fun i c -> forall (i1:size_nat{i1 < i}) (k:size_nat{k < n3}). c.(i1, k) == sum n2 (fun j -> a.(i1, j) *. b.(j, k)) (u16 0))
  (fun i c ->
    repeati_inductive n3
    (fun k c0 -> (forall (k1:size_nat{k1 < k}). c0.(i, k1) == sum n2 (fun j -> a.(i, j) *. b.(j, k1)) (u16 0)) /\
               (forall (i1:size_nat{i1 < n1 /\ i <> i1}) (k:size_nat{k < n3}). c0.(i1, k) == c.(i1, k)))
    (fun k c0 -> c0.(i, k) <- sum n2 (fun j -> a.(i, j) *. b.(j, k)) (u16 0)
    ) c
  ) c
