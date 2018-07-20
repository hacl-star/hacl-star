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

val extensionality:
  #n1:size_nat ->
  #n2:size_nat{n1 * n2 < max_size_t} ->
  a:matrix_t n1 n2 ->
  b:matrix_t n1 n2 ->
  Lemma
    (requires forall i j. a.(i, j) == b.(i, j))
    (ensures  a == b)
let extensionality #n1 #n2 a b =
  Classical.forall_intro_2 (Spec.Frodo.Lemmas.lemma_matrix_index n1 n2);
  assert (forall (i:size_nat{i < n1}) (j:size_nat{j < n2}). a.(i, j) == a.[i * n2 + j]);
  assert (forall (i:size_nat{i < n1}) (j:size_nat{j < n2}). b.(i, j) == b.[i * n2 + j]);
  assert (forall (i:size_nat{i < n1}) (j:size_nat{j < n2}). a.[i * n2 + j] == b.[i * n2 + j]);
  assume (forall (k:size_nat{k < n1 * n2}). a.[k] == b.[k]);
  eq_intro a b

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

val sum_:
  n:size_nat -> f:(j:size_nat{j < n} -> uint16) ->
  tmp0:uint16 -> i:size_nat{i <= n} -> Tot uint16
  (decreases (n - i))
let rec sum_ n f tmp0 i =
  if (i < n) then
    sum_ n f (tmp0 +. f i) (i + 1)
  else tmp0

let sum n f = sum_ n f (u16 0) 0

val matrix_mul_inner:
  #n1:size_nat ->
  #n2:size_nat{n1 * n2 < max_size_t} ->
  #n3:size_nat{n1 * n3 < max_size_t /\ n2 * n3 < max_size_t} ->
  a:matrix_t n1 n2 ->
  b:matrix_t n2 n3 ->
  c:matrix_t n1 n3 ->
  i:size_nat{i < n1} ->
  k:size_nat{k < n3} -> Pure (matrix_t n1 n3)
  (requires True)
  (ensures fun c1 -> 
    c1.(i, k) == sum n2 (fun j -> a.(i, j) *. b.(j, k)) /\ 
    (forall (i1:size_nat{i1 < n1 /\ i1 <> i}) (k1:size_nat{k1 < n3 /\ k1 <> k}). c1.(i1, k1) == c.(i1, k1)))
let matrix_mul_inner #n1 #n2 #n3 a b c i k =
  let c = c.(i, k) <- u16 0 in
  repeati_inductive n2
  (fun j c1 -> c1.(i, k) == sum j (fun j -> a.(i, j) *. b.(j, k)) /\ 
            (forall (i1:size_nat{i1 < n1 /\ i1 <> i}) (k1:size_nat{k1 < n3 /\ k1 <> k}). c1.(i1, k1) == c.(i1, k1)))
  (fun j c ->
    assert (c.(i, k) == sum j (fun j -> a.(i, j) *. b.(j, k)));
    let c1 = c.(i, k) <- c.(i, k) +. a.(i, j) *. b.(j, k) in
    assert (c1.(i, k) == sum j (fun j -> a.(i, j) *. b.(j, k)) +. a.(i, j) *. b.(j, k));
    assume (c1.(i, k) == sum (j + 1) (fun j -> a.(i, j) *. b.(j, k)));
    c1
  ) c
  
val matrix_mul:
  #n1:size_nat ->
  #n2:size_nat{n1 * n2 < max_size_t} ->
  #n3:size_nat{n1 * n3 < max_size_t /\ n2 * n3 < max_size_t} ->
  a:matrix_t n1 n2 ->
  b:matrix_t n2 n3 ->
  Tot (c:matrix_t n1 n3{ forall i k. c.(i, k) == sum n2 (fun j -> a.(i, j) *. b.(j, k))})
  #reset-options "--z3rlimit 150 --max_fuel 0"
let matrix_mul #n1 #n2 #n3 a b =
  let c = matrix_create n1 n3 in
  repeati_inductive n1
  (fun i c -> forall (i1:size_nat{i1 < i}) (k:size_nat{k < n3}). c.(i1, k) == sum n2 (fun j -> a.(i1, j) *. b.(j, k)))
  (fun i c ->
    repeati_inductive n3
    (fun k c0 -> (forall (k1:size_nat{k1 < k}). c0.(i, k1) == sum n2 (fun j -> a.(i, j) *. b.(j, k1))) /\
               (forall (i1:size_nat{i1 < n1 /\ i <> i1}) (k:size_nat{k < n3}). c0.(i1, k) == c.(i1, k)))
    (fun k c0 ->
      let c1 = matrix_mul_inner #n1 #n2 #n3 a b c0 i k in
      assume (forall (k1:size_nat{k1 < k + 1}). c1.(i, k1) == sum n2 (fun j -> a.(i, j) *. b.(j, k1)) /\
      (forall (i1:size_nat{i1 < n1 /\ i <> i1}) (k:size_nat{k < n3}). c1.(i1, k) == c.(i1, k)));
      //admit();
      //let c12 = c0.(i, k) <- sum n2 (fun j -> a.(i, j) *. b.(j, k)) in
      //let c1 = c0.(i, k) <- sum n2 (fun j -> a.(i, j) *. b.(j, k)) in
      //assume (c1 == c12); // /\ (forall (i1:size_nat{i1 < n1 /\ i1 <> i}) (k1:size_nat{k1 < n3 /\ k1 <> k}). c1.(i1, k1) == c0.(i1, k1)));
      c1
    ) c
  ) c
