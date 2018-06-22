module Spec.PQ.Lib

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open FStar.Math.Lemmas

let zqelem_t q = x:nat{x < q}
let zqelem #q x = x % q
let zqelem_v #q x = x
let zqadd #q a b = zqelem (a + b)
let zqsub #q a b = zqelem (a + q - b)
let zqmul #q a b = zqelem (a * b)

let zqvector_t q n = lseq (zqelem_t q) n
let zqvector_add #q #n a b =
  let c:zqvector_t q n = create n (zqelem #q 0) in
  repeati n
  (fun i c ->
    c.[i] <- zqadd a.[i] b.[i]
  ) c

let zqvector_sub #q #n a b =
  let c:zqvector_t q n = create n (zqelem #q 0) in
  repeati n
  (fun i c ->
    c.[i] <- zqsub a.[i] b.[i]
  ) c

let zqmatrix_t q n m = lseq (zqvector_t q n) m
let zqmatrix_create q n m = create m (create n (zqelem #q 0))

let get #q #n1 #n2 m i j = (m.[j]).[i]

let set #q #n1 #n2 m i j v =   //(m.[j]).[i] <- v
  let mj = m.[j] in
  let mji = mj.[i] <- v in
  m.[j] <- mji

let zqmatrix_zero #q #n #m = zqmatrix_create q n m

val zqmatrix_pred0:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> f:(zqelem_t q -> zqelem_t q -> zqelem_t q) ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n1 n2 ->
  i0:size_nat{i0 < n1} -> res0:zqmatrix_t q n1 n2 -> j:size_nat{j <= n2} -> res:zqmatrix_t q n1 n2 -> Tot Type0
let zqmatrix_pred0 #q #n1 #n2 f a b i0 res0 j res =
  (forall (j1:size_nat{j1 < j}). get res i0 j1 = f (get a i0 j1) (get b i0 j1)) /\
  (forall (i:size_nat{i < n1 /\ i <> i0}) (j:size_nat{j < n2}). get res0 i j = get res i j)

val zqmatrix_f0:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> f:(zqelem_t q -> zqelem_t q -> zqelem_t q) ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n1 n2 ->
  i0:size_nat{i0 < n1} -> res0:zqmatrix_t q n1 n2 -> Tot (repeatable #(zqmatrix_t q n1 n2) #n2 (zqmatrix_pred0 #q #n1 #n2 f a b i0 res0))
let zqmatrix_f0 #q #n1 #n2 f a b i0 res0 j c = set c i0 j (f (get a i0 j) (get b i0 j))

val zqmatrix_pred1:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> f:(zqelem_t q -> zqelem_t q -> zqelem_t q) ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n1 n2 ->
  i:size_nat{i <= n1} -> res:zqmatrix_t q n1 n2 -> Tot Type0
let zqmatrix_pred1 #q #n1 #n2 f a b i res = forall (i1:size_nat{i1 < i}) (j:size_nat{j < n2}). get res i1 j == f (get a i1 j) (get b i1 j)

val zqmatrix_f1:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> f:(zqelem_t q -> zqelem_t q -> zqelem_t q) ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n1 n2 ->
  Tot (repeatable #(zqmatrix_t q n1 n2) #n1 (zqmatrix_pred1 #q #n1 #n2 f a b))
let zqmatrix_f1 #q #n1 #n2 f a b i c =
  let res =
    repeati_inductive n2
    (zqmatrix_pred0 #q #n1 #n2 f a b i c)
    (fun j cj -> zqmatrix_f0 #q #n1 #n2 f a b i c j cj) c in
  res

let zqmatrix_add #q #n1 #n2 a b =
  let c = zqmatrix_create q n1 n2 in
  repeati_inductive n1
  (zqmatrix_pred1 #q #n1 #n2 zqadd a b)
  (fun i c -> zqmatrix_f1 #q #n1 #n2 zqadd a b i c) c

let zqmatrix_sub #q #n1 #n2 a b =
  let c = zqmatrix_create q n1 n2 in
  repeati_inductive n1
  (zqmatrix_pred1 #q #n1 #n2 zqsub a b)
  (fun i c -> zqmatrix_f1 #q #n1 #n2 zqsub a b i c) c

val zqmatrix_mul_pred0:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> #n3:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n2 n3 ->
  i0:size_nat{i0 < n1} -> res0:zqmatrix_t q n1 n3 -> k:size_nat{k <= n3} -> res:zqmatrix_t q n1 n3 -> Tot Type0
let zqmatrix_mul_pred0 #q #n1 #n2 #n3 a b i0 res0 k res =
  (forall (k1:size_nat{k1 < k}). get res i0 k1 = repeati n2 (fun j tmp -> zqadd tmp (zqmul (get a i0 j) (get b j k1))) 0) /\
  (forall (i:size_nat{i < n1 /\ i <> i0}) (k:size_nat{k < n3}). get res0 i k = get res i k)

val zqmatrix_mul_f0:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> #n3:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n2 n3 ->
  i0:size_nat{i0 < n1} -> res0:zqmatrix_t q n1 n3 -> Tot (repeatable #(zqmatrix_t q n1 n3) #n3 (zqmatrix_mul_pred0 #q #n1 #n2 #n3 a b i0 res0))
let zqmatrix_mul_f0 #q #n1 #n2 #n3 a b i0 res0 k c = set c i0 k (repeati n2 (fun j tmp -> zqadd tmp (zqmul (get a i0 j) (get b j k))) 0)

val zqmatrix_mul_pred1:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> #n3:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n2 n3 ->
  i:size_nat{i <= n1} -> res:zqmatrix_t q n1 n3 -> Tot Type0
let zqmatrix_mul_pred1 #q #n1 #n2 #n3 a b i res =
  forall (i1:size_nat{i1 < i}) (k:size_nat{k < n3}). get res i1 k == repeati n2 (fun j tmp -> zqadd tmp (zqmul (get a i1 j) (get b j k))) 0

val zqmatrix_mul_f1:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> #n3:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n2 n3 ->
  Tot (repeatable #(zqmatrix_t q n1 n3) #n1 (zqmatrix_mul_pred1 #q #n1 #n2 #n3 a b))
let zqmatrix_mul_f1 #q #n1 #n2 #n3 a b i c =
  let res =
    repeati_inductive n3
    (zqmatrix_mul_pred0 #q #n1 #n2 #n3 a b i c)
    (fun k ck -> zqmatrix_mul_f0 #q #n1 #n2 #n3 a b i c k ck) c in
  res

let zqmatrix_mul #q #n1 #n2 #n3 a b =
  let c = zqmatrix_create q n1 n3 in
  repeati_inductive n1
  (zqmatrix_mul_pred1 #q #n1 #n2 #n3 a b)
  (fun i c -> zqmatrix_mul_f1 #q #n1 #n2 #n3 a b i c) c

val matrix_equality:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n1 n2 -> Lemma
  (requires (forall (i:size_nat{i < n1}) (j:size_nat{j < n2}). get a i j == get b i j))
  (ensures  (a == b))
let matrix_equality #q #n1 #n2 a b = admit()

(* Lemmas *)
let matrix_distributivity_add_right #q #n1 #n2 #n3 a b c = admit()
let matrix_distributivity_add_left #q #n1 #n2 #n3 a b c = admit()
let matrix_associativity_mul #q #n1 #n2 #n3 #n4 a b c = admit()

val lemma_zqadd_associativity:
  #q:size_pos -> a:zqelem_t q -> b:zqelem_t q -> c:zqelem_t q -> Lemma
  (requires True)
  (ensures (zqadd (zqadd a b) c == zqadd a (zqadd b c)))
  [SMTPat (zqadd (zqadd a b) c)]
let lemma_zqadd_associativity #q a b c =
  let r = zqadd (zqadd a b) c in
  lemma_mod_plus_distr_l (zqelem_v a + zqelem_v b) (zqelem_v c) q;
  lemma_mod_plus_distr_l (zqelem_v b + zqelem_v c) (zqelem_v a) q

#reset-options "--z3rlimit 50 --max_fuel 0"
let matrix_associativity_add #q #n1 #n2 a b c =
  let r1 = zqmatrix_add a b in
  let r2 = zqmatrix_add r1 c in
  let r3 = zqmatrix_add b c in
  let r4 = zqmatrix_add a r3 in
  matrix_equality r2 r4

let matrix_commutativity_add #q #n1 #n2 a b =
  let r1 = zqmatrix_add a b in
  let r2 = zqmatrix_add b a in
  matrix_equality r1 r2

let matrix_sub_zero #q #n1 #n2 a =
  let r = zqmatrix_sub a a in
  matrix_equality r (zqmatrix_zero #q #n1 #n2)

#reset-options "--z3rlimit 50 --max_fuel 0"
let matrix_add_zero #q #n1 #n2 a =
  let r = zqmatrix_add a (zqmatrix_zero #q #n1 #n2) in
  matrix_equality #q #n1 #n2 r a
