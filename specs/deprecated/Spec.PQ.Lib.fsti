module Spec.PQ.Lib

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

//let size_pos = x:size_nat{x > 0}

type numeric_t = inttype
val numeric:#t:inttype -> x:nat{x <= maxint t} -> uint_t t
val to_numeric:#t:inttype -> t1:inttype -> x:uint_t t -> r:uint_t t1{uint_v r == uint_v x % modulus t1}

val vector_t:t:numeric_t -> len:size_nat -> Type0
val vector_create:t:numeric_t -> len:size_nat -> vector_t t len
val vget:#t:numeric_t -> #len:size_nat -> a:vector_t t len -> i:size_nat{i < len} -> uint_t t
val vset:#t:numeric_t -> #len:size_nat -> a:vector_t t len -> i:size_nat{i < len} -> v:uint_t t -> Pure (vector_t t len)
  (requires True)
  (ensures (fun res -> vget res i == v /\ (forall (j:size_nat). j < len /\ j <> i ==> vget res j == vget a j)))

val vector_zero:#t:numeric_t -> #len:size_nat -> Pure (vector_t t len)
  (requires True)
  (ensures (fun res -> forall (i:size_nat{i < len}).{:pattern vget res i} vget res i == numeric #t 0))

val vector_add:#t:numeric_t -> #len:size_nat -> a:vector_t t len -> b:vector_t t len -> Pure (vector_t t len)
  (requires True)
  (ensures (fun res -> forall (i:size_nat{i < len}).{:pattern vget res i} vget res i == vget a i +. vget b i))

val vector_sub:#t:numeric_t -> #len:size_nat -> a:vector_t t len -> b:vector_t t len -> Pure (vector_t t len)
  (requires True)
  (ensures (fun res -> forall (i:size_nat{i < len}).{:pattern vget res i} vget res i == vget a i -. vget b i))

val vector_pointwise_mul:#t:numeric_t -> #len:size_nat -> a:vector_t t len -> b:vector_t t len -> Pure (vector_t t len)
  (requires (t <> U128))
  (ensures (fun res -> forall (i:size_nat{i < len}).{:pattern vget res i} vget res i == vget a i *. vget b i))

//val vector_mul:#a:numeric_t -> #len1:size_nat -> #len2:size_nat{len1 + len2 < max_size_t} -> v1:vector_t a len1 -> v2:vector_t a len2 -> vector_t a (len1 + len2)

val matrix_t:t:numeric_t -> n1:size_nat -> n2:size_nat -> Type0
val matrix_create:t:numeric_t -> n1:size_nat -> n2:size_nat -> matrix_t t n1 n2
val mget:#t:numeric_t -> #n1:size_nat -> #n2:size_nat -> a:matrix_t t n1 n2 -> i:size_nat{i < n1} -> j:size_nat{j < n2} -> uint_t t
val mset:#t:numeric_t -> #n1:size_nat -> #n2:size_nat -> a:matrix_t t n1 n2 -> i:size_nat{i < n1} -> j:size_nat{j < n2} -> v:uint_t t -> Pure (matrix_t t n1 n2)
  (requires True)
  (ensures (fun res -> mget res i j == v /\ (forall (i1:size_nat) (j1:size_nat). i1 < n1 /\ i1 <> i /\ j1 < n2 /\ j1 <> j ==> mget res i1 j1 == mget a i1 j1)))

val sum:#t:numeric_t -> n:size_nat -> f:(i:size_nat{i < n} -> uint_t t) -> tmp0:uint_t t -> uint_t t

val matrix_zero:#t:numeric_t -> #n1:size_nat -> #n2:size_nat -> Pure (matrix_t t n1 n2)
  (requires True)
  (ensures (fun res -> forall (i:size_nat{i < n1}) (j:size_nat{j < n2}).{:pattern mget res i j} mget res i j == numeric #t 0))

val matrix_add:#t:numeric_t -> #n1:size_nat -> #n2:size_nat -> a:matrix_t t n1 n2 -> b:matrix_t t n1 n2 -> Pure (matrix_t t n1 n2)
  (requires True)
  (ensures (fun res -> forall (i:size_nat{i < n1}) (j:size_nat{j < n2}).{:pattern mget res i j} mget res i j == mget a i j +. mget b i j))

val matrix_sub:#t:numeric_t -> #n1:size_nat -> #n2:size_nat -> a:matrix_t t n1 n2 -> b:matrix_t t n1 n2 -> Pure (matrix_t t n1 n2)
  (requires True)
  (ensures (fun res -> forall (i:size_nat{i < n1}) (j:size_nat{j < n2}).{:pattern mget res i j} mget res i j == mget a i j -. mget b i j))

val matrix_mul:#t:numeric_t -> #n1:size_nat -> #n2:size_nat -> #n3:size_nat -> a:matrix_t t n1 n2 -> b:matrix_t t n2 n3 -> Pure (matrix_t t n1 n3)
  (requires (t <> U128))
  (ensures (fun res -> forall (i:size_nat{i < n1}) (k:size_nat{k < n3}).{:pattern mget res i k} mget res i k == sum n2 (fun j -> mget a i j *. mget b j k) (numeric #t 0)))

(* Lemmas *)
val matrix_distributivity_add_right:
  #t:numeric_t{t <> U128} -> #n1:size_nat -> #n2:size_nat -> #n3:size_nat ->
  a:matrix_t t n1 n2 -> b:matrix_t t n1 n2 -> c:matrix_t t n2 n3 -> Lemma
  (matrix_mul (matrix_add a b) c == matrix_add (matrix_mul a c) (matrix_mul b c))

val matrix_distributivity_add_left:
  #t:numeric_t{t <> U128} -> #n1:size_nat -> #n2:size_nat -> #n3:size_nat ->
  a:matrix_t t n1 n2 -> b:matrix_t t n1 n2 -> c:matrix_t t n3 n1 -> Lemma
  (matrix_mul c (matrix_add a b) == matrix_add (matrix_mul c a) (matrix_mul c b))

val matrix_associativity_mul:
  #t:numeric_t{t <> U128} -> #n1:size_nat -> #n2:size_nat -> #n3:size_nat -> #n4:size_nat ->
  a:matrix_t t n1 n2 -> b:matrix_t t n2 n3 -> c:matrix_t t n3 n4 -> Lemma
  (matrix_mul (matrix_mul a b) c == matrix_mul a (matrix_mul b c))

val matrix_associativity_add:
  #t:numeric_t -> #n1:size_nat -> #n2:size_nat ->
  a:matrix_t t n1 n2 -> b:matrix_t t n1 n2 -> c:matrix_t t n1 n2 -> Lemma
  (matrix_add (matrix_add a b) c == matrix_add a (matrix_add b c))

val matrix_commutativity_add:
  #t:numeric_t -> #n1:size_nat -> #n2:size_nat ->
  a:matrix_t t n1 n2 -> b:matrix_t t n1 n2 -> Lemma
  (matrix_add a b == matrix_add b a)

val matrix_sub_zero:
  #t:numeric_t -> #n1:size_nat -> #n2:size_nat ->
  a:matrix_t t n1 n2 -> Lemma
  (matrix_sub a a == matrix_zero #t #n1 #n2)

val matrix_add_zero:
  #t:numeric_t -> #n1:size_nat -> #n2:size_nat ->
  a:matrix_t t n1 n2 -> Lemma
  (matrix_add a (matrix_zero #t #n1 #n2) == a)
