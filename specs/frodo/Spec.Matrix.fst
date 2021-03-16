module Spec.Matrix

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module LSeq = Lib.Sequence
module Lemmas = Spec.Frodo.Lemmas
module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

/// Auxiliary lemmas

val index_lt:
    n1:size_nat
  -> n2:size_nat
  -> i:size_nat{i < n1}
  -> j:size_nat{j < n2}
  -> Lemma (i * n2 + j < n1 * n2)

let index_lt n1 n2 i j =
  calc (<=) {
    i * n2 + j;
    (<=) { Math.Lemmas.lemma_mult_le_right n2 i (n1 - 1) }
    (n1 - 1) * n2 + j;
    (==) { Math.Lemmas.distributivity_sub_left n1 1 n2 }
    n1 * n2 - n2 + j;
    (<=) { }
    n1 * n2 - 1;
    }


private
val index_neq:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t}
  -> i:size_nat{i < n1}
  -> j:nat{j < n2}
  -> i':nat{i' < n1}
  -> j':nat{j' < n2}
  -> Lemma (((i', j') <> (i, j) ==> (i' * n2 + j' <> i * n2 + j) /\ i' * n2 + j' < n1 * n2))

let index_neq #n1 #n2 i j i' j' =
  index_lt n1 n2 i' j';
  assert (i' * n2 + j' < n1 * n2);

  if i' < i then
    calc (<) {
      i' * n2 + j';
      (<) { }
      i' * n2 + n2;
      (==) { Math.Lemmas.distributivity_add_left i' 1 n2 }
      (i' + 1) * n2;
      (<=) { Math.Lemmas.lemma_mult_le_right n2 (i' + 1) i }
      i * n2;
      (<=) { }
      i * n2 + j;
      }
  else if i = i' then ()
  else
    calc (<) {
      i * n2 + j;
      (<) { }
      i * n2 + n2;
      (==) { Math.Lemmas.distributivity_add_left i 1 n2 }
      (i + 1) * n2;
      (<=) { Math.Lemmas.lemma_mult_le_right n2 (i + 1) i' }
      i' * n2;
      (<=) { }
      i' * n2 + j';
      }


/// Matrices as flat sequences

unfold
let elem = uint16

unfold
let matrix (n1:size_nat) (n2:size_nat{n1 * n2 <= max_size_t}) = LSeq.lseq elem (n1 * n2)

val create: n1:size_nat -> n2:size_nat{n1 * n2 <= max_size_t} -> matrix n1 n2
let create n1 n2 = LSeq.create (n1 * n2) (u16 0)


val mget:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t}
  -> a:matrix n1 n2
  -> i:size_nat{i < n1}
  -> j:size_nat{j < n2}
  -> elem

let mget #n1 #n2 a i j =
  index_lt n1 n2 i j;
  a.[i * n2 + j]


unfold
let op_Array_Access #n1 #n2 (m:matrix n1 n2) (i,j) = mget m i j


val mset:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t}
  -> a:matrix n1 n2
  -> i:size_nat{i < n1}
  -> j:size_nat{j < n2}
  -> v:elem
  -> Pure (matrix n1 n2)
  (requires True)
  (ensures  fun r ->
    r.(i,j) == v /\ (forall i' j'. (i', j') <> (i, j) ==> r.(i', j') == a.(i',j')))

let mset #n1 #n2 a i j v =
  Classical.forall_intro_2 (index_neq #n1 #n2 i j);
  index_lt n1 n2 i j;
  a.[i * n2 + j] <- v


unfold
let op_Array_Assignment #n1 #n2 (m:matrix n1 n2) (i,j) x = mset m i j x


val extensionality:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t}
  -> a:matrix n1 n2
  -> b:matrix n1 n2
  -> Lemma
    (requires forall i j. a.(i,j) == b.(i,j))
    (ensures  a == b)

let extensionality #n1 #n2 a b =
  let aux (k:size_nat{k < n1 * n2}) : Lemma (index a k == index b k) =
    let i = k / n2 in
    let j = k % n2 in
    div_mul_lt n2 k n1;
    assert (i < n1 /\ j < n2);
    index_lt n1 n2 i j;
    assert (a.(i, j) == a.[i * n2 + j] /\ b.(i, j) == b.[i * n2 + j]);
    assert (a.[k] == b.[k]) in

  Classical.forall_intro aux;
  eq_intro a b;
  eq_elim a b


(*
/// Example (of course it doesn't work with Lib.IntTypes)
///  [ 0   2 ]
///  [ 1   3 ]
let m:matrix 2 2 =
  assert_norm (List.length [0us; 2us; 1us; 3us] == 4);
  Seq.seq_of_list [0us; 2us; 1us; 3us]

let _ = assert_norm (m.(0,0) == 0us /\ m.(1,0) == 1us /\ m.(0,1) == 2us /\ m.(1,1) == 3us)

let _ = assert_norm (let m' = m.(0,0) <- 4us in m'.(0,0) == 4us)
*)

val map:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t}
  -> f:(elem -> elem)
  -> a:matrix n1 n2
  -> c:matrix n1 n2{ forall i j. c.(i,j) == f a.(i,j) }

let map #n1 #n2 f a =
  let c = create n1 n2 in
  Loops.repeati_inductive n1
    (fun i c -> forall (i0:size_nat{i0 < i}) (j:size_nat{j < n2}). c.(i0,j) == f a.(i0,j))
    (fun i c ->
      Loops.repeati_inductive n2
        (fun j c0 ->
          (forall (i0:size_nat{i0 < i}) (j:size_nat{j < n2}). c0.(i0,j) == c.(i0,j)) /\
          (forall (j0:size_nat{j0 < j}). c0.(i,j0) == f a.(i,j0)))
        (fun j c' -> c'.(i,j) <- f a.(i,j))
        c)
    c


val mod_pow2_felem: logq:size_pos{logq < 16} -> a:elem
  -> Pure elem
    (requires true)
    (ensures  fun r -> v r == v a % pow2 logq)

let mod_pow2_felem logq a =
  Math.Lemmas.pow2_lt_compat 16 logq;
  mod_mask_lemma #U16 a (size logq);
  assert (v (mod_mask #U16 #SEC (size logq)) == v ((u16 1 <<. size logq) -. u16 1));
  a &. ((u16 1 <<. size logq) -. u16 1)


val mod_pow2:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t}
  -> logq:size_pos{logq <= 16}
  -> a:matrix n1 n2
  -> c:matrix n1 n2{ forall i j. v c.(i,j) == v a.(i,j) % pow2 logq }

let mod_pow2 #n1 #n2 logq a =
  if logq < 16 then
    map (mod_pow2_felem logq) a
  else a


val map2:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t}
  -> f:(elem -> elem -> elem)
  -> a:matrix n1 n2
  -> b:matrix n1 n2
  -> c:matrix n1 n2{ forall i j. c.(i,j) == f a.(i,j) b.(i,j) }

let map2 #n1 #n2 f a b =
  let c = create n1 n2 in
  Loops.repeati_inductive n1
    (fun i c -> forall (i0:size_nat{i0 < i}) (j:size_nat{j < n2}). c.(i0,j) == f a.(i0,j) b.(i0,j))
    (fun i c ->
      Loops.repeati_inductive n2
        (fun j c0 ->
          (forall (i0:size_nat{i0 < i}) (j:size_nat{j < n2}). c0.(i0,j) == c.(i0,j)) /\
          (forall (j0:size_nat{j0 < j}). c0.(i,j0) == f a.(i,j0) b.(i,j0)))
        (fun j c' -> c'.(i,j) <- f a.(i,j) b.(i,j))
        c)
    c


val add:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t}
  -> a:matrix n1 n2
  -> b:matrix n1 n2
  -> c:matrix n1 n2{ forall i j. c.(i,j) == a.(i,j) +. b.(i,j) }

let add #n1 #n2 a b =
  map2 add_mod a b


val sub:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t}
  -> a:matrix n1 n2
  -> b:matrix n1 n2
  -> c:matrix n1 n2{ forall i j. c.(i,j) == a.(i,j) -. b.(i,j) }

let sub #n1 #n2 a b =
  map2 sub_mod a b


val sum_:
    #n:size_nat
  -> f:(j:size_nat{j < n} -> GTot uint16)
  -> i:size_nat{i <= n}
  -> GTot uint16
  (decreases i)

let rec sum_ #n f i =
  if i = 0 then u16 0
  else sum_ #n f (i - 1) +. f (i - 1)

let sum #n f = sum_ #n f n


#push-options "--fuel 1"
val sum_extensionality:
    n:size_nat
  -> f:(i:size_nat{i < n} -> GTot uint16)
  -> g:(i:size_nat{i < n} -> GTot uint16)
  -> i:size_nat{i <= n}
  -> Lemma
    (requires forall (i:size_nat{i < n}). f i == g i)
    (ensures  sum_ #n f i == sum_ #n g i)
    (decreases i)

let rec sum_extensionality n f g i =
  if i = 0 then ()
  else sum_extensionality n f g (i - 1)


val mul_inner:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t}
  -> #n3:size_nat{n1 * n3 <= max_size_t /\ n2 * n3 <= max_size_t}
  -> a:matrix n1 n2
  -> b:matrix n2 n3
  -> i:size_nat{i < n1}
  -> k:size_nat{k < n3}
  -> res:uint16{res == sum #n2 (fun l -> a.(i, l) *. b.(l, k))}

let mul_inner #n1 #n2 #n3 a b i k =
  let f l = a.(i, l) *. b.(l, k) in
  let res =
    Loops.repeati_inductive n2
      (fun j res -> res == sum_ #n2 f j)
      (fun j res ->
        res +. a.(i, j) *. b.(j, k)
      ) (u16 0) in
  sum_extensionality n2 f (fun l -> a.(i, l) *. b.(l, k)) n2;
  res
#pop-options


val mul:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t}
  -> #n3:size_nat{n1 * n3 <= max_size_t /\ n2 * n3 <= max_size_t}
  -> a:matrix n1 n2
  -> b:matrix n2 n3
  -> c:matrix n1 n3{ forall i k. c.(i, k) == sum #n2 (fun l -> a.(i, l) *. b.(l, k))}

let mul #n1 #n2 #n3 a b =
  let c = create n1 n3 in
  Loops.repeati_inductive n1
    (fun i c -> forall (i1:size_nat{i1 < i}) (k:size_nat{k < n3}). c.(i1, k) == sum #n2 (fun l -> a.(i1, l) *. b.(l, k)))
    (fun i c ->
      Loops.repeati_inductive n3
        (fun k c0 -> (forall (k1:size_nat{k1 < k}). c0.(i, k1) == sum #n2 (fun l -> a.(i, l) *. b.(l, k1))) /\
                   (forall (i1:size_nat{i1 < n1 /\ i <> i1}) (k:size_nat{k < n3}). c0.(i1, k) == c.(i1, k)))
        (fun k c0 ->
          c0.(i, k) <- mul_inner #n1 #n2 #n3 a b i k
        ) c
    ) c


val mget_s:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t}
  -> a:matrix n1 n2
  -> i:size_nat{i < n1}
  -> j:size_nat{j < n2}
  -> elem

let mget_s #n1 #n2 a i j =
  index_lt n2 n1 j i;
  a.[j * n1 + i]


#push-options "--fuel 1"
val mul_inner_s:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t}
  -> #n3:size_nat{n1 * n3 <= max_size_t /\ n2 * n3 <= max_size_t}
  -> a:matrix n1 n2
  -> b:matrix n2 n3
  -> i:size_nat{i < n1}
  -> k:size_nat{k < n3}
  -> res:uint16{res == sum #n2 (fun l -> a.(i, l) *. mget_s b l k)}

let mul_inner_s #n1 #n2 #n3 a b i k =
  let f l = a.(i, l) *. mget_s b l k in
  let res =
    Loops.repeati_inductive n2
      (fun j res -> res == sum_ #n2 f j)
      (fun j res ->
        res +. a.(i, j) *. mget_s b j k
      ) (u16 0) in
  sum_extensionality n2 f (fun l -> a.(i, l) *. mget_s b l k) n2;
  res
#pop-options


val mul_s:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t}
  -> #n3:size_nat{n1 * n3 <= max_size_t /\ n2 * n3 <= max_size_t}
  -> a:matrix n1 n2
  -> b:matrix n2 n3
  -> c:matrix n1 n3{ forall i k. c.(i, k) == sum #n2 (fun l -> a.(i, l) *. mget_s b l k)}

let mul_s #n1 #n2 #n3 a b =
  let c = create n1 n3 in
  Loops.repeati_inductive n1
    (fun i c -> forall (i1:size_nat{i1 < i}) (k:size_nat{k < n3}). c.(i1, k) == sum #n2 (fun l -> a.(i1, l) *. mget_s b l k))
    (fun i c ->
      Loops.repeati_inductive n3
        (fun k c0 -> (forall (k1:size_nat{k1 < k}). c0.(i, k1) == sum #n2 (fun l -> a.(i, l) *. mget_s b l k1)) /\
                   (forall (i1:size_nat{i1 < n1 /\ i <> i1}) (k:size_nat{k < n3}). c0.(i1, k) == c.(i1, k)))
        (fun k c0 ->
          c0.(i, k) <- mul_inner_s #n1 #n2 #n3 a b i k
        ) c
    ) c


val matrix_eq:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t}
  -> a:matrix n1 n2
  -> b:matrix n1 n2
  -> Pure uint16
    (requires True)
    (ensures  fun r ->
      (a == b ==> v r == v (ones U16 SEC)) /\
      (a =!= b ==> v r == 0))

let matrix_eq #n1 #n2 a b =
  seq_eq_mask a b (n1 * n2)


val matrix_to_lbytes_f:
    #n1:size_nat
  -> #n2:size_nat{2 * n1 * n2 <= max_size_t}
  -> m:matrix n1 n2
  -> i:size_nat{i < n1 * n2}
  -> lbytes 2

let matrix_to_lbytes_f #n1 #n2 m i =
  uint_to_bytes_le m.[i]


val matrix_to_lbytes:
    #n1:size_nat
  -> #n2:size_nat{2 * n1 * n2 <= max_size_t}
  -> m:matrix n1 n2
  -> lbytes (2 * n1 * n2)

let matrix_to_lbytes #n1 #n2 m =
  generate_blocks_simple 2 (n1 * n2) (n1 * n2) (matrix_to_lbytes_f m)


val matrix_from_lbytes_f:
    n1:size_nat
  -> n2:size_nat{2 * n1 * n2 <= max_size_t}
  -> b:lbytes (2 * n1 * n2)
  -> i:size_nat{i < n1 * n2}
  -> elem

let matrix_from_lbytes_f n1 n2 b i =
  uint_from_bytes_le (LSeq.sub b (2 * i) 2)


val matrix_from_lbytes:
    n1:size_nat
  -> n2:size_nat{2 * n1 * n2 <= max_size_t}
  -> b:lbytes (2 * n1 * n2)
  -> matrix n1 n2

let matrix_from_lbytes n1 n2 b =
  createi (n1 * n2) (matrix_from_lbytes_f n1 n2 b)
