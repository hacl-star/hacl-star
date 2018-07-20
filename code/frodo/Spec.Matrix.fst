module Spec.Matrix

open FStar.Seq
open FStar.UInt16
open FStar.Mul

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --z3seed 2"

type elem = UInt16.t

type matrix (n1:nat) (n2:nat) = s:seq elem {length s == n1 * n2}

val mcreate: n1:nat -> n2:nat -> matrix n1 n2
let mcreate n1 n2 = create (n1 * n2) 0us

let op_String_Access = index
let op_String_Assignment = upd

val lemma_matrix_index:
    n1:nat
  -> n2:nat
  -> i:nat{i < n1}
  -> j:nat{j < n2}
  -> Lemma (i * n2 + j < n1 * n2)
let lemma_matrix_index n1 n2 i j =
  assert (i * n2 + j <= (n1 - 1) * n2 + n2 - 1)

val mget:
    #n1:nat
  -> #n2:nat
  -> a:matrix n1 n2
  -> i:nat{i < n1}
  -> j:nat{j < n2}
  -> elem
let mget #n1 #n2 a i j =
  lemma_matrix_index n1 n2 i j;
  a.[i * n2 + j]

val index_neq:
    #n1:nat
  -> #n2:nat
  -> i:nat{i < n1}
  -> j:nat{j < n2}
  -> i':nat{i' < n1}
  -> j':nat{j' < n2}
  -> Lemma ((i', j') <> (i, j) ==>
           (i' * n2 + j' <> i * n2 + j /\ i' * n2 + j' < n1 * n2))
let index_neq #n1 #n2 i j i' j' =
  let open FStar.Math.Lemmas in
  let open FStar.Tactics in
  lemma_eucl_div_bound j i n2;
  lemma_eucl_div_bound j' i' n2;
  lemma_matrix_index n1 n2 i j;
  lemma_matrix_index n1 n2 i' j'

val mset:
    #n1:nat
  -> #n2:nat
  -> a:matrix n1 n2
  -> i:nat{i < n1}
  -> j:nat{j < n2}
  -> v:elem
  -> Pure (matrix n1 n2)
  (requires True)
  (ensures  fun res ->
      mget res i j == v
    /\ (forall i' j'. (i', j') <> (i, j) ==> mget res i' j' == mget a i' j'))
let mset #n1 #n2 a i j v =
  Classical.forall_intro_2 (index_neq #n1 #n2 i j);
  lemma_matrix_index n1 n2 i j;
  a.[i * n2 + j] <- v

let op_Array_Access (#n1:nat) (#n2:nat) (m:matrix n1 n2) (i,j) = mget m i j
let op_Array_Assignment (#n1:nat) (#n2:nat) (m:matrix n1 n2) (i,j) x = mset m i j x

(*
/// Example
///  [ 0   2 ]
///  [ 1   3 ]
let m:matrix 2 2 =
  assert_norm (List.length [0us; 2us; 1us; 3us] == 4);
  Seq.seq_of_list [0us; 2us; 1us; 3us]

let _ = assert_norm (m.(0,0) == 0us /\ m.(1,0) == 1us /\ m.(0,1) == 2us /\ m.(1,1) == 3us)

let _ = assert_norm (let m' = m.(0,0) <- 4us in m'.(0,0) == 4us)
*)


/// BEGIN Excerpt from Lib.Sequence, lightly edited
unfold
type repeatable (#a:Type) (#n:nat) (pred:(i:nat{i <= n} -> a -> Type0)) = 
  i:nat{i < n} -> x:a -> Pure a (requires pred i x) (ensures fun r -> pred (i+1) r)

val repeat_range_inductive: 
    #a:Type
  -> min:nat
  -> max:nat{min <= max}
  -> pred:(i:nat{i <= max} -> a -> Type0)
  -> f:repeatable #a #max pred
  -> x0:a{pred min x0}
  -> Tot (res:a{pred max res}) (decreases (max - min))
let rec repeat_range_inductive #a min max pred f x0 =
  if min = max then x0
  else repeat_range_inductive #a (min + 1) max pred f (f min x0)

val repeati_inductive: 
    #a:Type 
  -> max:nat 
  -> pred:(i:nat{i <= max} -> a -> Type0) 
  -> f:repeatable #a #max pred 
  -> x0:a{pred 0 x0} 
  -> res:a{pred max res}
let repeati_inductive #a =
  repeat_range_inductive #a 0
/// END Excerpt from Lib.Sequence, lightly edited

val mmap2:
    #n1:nat    
  -> #n2:nat
  -> f:(elem -> elem -> elem)
  -> a:matrix n1 n2
  -> b:matrix n1 n2
  -> c:matrix n1 n2{ forall i j. c.(i,j) == f a.(i,j) b.(i,j) }
let mmap2 #n1 #n2 f a b =
  let c = mcreate n1 n2 in
  repeati_inductive n1
    (fun i c -> forall (i0:nat{i0 < i}) (j:nat{j < n2}). c.(i0,j) == f a.(i0,j) b.(i0,j))
    (fun i c ->
      repeati_inductive n2
        (fun j c0 -> 
          (forall (i0:nat{i0 < i}) (j:nat{j < n2}). c0.(i0,j) == c.(i0,j)) /\
          (forall (j0:nat{j0 < j}). c0.(i,j0) == f a.(i,j0) b.(i,j0)))
        (fun j c' -> c'.(i,j) <- f a.(i,j) b.(i,j))
        c)
    c

val madd:
    #n1:nat
  -> #n2:nat
  -> a:matrix n1 n2
  -> b:matrix n1 n2
  -> c:matrix n1 n2{ forall i j. c.(i,j) == a.(i,j) +%^ b.(i,j) }
let madd #n1 #n2 a b =
  mmap2 UInt16.add_mod a b

val extensionality:
    #n1:nat
  -> #n2:nat
  -> a:matrix n1 n2
  -> b:matrix n1 n2
  -> Lemma 
    (requires forall i j. a.(i,j) == b.(i,j))
    (ensures  a == b)
let extensionality #n1 #n2 a b =
  admit()
  
