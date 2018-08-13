module Spec.Matrix

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module Seq = Lib.Sequence
module Lemmas = Spec.Frodo.Lemmas

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from 'FStar.Pervasives Prims FStar.Math.Lemmas Lib.Sequence Spec.Matrix'"

/// Auxiliary lemmas

val index_lt:
    n1:size_nat
  -> n2:size_nat
  -> i:size_nat{i < n1}
  -> j:size_nat{j < n2}
  -> Lemma (i * n2 + j < n1 * n2)
let index_lt n1 n2 i j =
  assert (i * n2 + j <= (n1 - 1) * n2 + n2 - 1)

// TODO: this proof is fragile; improve
private
val index_neq:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 < max_size_t}
  -> i:size_nat{i < n1}
  -> j:nat{j < n2}
  -> i':nat{i' < n1}
  -> j':nat{j' < n2}
  -> Lemma (((i', j') <> (i, j) ==> i' * n2 + j' <> i * n2 + j) /\ i' * n2 + j' < n1 * n2)
let index_neq #n1 #n2 i j i' j' =
  admit();
  index_lt n1 n2 i j;
  index_lt n1 n2 i' j';
  if i' = i then
    assert ((i', j') <> (i, j) ==> j' <> j)
  else
    begin
    let open FStar.Math.Lemmas in
    lemma_eucl_div_bound j i n2;
    lemma_eucl_div_bound j' i' n2
    end

/// Matrices as flat sequences

type elem = uint16

type matrix (n1:size_nat) (n2:size_nat{n1 * n2 < max_size_t}) = Seq.lseq elem (n1 * n2)

val create: n1:size_nat -> n2:size_nat{n1 * n2 < max_size_t} -> matrix n1 n2
let create n1 n2 = Seq.create (n1 * n2) (u16 0)

val mget:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 < max_size_t}
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
  -> #n2:size_nat{n1 * n2 < max_size_t}
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
  -> #n2:size_nat{n1 * n2 < max_size_t}
  -> a:matrix n1 n2
  -> b:matrix n1 n2
  -> Lemma
    (requires forall i j. a.(i,j) == b.(i,j))
    (ensures  a == b)
let extensionality #n1 #n2 a b =
  Classical.forall_intro_2 (index_lt n1 n2);
  assert (forall (i:size_nat{i < n1}) (j:size_nat{j < n2}). a.(i, j) == a.[i * n2 + j] /\ b.(i, j) == b.[i * n2 + j]);
  assert (forall (i:size_nat{i < n1}) (j:size_nat{j < n2}). a.[i * n2 + j] == b.[i * n2 + j]);
  assert (forall (k:size_nat{k < n1 * n2}). k == (k / n2) * n2 + k % n2 /\ k / n2 < n1 /\ k % n2 < n2);
  assert (forall (k:size_nat{k < n1 * n2}). index a k == index b k);
  Seq.eq_intro a b

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

val map2:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 < max_size_t}
  -> f:(elem -> elem -> elem)
  -> a:matrix n1 n2
  -> b:matrix n1 n2
  -> c:matrix n1 n2{ forall i j. c.(i,j) == f a.(i,j) b.(i,j) }
let map2 #n1 #n2 f a b =
  let c = create n1 n2 in
  repeati_inductive n1
    (fun i c -> forall (i0:size_nat{i0 < i}) (j:size_nat{j < n2}). c.(i0,j) == f a.(i0,j) b.(i0,j))
    (fun i c ->
      repeati_inductive n2
        (fun j c0 ->
          (forall (i0:size_nat{i0 < i}) (j:size_nat{j < n2}). c0.(i0,j) == c.(i0,j)) /\
          (forall (j0:size_nat{j0 < j}). c0.(i,j0) == f a.(i,j0) b.(i,j0)))
        (fun j c' -> c'.(i,j) <- f a.(i,j) b.(i,j))
        c)
    c

//TODO: revisit when the "friends" mechanism is in place
#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 0 --using_facts_from 'FStar.Pervasives Prims FStar.Math.Lemmas Lib.IntTypes Lib.Sequence Spec.Matrix'"

val add:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 < max_size_t}
  -> a:matrix n1 n2
  -> b:matrix n1 n2
  -> c:matrix n1 n2{ forall i j. c.(i,j) == a.(i,j) +. b.(i,j) }
let add #n1 #n2 a b =
  map2 add_mod a b

val sub:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 < max_size_t}
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
  -> #n2:size_nat{n1 * n2 < max_size_t}
  -> #n3:size_nat{n1 * n3 < max_size_t /\ n2 * n3 < max_size_t}
  -> a:matrix n1 n2
  -> b:matrix n2 n3
  -> i:size_nat{i < n1}
  -> k:size_nat{k < n3}
  -> res:uint16{res == sum #n2 (fun l -> a.(i, l) *. b.(l, k))}
let mul_inner #n1 #n2 #n3 a b i k =
  let f l = a.(i, l) *. b.(l, k) in
  let res =
    repeati_inductive n2
      (fun j res -> res == sum_ #n2 f j)
      (fun j res ->
        res +. a.(i, j) *. b.(j, k)
      ) (u16 0) in
  sum_extensionality n2 f (fun l -> a.(i, l) *. b.(l, k)) n2;
  res

#set-options "--max_fuel 0"

val mul:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 < max_size_t}
  -> #n3:size_nat{n1 * n3 < max_size_t /\ n2 * n3 < max_size_t}
  -> a:matrix n1 n2
  -> b:matrix n2 n3
  -> c:matrix n1 n3{ forall i k. c.(i, k) == sum #n2 (fun l -> a.(i, l) *. b.(l, k))}
let mul #n1 #n2 #n3 a b =
  let c = create n1 n3 in

  repeati_inductive n1
    (fun i c -> forall (i1:size_nat{i1 < i}) (k:size_nat{k < n3}). c.(i1, k) == sum #n2 (fun l -> a.(i1, l) *. b.(l, k)))
    (fun i c ->
      repeati_inductive n3
        (fun k c0 -> (forall (k1:size_nat{k1 < k}). c0.(i, k1) == sum #n2 (fun l -> a.(i, l) *. b.(l, k1))) /\
                   (forall (i1:size_nat{i1 < n1 /\ i <> i1}) (k:size_nat{k < n3}). c0.(i1, k) == c.(i1, k)))
        (fun k c0 ->
          c0.(i, k) <- mul_inner #n1 #n2 #n3 a b i k
        ) c
    ) c

val mget_s:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 < max_size_t}
  -> a:matrix n1 n2
  -> i:size_nat{i < n1}
  -> j:size_nat{j < n2}
  -> elem
let mget_s #n1 #n2 a i j =
  assert (j * n1 + i <= (n2 - 1) * n1 + n1 - 1);
  a.[j * n1 + i]

#set-options "--max_fuel 1"

val mul_inner_s:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 < max_size_t}
  -> #n3:size_nat{n1 * n3 < max_size_t /\ n2 * n3 < max_size_t}
  -> a:matrix n1 n2
  -> b:matrix n2 n3
  -> i:size_nat{i < n1}
  -> k:size_nat{k < n3}
  -> res:uint16{res == sum #n2 (fun l -> a.(i, l) *. mget_s b l k)}
let mul_inner_s #n1 #n2 #n3 a b i k =
  let f l = a.(i, l) *. mget_s b l k in
  let res =
    repeati_inductive n2
      (fun j res -> res == sum_ #n2 f j)
      (fun j res ->
        res +. a.(i, j) *. mget_s b j k
      ) (u16 0) in
  sum_extensionality n2 f (fun l -> a.(i, l) *. mget_s b l k) n2;
  res

#set-options "--max_fuel 0"

val mul_s:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 < max_size_t}
  -> #n3:size_nat{n1 * n3 < max_size_t /\ n2 * n3 < max_size_t}
  -> a:matrix n1 n2
  -> b:matrix n2 n3
  -> c:matrix n1 n3{ forall i k. c.(i, k) == sum #n2 (fun l -> a.(i, l) *. mget_s b l k)}
let mul_s #n1 #n2 #n3 a b =
  let c = create n1 n3 in

  repeati_inductive n1
    (fun i c -> forall (i1:size_nat{i1 < i}) (k:size_nat{k < n3}). c.(i1, k) == sum #n2 (fun l -> a.(i1, l) *. mget_s b l k))
    (fun i c ->
      repeati_inductive n3
        (fun k c0 -> (forall (k1:size_nat{k1 < k}). c0.(i, k1) == sum #n2 (fun l -> a.(i, l) *. mget_s b l k1)) /\
                   (forall (i1:size_nat{i1 < n1 /\ i <> i1}) (k:size_nat{k < n3}). c0.(i1, k) == c.(i1, k)))
        (fun k c0 ->
          c0.(i, k) <- mul_inner_s #n1 #n2 #n3 a b i k
        ) c
    ) c

val fold_land_:
    #n:size_nat
  -> f:(j:size_nat{j < n} -> GTot bool)
  -> i:size_nat{i <= n}
  -> GTot bool
let rec fold_land_ #n f i =
  if i = 0 then true
  else f (i - 1) && fold_land_ #n f (i - 1)

val eq_m:m:size_nat -> a:uint16 -> b:uint16 -> Tot bool
let eq_m m a b =
  let open Lib.RawIntTypes in
  uint_to_nat a % (pow2 m) = uint_to_nat b % (pow2 m)

#set-options "--max_fuel 1"

val matrix_eq_fc:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 < max_size_t}
  -> m:size_nat{0 < m /\ m <= 16}
  -> a:matrix n1 n2
  -> b:matrix n1 n2
  -> i:size_nat{i <= n1 * n2}
  -> GTot bool
let matrix_eq_fc #n1 #n2 m a b i =
  let f i = eq_m m a.[i] b.[i] in
  fold_land_ #(n1 * n2) (fun i -> eq_m m a.[i] b.[i]) i

val matrix_eq:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 < max_size_t}
  -> m:size_nat{0 < m /\ m <= 16}
  -> a:matrix n1 n2
  -> b:matrix n1 n2
  -> res:bool{res == matrix_eq_fc #n1 #n2 m a b (n1 * n2)}
let matrix_eq #n1 #n2 m a b =
  let open Lib.RawIntTypes in
  let res =
    repeati_inductive (n1 * n2)
    (fun i res -> res == matrix_eq_fc #n1 #n2 m a b i)
    (fun i res ->
      res && eq_m m a.[i] b.[i]
    ) true in
  res

#set-options "--max_fuel 0"

//TODO: prove in Lib.Bytesequence
assume val lemma_uint_to_bytes_le:
    #t:m_inttype
  -> u:uint_t t
  -> Lemma
    (forall (i:nat{i < numbytes t}).
      index (uint_to_bytes_le #t u) i == u8 (uint_v u / pow2 (8 * i) % pow2 8))

val matrix_to_lbytes_fc:
    #n1:size_nat
  -> #n2:size_nat{2 * n1 * n2 < max_size_t}
  -> m:matrix n1 n2
  -> res:lbytes (2 * n1 * n2)
  -> i:size_nat{i < n1 * n2}
  -> k:size_nat{k < 2}
  -> Type0
let matrix_to_lbytes_fc #n1 #n2 m res i k =
  res.[2 * i + k] == u8 (uint_v m.[i] / pow2 (8 * k) % pow2 8)

val lemma_matrix_to_lbytes_fc:
    #n1:size_nat
  -> #n2:size_nat{2 * n1 * n2 < max_size_t}
  -> m:matrix n1 n2
  -> res:lbytes (2 * n1 * n2)
  -> i:size_nat{i < n1 * n2}
  -> k:size_nat{k < 2}
  -> Lemma
    (requires matrix_to_lbytes_fc m res i k)
    (ensures  res.[2 * i + k] == u8 (uint_v m.[i] / pow2 (8 * k) % pow2 8))
let lemma_matrix_to_lbytes_fc #n1 #n2 m res i k = ()

val lemma_matrix_to_lbytes:
    #n1:size_nat
  -> #n2:size_nat{2 * n1 * n2 < max_size_t}
  -> m:matrix n1 n2
  -> res:lbytes (2 * n1 * n2)
  -> res1:lbytes (2 * n1 * n2)
  -> i:size_nat{i < n1 * n2}
  -> Lemma
    (requires
      (forall (i0:size_nat{i0 < i}) (k:size_nat{k < 2}). matrix_to_lbytes_fc m res i0 k) /\
      (forall (i0:size_nat{i0 < i}) (k:size_nat{k < 2}). res1.[2 * i0 + k] == res.[2 * i0 + k]))
    (ensures
      (forall (i0:size_nat{i0 < i}) (k:size_nat{k < 2}). matrix_to_lbytes_fc m res1 i0 k))
let lemma_matrix_to_lbytes #n1 #n2 m res res1 i =
  Classical.forall_intro_2 #(i0:size_nat{i0 < i}) #(fun i -> k:size_nat{k < 2})
  #(fun i0 k -> res.[2 * i0 + k] == u8 (uint_v m.[i0] / pow2 (8 * k) % pow2 8))
  (fun i0 k ->
    (lemma_matrix_to_lbytes_fc #n1 #n2 m res i0 k) <:
    (Lemma (res.[2 * i0 + k] == u8 (uint_v m.[i0] / pow2 (8 * k) % pow2 8)))
  )

val lemma_matrix_to_lbytes_ext:
    #n1:size_nat
  -> #n2:size_nat{2 * n1 < max_size_t /\ 2 * n1 * n2 < max_size_t}
  -> m:matrix n1 n2
  -> res1:lbytes (2 * n1 * n2)
  -> res2:lbytes (2 * n1 * n2)
  -> Lemma
    (requires
      (forall (i:size_nat{i < n1 * n2}) (k:size_nat{k < 2}). matrix_to_lbytes_fc m res1 i k) /\
      (forall (i:size_nat{i < n1 * n2}) (k:size_nat{k < 2}). matrix_to_lbytes_fc m res2 i k))
    (ensures res1 == res2)
let lemma_matrix_to_lbytes_ext #n1 #n2 m res1 res2 =
  Classical.forall_intro_2 #(i:size_nat{i < n1 * n2}) #(fun i -> k:size_nat{k < 2})
  (fun i k ->
    (lemma_matrix_to_lbytes_fc #n1 #n2 m res1 i k) <:
    (Lemma (res1.[2 * i + k] == u8 (uint_v m.[i] / pow2 (8 * k) % pow2 8)))
  );
  Classical.forall_intro_2 #(i:size_nat{i < n1 * n2}) #(fun i -> k:size_nat{k < 2})
  (fun i k ->
    (lemma_matrix_to_lbytes_fc #n1 #n2 m res2 i k) <:
    (Lemma (res2.[2 * i + k] == u8 (uint_v m.[i] / pow2 (8 * k) % pow2 8)))
  );
  assert (forall (i:size_nat{i < n1 * n2}) (k:size_nat{k < 2}). res1.[2 * i + k] == res1.[i * 2 + k]);
  assert (forall (i:size_nat{i < n1 * n2}) (k:size_nat{k < 2}). res1.[i * 2 + k] == res2.[i * 2 + k]);
  assert (forall (i:size_nat{i < 2 * n1 * n2}). i == (i / 2) * 2 + i % 2 /\ i / 2 < n1 * n2 /\ i % 2 < 2);
  assert (forall (i:size_nat{i < 2 * n1 * n2}). index res1 i == index res2 i);
  eq_intro res1 res2;
  eq_elim res1 res2

val matrix_to_lbytes:
    #n1:size_nat
  -> #n2:size_nat{2 * n1 * n2 < max_size_t}
  -> m:matrix n1 n2
  -> res:lbytes (2 * n1 * n2)
    {forall (i:size_nat{i < n1 * n2}) (k:size_nat{k < 2}).
      matrix_to_lbytes_fc #n1 #n2 m res i k}
let matrix_to_lbytes #n1 #n2 m =
  let res = Seq.create (2 * n1 * n2) (u8 0) in
  repeati_inductive (n1 * n2)
  (fun i res ->
    forall (i0:size_nat{i0 < i}) (k:size_nat{k < 2}). matrix_to_lbytes_fc m res i0 k)
  (fun i res ->
    lemma_uint_to_bytes_le m.[i];
    let res1 = update_sub res (2 * i) 2 (uint_to_bytes_le m.[i]) in
    lemma_matrix_to_lbytes #n1 #n2 m res res1 i;
    res1
  ) res

val matrix_from_lbytes_fc:
    n1:size_nat
  -> n2:size_nat{2 * n1 * n2 < max_size_t}
  -> b:lbytes (2 * n1 * n2)
  -> i:size_nat{i < n1 * n2}
  -> GTot uint16
let matrix_from_lbytes_fc n1 n2 b i =
  uint_from_bytes_le (Seq.sub b (2 * i) 2)

val matrix_from_lbytes:
    n1:size_nat
  -> n2:size_nat{2 * n1 * n2 < max_size_t}
  -> b:lbytes (2 * n1 * n2)
  -> res:matrix n1 n2
    {forall (i:size_nat{i < n1 * n2}).
      res.[i] == matrix_from_lbytes_fc n1 n2 b i}
let matrix_from_lbytes n1 n2 b =
  let res = create n1 n2 in
  repeati_inductive (n1 * n2)
  (fun i res ->
    forall (i0:size_nat{i0 < i}). res.[i0] == matrix_from_lbytes_fc n1 n2 b i0)
  (fun i res ->
    res.[i] <- uint_from_bytes_le (Seq.sub b (2 * i) 2)
  ) res
