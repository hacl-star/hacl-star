module Lib.Sequence

open FStar.Mul
open Lib.IntTypes

#set-options "--z3rlimit 15"

/// Definition of sequences

let seq (a:Type0) = s:Seq.seq a{Seq.length s <= max_size_t}

let lseq (a:Type0) (len:size_nat) = s:seq a{Seq.length s == len}

let intseq (t:m_inttype) (len:size_nat) = lseq (uint_t t) len

val length: #a:Type0 -> seq a -> size_nat

val to_lseq: #a:Type0 -> s:seq a -> l:lseq a (Seq.length s){l == s}
val to_seq: #a:Type0 -> #len:size_nat -> s:lseq a len -> o:seq a {o == s /\ Seq.length o == len}

val index: #a:Type -> #len:size_nat -> s:lseq a len -> n:size_nat{n < len} -> a

abstract
type equal (#a:Type) (#len:size_nat) (s1:lseq a len) (s2:lseq a len) =
 forall (i:size_nat{i < len}).{:pattern (index s1 i); (index s2 i)} index s1 i == index s2 i

val eq_intro:
    #a:Type
  -> #len:size_nat
  -> s1:lseq a len
  -> s2:lseq a len
  -> Lemma
    (requires (forall (i:size_nat{i < len}).{:pattern (index s1 i); (index s2 i)} index s1 i == index s2 i))
    (ensures  (equal s1 s2))
  [SMTPat (equal s1 s2)]

val eq_elim:
    #a:Type
  -> #len:size_nat
  -> s1:lseq a len
  -> s2:lseq a len
  -> Lemma
    (requires equal s1 s2)
    (ensures  s1 == s2)
  [SMTPat (equal s1 s2)]

val upd:
    #a:Type
  -> #len:size_nat
  -> s:lseq a len
  -> n:size_nat{n < len /\ len > 0}
  -> x:a
  -> o:lseq a len{index o n == x /\ (forall (i:size_nat).
    {:pattern (index s i)} (i < len /\ i <> n) ==> index o i == index s i)}

///
/// Allocation functions for sequences
///

val create:
    #a:Type
  -> len:size_nat
  -> init:a
  -> s:lseq a len{forall (i:size_nat).
    {:pattern (index s i)} i < len ==> index s i == init}

/// TODO: rename this to of_list. Used in Lib.Buffer
val createL:#a:Type -> l:list a{List.Tot.length l <= maxint U32} -> lseq a (List.Tot.length l)

val of_list:#a:Type -> l:list a{List.Tot.length l <= maxint U32} -> seq a

val sub:
    #a:Type
  -> #len:size_nat
  -> s1:lseq a len
  -> start:size_nat
  -> n:size_nat{start + n <= len}
  -> s2:lseq a n{forall (k:size_nat{k < n}).
    {:pattern (index s2 k)} index s2 k == index s1 (start + k)}

val slice:
    #a:Type
  -> #len:size_nat
  -> i:lseq a len
  -> start:size_nat
  -> fin:size_nat{start <= fin /\ fin <= len}
  -> lseq a (fin - start)

val update_sub:
    #a:Type
  -> #len:size_nat
  -> i:lseq a len
  -> start:size_nat
  -> n:size_nat{start + n <= len}
  -> x:lseq a n
  -> o:lseq a len{sub o start n == x /\
    (forall (k:nat{(0 <= k /\ k < start) \/ (start + n <= k /\ k < len)}).
      {:pattern (index o k)} index o k == index i k)}

val update_slice:
    #a:Type
  -> #len:size_nat
  -> i:lseq a len
  -> start:size_nat
  -> fin:size_nat{start <= fin /\ fin <= len}
  -> upd:lseq a (fin - start)
  -> lseq a len

unfold
let op_String_Access #a #len = index #a #len

unfold
let op_String_Assignment #a #len = upd #a #len

/// Iteration

(**
* fold_left-like loop combinator:
* [ repeat_left lo hi a f acc == f (hi - 1) .. ... (f (lo + 1) (f lo acc)) ]
*
* e.g. [ repeat_left 0 3 (fun _ -> list int) Cons [] == [2;1;0] ]
*
* It satisfies
* [ repeat_left lo hi (fun _ -> a) f acc == fold_left (flip f) acc [lo..hi-1] ]
*
* A simpler variant with a non-dependent accumuator used to be called [repeat_range]
*)
val repeat_left:
    lo:size_nat
  -> hi:size_nat{lo <= hi}
  -> a:(i:size_nat{lo <= i /\ i <= hi} -> Type)
  -> f:(i:size_nat{lo <= i /\ i < hi} -> a i -> a (i + 1))
  -> acc:a lo
  -> Tot (a hi) (decreases (hi - lo))

(**
* fold_right-like loop combinator:
* [ repeat_right lo hi a f acc == f (hi - 1) .. ... (f (lo + 1) (f lo acc)) ]
*
* e.g. [ repeat_right 0 3 (fun _ -> list int) Cons [] == [2;1;0] ]
*
* It satisfies
* [ repeat_right lo hi (fun _ -> a) f acc == fold_right f acc [hi-1..lo] ]
*)
val repeat_right:
    lo:size_nat
  -> hi:size_nat{lo <= hi}
  -> a:(i:size_nat{lo <= i /\ i <= hi} -> Type)
  -> f:(i:size_nat{lo <= i /\ i < hi} -> a i -> a (i + 1))
  -> acc:a lo
  -> Tot (a hi) (decreases (hi - lo))

(** Splitting a repetition *)
val repeat_right_plus:
    lo:size_nat
  -> mi:size_nat{lo <= mi}
  -> hi:size_nat{mi <= hi}
  -> a:(i:size_nat{lo <= i /\ i <= hi} -> Type)
  -> f:(i:size_nat{lo <= i /\ i < hi} -> a i -> a (i + 1))
  -> acc:a lo
  -> Lemma (ensures
      repeat_right lo hi a f acc ==
      repeat_right mi hi a f (repeat_right lo mi a f acc))
    (decreases hi)

(**
* [repeat_left] and [repeat_right] are equivalent.
*
* This follows from the third duality theorem
* [ fold_right f acc xs = fold_left (flip f) acc (reverse xs) ]
*)
val repeat_left_right:
    lo:size_nat
  -> hi:size_nat{lo <= hi}
  -> a:(i:size_nat{lo <= i /\ i <= hi} -> Type)
  -> f:(i:size_nat{lo <= i /\ i < hi} -> a i -> a (i + 1))
  -> acc:a lo
  -> Lemma (ensures repeat_right lo hi a f acc == repeat_left lo hi a f acc)
    (decreases (hi - lo))

(**
* Repetition starting from 0
*
* Defined as [repeat_right] for convenience, but [repeat_left] may be more
* efficient when extracted to OCaml.
*)

val repeat:
    n:size_nat
  -> a:(i:size_nat{i <= n} -> Type)
  -> f:(i:size_nat{i < n} -> a i -> a (i + 1))
  -> acc0:a 0
  -> a n

(** Unfolding one iteration *)
val unfold_repeat:
    n:size_nat
  -> a:(i:size_nat{i <= n} -> Type)
  -> f:(i:size_nat{i < n} -> a i -> a (i + 1))
  -> acc0:a 0
  -> i:size_nat{i < n}
  -> Lemma (repeat (i + 1) a f acc0 == f i (repeat i a f acc0))

(**
* Repetition with a fixed accumulator type
*)

val repeati:
    #a:Type
  -> n:size_nat
  -> f:(i:size_nat{i < n} -> a -> a)
  -> acc0:a
  -> a

(** Unfolding one iteration *)
val unfold_repeati:
    #a:Type
  -> n:size_nat
  -> f:(i:size_nat{i < n} -> a -> a)
  -> acc0:a
  -> i:size_nat{i < n}
  -> Lemma (repeati #a (i + 1) f acc0 == f i (repeati #a i f acc0))

/// Old combinators; all subsumed by [repeat_left]

val repeat_range:
  #a:Type
  -> min:size_nat
  -> max:size_nat{min <= max}
  -> (s:size_nat{s >= min /\ s < max} -> a -> Tot a)
  -> a
  -> Tot a (decreases (max - min))

val repeath:
    #a:Type
  -> max:size_nat
  -> (a -> Tot a)
  -> a
  -> Tot a (decreases max)

unfold
type repeatable (#a:Type) (#n:size_nat) (pred:(i:size_nat{i <= n} -> a -> Tot Type)) =
  i:size_nat{i < n} -> x:a{pred i x} -> y:a{pred (i+1) y}

val repeat_range_inductive:
    #a:Type
  -> min:size_nat
  -> max:size_nat{min <= max}
  -> pred:(i:size_nat{i <= max} -> a -> Type)
  -> f:repeatable #a #max pred
  -> x0:a{pred min x0}
  -> Tot (res:a{pred max res}) (decreases (max - min))

val repeati_inductive:
   #a:Type
 -> n:size_nat
 -> pred:(i:size_nat{i <= n} -> a -> Type)
 -> f:repeatable #a #n pred
 -> x0:a{pred 0 x0}
 -> res:a{pred n res}

val lbytes_eq_inner:
    #len:size_nat
  -> a:lseq uint8 len
  -> b:lseq uint8 len
  -> i:size_nat{i < len}
  -> r:bool
  -> bool

val lbytes_eq:#len:size_nat -> lseq uint8 len -> lseq uint8 len -> bool

val fold_left_range_:
    #a:Type
  -> #b:Type
  -> #len:size_nat
  -> min:size_nat
  -> max:size_nat{min <= max /\ len = max - min}
  -> (i:size_nat{i >= min /\ i < max} -> a -> b -> Tot b)
  -> lseq a len
  -> b
  -> Tot b (decreases (max - min))

val fold_left_range:
    #a:Type
  -> #b:Type
  -> #len:size_nat
  -> min:size_nat
  -> max:size_nat{min <= max /\ max <= len}
  -> (i:size_nat{i >= min /\ i < max} -> a -> b -> Tot b)
  -> lseq a len
  -> b
  -> b

val fold_lefti:#a:Type -> #b:Type -> #len:size_nat -> (i:size_nat{i < len} -> a -> b -> Tot b) -> lseq a len -> b -> b

val fold_left:#a:Type -> #b:Type -> #len:size_nat -> (a -> b -> Tot b) -> lseq a len -> b -> b

val map:#a:Type -> #b:Type -> #len:size_nat -> (a -> Tot b) -> lseq a len -> lseq b len

val for_all:#a:Type -> #len:size_nat -> (a -> Tot bool) -> lseq a len -> bool

val map2:#a:Type -> #b:Type -> #c:Type -> #len:size_nat -> (a -> b -> Tot c) -> lseq a len -> lseq b len -> lseq c len

val for_all2:#a:Type -> #b:Type -> #len:size_nat -> (a -> b -> Tot bool) -> lseq a len -> lseq b len -> bool

val as_list:#a:Type -> #len:size_nat -> lseq a len -> l:list a{List.Tot.length l = len}

val concat:#a:Type -> #len1:size_nat -> #len2:size_nat{len1 + len2 <= maxint SIZE} -> lseq a len1 -> lseq a len2 -> lseq a (len1 + len2)

let (@|) #a #len1 #len2 s1 s2 = concat #a #len1 #len2 s1 s2

val map_blocks:
    #a:Type0
  -> blocksize:size_nat{blocksize > 0}
  -> nblocks:size_nat{nblocks * blocksize <= maxint SIZE}
  -> f:(i:size_nat{i + 1 <= nblocks} -> lseq a blocksize -> lseq a blocksize)
  -> inp:lseq a (nblocks * blocksize)
  -> out:lseq a (nblocks * blocksize)

val reduce_blocks:
    #a:Type0
  -> #b:Type0
  -> blocksize:size_nat{blocksize > 0}
  -> nblocks:size_nat{nblocks * blocksize <= maxint SIZE}
  -> f:(i:size_nat{i + 1 <= nblocks} -> lseq a blocksize -> b -> b)
  -> inp:lseq a (nblocks * blocksize)
  -> init:b
  -> out:b
