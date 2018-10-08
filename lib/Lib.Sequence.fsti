module Lib.Sequence

open FStar.Mul
open Lib.IntTypes

#set-options "--z3rlimit 15"

/// Definition of sequences

(* This is the type of unbounded sequences. 
   Use this only when dealing with, say, user input whose length is unbounded *)
   
let seq (a:Type0) = s:Seq.seq a

(* This is the type of bounded sequences. 
   Use this as much as possible. 
   It adds additional length checks that you'd have to prove in the implementation otherwise *)

let lseq (a:Type0) (len:size_nat) = s:seq a{len > 0 /\ Seq.length s == len}

let length (#a:Type0) (s:seq a) : nat = Seq.length s

let to_lseq (#a:Type0) (s:seq a{length s > 0 /\ length s <= max_size_t}) : l:lseq a (length s){l == s} = s

val index: #a:Type -> s:seq a -> n:nat{length s > 0 /\ n < length s} -> a

abstract
type equal (#a:Type) (s1:seq a) (s2:seq a) =
 length s1 == length s2 /\
 (forall (i:nat{i < length s1}).{:pattern (index s1 i); (index s2 i)} index s1 i == index s2 i)

val eq_intro:
    #a:Type
  -> s1:seq a
  -> s2:seq a
  -> Lemma
    (requires (length s1 == length s2 /\ (forall (i:nat{i < length s1}).{:pattern (index s1 i); (index s2 i)} index s1 i == index s2 i)))
    (ensures  (equal s1 s2))
  [SMTPat (equal s1 s2)]

val eq_elim:
    #a:Type
  -> s1:seq a 
  -> s2:seq a 
  -> Lemma
    (requires equal s1 s2)
    (ensures  s1 == s2)
  [SMTPat (equal s1 s2)]

val upd:
    #a:Type
  -> s:seq a
  -> n:nat{n < length s}
  -> x:a
  -> o:seq a{length o == length s /\ index o n == x /\ (forall (i:nat).
    {:pattern (index s i)} (i < length s /\ i <> n) ==> index o i == index s i)}

val sub:
    #a:Type
  -> s1:seq a
  -> start:nat
  -> n:nat{start + n <= length s1}
  -> s2:seq a{length s2 == n /\ 
	     (forall (k:nat{k < n}). {:pattern (index s2 k)} index s2 k == index s1 (start + k))}

let slice (#a:Type) (s1:seq a) (start:nat) (fin:nat{start <= fin /\ fin <= length s1}) = sub #a s1 start (fin - start)

val update_sub:
    #a:Type
  -> i:seq a
  -> start:nat
  -> n:nat{start + n <= length i}
  -> x:seq a{length x == n}
  -> o:seq a{length o == length i /\ sub o start n == x /\
    (forall (k:nat{(0 <= k /\ k < start) \/ (start + n <= k /\ k < length i)}).
      {:pattern (index o k)} index o k == index i k)}

val lemma_update_sub:
    #a:Type
  -> dst:seq a
  -> start:nat
  -> n:nat{start + n <= length dst}
  -> src:seq a
  -> res:seq a
  -> Lemma
    (requires
      length res == length dst /\
      length src == n /\
      sub res 0 start == sub dst 0 start /\
      sub res start n == src /\
      sub res (start + n) (length dst - start - n) ==
      sub dst (start + n) (length dst - start - n))
    (ensures
      res == update_sub dst start n src)

let update_slice (#a:Type) (i:seq a) (start:nat) (fin:nat{start <= fin /\ fin <= length i}) 
                 (upd:seq a{length upd == fin - start}) = update_sub #a i start (fin - start) upd


///
/// Allocation functions for bounded sequences
///

val seq_create:
    #a:Type
  -> len:nat
  -> init:a
  -> s:seq a{length s == len /\ (forall (i:nat).
    {:pattern (index s i)} i < len ==> index s i == init)}

val create:
    #a:Type
  -> len:size_nat{len > 0}
  -> init:a
  -> s:lseq a len{(forall (i:nat).
    {:pattern (index s i)} i < len ==> index s i == init)}

val to_list:
    #a:Type 
  -> s:seq a 
  -> l:list a{List.Tot.length l = length s}

val of_list:
    #a:Type 
  -> l:list a
  -> s:seq a{length s == List.Tot.length l}

let createL #a l = of_list #a l

val concat:#a:Type -> s1:seq a -> s2:seq a -> r:seq a{length r == length s1 + length s2}
let (@|) #a s1 s2 = concat #a s1 s2

unfold
let op_String_Access #a = index #a 

unfold
let op_String_Assignment #a = upd #a




/// Iteration Patterns (may be good to move this to a different module)

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
    lo:nat
  -> hi:nat{lo <= hi}
  -> a:(i:nat{lo <= i /\ i <= hi} -> Type)
  -> f:(i:nat{lo <= i /\ i < hi} -> a i -> a (i + 1))
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
    lo:nat
  -> hi:nat{lo <= hi}
  -> a:(i:nat{lo <= i /\ i <= hi} -> Type)
  -> f:(i:nat{lo <= i /\ i < hi} -> a i -> a (i + 1))
  -> acc:a lo
  -> Tot (a hi) (decreases (hi - lo))

(** Splitting a repetition *)
val repeat_right_plus:
    lo:nat
  -> mi:nat{lo <= mi}
  -> hi:nat{mi <= hi}
  -> a:(i:nat{lo <= i /\ i <= hi} -> Type)
  -> f:(i:nat{lo <= i /\ i < hi} -> a i -> a (i + 1))
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
    lo:nat
  -> hi:nat{lo <= hi}
  -> a:(i:nat{lo <= i /\ i <= hi} -> Type)
  -> f:(i:nat{lo <= i /\ i < hi} -> a i -> a (i + 1))
  -> acc:a lo
  -> Lemma (ensures repeat_right lo hi a f acc == repeat_left lo hi a f acc)
    (decreases (hi - lo))

(**
* Repetition starting from 0
*
* Defined as [repeat_right] for convenience, but [repeat_left] may be more
* efficient when extracted to OCaml.
*)

val repeat_gen:
    n:nat
  -> a:(i:nat{i <= n} -> Type)
  -> f:(i:nat{i < n} -> a i -> a (i + 1))
  -> acc0:a 0
  -> a n

(** Unfolding one iteration *)
val unfold_repeat_gen:
    n:nat
  -> a:(i:nat{i <= n} -> Type)
  -> f:(i:nat{i < n} -> a i -> a (i + 1))
  -> acc0:a 0
  -> i:nat{i < n}
  -> Lemma (repeat_gen (i + 1) a f acc0 == f i (repeat_gen i a f acc0))

(**
* Repetition with a fixed accumulator type
*)

val repeati:
    #a:Type
  -> n:nat
  -> f:(i:nat{i < n} -> a -> a)
  -> acc0:a
  -> a

(** Unfolding one iteration *)
val unfold_repeati:
    #a:Type
  -> n:nat
  -> f:(i:nat{i < n} -> a -> a)
  -> acc0:a
  -> i:nat{i < n}
  -> Lemma (repeati #a (i + 1) f acc0 == f i (repeati #a i f acc0))

val repeat:
    #a:Type
  -> n:nat
  -> f:(a -> a)
  -> acc0:a
  -> a

val repeat_range:
  #a:Type
  -> min:nat
  -> max:nat{min <= max}
  -> (s:nat{s >= min /\ s < max} -> a -> Tot a)
  -> a
  -> Tot a (decreases (max - min))

unfold
type repeatable (#a:Type) (#n:nat) (pred:(i:nat{i <= n} -> a -> Tot Type)) =
  i:nat{i < n} -> x:a{pred i x} -> y:a{pred (i+1) y}

val repeat_range_inductive:
    #a:Type
  -> min:nat
  -> max:nat{min <= max}
  -> pred:(i:nat{i <= max} -> a -> Type)
  -> f:repeatable #a #max pred
  -> x0:a{pred min x0}
  -> Tot (res:a{pred max res}) (decreases (max - min))

val repeati_inductive:
   #a:Type
 -> n:nat
 -> pred:(i:nat{i <= n} -> a -> Type)
 -> f:repeatable #a #n pred
 -> x0:a{pred 0 x0}
 -> res:a{pred n res}

val map:#a:Type -> #b:Type -> (a -> Tot b) -> s1:seq a -> s2:seq b{length s2 == length s1}

val map2:#a:Type -> #b:Type -> #c:Type 
  -> f:(a -> b -> Tot c) 
  -> s1:seq a 
  -> s2:seq b{length s1 == length s2} 
  -> s3:seq c{length s3 == length s2}

val for_all:#a:Type -> (a -> Tot bool) -> seq a -> bool

val for_all2:#a:Type -> #b:Type 
  -> (a -> b -> Tot bool) 
  -> s1:seq a 
  -> s2:seq b{length s1 == length s2}
  -> bool

val lbytes_eq:#len:size_nat -> lseq uint8 len -> lseq uint8 len -> bool

val map_blocks:
    #a:Type0
  -> blocksize:size_nat{blocksize > 0}
  -> inp:seq a 
  -> f:(i:nat{i < length inp / blocksize} -> lseq a blocksize -> lseq a blocksize)
  -> g:(i:nat{i <= length inp / blocksize} -> len:size_nat{len < blocksize} -> lseq a len -> lseq a len)
  -> out:seq a {length out == length inp}
  

val repeat_blocks:
    #a:Type0
  -> #b:Type0
  -> blocksize:size_nat{blocksize > 0}
  -> inp:seq a
  -> f:(i:nat{i < length inp / blocksize} -> lseq a blocksize -> b -> b)
  -> l:(i:nat{i <= length inp / blocksize} -> len:size_nat{len < blocksize} -> lseq a len -> b -> b)
  -> init:b
  -> out:b
