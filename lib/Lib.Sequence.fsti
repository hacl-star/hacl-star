module Lib.Sequence

open FStar.Mul
open Lib.IntTypes
#set-options "--z3rlimit 15"

/// Unbounded sequences, derived from FStar.Seq

(* This is the type of unbounded sequences.
   Use this only when dealing with, say, user input whose length is unbounded.
   As far as possible use the API for bounded sequences defined later in this file.*)

(** Definition of a Sequence *)
let seq (a:Type0) = s:Seq.seq a

(** Length of a Sequence *)
let length (#a:Type0) (s:seq a) : nat = Seq.length s

(** Access to an element of a Sequence *)
val index: #a:Type -> s:seq a -> n:nat{length s > 0 /\ n < length s} -> a

(** Concatenation of two Sequences *)
val concat:#a:Type -> s1:seq a -> s2:seq a -> r:seq a{length r == length s1 + length s2}

(** Operator for concatenation of two Sequences*)
let (@|) #a s1 s2 = concat #a s1 s2

(** Equality of two Sequences *)
abstract
type equal (#a:Type) (s1:seq a) (s2:seq a) =
 length s1 == length s2 /\
 (forall (i:nat{i < length s1}).{:pattern (index s1 i); (index s2 i)} index s1 i == index s2 i)

(** Lemma on equality of two Sequences *)
val eq_intro:
    #a:Type
  -> s1:seq a
  -> s2:seq a
  -> Lemma
    (requires (length s1 == length s2 /\ (forall (i:nat{i < length s1}).{:pattern (index s1 i); (index s2 i)} index s1 i == index s2 i)))
    (ensures  (equal s1 s2))
  [SMTPat (equal s1 s2)]

(** Lemma on equality of two Sequences *)
val eq_elim:
    #a:Type
  -> s1:seq a
  -> s2:seq a
  -> Lemma
    (requires equal s1 s2)
    (ensures  s1 == s2)
  [SMTPat (equal s1 s2)]

(* The following functions on unbounded sequences should not be needed in normal crypto specs.
   Maybe we should leave them in the .fst and not expose them here. *)

(** Updating an element of un unbounded Sequence *)
val seq_upd:
    #a:Type
  -> s:seq a
  -> n:nat{n < length s}
  -> x:a
  -> o:seq a{length o == length s /\ index o n == x /\ (forall (i:nat).
    {:pattern (index s i)} (i < length s /\ i <> n) ==> index o i == index s i)}

(** Selecting a subset of an unbounded Sequence *)
val seq_sub:
    #a:Type
  -> s1:seq a
  -> start:nat
  -> n:nat{start + n <= length s1}
  -> s2:seq a{length s2 == n /\
	     (forall (k:nat{k < n}). {:pattern (index s2 k)} index s2 k == index s1 (start + k))}

(** Updating a subset of an unbounded Sequence with another Sequence *)
val seq_update_sub:
    #a:Type
  -> i:seq a
  -> start:nat
  -> n:nat{start + n <= length i}
  -> x:seq a{length x == n}
  -> o:seq a{length o == length i /\ seq_sub o start n == x /\
    (forall (k:nat{(0 <= k /\ k < start) \/ (start + n <= k /\ k < length i)}).
      {:pattern (index o k)} index o k == index i k)}

(** Lemma on update of a sub-Sequence *)
val lemma_seq_update_sub:
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
      seq_sub res 0 start == seq_sub dst 0 start /\
      seq_sub res start n == src /\
      seq_sub res (start + n) (length dst - start - n) ==
      seq_sub dst (start + n) (length dst - start - n))
    (ensures
      res == seq_update_sub dst start n src)

(** Creation of a Sequence from an initial value *)
val seq_create:
    #a:Type
  -> len:nat
  -> init:a
  -> s:seq a{length s == len /\ (forall (i:nat).
    {:pattern (index s i)} i < len ==> index s i == init)}

(** Creation of a Sequence from a list of values *)
val seq_of_list:
    #a:Type
  -> l:list a
  -> s:seq a{length s == List.Tot.length l}

val seq_of_list_index:
    #a:Type
  -> l:list a
  -> i:nat{i < List.Tot.length l}
  -> Lemma (index (seq_of_list l) i == List.Tot.index l i)
    [SMTPat (index (seq_of_list l) i)]

(** Map function for Sequences *)
val seq_map:#a:Type -> #b:Type -> (a -> Tot b) -> s1:seq a -> s2:seq b{length s2 == length s1}

(** Map2 function for Sequences *)
val seq_map2:#a:Type -> #b:Type -> #c:Type
  -> f:(a -> b -> Tot c)
  -> s1:seq a
  -> s2:seq b{length s1 == length s2}
  -> s3:seq c{length s3 == length s2}

(** Forall function for Sequences *)
val seq_for_all:#a:Type -> (a -> Tot bool) -> seq a -> bool

(** Forall2 function for Sequences *)
val seq_for_all2:#a:Type -> #b:Type
  -> (a -> b -> Tot bool)
  -> s1:seq a
  -> s2:seq b{length s1 == length s2}
  -> bool

/// Bounded Sequences

(* This is the type of bounded sequences.
   Use this as much as possible.
   It adds additional length checks that you'd have to prove in the implementation otherwise *)

(** Definition of a fixed-length Sequence *)
let lseq (a:Type0) (len:size_nat) = s:seq a{(* len > 0 /\*) Seq.length s == len}

(** Creation of a fixed-length Sequence from an initial value *)
val create:
    #a:Type
  -> len:size_nat
  -> init:a
  -> s:lseq a len{(forall (i:nat).
    {:pattern (index s i)} i < len ==> index s i == init)}

(** Conversion from Sequence to fixed-length Sequence *)
let to_lseq (#a:Type0) (s:seq a{length s <= max_size_t}) : l:lseq a (length s){l == s} = s

(** Conversion of a Sequence to a list *)
val to_list:
    #a:Type
  -> s:seq a
  -> l:list a{List.Tot.length l = length s}

(** Creation of a fixed-length Sequence from a list of values *)
val of_list:
    #a:Type
  -> l:list a{List.Tot.length l <= max_size_t}
  -> s:lseq a (List.Tot.length l)

val of_list_index:
    #a:Type
  -> l:list a{List.Tot.length l <= max_size_t}
  -> i:nat{i < List.Tot.length l}
  -> Lemma (index (of_list l) i == List.Tot.index l i)
    [SMTPat (index (of_list l) i)]

(* Alias for creation from a list *)
let createL #a l = of_list #a l

(** Updating an element of a fixed-length Sequence *)
val upd:
    #a:Type
  -> #len:size_nat
  -> s:lseq a len
  -> n:size_nat{n < len}
  -> x:a
  -> o:lseq a len{index o n == x /\ (forall (i:size_nat).
    {:pattern (index s i)} (i < length s /\ i <> n) ==> index o i == index s i)}

(** Operator for accessing an element of a fixed-length Sequence *)
unfold
let op_String_Access #a = index #a

(** Operator for updating an element of a fixed-length Sequence *)
unfold
let op_String_Assignment #a #len = upd #a #len

(** Selecting a subset of a fixed-length Sequence *)
val sub:
    #a:Type
  -> #len:size_nat
  -> s1:lseq a len
  -> start:size_nat
  -> n:size_nat{start + n <= len}
  -> s2:lseq a n{
	     (forall (k:nat{k < n}). {:pattern (index s2 k)} index s2 k == index s1 (start + k))}

(** Selecting a subset of a fixed-length Sequence *)
let slice
    (#a:Type)
    (#len:size_nat)
    (s1:lseq a len)
    (start:nat)
    (fin:nat{start <= fin /\ fin <= len})
  =
  sub #a s1 start (fin - start)

(** Updating a sub-Sequence from another fixed-length Sequence *)
val update_sub:
    #a:Type
  -> #len:size_nat
  -> i:lseq a len
  -> start:size_nat
  -> n:size_nat{start + n <= len}
  -> x:lseq a n
  -> o:lseq a len{sub o start n == x /\
    (forall (k:nat{(0 <= k /\ k < start) \/ (start + n <= k /\ k < length i)}).
      {:pattern (index o k)} index o k == index i k)}

(** Lemma regarding updating a sub-Sequence with another Sequence *)
val lemma_update_sub:
    #a:Type
  -> #len:size_nat
  -> dst:lseq a len
  -> start:size_nat
  -> n:size_nat{start + n <= len}
  -> src:lseq a n
  -> res:lseq a len
  -> Lemma
    (requires
      seq_sub res 0 start == seq_sub dst 0 start /\
      sub res start n == src /\
      seq_sub res (start + n) (length dst - start - n) ==
      seq_sub dst (start + n) (length dst - start - n))
    (ensures
      res == update_sub dst start n src)

(** Updating a sub-Sequence from another fixed-length Sequence *)
let update_slice
    (#a:Type)
    (#len:size_nat)
    (i:lseq a len)
    (start:size_nat)
	 (fin:size_nat{start <= fin /\ fin <= len})
    (upd:lseq a (fin - start))
  =
  update_sub #a i start (fin - start) upd

(** Map function for fixed-length Sequences *)
val map:#a:Type -> #b:Type -> #len:size_nat -> (a -> Tot b) -> s1:lseq a len -> s2:lseq b len

(** Map2 function for fixed-length Sequences *)
val map2:#a:Type -> #b:Type -> #c:Type -> #len:size_nat
  -> f:(a -> b -> Tot c)
  -> s1:lseq a len
  -> s2:lseq b len
  -> s3:lseq c len

(** Forall function for fixed-length Sequences *)
val for_all:#a:Type -> #len:size_nat -> (a -> Tot bool) -> lseq a len -> bool

(** Forall2 function for fixed-length Sequences *)
val for_all2:#a:Type -> #b:Type -> #len:size_nat
  -> (a -> b -> Tot bool)
  -> s1:lseq a len
  -> s2:lseq b len
  -> bool

(** Secure comparison of Byte Sequences *)
(* BB. TODO: The following function should move to ByteSequence *)
val lbytes_eq:#len:size_nat -> lseq uint8 len -> lseq uint8 len -> bool

(* The following functions allow us to bridge between unbounded and bounded sequences *)
val map_blocks:
    #a:Type0
  -> blocksize:size_nat{blocksize > 0}
  -> inp:seq a
  -> f:(i:nat{i < length inp / blocksize} -> lseq a blocksize -> lseq a blocksize)
  -> g:(i:nat{i <= length inp / blocksize} -> len:size_nat{len < blocksize} -> s:lseq a len -> lseq a len)
  -> out:seq a {length out == length inp}

val repeat_blocks:
    #a:Type0
  -> #b:Type0
  -> blocksize:size_nat{blocksize > 0}
  -> inp:seq a
  -> f:(i:nat{i < length inp / blocksize} -> lseq a blocksize -> b -> b)
  -> l:(i:nat{i <= length inp / blocksize} -> len:size_nat{len < blocksize} -> s:lseq a len -> b -> b)
  -> init:b
  -> out:b
