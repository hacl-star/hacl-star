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

/// Bounded Sequences

(* This is the type of bounded sequences.
   Use this as much as possible.
   It adds additional length checks that you'd have to prove in the implementation otherwise *)

(** Definition of a fixed-length Sequence *)
let lseq (a:Type0) (len:size_nat) = s:seq a{Seq.length s == len}

val index:
    #a:Type
  -> #len:size_nat
  -> s:lseq a len
  -> i:size_nat{i < len}
  -> a

(** Creation of a fixed-length Sequence from an initial value *)
val create:
    #a:Type
  -> len:size_nat
  -> init:a
  -> s:lseq a len{(forall (i:nat).
    {:pattern (index s i)} i < len ==> index s i == init)}

(** Concatenate sequences: use with care, may make implementation hard to verify *)
val concat:
    #a:Type
  -> #len0:size_nat
  -> #len1:size_nat{len0 + len1 <= max_size_t}
  -> s0:lseq a len0
  -> s1:lseq a len1
  -> s2:lseq a (len0 + len1)


(** Conversion from Sequence to fixed-length Sequence *)
let to_lseq (#a:Type0) (s:seq a{length s <= max_size_t}) : l:lseq a (length s){l == s} = s

(** Conversion of a Sequence to a list *)
val to_list:
    #a:Type
  -> #len:size_nat
  -> s:lseq a len
  -> l:list a{List.Tot.length l = len}

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
let op_String_Access #a #len = index #a #len

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
      sub res 0 start == sub dst 0 start /\
      sub res start n == src /\
      sub res (start + n) (length dst - start - n) ==
      sub dst (start + n) (length dst - start - n))
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
