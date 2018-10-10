module Lib.Sequence

open FStar.Mul
open Lib.IntTypes
open Lib.LoopCombinators

#set-options "--z3rlimit 15"

(** Access to an element of a Sequence *)
val seq_index: #a:Type -> s:seq a -> n:nat{length s > 0 /\ n < length s} -> a
let seq_index #a s n = Seq.index s n

(** Concatenation of two Sequences *)
val seq_concat:#a:Type -> s1:seq a -> s2:seq a -> r:seq a{length r == length s1 + length s2}

let seq_concat #a s1 s2 =
  let r = (Seq.append s1 s2 <: seq a) in
  assert (length r == length s1 + length s2);
  r

(** Equality of two Sequences *)
abstract
type equal (#a:Type) (s1:seq a) (s2:seq a) =
 length s1 == length s2 /\
 (forall (i:nat{i < length s1}).{:pattern (seq_index s1 i); (seq_index s2 i)} seq_index s1 i == seq_index s2 i)

(** Lemma on equality of two Sequences *)
val eq_intro:
    #a:Type
  -> s1:seq a
  -> s2:seq a
  -> Lemma
    (requires (length s1 == length s2 /\ (forall (i:nat{i < length s1}).{:pattern (seq_index s1 i); (seq_index s2 i)} seq_index s1 i == seq_index s2 i)))
    (ensures  (equal s1 s2))
  [SMTPat (equal s1 s2)]
let eq_intro #a s1 s2 =
  assert (forall (i:nat{i < length s1}).{:pattern (Seq.index s1 i); (Seq.index s2 i)}
    seq_index s1 i == seq_index s2 i);
  Seq.lemma_eq_intro #a s1 s2

(** Lemma on equality of two Sequences *)
val eq_elim:
    #a:Type
  -> s1:seq a
  -> s2:seq a
  -> Lemma
    (requires equal s1 s2)
    (ensures  s1 == s2)
  [SMTPat (equal s1 s2)]
let eq_elim #a s1 s2 =
  assert (length s1 == length s2);
  assert (forall (i:nat{i < length s1}).{:pattern (Seq.index s1 i); (Seq.index s2 i)}
    seq_index s1 i == seq_index s2 i);
  Seq.lemma_eq_elim #a s1 s2

(* The following functions on unbounded sequences should not be needed in normal crypto specs.
   Maybe we should leave them in the .fst and not expose them here. *)

(** Updating an element of un unbounded Sequence *)
val seq_upd:
    #a:Type
  -> s:seq a
  -> n:nat{n < length s}
  -> x:a
  -> o:seq a{length o == length s /\ seq_index o n == x /\ (forall (i:nat).
    {:pattern (seq_index s i)} (i < length s /\ i <> n) ==> seq_index o i == seq_index s i)}
let seq_upd #a s n x = Seq.upd #a s n x

(** Selecting a subset of an unbounded Sequence *)
val seq_sub:
    #a:Type
  -> s1:seq a
  -> start:nat
  -> n:nat{start + n <= length s1}
  -> s2:seq a{length s2 == n /\
	     (forall (k:nat{k < n}). {:pattern (seq_index s2 k)} seq_index s2 k == seq_index s1 (start + k))}
let seq_sub #a s start n =
  let r = Seq.slice #a s start (start + n) in
  assert (length r == n);
  r

(** Updating a subset of an unbounded Sequence with another Sequence *)
val seq_update_sub:
    #a:Type
  -> i:seq a
  -> start:nat
  -> n:nat{start + n <= length i}
  -> x:seq a{length x == n}
  -> o:seq a{length o == length i /\ seq_sub o start n == x /\
    (forall (k:nat{(0 <= k /\ k < start) \/ (start + n <= k /\ k < length i)}).
      {:pattern (seq_index o k)} seq_index o k == seq_index i k)}
let seq_update_sub #a s start n x =
  let o =
    Seq.append
      (Seq.append (Seq.slice s 0 start) x)
      (Seq.slice s (start + n) (length s)) in
  Seq.lemma_eq_intro (Seq.slice o start (start + n)) x;
  o

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
let lemma_seq_update_sub #a dst start n src res =
  let res1 = seq_update_sub dst start n src in
  FStar.Seq.Properties.lemma_split (seq_sub res 0 (start + n)) start;
  FStar.Seq.Properties.lemma_split (seq_sub res1 0 (start + n)) start;
  FStar.Seq.Properties.lemma_split res (start + n);
  FStar.Seq.Properties.lemma_split res1 (start + n)

(** Creation of a Sequence from an initial value *)
val seq_create:
    #a:Type
  -> len:nat
  -> init:a
  -> s:seq a{length s == len /\ (forall (i:nat).
    {:pattern (seq_index s i)} i < len ==> seq_index s i == init)}
let seq_create #a len init = Seq.create #a len init

(** Creation of a Sequence from a list of values *)
val seq_of_list:
    #a:Type
  -> l:list a
  -> s:seq a{length s == List.Tot.length l}
let seq_of_list #a l = Seq.seq_of_list #a l

val seq_of_list_index:
    #a:Type
  -> l:list a
  -> i:nat{i < List.Tot.length l}
  -> Lemma (seq_index (seq_of_list l) i == List.Tot.index l i)
    [SMTPat (seq_index (seq_of_list l) i)]
let seq_of_list_index #a l i =
  Seq.lemma_seq_of_list_index #a l i


(** Map function for Sequences *)
val seq_map:#a:Type -> #b:Type -> (a -> Tot b) -> s1:seq a -> s2:seq b{length s2 == length s1}
let seq_map #a #b f s =
  Seq.seq_of_list (List.Tot.map f (Seq.seq_to_list s))

private inline_for_extraction noextract
val map2_list: #a:Type -> #b:Type -> #c:Type
  -> f:(a -> b -> c) -> l1:list a -> l2:list b{List.Tot.length l1 == List.Tot.length l2}
  -> l:list c{List.Tot.length l == List.Tot.length l1}
let rec map2_list #a #b #c f l1 l2 =
  match l1, l2 with
  | [], [] -> []
  | x::l1', y::l2' -> f x y :: map2_list f l1' l2'


(** Map2 function for Sequences *)
val seq_map2:#a:Type -> #b:Type -> #c:Type
  -> f:(a -> b -> Tot c)
  -> s1:seq a
  -> s2:seq b{length s1 == length s2}
  -> s3:seq c{length s3 == length s2}
let seq_map2 #a #b #c f s1 s2 =
  Seq.seq_of_list (map2_list f (Seq.seq_to_list s1) (Seq.seq_to_list s2))

(** Forall function for Sequences *)
val seq_for_all:#a:Type -> (a -> Tot bool) -> seq a -> bool
let seq_for_all #a f x = Seq.for_all f x

(** Forall2 function for Sequences *)
val seq_for_all2:#a:Type -> #b:Type
  -> (a -> b -> Tot bool)
  -> s1:seq a
  -> s2:seq b{length s1 == length s2}
  -> bool
let seq_for_all2 #a #b f x y =
  let r = seq_map2 (fun xi yi -> f xi yi) x y in
  seq_for_all (fun bi -> bi = true) r


let index #a #len s n = seq_index s n

let create #a len init = Seq.create #a len init

let concat #a #len0 #len1 s0 s1 = seq_concat s0 s1

let to_list #a #len s = Seq.Properties.seq_to_list s

let of_list #a l = seq_of_list #a l

let of_list_index #a l i =
  Seq.lemma_seq_of_list_index #a l i  

let upd #a #len s n x = seq_upd #a s n x

let sub #a #len s start n =
  to_lseq (seq_sub #a s start n)

let update_sub #a #len i start n x =
    to_lseq (seq_update_sub #a i start n x)

let lemma_update_sub #a #len dst start n src res =
    lemma_seq_update_sub #a dst start n src res

let map #a #b #len f s = seq_map #a #b f s

let map2 #a #b #c #len f s1 s2 = seq_map2 #a #b #c f s1 s2

let for_all #a #len f x = seq_for_all #a f x

let for_all2 #a #b #len f x y = seq_for_all2 #a #b f x y

val lbytes_eq_inner:
    #len:size_nat
  -> a:lseq uint8 len
  -> b:lseq uint8 len
  -> i:size_nat{i < len}
  -> r:bool
  -> bool
let lbytes_eq_inner #len a b i r =
  let open Lib.RawIntTypes in
  let open FStar.UInt8 in
  r && (u8_to_UInt8 (index a i) =^ u8_to_UInt8 (index b i))

val lbytes_eq_state: len:size_nat -> i:size_nat{i <= len} -> Type0
let lbytes_eq_state len i = bool

let lbytes_eq #len a b =
  repeat_gen len (lbytes_eq_state len) (lbytes_eq_inner a b) true

let map_blocks #a bs inp f g =
  let len = length inp in
  let nb = len / bs in
  let rem = len % bs in
  let out = inp in
  let out =
    repeati #(s:seq a{length s == len}) nb
    (fun i out ->
      assert ((i+1) * bs <= nb * bs);
      seq_update_sub #a out (i * bs) bs
	   (f i (seq_sub inp (i * bs) bs))
    ) out in
  if rem > 0 then
    seq_update_sub out (nb * bs) rem (g nb rem (seq_sub inp (nb * bs) rem))
  else out

let repeat_blocks #a #b bs inp f g init =
  let len = length inp in
  let nb = len / bs in
  let rem = len % bs in
  let acc =
    repeati nb
    (fun i acc ->
       assert ((i+1) * bs <= nb * bs);
       let block = seq_sub inp (i * bs) bs in
       f i block acc)
    init in
  let last = seq_sub inp (nb * bs) rem in
  g nb rem last acc
