module Lib.Sequence

open FStar.Mul
open Lib.IntTypes

let seq a = s:Seq.seq a{Seq.length s <= max_size_t}

let length #a l = Seq.length l

let to_lseq #a s = s

let to_seq #a #len s = s

let index #a #len s n = Seq.index s n

let eq_intro #a #len s1 s2 =
  assert (forall (i:nat{i < len}).{:pattern (Seq.index s1 i); (Seq.index s2 i)}
    index s1 i == index s2 i);
  Seq.lemma_eq_intro #a s1 s2

let eq_elim #a #len s1 s2 =
  assert (forall (i:nat{i < len}).{:pattern (Seq.index s1 i); (Seq.index s2 i)}
    index s1 i == index s2 i);
  Seq.lemma_eq_elim #a s1 s2

let upd #a #len s n x = Seq.upd #a s n x

let create #a len init = Seq.create #a len init

let createL #a l = Seq.createL #a l

let of_list #a l = Seq.of_list #a l

let sub #a #len s start n = Seq.slice #a s start (start + n)

let update_sub #a #len s start n x =
  let o =
    Seq.append
      (Seq.append (Seq.slice s 0 start) x)
      (Seq.slice s (start + n) len) in
  assert (Seq.equal (Seq.slice o start (start + n)) x);
  assert (forall (i:nat{0 <= i /\ i < len /\ (i < start \/ i >= start + n)}).
    Seq.index o i == Seq.index s i);
  o

// 2018.07.13 SZ: TODO
// Unsure why these functions are in Lib.Sequence; nothing to do with sequences

val repeat_range_: #a:Type
  -> min:size_nat
  -> max:size_nat{min <= max}
  -> (s:size_nat{s >= min /\ s < max} -> a -> Tot a)
  -> a
  -> Tot a (decreases (max - min))
let rec repeat_range_ #a min max f x =
  if min = max then x
  else repeat_range_ #a (min + 1) max f (f min x)

let repeat_range = repeat_range_

let repeati #a n = repeat_range #a 0 n

let repeat #a n f x = repeat_range 0 n (fun i -> f) x

val repeat_range_inductive_: #a:Type
  -> min:size_nat
  -> max:size_nat{min <= max}
  -> pred:(i:size_nat{i <= max} -> a -> Tot Type)
  -> f:repeatable #a #max pred
  -> x0:a{pred min x0}
  -> Tot (res:a{pred max res}) (decreases (max - min))
let rec repeat_range_inductive_ #a min max pred f x =
  if min = max then x
  else repeat_range_inductive_ #a (min + 1) max pred f (f min x)

let repeat_range_inductive = repeat_range_inductive_

let repeati_inductive #a = repeat_range_inductive #a 0

val fold_left_range_: #a:Type -> #b:Type -> #len:size_nat
  -> min:size_nat
  -> max:size_nat{min <= max /\ len = max - min}
  -> (i:size_nat{i >= min /\ i < max} -> a -> b -> Tot b)
  -> lseq a len
  -> b
  -> Tot b (decreases (max - min))
let rec fold_left_range_ #a #b #len min max f l x =
  admit()
(*
  match l with
  | [] -> x
  | h::t -> fold_left_range_ #a #b #(len - 1) (min + 1) max f t (f min h x)
*)

let fold_left_range #a #b #len min max f l x =
  fold_left_range_ #a #b #(max - min) min max f (slice #a #len l min max) x

let fold_lefti #a #b #len = fold_left_range #a #b #len 0 len

let fold_left #a #b #len f = fold_left_range #a #b #len 0 len (fun i -> f)

let rec map #a #b #len f x =
  admit()

let rec for_all #a #len f x = Seq.for_all f x

let rec map2 #a #b #c #len f x y =
  admit()

let rec for_all2 #a #b #len f x y =
  admit()

let as_list #a #len s = Seq.Properties.seq_to_list s

let rec concat #a #len1 #len2 s1 s2 = Seq.append s1 s2
