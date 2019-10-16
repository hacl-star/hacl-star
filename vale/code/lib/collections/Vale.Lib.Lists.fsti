module Vale.Lib.Lists

open FStar.Seq
open FStar.UInt
open FStar.Mul
module List = FStar.List.Tot
open FStar.List.Tot.Properties

val singleton_list_rev (#a:Type) (x:a) : Lemma
  (List.rev [x] == [x])

val list_cons_is_append (#a:Type) (h:a) (t:list a) : Lemma
  (h::t == [h] @ t)

val singleton_list_seq (#a:Type) (x:a) : Lemma
  (seq_of_list [x] == create 1 x)

val list_append_length (#a:Type) (x y:list a) : Lemma
  (List.length (x @ y) == List.length x + List.length y)

val list_append_index (#a:Type) (x y:list a) (i:nat) : Lemma
  (requires i < List.length (x @ y))
  (ensures (
    let nx = List.length x in
    (i >= nx ==> i - nx < List.length y) /\
    List.index (x @ y) i == (if i < nx then List.index x i else List.index y (i - nx))
  ))

val append_list_seq (#a:Type) (x y:list a) : Lemma
  (seq_of_list (x @ y) == append (seq_of_list x) (seq_of_list y))

let rec from_list_le (l:list bool) : int =
  match l with
  | [] -> 0
  | h::t -> (if h then 1 else 0) + 2 * (from_list_le t)

let from_list_be (l:list bool) : int =
  from_list_le (List.rev l)

val lemma_from_list_le (l:list bool) : Lemma
  (ensures (
    let rl = List.rev l in
    let s = seq_of_list rl in
    from_list_le l == from_vec #(List.length rl) s
  ))

val lemma_from_list_be (l:list bool) : Lemma
  (ensures (
    let s = seq_of_list l in
    from_list_be l == from_vec #(List.length l) s
  ))
