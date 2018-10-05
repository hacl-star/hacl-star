module Lib.Sequence

open FStar.Mul
open Lib.IntTypes

#set-options "--z3rlimit 15"

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

let slice #a #len i start fin = sub #a #len i start (fin - start)

let update_sub #a #len s start n x =
  let o =
    Seq.append
      (Seq.append (Seq.slice s 0 start) x)
      (Seq.slice s (start + n) len) in
  Seq.lemma_eq_intro (Seq.slice o start (start + n)) x;
  o

let lemma_update_sub #a #len dst start n src res =
  let res1 = update_sub dst start n src in
  FStar.Seq.Properties.lemma_split (sub res 0 (start + n)) start;
  FStar.Seq.Properties.lemma_split (sub res1 0 (start + n)) start;
  FStar.Seq.Properties.lemma_split res (start + n);
  FStar.Seq.Properties.lemma_split res1 (start + n)

let update_slice #a #len i start fin upd =
  update_sub #a #len i start (fin-start) upd

let rec repeat_left lo hi a f acc =
  if lo = hi then acc
  else repeat_left (lo + 1) hi a f (f lo acc)

let rec repeat_right lo hi a f acc =
  if lo = hi then acc
  else f (hi - 1) (repeat_right lo (hi - 1) a f acc)

let rec repeat_right_plus lo mi hi a f acc =
  if hi = mi then ()
  else repeat_right_plus lo mi (hi - 1) a f acc

let rec repeat_left_right lo hi a f acc =
  if lo = hi then ()
  else
    begin
    repeat_right_plus lo (lo + 1) hi a f acc;
    repeat_left_right (lo + 1) hi a f (f lo acc)
    end

let repeat n a f acc0 =
  repeat_right 0 n a f acc0

let unfold_repeat n a f acc0 i = ()
(* // Proof when using [repeat_left]:
  repeat_left_right 0 (i + 1) a f acc0;
  repeat_left_right 0 i a f acc0
*)

let fixed_a (a:Type) (i:size_nat) = a

let repeati #a n f acc0 =
  repeat n (fixed_a a) f acc0

let unfold_repeati #a n f acc0 i =
  unfold_repeat n (fixed_a a) f acc0 i

let repeat_range #a min max f x =
  repeat_left min max (fun _ -> a) f x

let repeath #a n f x = repeat_range 0 n (fun _ -> f) x

let rec repeat_range_inductive #a min max pred f x =
  repeat_left min max (fun i -> x:a{pred i x}) f x

let repeati_inductive #a =
  repeat_range_inductive #a 0

let lbytes_eq_inner #len a b i r =
  let open Lib.RawIntTypes in
  let open FStar.UInt8 in
  r && (u8_to_UInt8 a.[i] =^ u8_to_UInt8 b.[i])

let lbytes_eq #len a b =
  repeat len (fun _ -> bool) (lbytes_eq_inner a b) true

let rec fold_left_range_ #a #b #len min max f l x =
  if len = 0 then x
  else
    let h = Seq.head l in
    let t = Seq.tail l in
    fold_left_range_ #a #b #(len - 1) (min + 1) max f t (f min h x)

let fold_left_range #a #b #len min max f l x =
  fold_left_range_ #a #b #(max - min) min max f (slice #a #len l min max) x

let fold_lefti #a #b #len = fold_left_range #a #b #len 0 len

let fold_left #a #b #len f = fold_left_range #a #b #len 0 len (fun i -> f)

let map #a #b #len f s =
  Seq.seq_of_list (List.Tot.map f (Seq.seq_to_list s))

let for_all #a #len f x = Seq.for_all f x

private inline_for_extraction noextract
val map2_list: #a:Type -> #b:Type -> #c:Type
  -> f:(a -> b -> c) -> l1:list a -> l2:list b{List.Tot.length l1 == List.Tot.length l2}
  -> l:list c{List.Tot.length l == List.Tot.length l1}
let rec map2_list #a #b #c f l1 l2 =
  match l1, l2 with
  | [], [] -> []
  | x::l1', y::l2' -> f x y :: map2_list f l1' l2'

let map2 #a #b #c #len f s1 s2 =
  Seq.seq_of_list (map2_list f (Seq.seq_to_list s1) (Seq.seq_to_list s2))

let rec for_all2 #a #b #len f x y =
  if Seq.length x = 0 then true
  else
    f (Seq.head x) (Seq.head y) && for_all2 #a #b #(len - 1) f (Seq.tail x) (Seq.tail y)

let as_list #a #len s = Seq.Properties.seq_to_list s

let concat #a #len1 #len2 s1 s2 = Seq.append s1 s2

let map_blocks #a bs nb f inp =
  let len = nb * bs in
  let out = inp in
  let out =
    repeati #(lseq a len) nb
    (fun i out ->
      update_slice #a out (i * bs) ((i+1) * bs) (f i (slice #a inp (i * bs) ((i+1) * bs))))
    out in
  out

let reduce_blocks #a #b bs nb f inp init =
  let len = nb * bs in
  let acc = init in
  let acc =
    repeati #b nb
    (fun i acc ->
      f i (slice #a inp (i * bs) ((i+1) * bs)) acc)
    acc in
  acc
