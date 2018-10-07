module Lib.Sequence

open FStar.Mul
open Lib.IntTypes

#set-options "--z3rlimit 15"

let index #a s n = Seq.index s n

let eq_intro #a s1 s2 =
  assert (forall (i:nat{i < length s1}).{:pattern (Seq.index s1 i); (Seq.index s2 i)}
    index s1 i == index s2 i);
  Seq.lemma_eq_intro #a s1 s2

let eq_elim #a s1 s2 =
  assert (length s1 == length s2);
  assert (forall (i:nat{i < length s1}).{:pattern (Seq.index s1 i); (Seq.index s2 i)}
    index s1 i == index s2 i);
  Seq.lemma_eq_elim #a s1 s2

let upd #a s n x = Seq.upd #a s n x

let sub #a s start n = 
  let r = Seq.slice #a s start (start + n) in
  assert (length r == n);
  r

let update_sub #a s start n x =
  let o =
    Seq.append
      (Seq.append (Seq.slice s 0 start) x)
      (Seq.slice s (start + n) (length s)) in
  Seq.lemma_eq_intro (Seq.slice o start (start + n)) x;
  o

let lemma_update_sub #a dst start n src res =
  let res1 = update_sub dst start n src in
  FStar.Seq.Properties.lemma_split (sub res 0 (start + n)) start;
  FStar.Seq.Properties.lemma_split (sub res1 0 (start + n)) start;
  FStar.Seq.Properties.lemma_split res (start + n);
  FStar.Seq.Properties.lemma_split res1 (start + n)

let seq_create #a len init = Seq.create #a len init

let create #a len init = seq_create #a len init

let to_list #a s = Seq.Properties.seq_to_list s

let of_list #a l = Seq.seq_of_list #a l

let concat #a s1 s2 = 
  let r = (Seq.append s1 s2 <: seq a) in
  assert (length r == length s1 + length s2);
  r


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

let repeat_gen n a f acc0 =
  repeat_right 0 n a f acc0

let unfold_repeat_gen n a f acc0 i = ()
(* // Proof when using [repeat_left]:
  repeat_left_right 0 (i + 1) a f acc0;
  repeat_left_right 0 i a f acc0
*)

let fixed_a (a:Type) (i:nat) = a

let repeati #a n f acc0 =
  repeat_gen n (fixed_a a) f acc0

let unfold_repeati #a n f acc0 i =
  unfold_repeat_gen n (fixed_a a) f acc0 i

let repeat #a n f acc0 =
  repeati n (fun i -> f) acc0

let repeat_range #a min max f x =
  repeat_left min max (fun _ -> a) f x

let rec repeat_range_inductive #a min max pred f x =
  repeat_left min max (fun i -> x:a{pred i x}) f x

let repeati_inductive #a =
  repeat_range_inductive #a 0

let map #a #b f s =
  Seq.seq_of_list (List.Tot.map f (Seq.seq_to_list s))

private inline_for_extraction noextract
val map2_list: #a:Type -> #b:Type -> #c:Type
  -> f:(a -> b -> c) -> l1:list a -> l2:list b{List.Tot.length l1 == List.Tot.length l2}
  -> l:list c{List.Tot.length l == List.Tot.length l1}
let rec map2_list #a #b #c f l1 l2 =
  match l1, l2 with
  | [], [] -> []
  | x::l1', y::l2' -> f x y :: map2_list f l1' l2'

let map2 #a #b #c f s1 s2 =
  Seq.seq_of_list (map2_list f (Seq.seq_to_list s1) (Seq.seq_to_list s2))

let for_all #a f x = Seq.for_all f x

let for_all2 #a #b f x y =
  let r = map2 (fun xi yi -> f xi yi) x y in
  for_all (fun bi -> bi = true) r
  


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
      update_sub #a out (i * bs) bs
	(f i (sub inp (i * bs) bs)))
    out in
  if rem > 0 then
    update_sub out (nb * bs) rem 
      (g nb rem (sub inp (nb * bs) rem))
  else out


let repeat_blocks #a #b bs inp f g init =
  let len = length inp in
  let nb = len / bs in
  let rem = len % bs in
  let blocks : s:seq a{length s == nb * bs } = sub inp 0 (nb * bs) in
  let acc : b = init in
  let acc =
    repeati #b nb 
    (fun i acc ->
       assert ((i+1) * bs <= nb * bs);
       let block : lseq a bs = sub inp (i * bs) bs in
       f i block acc)
    acc in
  if rem > 0 then
    let last : lseq a rem = sub #a inp (nb * bs) rem in
    g nb rem last acc
  else acc
