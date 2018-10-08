module Lib.Sequence

open FStar.Mul
open Lib.IntTypes
open Lib.LoopCombinators

#set-options "--z3rlimit 15"


let index #a s n = Seq.index s n
let concat #a s1 s2 =
  let r = (Seq.append s1 s2 <: seq a) in
  assert (length r == length s1 + length s2);
  r

let eq_intro #a s1 s2 =
  assert (forall (i:nat{i < length s1}).{:pattern (Seq.index s1 i); (Seq.index s2 i)}
    index s1 i == index s2 i);
  Seq.lemma_eq_intro #a s1 s2

let eq_elim #a s1 s2 =
  assert (length s1 == length s2);
  assert (forall (i:nat{i < length s1}).{:pattern (Seq.index s1 i); (Seq.index s2 i)}
    index s1 i == index s2 i);
  Seq.lemma_eq_elim #a s1 s2

let seq_upd #a s n x = Seq.upd #a s n x

let seq_sub #a s start n =
  let r = Seq.slice #a s start (start + n) in
  assert (length r == n);
  r

let seq_update_sub #a s start n x =
  let o =
    Seq.append
      (Seq.append (Seq.slice s 0 start) x)
      (Seq.slice s (start + n) (length s)) in
  Seq.lemma_eq_intro (Seq.slice o start (start + n)) x;
  o

let lemma_seq_update_sub #a dst start n src res =
  let res1 = seq_update_sub dst start n src in
  FStar.Seq.Properties.lemma_split (seq_sub res 0 (start + n)) start;
  FStar.Seq.Properties.lemma_split (seq_sub res1 0 (start + n)) start;
  FStar.Seq.Properties.lemma_split res (start + n);
  FStar.Seq.Properties.lemma_split res1 (start + n)

let seq_create #a len init = Seq.create #a len init

let seq_of_list #a l = Seq.seq_of_list #a l

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

let seq_map2 #a #b #c f s1 s2 =
  Seq.seq_of_list (map2_list f (Seq.seq_to_list s1) (Seq.seq_to_list s2))

let seq_for_all #a f x = Seq.for_all f x

let seq_for_all2 #a #b f x y =
  let r = seq_map2 (fun xi yi -> f xi yi) x y in
  seq_for_all (fun bi -> bi = true) r


let create #a len init = seq_create #a len init

let to_list #a s = Seq.Properties.seq_to_list s

let of_list #a l = seq_of_list #a l

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
  let blocks : s:seq a{length s == nb * bs } = seq_sub inp 0 (nb * bs) in
  let acc : b = init in
  let acc =
    repeati #b nb
    (fun i acc ->
       assert ((i+1) * bs <= nb * bs);
       let block : lseq a bs = seq_sub inp (i * bs) bs in
       f i block acc)
    acc in
  let last : lseq a rem = seq_sub #a inp (nb * bs) rem in
  g nb rem last acc
