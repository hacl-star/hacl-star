module Lib.Sequence

open FStar.Mul
open Lib.IntTypes

#reset-options "--z3rlimit 300"

private
let decr (x:size_nat{x > 0}) : size_nat = x - 1

private
let incr (x:size_nat{x < max_size_t}) : size_nat = x + 1

let seq a = s:list a{List.Tot.length s <= max_size_t}
let length #a l = List.Tot.length l

let to_lseq #a s = s
let to_seq #a #len s = s

private abstract
val hd: #a:Type -> #len:size_nat{0 < len} -> s:lseq a len -> Tot a
let hd #a #len = function
  | h::_ -> h

private abstract
val tl: #a:Type -> #len:size_nat{len > 0} -> s:lseq a len -> Tot (lseq a (decr len))
let tl #a #len s = List.Tot.tl s

let rec index #a #len l i =
  if i = 0 then hd l
  else index (tl l) (i - 1)

let eq_intro #a #len s1 s2 = ()

private
val extensionality_: #a:Type -> len:size_nat -> s1:lseq a len -> s2:lseq a len ->
  p:((i:size_nat{i < len}) -> squash (index s1 i == index s2 i)) -> Lemma (s1 == s2)
let rec extensionality_ #a len s1 s2 p =
  match s1, s2 with
  | x1 :: s1', x2  :: s2' ->
    p 0; extensionality_ (decr len) s1' s2' (fun i -> p (incr i))
  | _ -> ()

let eq_elim #a #len s1 s2 = extensionality_ #a len s1 s2 (fun i -> ())

let rec upd #a #len l i x =
  match i,l with
  | 0, h::t -> x::t
  | n, h::t -> h::upd #a #(decr len) t (decr i) x

let rec create #a len x =
  if len = 0 then []
  else
    let t = create #a (decr len) x in
    x :: t

let createL #a l = l

val prefix: #a:Type -> #len:size_nat -> lseq a len -> n:size_nat{n <= len}
  -> Tot (lseq a n) (decreases n)
let rec prefix #a #len l n =
  match n,l with
  | 0, _ -> []
  | n', h::t -> h::prefix #a #(decr len) t (decr n)

val suffix: #a:Type -> #len:size_nat -> lseq a len -> n:size_nat{n <= len}
  -> Tot (lseq a (len - n)) (decreases n)
let rec suffix #a #len l n =
  match n with
  | 0 -> l
  | _ ->
    // 2018.06.26 SZ: Explicit coercion unavoidable?
    let f (#a:Type) (#b:Type{a == b}) (x:a) : b = x in
    f (suffix #a #(decr len) (tl l) (decr n))

let sub #a #len l s n =
  let suf = suffix #a #len l s in
  prefix #a #(len - s) suf n

val last: #a:Type -> #len:size_nat{len > 0} -> x:lseq a len -> a
let last #a #len x = index #a #len x (decr len)

val snoc: #a:Type -> #len:size_nat{len < maxint U32} -> i:lseq a len -> x:a -> Tot (o:lseq a (incr len){i == prefix #a #(incr len) o len /\ last o == x}) (decreases (len))
let rec snoc #a #len i x =
  match i with
  | [] -> [x]
  | h::t -> h::snoc #a #(decr len) t x

val update_prefix: #a:Type -> #len:size_nat -> lseq a len -> n:size_nat{n <= len} -> x:lseq a n -> Tot (o:lseq a len{sub o 0 n == x}) (decreases (len))
let rec update_prefix #a #len l n l' =
  match n,l,l' with
  | 0, _, _ -> l
  | _, h::t, h'::t' -> h':: update_prefix #a #(decr len) t (decr n) t'

let rec update_sub #a #len l s n l' =
  match s,l with
  | 0, l -> update_prefix #a #len l n l'
  | _, h::t -> h:: update_sub #a #(decr len) t (decr s) n l'

val repeat_range_: #a:Type -> min:size_nat -> max:size_nat{min <= max} -> (s:size_nat{s >= min /\ s < max} -> a -> Tot a) -> a -> Tot a (decreases (max - min))
let rec repeat_range_ #a min max f x =
  if min = max then x
  else repeat_range_ #a (incr min) max f (f min x)

val repeat_range_ghost_: #a:Type -> min:size_nat -> max:size_nat{min <= max} -> (s:size_nat{s >= min /\ s < max} -> a -> GTot a) -> a -> GTot (a) (decreases (max - min))
let rec repeat_range_ghost_ #a min max f x =
  if min = max then x
  else repeat_range_ghost_ #a (incr min) max f (f min x)

let repeat_range = repeat_range_
let repeat_range_ghost = repeat_range_ghost_
let repeati #a = repeat_range #a 0
let repeati_ghost #a = repeat_range_ghost #a 0
let repeat #a n f x = repeat_range 0 n (fun i -> f) x

val repeat_range_inductive_:
  #a:Type -> min:size_nat -> max:size_nat{min <= max} -> pred:(i:size_nat{i <= max} -> a -> Tot Type) -> f:repeatable #a #max pred -> x0:a{pred min x0} -> Tot (res:a{pred max res})
  (decreases (max - min))
let rec repeat_range_inductive_ #a min max pred f x =
  if min = max then x
  else repeat_range_inductive_ #a (incr min) max pred f (f min x)

let repeat_range_inductive = repeat_range_inductive_
let repeati_inductive #a = repeat_range_inductive #a 0

val fold_left_range_: #a:Type -> #b:Type -> #len:size_nat -> min:size_nat ->
  max:size_nat{min <= max /\ len = max - min} ->
  (i:size_nat{i >= min /\ i < max} -> a -> b -> Tot b) ->
  lseq a len -> b -> Tot b (decreases (max - min))
let rec fold_left_range_ #a #b #len min max f l x =
  match l with
  | [] -> x
  | h::t -> fold_left_range_ #a #b #(len - 1) (min + 1) max f t (f min h x)

let fold_left_range #a #b #len min max f l x =
  fold_left_range_ #a #b #(max - min) min max f (slice #a #len l min max) x

let fold_lefti #a #b #len = fold_left_range #a #b #len 0 len

let fold_left #a #b #len f = fold_left_range #a #b #len 0 len (fun i -> f)

(*
let fold_left_slices #a #b #len #slice_len f l b =
  let n = lin / slice_len in
  repeati #a n (fun i -> let sl = sub #a #len
*)
let rec map #a #b #len f x =
  match x with
  | [] -> []
  | h :: t ->
    let t' : lseq a (decr len) = t in
    f h :: map #a #b #(decr len) f t'

let rec for_all #a #len f x =
  match x with
  | [] -> true
  | h :: t ->
    let t' : lseq a (decr len) = t in
    f h && for_all #a #(decr len) f t'

let rec ghost_map #a #b #len f x = match x with
  | [] -> []
  | h :: t ->
    let t' : lseq a (decr len) = t in
    f h :: ghost_map #a #b #(decr len) f t'

let rec map2 #a #b #c #len f x y = match x,y with
  | [],[] -> []
  | h1 :: t1, h2 :: t2 ->
    let t1' : lseq a (decr len) = t1 in
    let t2' : lseq b (decr len) = t2 in
    f h1 h2 :: map2 #a #b #c #(decr len) f t1' t2'

let rec for_all2 #a #b #len f x y = match x,y with
  | [],[] -> true
  | h1 :: t1, h2 :: t2 ->
    let t1' : lseq a (decr len) = t1 in
    let t2' : lseq b (decr len) = t2 in
    f h1 h2 && for_all2 #a #b #(decr len) f t1' t2'

let as_list #a #len l = l

let rec concat #a #len1 #len2 s1 s2 =
  match s1 with
  | [] -> s2
  | h :: t -> h :: (concat #a #(len1 - 1) #len2 t s2)

let map_blocks #a bs nb f inp =
  let len = nb * bs in
  let out = inp in
  let out = repeati #(lseq a len) nb
	    (fun i out ->
	         update_slice #a out (i * bs) ((i+1) * bs)
			      (f i (slice #a inp (i * bs) ((i+1) * bs))))
	    out in
  out

let reduce_blocks #a #b bs nb f inp init =
  let len = nb * bs in
  let acc = init in
  let acc = repeati #b nb
	    (fun i acc ->
	       f i (slice #a inp (i * bs) ((i+1) * bs)) acc)
	    acc in
  acc


(*
#reset-options "--z3rlimit 400 --max_fuel 0"

let reduce_blocks #a #b bs inp f g init =
  let len = length inp in
  let blocks = len / bs in
  let rem = len % bs in
  let acc = repeati #b blocks
	       (fun i acc -> f i (slice (to_lseq inp) (i * bs) ((i+1) * bs)) acc)
	    init in
  let acc = g blocks rem (sub (to_lseq inp) (blocks * bs) rem) acc in
  acc
*)
