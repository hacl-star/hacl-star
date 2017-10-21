module Spec.Lib.IntSeq

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes

#reset-options "--z3rlimit 300"

let lseq (a:Type0) (len:size_t) =  s:list a {List.Tot.length s = len}

val create_: #a:Type -> len:size_t -> init:a -> Tot (lseq a len) (decreases (len))
let rec create_ #a len x = 
  if len = 0 then []
  else
    let t = create_ #a (size_decr len) x in
    x :: t 
let create = create_

let createL #a l = l

val index_: #a:Type -> #len:size_t{len > 0} -> lseq a len -> n:size_t{n < len} -> Tot a (decreases (n))
let rec index_ #a #len l i = 
  match i, l with
  | 0, h::t -> h
  | n, h::t -> index_ #a #(size_decr len) t (size_decr i)

let index = index_

val upd_: #a:Type -> #len:size_t -> lseq a len -> n:size_t{n < len /\ len > 0} -> x:a -> Tot (lseq a len) (decreases (n))
let rec upd_ #a #len l i x = 
  match i,l with
  | 0, h::t -> x::t
  | n, h::t -> h::upd_ #a #(size_decr len) t (size_decr i) x

let upd = upd_

val prefix_: #a:Type -> #len:size_t -> lseq a len -> n:size_t{n <= len} -> Tot (lseq a n) (decreases (n))
let rec prefix_ #a #len l n =
  match n,l with
  | 0, _ -> []
  | n', h::t -> h::prefix_ #a #(size_decr len) t (size_decr n)

let prefix = prefix_

val suffix: #a:Type -> #len:size_t -> lseq a len -> n:size_t{n <= len} -> Tot (lseq a (len - n)) (decreases (n))
let rec suffix #a #len l n =
  match n,l with
  | 0, _ ->   l
  | _, h::t -> suffix #a #(size_decr len) t (size_decr n) 

let sub #a #len l s n = 
  let suf = suffix #a #len l s in
  prefix #(len - s) suf n

let slice #a #len l s f = sub #a #len l s (f-s)

val last: #a:Type -> #len:size_t{len > 0} -> x:lseq a len -> a
let last #a #len x = index #a #len x (size_decr len)

val snoc: #a:Type -> #len:size_t{len < maxint U32} -> i:lseq a len -> x:a -> Tot (o:lseq a (size_incr len){i == prefix #(size_incr len) o len /\ last o == x}) (decreases (len))
let rec snoc #a #len i x = 
  match i with 
  | [] -> [x] 
  | h::t -> h::snoc #a #(size_decr len) t x

val update_prefix: #a:Type -> #len:size_t -> lseq a len -> n:size_t{n <= len} -> lseq a n -> Tot (lseq a len) (decreases (len))
let rec update_prefix #a #len l n l' =
  match n,l,l' with
  | 0, _, _ -> l
  | _, h::t, h'::t' -> h':: update_prefix #a #(size_decr len) t (size_decr n) t'

val update_sub_: #a:Type -> #len:size_t -> lseq a len -> start:size_t -> n:size_t{start + n <= len} -> lseq a n -> Tot (lseq a len) (decreases (len))
let rec update_sub_ #a #len l s n l' = 
  match s,l with 
  | 0, l -> update_prefix #a #len l n l'
  | _, h::t -> h:: update_sub_ #a #(size_decr len) t (size_decr s) n l'

let update_sub = update_sub_ 

let update_slice #a #len l s f sl = update_sub #a #len l s (f-s) sl

val repeat_range_: #a:Type -> min:size_t -> max:size_t{min <= max} -> (s:size_t{s >= min /\ s < max} -> a -> Tot a) -> a -> Tot (a) (decreases (max - min))
let rec repeat_range_ #a min max f x = 
  if min = max then x
  else repeat_range_ #a (size_incr min) max f (f min x)

let repeat_range = repeat_range_
let repeati #a = repeat_range #a 0
let repeat #a n f x = repeat_range 0 n (fun i -> f) x


val fold_left_range_: #a:Type -> #b:Type -> #len:size_t -> min:size_t ->
  max:size_t{min <= max /\ len = max - min} -> 
  (i:size_t{i >= min /\ i < max} -> a -> b -> Tot b) ->
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
val map_: #a:Type -> #b:Type -> #len:size_t -> (a -> Tot b) -> lseq a len -> Tot (lseq b len) (decreases (len))
let rec map_ #a #b #len f x =
  match x with
  | [] -> []
  | h :: t -> 
	 let t' : lseq a (size_decr len) = t in
	 f h :: map_ #a #b #(size_decr len) f t'

let map = map_


val for_all_: #a:Type -> #len:size_t -> (a -> Tot bool) -> lseq a len -> Tot bool (decreases (len))
let rec for_all_ #a #len f x =
  match x with
  | [] -> true
  | h :: t -> 
	 let t' : lseq a (size_decr len) = t in
	 f h && for_all_ #a #(size_decr len) f t'

let for_all = for_all_

val ghost_map_: #a:Type -> #b:Type -> #len:size_t -> (a -> GTot b) -> lseq a len -> GTot (lseq b len) (decreases (len))
let rec ghost_map_ #a #b #len f x = match x with
  | [] -> []
  | h :: t -> 
	 let t' : lseq a (size_decr len) = t in
	 f h :: ghost_map_ #a #b #(size_decr len) f t'

let ghost_map = ghost_map_

val map2_: #a:Type -> #b:Type -> #c:Type -> #len:size_t -> (a -> b -> Tot c) -> lseq a len -> lseq b len -> Tot (lseq c len) (decreases (len))
let rec map2_ #a #b #c #len f x y = match x,y with
  | [],[] -> []
  | h1 :: t1, h2 :: t2 -> 
	 let t1' : lseq a (size_decr len) = t1 in
	 let t2' : lseq b (size_decr len) = t2 in
	 f h1 h2 :: map2_ #a #b #c #(size_decr len) f t1' t2'

let map2 = map2_

val for_all2_: #a:Type -> #b:Type -> #len:size_t -> (a -> b -> Tot bool) -> lseq a len -> lseq b len -> Tot (bool) (decreases (len))
let rec for_all2_ #a #b #len f x y = match x,y with
  | [],[] -> true
  | h1 :: t1, h2 :: t2 -> 
	 let t1' : lseq a (size_decr len) = t1 in
	 let t2' : lseq b (size_decr len) = t2 in
	 f h1 h2 && for_all2_ #a #b #(size_decr len) f t1' t2'

let for_all2 = for_all2_


val nat_from_intseq_be_:#t:inttype -> #len:size_t -> b:intseq t len -> Tot (n:nat{n < pow2 (len * bits t)})  (decreases (len))
let rec nat_from_intseq_be_ #t #len b = 
  if len = 0 then 0
  else
    let l = uint_to_nat #t (last #(uint_t t) #len b) in
    let pre : intseq t (size_decr len) = prefix #len b (size_decr len) in
    let shift = pow2 (bits t) in
    let n' : n:nat{n < pow2 ((len-1) * bits t)}  = nat_from_intseq_be_ #t #(size_decr len) pre in
    assert (l <= shift - 1);
    assert (l + shift * n' <= shift * (n' + 1) - 1);
    assert (n' + 1 <= pow2 ((len -1) * bits t));
    assert (shift * (n' + 1) <= shift * pow2 (len * bits t - bits t));
    assert (shift * (n' + 1) <= pow2 (bits t) * pow2 (len * bits t - bits t));
    Math.Lemmas.pow2_plus (bits t) ( len * bits t - bits t);
    assert (shift * (n' + 1) <= pow2 (len  * bits t));
    l + shift * n'

let nat_from_intseq_be = nat_from_intseq_be_


val nat_from_intseq_le_:#t:inttype -> #len:size_t -> b:intseq t len -> Tot (n:nat{n < pow2 (len * bits t)}) (decreases (len))
let rec nat_from_intseq_le_ #t #len (b:intseq t len)  =
  match len,b with
  | 0, _ -> (0) 
  | _, h::tt -> 
    let shift = pow2 (bits t) in
    let n' : n:nat{n < pow2 ((len-1) * bits t)}  = nat_from_intseq_le_ #t #(size_decr len) tt in
    let l = uint_to_nat #t h in
    assert (l <= shift - 1);
    assert (l + shift * n' <= shift * (n' + 1) - 1);
    assert (n' + 1 <= pow2 ((len -1) * bits t));
    assert (shift * (n' + 1) <= pow2 (bits t) * pow2 (len * bits t - bits t));
    Math.Lemmas.pow2_plus (bits t) ( len * bits t - bits t);
    assert (shift * (n' + 1) <= pow2 (len  * bits t));
    l + shift * n'

let nat_from_intseq_le = nat_from_intseq_le_

let nat_from_bytes_be = nat_from_intseq_be
let nat_from_bytes_le = nat_from_intseq_le

val nat_to_bytes_be: 
  len:size_t -> n:nat{ n < pow2 (8 * len)} ->
  Tot (b:intseq U8 len {n == nat_from_intseq_be #U8 #len b}) (decreases (len))
let rec nat_to_bytes_be len n = 
  if len = 0 then [] 
  else (
    let len' = size_decr len in 
    let byte = u8 (n % 256) in
    let n' =  n / 256 in 
    Math.Lemmas.pow2_plus 8 (8 * len');
    assert( n' < pow2 (8 * len' ));
    let b' : intseq U8 len' = nat_to_bytes_be len' n' in
    let b  : intseq U8 len = snoc #uint8 #len' b' byte in
    assert(b' == prefix b len');
    assert(byte == last #uint8 #len b);
    b)

val nat_to_bytes_le_:
  len:size_t -> n:nat{n < pow2 (8 * len)} ->
  Tot (b:intseq U8 len {n == nat_from_intseq_le #U8 #len b}) (decreases (len))
let rec nat_to_bytes_le_ len n = 
  if len = 0 then  []
  else
    let len = size_decr len in 
    let byte = u8 (n % 256) in
    let n' = n / 256 in 
    Math.Lemmas.pow2_plus 8 (8 * len);
    assert(n' < pow2 (8 * len ));
    let b' : intseq U8 len = nat_to_bytes_le_ len n' in
    let b = byte :: b' in
    b

let nat_to_bytes_le = nat_to_bytes_le_

let uint_to_bytes_le #t n = 
  nat_to_bytes_le (numbytes t) (uint_to_nat n)

let uint_to_bytes_be #t n = 
  nat_to_bytes_be (numbytes t) (uint_to_nat n)

let uint_from_bytes_le #t b = 
  let n = nat_from_intseq_le #U8 #(numbytes t) b in
  nat_to_uint #t n
  
let uint_from_bytes_be #t b = 
  let n = nat_from_intseq_be #U8 #(numbytes t) b in
  nat_to_uint #t n

let uints_to_bytes_le #t (#len:size_t{len * numbytes t < pow2 32}) (l:intseq t len) : lbytes (len * numbytes t) =
  let b = create (len * numbytes t) (u8 0) in
  repeati len (fun i b -> update_sub b (i * numbytes t) (numbytes t) (uint_to_bytes_le l.[i])) b

let uints_to_bytes_be #t (#len:size_t{len * numbytes t < pow2 32}) (l:intseq t len) : lbytes (len * numbytes t) =
  let b = create (len * numbytes t) (u8 0) in
  repeati len (fun i b -> update_sub b (i * numbytes t) (numbytes t) (uint_to_bytes_be l.[i])) b

let uints_from_bytes_le #t (#len:size_t{len * numbytes t < pow2 32}) (b:lbytes (len * numbytes t)) : intseq t len =
  let l = create #(uint_t t) len (nat_to_uint 0) in
  repeati len (fun i l -> l.[i] <- uint_from_bytes_le (sub b (i * numbytes t) (numbytes t))) l

let uints_from_bytes_be #t (#len:size_t{len * numbytes t < pow2 32}) (b:lbytes (len * numbytes t)) : intseq t len =
  let l = create #(uint_t t) len (nat_to_uint 0) in
  repeati len (fun i l -> l.[i] <- uint_from_bytes_be (sub b (i * numbytes t) (numbytes t))) l

let rec iter_ml #a #len f l =
  match l with 
  | [] -> () 
  | h::t -> f h; iter_ml #a #(len - 1) f t 

