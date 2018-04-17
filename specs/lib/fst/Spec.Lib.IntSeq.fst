module Spec.Lib.IntSeq

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes

#reset-options "--z3rlimit 300"

let decr (x:size_nat{x > 0}) : size_nat = x - 1
let incr (x:size_nat{x < max_size_t}) : size_nat = x + 1

let lseq (a:Type0) (len:size_nat) =  s:list a {List.Tot.length s = len}

val create_: #a:Type -> len:size_nat -> init:a -> Tot (lseq a len) (decreases (len))
let rec create_ #a len x =
  if len = 0 then []
  else
    let t = create_ #a (decr len) x in
    x :: t
let create = create_

let createL #a l = l

val index_: #a:Type -> #len:size_nat{len > 0} -> lseq a len -> n:size_nat{n < len} -> Tot a (decreases (n))
let rec index_ #a #len l i =
  match i, l with
  | 0, h::t -> h
  | n, h::t -> index_ #a #(decr len) t (decr i)

let index = index_

val upd_: #a:Type -> #len:size_nat -> lseq a len -> n:size_nat{n < len /\ len > 0} -> x:a -> Tot (o:lseq a len{index o n == x}) (decreases (n))
let rec upd_ #a #len l i x =
  match i,l with
  | 0, h::t -> x::t
  | n, h::t -> h::upd_ #a #(decr len) t (decr i) x

let upd = upd_

val prefix_: #a:Type -> #len:size_nat -> lseq a len -> n:size_nat{n <= len} -> Tot (lseq a n) (decreases (n))
let rec prefix_ #a #len l n =
  match n,l with
  | 0, _ -> []
  | n', h::t -> h::prefix_ #a #(decr len) t (decr n)

let prefix = prefix_

val suffix: #a:Type -> #len:size_nat -> lseq a len -> n:size_nat{n <= len} -> Tot (lseq a (len - n)) (decreases (n))
let rec suffix #a #len l n =
  match n,l with
  | 0, _ ->   l
  | _, h::t -> suffix #a #(decr len) t (decr n)

let sub #a #len l s n =
  let suf = suffix #a #len l s in
  prefix #(len - s) suf n

let slice #a #len l s f = sub #a #len l s (f-s)

val last: #a:Type -> #len:size_nat{len > 0} -> x:lseq a len -> a
let last #a #len x = index #a #len x (decr len)

val snoc: #a:Type -> #len:size_nat{len < maxint U32} -> i:lseq a len -> x:a -> Tot (o:lseq a (incr len){i == prefix #(incr len) o len /\ last o == x}) (decreases (len))
let rec snoc #a #len i x =
  match i with
  | [] -> [x]
  | h::t -> h::snoc #a #(decr len) t x

val update_prefix: #a:Type -> #len:size_nat -> lseq a len -> n:size_nat{n <= len} -> x:lseq a n -> Tot (o:lseq a len{sub o 0 n == x}) (decreases (len))
let rec update_prefix #a #len l n l' =
  match n,l,l' with
  | 0, _, _ -> l
  | _, h::t, h'::t' -> h':: update_prefix #a #(decr len) t (decr n) t'

val update_sub_: #a:Type -> #len:size_nat -> lseq a len -> start:size_nat -> n:size_nat{start + n <= len} -> x:lseq a n -> Tot (o:lseq a len{sub o start n == x}) (decreases (len))
let rec update_sub_ #a #len l s n l' =
  match s,l with
  | 0, l -> update_prefix #a #len l n l'
  | _, h::t -> h:: update_sub_ #a #(decr len) t (decr s) n l'

let update_sub = update_sub_

let update_slice #a #len l s f sl = update_sub #a #len l s (f-s) sl

val repeat_range_: #a:Type -> min:size_nat -> max:size_nat{min <= max} -> (s:size_nat{s >= min /\ s < max} -> a -> Tot a) -> a -> Tot (a) (decreases (max - min))
let rec repeat_range_ #a min max f x =
  if min = max then x
  else repeat_range_ #a (incr min) max f (f min x)


let repeat_range = repeat_range_
let repeati #a = repeat_range #a 0
let repeat #a n f x = repeat_range 0 n (fun i -> f) x

unfold type repeatable (#a:Type) (#n:size_nat) (pred:(i:size_nat{i <= n} -> a -> Tot Type)) = i:size_nat{i < n} -> x:a -> Pure a (requires (pred i x)) (ensures (fun r -> pred (i+1) r))

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
val map_: #a:Type -> #b:Type -> #len:size_nat -> (a -> Tot b) -> lseq a len -> Tot (lseq b len) (decreases (len))
let rec map_ #a #b #len f x =
  match x with
  | [] -> []
  | h :: t ->
	 let t' : lseq a (decr len) = t in
	 f h :: map_ #a #b #(decr len) f t'
let map = map_


val for_all_: #a:Type -> #len:size_nat -> (a -> Tot bool) -> lseq a len -> Tot bool (decreases (len))
let rec for_all_ #a #len f x =
  match x with
  | [] -> true
  | h :: t ->
	 let t' : lseq a (decr len) = t in
	 f h && for_all_ #a #(decr len) f t'

let for_all = for_all_

val ghost_map_: #a:Type -> #b:Type -> #len:size_nat -> (a -> GTot b) -> lseq a len -> GTot (lseq b len) (decreases (len))
let rec ghost_map_ #a #b #len f x = match x with
  | [] -> []
  | h :: t ->
	 let t' : lseq a (decr len) = t in
	 f h :: ghost_map_ #a #b #(decr len) f t'

let ghost_map = ghost_map_

val map2_: #a:Type -> #b:Type -> #c:Type -> #len:size_nat -> (a -> b -> Tot c) -> lseq a len -> lseq b len -> Tot (lseq c len) (decreases (len))
let rec map2_ #a #b #c #len f x y = match x,y with
  | [],[] -> []
  | h1 :: t1, h2 :: t2 ->
	 let t1' : lseq a (decr len) = t1 in
	 let t2' : lseq b (decr len) = t2 in
	 f h1 h2 :: map2_ #a #b #c #(decr len) f t1' t2'

let map2 = map2_

val for_all2_: #a:Type -> #b:Type -> #len:size_nat -> (a -> b -> Tot bool) -> lseq a len -> lseq b len -> Tot (bool) (decreases (len))
let rec for_all2_ #a #b #len f x y = match x,y with
  | [],[] -> true
  | h1 :: t1, h2 :: t2 ->
	 let t1' : lseq a (decr len) = t1 in
	 let t2' : lseq b (decr len) = t2 in
	 f h1 h2 && for_all2_ #a #b #(decr len) f t1' t2'

let for_all2 = for_all2_


val nat_from_intseq_be_:#t:inttype -> #len:size_nat -> b:intseq t len -> Tot (n:nat{n < pow2 (len * bits t)})  (decreases (len))
let rec nat_from_intseq_be_ #t #len b =
  if len = 0 then 0
  else
    let l = uint_to_nat #t (last #(uint_t t) #len b) in
    let pre : intseq t (decr len) = prefix #len b (decr len) in
    let shift = pow2 (bits t) in
    let n' : n:nat{n < pow2 ((len-1) * bits t)}  = nat_from_intseq_be_ #t #(decr len) pre in
    assert (l <= shift - 1);
    assert (l + shift * n' <= shift * (n' + 1) - 1);
    assert (n' + 1 <= pow2 ((len -1) * bits t));
    assert (shift * (n' + 1) <= shift * pow2 (len * bits t - bits t));
    assert (shift * (n' + 1) <= pow2 (bits t) * pow2 (len * bits t - bits t));
    Math.Lemmas.pow2_plus (bits t) ( len * bits t - bits t);
    assert (shift * (n' + 1) <= pow2 (len  * bits t));
    l + shift * n'

let nat_from_intseq_be = nat_from_intseq_be_


val nat_from_intseq_le_:#t:inttype -> #len:size_nat -> b:intseq t len -> Tot (n:nat{n < pow2 (len * bits t)}) (decreases (len))
let rec nat_from_intseq_le_ #t #len (b:intseq t len)  =
  match len,b with
  | 0, _ -> (0)
  | _, h::tt ->
    let shift = pow2 (bits t) in
    let n' : n:nat{n < pow2 ((len-1) * bits t)}  = nat_from_intseq_le_ #t #(decr len) tt in
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

val nat_to_bytes_be_:
  len:size_nat -> n:nat{ n < pow2 (8 * len)} ->
  Tot (b:intseq U8 len {n == nat_from_intseq_be #U8 #len b}) (decreases (len))
let rec nat_to_bytes_be_ len n =
  if len = 0 then []
  else (
    let len' = decr len in
    let byte = u8 (n % 256) in
    let n' =  n / 256 in
    Math.Lemmas.pow2_plus 8 (8 * len');
    assert( n' < pow2 (8 * len' ));
    let b' : intseq U8 len' = nat_to_bytes_be_ len' n' in
    let b  : intseq U8 len = snoc #uint8 #len' b' byte in
    assert(b' == prefix b len');
    assert(byte == last #uint8 #len b);
    b)
let nat_to_bytes_be = nat_to_bytes_be_

val nat_to_bytes_le_:
  len:size_nat -> n:nat{n < pow2 (8 * len)} ->
  Tot (b:intseq U8 len {n == nat_from_intseq_le #U8 #len b}) (decreases (len))
let rec nat_to_bytes_le_ len n =
  if len = 0 then  []
  else
    let len = decr len in
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

let uints_to_bytes_le #t (#len:size_nat{len * numbytes t < pow2 32}) (l:intseq t len) : lbytes (len * numbytes t) =
  let b = create (len * numbytes t) (u8 0) in
  repeati len (fun i b -> update_sub b (i * numbytes t) (numbytes t) (uint_to_bytes_le l.[i])) b

let uints_to_bytes_be #t (#len:size_nat{len * numbytes t < pow2 32}) (l:intseq t len) : lbytes (len * numbytes t) =
  let b = create (len * numbytes t) (u8 0) in
  repeati len (fun i b -> update_sub b (i * numbytes t) (numbytes t) (uint_to_bytes_be l.[i])) b

let uints_from_bytes_le #t (#len:size_nat{len * numbytes t < pow2 32}) (b:lbytes (len * numbytes t)) : intseq t len =
  let l = create #(uint_t t) len (nat_to_uint 0) in
  repeati len (fun i l -> l.[i] <- uint_from_bytes_le (sub b (i * numbytes t) (numbytes t))) l

let uints_from_bytes_be #t (#len:size_nat{len * numbytes t < pow2 32}) (b:lbytes (len * numbytes t)) : intseq t len =
  let l = create #(uint_t t) len (nat_to_uint 0) in
  repeati len (fun i l -> l.[i] <- uint_from_bytes_be (sub b (i * numbytes t) (numbytes t))) l

let as_list #a #len l = l

(*
val map_block_: #a:Type -> #b:Type -> min:size_nat -> max:size_nat{min <= max} ->
		blocksize:size_nat{max * blocksize <= max_size_t} -> 
		(i:size_nat{i >= min /\ i < max} -> lseq a blocksize -> lseq b blocksize) -> 
		lseq a ((max - min) * blocksize) -> 
		Tot (lseq b ((max - min) * blocksize)) (decreases (max - min))
let rec map_block_ #a #b min max sz f x =
  if min = max then []
  else 
    let h = slice x 0 sz in 
    let t = slice x sz ((max - min) * sz) in
    let h' = f min h in
    let t' = map_block_ #a #b (min+1) max sz f t in
    let r = h' @ t' in
    List.Tot.append_length h' t';
    r

let map_block #a #b n sz f x = map_block_ #a #b 0 n sz f x
*)
