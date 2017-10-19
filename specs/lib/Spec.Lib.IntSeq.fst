module Spec.Lib.IntSeq

open FStar.Mul
open Spec.Lib.IntTypes

#set-options "--z3rlimit 100"

let lseq (a:Type0) (len:size_t) =  s:list a {List.Tot.length s = len}

val create_: #a:Type -> len:size_t -> init:a -> Tot (lseq a len) (decreases (len))
let rec create_ #a len x = 
  if len = 0 then []
  else
    let t = create_ #a (size_decr len) x in
    x :: t 
let create = create_

let createL #a l = l


val repeat_: #a:Type -> n:size_t -> (a -> Tot a) -> a -> Tot (a) (decreases (n))
let rec repeat_ #a n f x = 
  match n with
  | 0 -> x
  | _ -> repeat_ #a (size_decr n) f (f x)
let repeat = repeat_

val repeati_: #a:Type -> i:size_t -> n:size_t{i <= n} -> (s:size_t{s < n} -> a -> Tot a) -> a -> Tot (a) (decreases (n - i))
let rec repeati_ #a i n f x = 
  if i = n then x
  else repeati_ #a (size_incr i) n f (f i x)
let repeati #a = repeati_ #a ( 0)

val fold_left_: #a:Type -> #b:Type -> #len:size_t -> (a -> b -> Tot b) -> lseq a len -> b -> Tot (b) (decreases (len))
let rec fold_left_ #a #b #len f l init =
  match l with
  | [] -> init 
  | h :: t -> fold_left_ #a #b #(size_decr len) f t (f h init)
let fold_left = fold_left_

val fold_lefti_: #a:Type -> #b:Type -> #fulllen:size_t -> #len:size_t{len <= fulllen} -> (size_t -> a -> b -> Tot b) -> lseq a len -> b -> Tot (b) (decreases (len))
let rec fold_lefti_ #a #b #fulllen #len f l init =
  match l with
  | [] -> init 
  | h :: t -> let i = fulllen - len in 
	    fold_lefti_ #a #b #fulllen #(size_decr len) f t (f i h init)
let fold_lefti #a #b #len = fold_lefti_ #a #b #len #len

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

val nat_from_intseq_be_:#t:inttype -> #len:size_t -> b:intseq t len -> Tot (n:nat{n < pow2 (len * bits t)})  (decreases (len))
let rec nat_from_intseq_be_ #t #len b = 
  if len = 0 then 0
  else
    let l = uint_to_nat #t (last #(uint_t t) #len b) in
    let pre : intseq t (size_decr len) = prefix #len b (size_decr len) in
    admit();
    l + (pow2 (bits t)) * (nat_from_intseq_be_ #t #(size_decr len) pre)

let nat_from_intseq_be = nat_from_intseq_be_


val nat_from_intseq_le_:#t:inttype -> #len:size_t -> b:intseq t len -> Tot (n:nat{n < pow2 (len * bits t)}) (decreases (len))
let rec nat_from_intseq_le_ #t #len (b:intseq t len)  =
  match len,b with
  | 0, _ -> (0) 
  | _, h::tt -> 
    admit();
    uint_to_nat h + pow2 (bits t) * (nat_from_intseq_le_ #t #(size_decr len) tt)

let nat_from_intseq_le = nat_from_intseq_le_

val nat_to_bytes_be: 
  len:size_t -> n:nat{ n < pow2 (8 * len)} ->
  Tot (b:intseq U8 len {n == nat_from_intseq_be #U8 #len b}) (decreases (len))
#reset-options "--z3rlimit 200"
let rec nat_to_bytes_be len n = 
  if len = 0 then [] 
  else (
    let len' = size_decr len in 
    let byte = u8 (n % 256) in
    let n' =  n / 256 in 
    Math.Lemmas.pow2_plus 8 (8 * len');
    assume( n' < pow2 (8 * len' ));
    let b' : intseq U8 len' = nat_to_bytes_be len' n' in
    let b  : intseq U8 len = snoc #uint8 #len' b' byte in
    assert(b' == prefix b len');
    assert(byte == last #uint8 #len b);
    admit();
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
    admit();
    b

let nat_to_bytes_le = nat_to_bytes_le_

let uint_to_bytes_le #t n = 
  admit();
  nat_to_bytes_le (numbytes t) (uint_to_nat n)
let uint_to_bytes_be #t n = 
  admit();
  nat_to_bytes_be (numbytes t) (uint_to_nat n)
let uint_from_bytes_le #t b = 
  let n = nat_from_intseq_le #U8 #(numbytes t) b in
  admit();
  nat_to_uint #t n
  
let uint_from_bytes_be #t b = 
  let n = nat_from_intseq_be #U8 #(numbytes t) b in
  admit();
  nat_to_uint #t n

