module Spec.Lib.IntSeq

open FStar.Mul
open Spec.Lib.IntTypes

#set-options "--z3rlimit 100"

type lseq (a:Type0) (len:size_t) = s:list a {List.Tot.length s = size_to_nat len}

val create_: #a:Type -> len:size_t -> init:a -> Tot (lseq a len) (decreases (size_to_nat len))
let rec create_ #a len x = 
  if size_to_nat len = 0 then []
  else
    let t = create_ #a (size_decr len) x in
    x :: t 
let create = create_

let createL #a l = l


val repeat_: #a:Type -> n:size_t -> (a -> Tot a) -> a -> Tot (a) (decreases (size_to_nat n))
let rec repeat_ #a n f x = 
  match size_to_nat n with
  | 0 -> x
  | _ -> repeat_ #a (size_decr n) f (f x)
let repeat = repeat_

val repeati_: #a:Type -> i:size_t -> n:size_t{size_to_nat i <= size_to_nat n} -> (size_t -> a -> Tot a) -> a -> Tot (a) (decreases (size_to_nat n - size_to_nat i))
let rec repeati_ #a i n f x = 
  if size_to_nat i = size_to_nat n then x
  else repeati_ #a (size_incr i) n f (f i x)
let repeati #a = repeati_ #a (nat_to_size 0)

val fold_left_: #a:Type -> #b:Type -> #len:size_t -> (a -> b -> Tot b) -> lseq a len -> b -> Tot (b) (decreases (size_to_nat len))
let rec fold_left_ #a #b #len f l init =
  match l with
  | [] -> init 
  | h :: t -> fold_left_ #a #b #(size_decr len) f t (f h init)
let fold_left = fold_left_

val fold_lefti_: #a:Type -> #b:Type -> #fulllen:size_t -> #len:size_t{size_to_nat len <= size_to_nat fulllen} -> (size_t -> a -> b -> Tot b) -> lseq a len -> b -> Tot (b) (decreases (size_to_nat len))
let rec fold_lefti_ #a #b #fulllen #len f l init =
  match l with
  | [] -> init 
  | h :: t -> let i = size_sub fulllen len in 
	    fold_lefti_ #a #b #fulllen #(size_decr len) f t (f i h init)
let fold_lefti #a #b #len = fold_lefti_ #a #b #len #len

val map_: #a:Type -> #b:Type -> #len:size_t -> (a -> Tot b) -> lseq a len -> Tot (lseq b len) (decreases (size_to_nat len))
let rec map_ #a #b #len f x =
  match x with
  | [] -> []
  | h :: t -> 
	 let t' : lseq a (size_decr len) = t in
	 f h :: map_ #a #b #(size_decr len) f t'

let map = map_


val ghost_map_: #a:Type -> #b:Type -> #len:size_t -> (a -> GTot b) -> lseq a len -> GTot (lseq b len) (decreases (size_to_nat len))
let rec ghost_map_ #a #b #len f x = match x with
  | [] -> []
  | h :: t -> 
	 let t' : lseq a (size_decr len) = t in
	 f h :: ghost_map_ #a #b #(size_decr len) f t'

let ghost_map = ghost_map_

val map2_: #a:Type -> #b:Type -> #c:Type -> #len:size_t -> (a -> b -> Tot c) -> lseq a len -> lseq b len -> Tot (lseq c len) (decreases (size_to_nat len))
let rec map2_ #a #b #c #len f x y = match x,y with
  | [],[] -> []
  | h1 :: t1, h2 :: t2 -> 
	 let t1' : lseq a (size_decr len) = t1 in
	 let t2' : lseq b (size_decr len) = t2 in
	 f h1 h2 :: map2_ #a #b #c #(size_decr len) f t1' t2'

let map2 = map2_

val index_: #a:Type -> #len:size_t{size_to_nat len > 0} -> lseq a len -> n:size_t{size_to_nat n < size_to_nat len} -> Tot a (decreases (size_to_nat n))
let rec index_ #a #len l i = 
  match size_to_nat i, l with
  | 0, h::t -> h
  | n, h::t -> index_ #a #(size_decr len) t (size_decr i)

let index = index_

val upd_: #a:Type -> #len:size_t -> lseq a len -> n:size_t{size_to_nat n < size_to_nat len /\ size_to_nat len > 0} -> x:a -> Tot (lseq a len) (decreases (size_to_nat n))
let rec upd_ #a #len l i x = 
  match size_to_nat i,l with
  | 0, h::t -> x::t
  | n, h::t -> h::upd_ #a #(size_decr len) t (size_decr i) x

let upd = upd_

val prefix_: #a:Type -> #len:size_t -> lseq a len -> n:size_t{size_to_nat n <= size_to_nat len} -> Tot (lseq a n) (decreases (size_to_nat n))
let rec prefix_ #a #len l n =
  match size_to_nat n,l with
  | 0, _ -> []
  | n', h::t -> h::prefix_ #a #(size_decr len) t (size_decr n)

let prefix = prefix_

val suffix_: #a:Type -> #len:size_t -> lseq a len -> n:size_t{size_to_nat n <= size_to_nat len} -> fin:size_t{fin = size_sub len n} -> Tot (lseq a fin) (decreases (size_to_nat n))

let rec suffix_ #a #len l n fin =
  match size_to_nat n,l with
  | 0, _ ->  
    assert (fin = len);
    l
  | _, h::t -> 
    assert(fin = size_sub (size_decr len) (size_decr n));
    suffix_ #a #(size_decr len) t (size_decr n) fin


let suffix #a #len l n = suffix_ #a #len l n (size_sub len n)

let rec slice #a #len l s n = 
  let suf = suffix #a #len l s in
  prefix #(size_sub len s) suf n

val last: #a:Type -> #len:size_t{size_to_nat len > 0} -> x:lseq a len -> a
let last #a #len x = index #a #len x (size_decr len)

val snoc: #a:Type -> #len:size_t{size_to_nat len < maxint U32} -> i:lseq a len -> x:a -> Tot (o:lseq a (size_incr len){i == prefix #(size_incr len) o len /\ last o == x}) (decreases (size_to_nat len))
let rec snoc #a #len i x = 
  match i with 
  | [] -> [x] 
  | h::t -> h::snoc #a #(size_decr len) t x

val update_prefix: #a:Type -> #len:size_t -> lseq a len -> n:size_t{size_to_nat n <= size_to_nat len} -> lseq a n -> Tot (lseq a len) (decreases (size_to_nat len))
let rec update_prefix #a #len l n l' =
  match size_to_nat n,l,l' with
  | 0, _, _ -> l
  | _, h::t, h'::t' -> h':: update_prefix #a #(size_decr len) t (size_decr n) t'

val update_slice_: #a:Type -> #len:size_t -> lseq a len -> start:size_t -> n:size_t{size_to_nat start + size_to_nat n <= size_to_nat len} -> lseq a n -> Tot (lseq a len) (decreases (size_to_nat len))
let rec update_slice_ #a #len l s n l' = 
  match size_to_nat s,l with 
  | 0, l -> update_prefix #a #len l n l'
  | _, h::t -> h:: update_slice_ #a #(size_decr len) t (size_decr s) n l'

let update_slice = update_slice_ 

val nat_from_intseq_be:#t:inttype -> #len:size_t -> b:intseq t len -> Tot nat (decreases (size_to_nat len))
let rec nat_from_intseq_be #t #len b = 
  if size_to_nat len = 0 then 0
  else
    let l = uint_to_nat #t (last #(uint_t t) #len b) in
    let pre : intseq t (size_decr len) = prefix #len b (size_decr len) in
    l + (pow2 (bits t)) * (nat_from_intseq_be #t #(size_decr len) pre)

val nat_from_intseq_le:#t:inttype -> #len:size_t -> b:intseq t len -> Tot nat (decreases (size_to_nat len))
let rec nat_from_intseq_le #t #len (b:intseq t len)  =
  match size_to_nat len,b with
  | 0, _ -> (0) 
  | _, h::tt -> 
    uint_to_nat h + pow2 (bits t) * (nat_from_intseq_le #t #(size_decr len) tt)

val nat_to_bytes_be: 
  len:size_t -> n:nat{ n < pow2 (8 * size_to_nat len)} ->
  Tot (b:intseq U8 len {n == nat_from_intseq_be #U8 #len b}) (decreases (size_to_nat len))
#reset-options "--z3rlimit 200"
let rec nat_to_bytes_be len n = 
  if size_to_nat len = 0 then [] 
  else (
    let len' = size_decr len in 
    let byte = u8 (n % 256) in
    let n' =  n / 256 in 
    Math.Lemmas.pow2_plus 8 (8 * size_to_nat len');
    assume( n' < pow2 (8 * size_to_nat len' ));
    let b' : intseq U8 len' = nat_to_bytes_be len' n' in
    let b  : intseq U8 len = snoc #uint8 #len' b' byte in
    assert(b' == prefix b len');
    assert(byte == last #uint8 #len b);
    admit();
    b)

val nat_to_bytes_le:
  len:size_t -> n:nat{n < pow2 (8 * size_to_nat len)} ->
  Tot (b:intseq U8 len {n == nat_from_intseq_le #U8 #len b}) (decreases (size_to_nat len))
let rec nat_to_bytes_le len n = 
  if size_to_nat len = 0 then  []
  else
    let len = size_decr len in 
    let byte = u8 (n % 256) in
    let n' = n / 256 in 
    Math.Lemmas.pow2_plus 8 (8 * size_to_nat len);
    assert(n' < pow2 (8 * size_to_nat len ));
    let b' : intseq U8 len = nat_to_bytes_le len n' in
    let b = byte :: b' in
    admit();
    b

let uint_to_bytes_le #t n = 
  admit();
  nat_to_bytes_le (nat_to_size (numbytes t)) (uint_to_nat n)
let uint_to_bytes_be #t n = 
  admit();
  nat_to_bytes_be (nat_to_size (numbytes t)) (uint_to_nat n)
let uint_from_bytes_le #t b = 
  let n = nat_from_intseq_le #U8 #(nat_to_size (numbytes t)) b in
  admit();
  nat_to_uint #t n
  
let uint_from_bytes_be #t b = 
  let n = nat_from_intseq_be #U8 #(nat_to_size (numbytes t)) b in
  admit();
  nat_to_uint #t n

