module Spec.Lib

open FStar.Mul
open FStar.Seq
open FStar.UInt32
open FStar.Endianness



let rotate_left (a:UInt32.t) (s:UInt32.t {v s<32}) : Tot UInt32.t =
  ((a <<^ s) |^ (a >>^ (32ul -^ s)))

let rotate_right (a:UInt32.t) (s:UInt32.t {v s<32}) : Tot UInt32.t =
  ((a >>^ s) |^ (a <<^ (32ul -^ s)))

let op_Less_Less_Less (a:UInt32.t) (s:UInt32.t {v s<32}) = rotate_left a s
let op_Greater_Greater_Greater (a:UInt32.t) (s:UInt32.t {v s<32}) = rotate_right a s


let lbytes (l:nat) = b:seq UInt8.t {length b = l}
let op_At f g = fun x -> g (f x)
let set i x s = upd s i x

val iter: n:nat -> (f: 'a -> Tot 'a) -> 'a -> 'a
let rec iter n f x = if n = 0 then x else iter (n-1) f (f x)
val map2: ('a -> 'b -> Tot 'c) ->
	  a:seq 'a -> b:seq 'b{length b = length a} ->
    	  Tot (c:seq 'c{length c = length a}) (decreases (length a))
let rec map2 f s1 s2 =
  let len = length s1 in
  if len = 0 then Seq.createEmpty
  else
     let h1 = index s1 0 in
     let h2 = index s2 0 in
     let t1 = slice s1 1 len in
     let t2 = slice s2 1 len in
     let r = map2 f t1 t2 in
     cons (f h1 h2) r


let uint32_from_le (b:lbytes 4) : UInt32.t =
    let n = little_endian b  in
    UInt32.uint_to_t (UInt.to_uint_t 32 n)

let uint32_to_le (a:UInt32.t) : lbytes 4 =
    little_bytes 4ul (v a)


val uint32s_from_le: len:nat -> b:lbytes (4 * len) -> Tot (s:seq UInt32.t{length s = len}) (decreases len)
let rec uint32s_from_le len src =
  if len = 0 then Seq.createEmpty #UInt32.t
  else
    let h = slice src 0 4 in
    let t = slice src 4 (4*len) in
    Seq.cons (uint32_from_le h)
             (uint32s_from_le (len-1) t)

val uint32s_to_le: len:nat -> s:seq UInt32.t{length s = len} -> Tot (lbytes (4 * len))  (decreases len)
let rec uint32s_to_le len src =
  if len = 0 then Seq.createEmpty #UInt8.t
  else
    let h = index src 0 in
    let t = slice src 1 len in
    Seq.append (uint32_to_le h)
               (uint32s_to_le (len-1) t)
