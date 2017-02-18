module Spec.Lib

open FStar.Seq

let lbytes (l:nat) = b:seq UInt8.t {length b = l}
let op_At f g = fun x -> g (f x) 
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
val xor: #len:nat -> x:lbytes len -> y:lbytes len -> Tot (lbytes len)
let rec xor #len x y = map2 (fun x y -> FStar.UInt8.(x ^^ y)) x y





