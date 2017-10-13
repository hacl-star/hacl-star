module Spec.Bignum.Lib

open FStar.Seq
open FStar.Mul
open FStar.UInt
open Spec.Seq.Lib
open Spec.Bignum

module U8 = FStar.UInt8
module U32 = FStar.UInt32
open U32

val for_loop: min:U32.t -> max:U32.t{U32.v min <= U32.v max} -> f:('a -> i:U32.t{U32.v i < U32.v max} -> Tot 'a) -> x:'a -> Tot 'a
let for_loop min max f a = 
    Spec.Loops.repeat_range_spec (U32.v min) (U32.v max) (fun x i -> f x (U32.uint_to_t i)) a

val xor_bytes: b1:bytes -> b2:bytes{length b2 = length b1} -> Tot (res:bytes{length res = length b1})
let xor_bytes b1 b2 = Spec.Lib.map2 (fun x y -> U8.(x ^^ y)) b1 b2

(* NEED TO PROVE: x <= m * r *)
val blocks: x:U32.t{U32.v x > 0} -> m:U32.t{U32.v m > 0} -> r:U32.t{U32.v r > 0}
let blocks (x:U32.t{U32.v x > 0}) (m:U32.t{U32.v m > 0}) = (x -^ 1ul) /^ m +^ 1ul

val store32_be: U32.t -> lbytes 4ul -> lbytes 4ul
let store32_be (i:U32.t) (b:lbytes 4ul) : lbytes 4ul = FStar.Endianness.uint32_be 4ul i

#reset-options "--z3rlimit 30"

val os2ip: b:bytes -> Tot bignum 
let os2ip b =
  let bLen = seq_length b in
  if (bLen = 0ul) 
  then 0 
  else
    let next (a:bignum) (i:U32.t{U32.v i < U32.v bLen - 1}): bignum = 
	       bignum_mul (bignum_add a (uint8_to_bignum b.[i])) 256 in
    let acc = for_loop 0ul (bLen -^ 1ul) next 0 in
    acc + U8.v (b.[bLen -^ 1ul])
    
val i2osp:
	n:bignum -> b:bytes{n < pow2 (8 * length b)} ->
	Tot (b':bytes{length b' = length b})
let i2osp n b =
	let bLen = seq_length b in
	if (bLen = 0ul)
	then b
	else
	let next (c:tuple2 bignum (lbytes bLen)) (i:U32.t{U32.v i < U32.v bLen}) : tuple2 bignum (lbytes bLen) =
	    let (n,b) = c in
	    let b' = b.[bLen -^ i -^ 1ul] <- bignum_to_uint8 (bignum_mod n 256) in
	    let n' = bignum_div n 256 in
	    (n',b') in
  
        let (n',b') = for_loop 0ul bLen next (n,b) in
	b'