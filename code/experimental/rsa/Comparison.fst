module Comparison

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I32 = FStar.Int32

type bignum = buffer FStar.UInt64.t

val isMore_loop:
    a:bignum -> b:bignum{length b = length a} -> 
    count:U32.t{U32.v count <= length a} -> Stack bool
    (requires (fun h -> live h a /\ live h b))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 b
         /\ live h1 a /\ live h1 b))
let rec isMore_loop a b count =
    if U32.(count >^ 0ul) then
        let count = U32.(count -^ 1ul) in
        let t1 = a.(count) in
        let t2 = b.(count) in
        (if not (U64.(t1 =^ t2)) then
            if U64.(t1 >^ t2) then true else false
        else isMore_loop a b count)
    else false

(* if a > b then true else false *)
val isMore:
    aLen:U32.t -> bLen:U32.t ->
    a:bignum{length a = U32.v aLen} -> 
    b:bignum{length b = U32.v bLen} -> Stack bool
    (requires (fun h -> live h a /\ live h b))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 b 
        /\ live h1 a /\ live h1 b))
let isMore aLen bLen a b =
    if U32.(aLen >^ bLen) then true
    else if U32.(aLen <^ bLen) then false
         else isMore_loop a b aLen