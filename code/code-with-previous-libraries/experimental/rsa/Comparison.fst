module Comparison

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open Lib

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I32 = FStar.Int32

val isMore_loop:
    aLen:bnlen ->
    bLen:bnlen{U32.v aLen = U32.v bLen} ->
    a:lbignum aLen ->
    b:lbignum bLen{disjoint a b} ->
    count:U32.t{U32.v count <= length a} -> Stack bool
    (requires (fun h -> live h a /\ live h b))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 b
         /\ live h1 a /\ live h1 b /\ h0 == h1))

let rec isMore_loop aLen bLen a b count =
    if U32.(count >^ 0ul) then
        let count = U32.(count -^ 1ul) in
        let t1 = a.(count) in
        let t2 = b.(count) in
        (if not (U64.(t1 =^ t2)) then
            if U64.(t1 >^ t2) then true else false
        else isMore_loop aLen bLen a b count)
    else false

(* if a > b then true else false *)
val isMore:
    aLen:bnlen ->
    bLen:bnlen ->
    a:lbignum aLen ->
    b:lbignum bLen{disjoint a b} -> Stack bool
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b
        /\ live h1 a /\ live h1 b /\ h0 == h1))

let isMore aLen bLen a b =
    if U32.(aLen >^ bLen) then true
    else if U32.(aLen <^ bLen) then false
         else isMore_loop aLen bLen a b aLen