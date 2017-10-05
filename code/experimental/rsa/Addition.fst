module Addition

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open Lib

module U32 = FStar.UInt32
module U64 = FStar.UInt64

val sub_loop:
    aLen:bnlen -> bLen:bnlen ->
    a:lbignum aLen -> b:lbignum bLen{disjoint a b} ->
    ind:U32.t{U32.v ind <= length a} -> carry:U64.t ->
    res:lbignum aLen{disjoint res a /\ disjoint res b} -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h0 res /\ 
        live h1 a /\ live h1 b /\ live h1 res /\ modifies_1 res h0 h1))

#set-options "--z3rlimit 150"

let rec sub_loop aLen bLen a b ind carry res =
    if U32.(ind <^ aLen) then
        begin
        let t1 = a.(ind) in
        let t2 = if U32.(ind <^ bLen) then b.(ind) else 0uL in
        res.(ind) <- U64.(t1 -%^ t2 -%^ carry);
        let carry = 
            (if U64.(carry =^ 1uL) then
                (if U64.(t1 <=^ t2) then 1uL else 0uL)
            else
                (if U64.(t1 <^ t2) then 1uL else 0uL)) in
        let ind = U32.(ind +^ 1ul) in
        sub_loop aLen bLen a b ind carry res
        end

(* a must be greater than b *)
(* ADD: isMore aLen bLen a b *)
(* res = a - b *)
val sub:
    aLen:bnlen -> bLen:bnlen ->
    a:lbignum aLen -> b:lbignum bLen{disjoint a b} ->
    res:lbignum aLen{disjoint res a /\ disjoint res b} -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\  live h0 res /\
        live h1 a /\ live h1 b /\ live h1 res /\ modifies_1 res h0 h1))

let sub aLen bLen a b res =
    sub_loop aLen bLen a b 0ul 0uL res