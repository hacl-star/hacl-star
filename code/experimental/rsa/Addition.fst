module Addition

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast

module ST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module U64 = FStar.UInt64

type bignum = buffer FStar.UInt64.t

val sub_loop:
    aLen:U32.t -> bLen:U32.t{U32.(bLen <=^ aLen)} ->
    a:bignum{length a = U32.v aLen} -> b:bignum{length b = U32.v bLen} -> 
    ind:U32.t{U32.(ind <=^ aLen)} -> carry:U64.t ->
    res:bignum{length res = U32.v aLen} -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h0 res /\ 
        live h1 a /\ live h1 b /\ live h1 res /\ modifies_1 res h0 h1))
let rec sub_loop aLen bLen a b ind carry res = 
    let h0 = ST.get () in
    if U32.(ind <^ aLen) then
        begin
        let t1 = a.(ind) in
        let x =
            if U32.(ind <^ bLen) then
                (let t2 = b.(ind) in 
                U64.(t1 -%^ t2))
            else t1 in
        res.(ind) <- U64.(x -%^ carry);
        let carry = if U64.(x <^ carry) then 1uL else 0uL in
        let ind = U32.(ind +^ 1ul) in
        sub_loop aLen bLen a b ind carry res
        end
    else ();
    lemma_modifies_sub_1 h0 h0 res

(* a must be greater than b *)
(* res = a - b *)
val sub:
    aLen:U32.t -> bLen:U32.t{U32.(bLen <=^ aLen)} ->
    a:bignum{length a = U32.v aLen} -> b:bignum{length b = U32.v bLen} ->
    res:bignum{length res = U32.v aLen} -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\  live h0 res /\
        live h1 a /\ live h1 b /\ live h1 res /\ modifies_1 res h0 h1))
let sub aLen bLen a b res =
    sub_loop aLen bLen a b 0ul 0uL res