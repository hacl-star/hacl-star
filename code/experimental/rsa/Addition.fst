module Addition

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast

module U32 = FStar.UInt32
module U64 = FStar.UInt64

type bignum = buffer FStar.UInt64.t

val sub_loop_min:
    bLen:U32.t -> a:bignum -> b:bignum{length b = U32.v bLen} -> carry:bool ->
    count:U32.t{(U32.v count <= U32.v bLen) /\ (U32.v count <= length a)} ->
    res:bignum{U32.v count <= length res} -> Stack bool
    (requires (fun h -> live h a /\ live h b /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\  live h0 res /\ live h1 res /\ modifies_1 res h0 h1))
let rec sub_loop_min bLen a b carry count res =
    push_frame();
    let carry =
    if U32.(count <^ bLen) then
    let t1 = a.(count) in
    let t2 = b.(count) in
    let carry =
        if (carry) then
        (res.(count) <- U64.(t1 -^ t2 -^ 1uL); U64.(t1 <=^ t2))
        else (res.(count) <- U64.(t1 -^ t2); U64.(t1 <^ t2)) in
    sub_loop_min bLen a b carry U32.(count +^ 1ul) res
    else carry in
    pop_frame();
    carry

val sub_loop_dif:
    aLen:U32.t -> a:bignum{length a = U32.v aLen} ->
    ind:U32.t -> dif:U32.t{U32.(v (ind +^ dif)) <= length a} ->
    res:bignum{length res = length a} -> Stack U32.t
    (requires (fun h -> live h a /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\  live h0 res /\ live h1 res /\ modifies_1 res h0 h1))
let rec sub_loop_dif aLen a ind dif res =
    push_frame();
    let dif =
    if U32.(dif >^ 0ul) then
    let dif = U32.(dif -^ 1ul) in
    res.(ind) <- U64.(a.(ind) -^ 1uL);
    let ind = U32.(ind +^ 1ul) in
    (if U64.(a.(ind) =^ 1uL) then dif
    else sub_loop_dif aLen a ind dif res)
    else dif in
    pop_frame();
    dif

(* a must be more than b *)
(* the length of the result should be fixed, if res[resLen - 1] == 0uL *)
(* res = a - b *)
val sub:
    aLen:U32.t -> bLen:U32.t{U32.(bLen <=^ aLen)} ->
    a:bignum{length a = U32.v aLen} -> b:bignum{length b = U32.v bLen} ->
    res:bignum{length res = U32.v aLen} -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\  live h0 res /\ live h1 res /\ modifies_1 res h0 h1))
let sub aLen bLen a b res =
    push_frame();
    let dif = U32.(aLen -^ bLen) in
    let carry = sub_loop_min bLen a b false 0ul res in
    let dif = if (carry) then sub_loop_dif aLen a bLen dif res else dif in
    (if U32.(dif >^ 0ul) then
    let ind = U32.(aLen -^ dif) in
    blit a ind res ind dif);
    pop_frame()
