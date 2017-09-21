module Shift

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast

module U32 = FStar.UInt32
module U64 = FStar.UInt64

type bignum = buffer FStar.UInt64.t

let bn_tbit = 0x8000000000000000uL

val lshift_loop:
    a:bignum{length a > 0} ->
    count:U32.t{U32.v count <= length a} ->
    nw:U32.t -> lb:U32.t{0 < U32.v lb /\ U32.v lb < 64} ->
    res:bignum{length res = length a + U32.v nw + 1 /\ U32.v count + U32.v nw < length res /\ disjoint a res} -> 
    Stack unit
	(requires (fun h -> live h a /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 res /\ 
        live h1 a /\ live h1 res /\ modifies_1 res h0 h1))

let rec lshift_loop a count nw lb res =
    if U32.(count >^ 0ul) then
        let ind = U32.(nw +^ count) in
        let tmp = res.(ind) in
        let count = U32.(count -^ 1ul) in
        let t1 = a.(count) in
        let rb = U32.(64ul -^ lb) in
        assert(0 < U32.v rb /\ U32.v rb < 64);
        res.(ind) <- U64.(tmp |^ U64.(t1 >>^ rb));
        res.(U32.(ind -^ 1ul)) <- U64.(t1 <<^ lb);
        lshift_loop a count nw lb res
    else ()

(* res = a << n *)
val lshift:
    aLen:U32.t{U32.v aLen > 0} ->
    a:bignum{length a = U32.v aLen} -> 
    nCount:U32.t ->
    res:bignum{length res = U32.v aLen + U32.v nCount / 64 + 1 /\ disjoint a res} -> 
    Stack unit
	(requires (fun h -> live h a /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 res /\ 
        live h1 a /\ live h1 res /\ modifies_1 res h0 h1))

let lshift aLen a nCount res =
    let nw = U32.(nCount/^ 64ul) in
    let resLen = U32.(aLen +^ nw +^ 1ul) in
    let lb = U32.(nCount %^ 64ul) in
    (if U32.(lb =^ 0ul) then
        blit a 0ul res nw aLen
    else lshift_loop a aLen nw lb res)


val rshift1_loop:
    a:bignum -> 
    carry:U64.t -> 
    ind:U32.t{U32.v ind < length a} ->
    res:bignum{U32.v ind < length res /\ length res = length a} -> 
    Stack unit
    (requires (fun h -> live h a /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 res /\ 
        live h1 a /\ live h1 res /\ modifies_1 res h0 h1))

let rec rshift1_loop a carry ind res =
    if U32.(ind >^ 0ul) then
        let ind = U32.(ind -^ 1ul) in
        let tmp = a.(ind) in
        res.(ind) <- U64.((tmp >>^ 1ul) |^ carry);
        let carry = if U64.((tmp &^ 1uL) =^ 1uL) then bn_tbit else 0uL in
        rshift1_loop a carry ind res
    else ()

(* res = a >> 1 *)
val rshift1:
    aLen:U32.t{U32.v aLen > 0} ->
    a:bignum{length a = U32.v aLen} ->
    res:bignum{length res = U32.v aLen} -> Stack unit
	(requires (fun h -> live h a /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 res /\ 
        live h1 a /\ live h1 res /\ modifies_1 res h0 h1))

#set-options "--z3rlimit 50"

let rshift1 aLen a res =
    let i = U32.(aLen -^ 1ul) in
    let tmp = a.(i) in
    let carry = if U64.((tmp &^ 1uL) =^ 1uL) then bn_tbit else 0uL in
    let tmp = U64.(tmp >>^ 1ul) in
    (if U64.(tmp >^ 0uL) then res.(i) <- tmp);
    rshift1_loop a carry i res