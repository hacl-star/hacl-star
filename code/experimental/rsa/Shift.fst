module Shift

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open Lib

module U32 = FStar.UInt32
module U64 = FStar.UInt64
open U32

let bn_tbit = 0x8000000000000000uL

val lshift_loop:
    aLen:bnlen ->
    a:lbignum aLen ->
    count:U32.t ->
    nw:U32.t ->
    lb:U32.t{0 < v lb /\ v lb < 64} ->
    res:lbignum aLen{v count + v nw < v aLen /\ disjoint a res} -> Stack unit
	(requires (fun h -> live h a /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 res /\
        live h1 a /\ live h1 res /\ modifies_1 res h0 h1))

let rec lshift_loop aLen a count nw lb res =
    if count >^ 0ul then begin
        let ind = nw +^ count in
        let tmp = res.(ind) in
        let count = count -^ 1ul in
        let t1 = a.(count) in
        let rb = 64ul -^ lb in
        assert(0 < v rb /\ v rb < 64);
        res.(ind) <- U64.(tmp |^ U64.(t1 >>^ rb));
        res.(ind -^ 1ul) <- U64.(t1 <<^ lb);
        lshift_loop aLen a count nw lb res end

(* res = a << n *)
val lshift:
    aLen:bnlen ->
    a:lbignum aLen ->
    nCount:U32.t{v nCount > 0 /\ v aLen - (v nCount) / 64 - 1 > 0} ->
    res:lbignum aLen{disjoint a res} ->
    Stack unit
	(requires (fun h -> live h a /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 res /\
        live h1 a /\ live h1 res /\ modifies_1 res h0 h1))

let lshift aLen a nCount res =
    let nw = nCount /^ 64ul in
    let lb = nCount %^ 64ul in
    (if lb =^ 0ul then
        blit a 0ul res nw (aLen -^ nw)
    else lshift_loop aLen a (aLen -^ nw -^ 1ul) nw lb res)

val rshift1_loop:
    aLen:bnlen ->
    a:lbignum aLen ->
    carry:U64.t ->
    ind:U32.t{v ind < length a} ->
    res:lbignum aLen{disjoint a res} -> Stack unit
    (requires (fun h -> live h a /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 res /\ 
        live h1 a /\ live h1 res /\ modifies_1 res h0 h1))

let rec rshift1_loop aLen a carry ind res =
    if ind >^ 0ul then begin
        let ind = ind -^ 1ul in
        let tmp = a.(ind) in
        res.(ind) <- U64.((tmp >>^ 1ul) |^ carry);
        let carry = if U64.((tmp &^ 1uL) =^ 1uL) then bn_tbit else 0uL in
        rshift1_loop aLen a carry ind res end

(* res = a >> 1 *)
val rshift1:
    aLen:bnlen ->
    a:lbignum aLen ->
    res:lbignum aLen{disjoint a res} -> Stack unit
	(requires (fun h -> live h a /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 res /\
        live h1 a /\ live h1 res /\ modifies_1 res h0 h1))

#set-options "--z3rlimit 50"

let rshift1 aLen a res =
    let i = aLen -^ 1ul in
    let tmp = a.(i) in
    let carry = if U64.((tmp &^ 1uL) =^ 1uL) then bn_tbit else 0uL in
    let tmp = U64.(tmp >>^ 1ul) in
    (if U64.(tmp >^ 0uL) then res.(i) <- tmp);
    rshift1_loop aLen a carry i res