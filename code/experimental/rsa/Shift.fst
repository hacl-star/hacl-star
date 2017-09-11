module Shift

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast

module U32 = FStar.UInt32
module U64 = FStar.UInt64

type bignum = buffer FStar.UInt64.t

let bn_bits2 = 64ul
let bn_tbit = 0x8000000000000000uL
let bn_mask2 = 0xffffffffffffffffuL

val lshift_loop:
    a:bignum -> count:U32.t{U32.v count <= length a} -> nw:U32.t ->
    lb:U32.t -> res:bignum{U32.(v (count +^ nw)) < length res} -> Stack unit
	(requires (fun h -> live h a /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 res /\ live h1 res /\ modifies_1 res h0 h1))
let rec lshift_loop a count nw lb res =
    push_frame();
    (if U32.(count >^ 0ul) then
    let count = U32.(count -^ 1ul) in
    let l = a.(count) in
    let ind = U32.(nw +^ count +^ 1ul) in
    let rb = U32.(bn_bits2 -^ lb) in
    let tmp = res.(ind) in
    res.(ind) <- U64.(tmp |^ ((l >>^ rb) &^ bn_mask2));
    res.(U32.(ind -^ 1ul)) <- U64.((l <<^ lb) &^ bn_mask2);
    lshift_loop a count nw lb res);
    pop_frame()

(* res = a << n *)
val lshift:
    aLen:U32.t -> a:bignum{length a = U32.v aLen} -> nCount:U32.t ->
    res:bignum{length res = U32.(v (aLen +^ (nCount /^ bn_bits2) +^ 1ul))} -> Stack unit
	(requires (fun h -> live h a /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 res /\ live h1 res /\ modifies_1 res h0 h1))
let lshift aLen a nCount res =
    push_frame();
    let nw = U32.(nCount/^ bn_bits2) in
    let resLen = U32.(aLen +^ nw) in
    let lb = U32.(nCount %^ bn_bits2) in
    (if U32.(lb =^ 0ul)
    then blit a 0ul res nw aLen
    else lshift_loop a aLen nw lb res);
    pop_frame()

val rshift1_loop:
    a:bignum -> carry:U64.t -> ind:U32.t{U32.v ind <= length a} ->
    res:bignum{U32.v ind <= length res} -> Stack unit
    (requires (fun h -> live h a /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 res /\ live h1 res /\ modifies_1 res h0 h1))
let rec rshift1_loop a carry ind res =
    push_frame();
    (if U32.(ind >^ 0ul) then
    let ind = U32.(ind -^ 1ul) in
    let tmp = a.(ind) in
    res.(ind) <- U64.(((tmp >>^ 1ul) &^ bn_mask2) |^ carry);
    let carry = if U64.((tmp &^ 1uL) =^ 1uL) then bn_tbit else 0uL in
    rshift1_loop a carry ind res);
    pop_frame()

(* res = a >> 1 *)
val rshift1:
    aLen:U32.t -> a:bignum{length a = U32.v aLen} ->
    res:bignum{length res = U32.v aLen /\ length res = U32.(v (aLen -^ 1ul))} -> Stack unit
	(requires (fun h -> live h a /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 res /\ live h1 res /\ modifies_1 res h0 h1))
let rshift1 aLen a res =
    (* if a = 0 then res = 0 *)
    push_frame();
    let i = U32.(aLen -^ 1ul) in
    let tmp = a.(i) in
    let carry = if U64.((tmp &^ 1uL) =^ 1uL) then bn_tbit else 0uL in
    let tmp = U64.(tmp >>^ 1ul) in
    (if U64.(tmp >^ 0uL) then res.(i) <- tmp);
    rshift1_loop a carry i res;
    pop_frame()
