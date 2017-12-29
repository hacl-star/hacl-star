module Shift

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast

open Lib
open Addition

module U32 = FStar.UInt32
module U64 = FStar.UInt64
open U32

let bn_tbit = 0x8000000000000000uL

val bn_lshift_:
    aLen:U32.t -> a:lbignum aLen ->
    count:U32.t -> nw:U32.t ->
    lb:U32.t{0 < v lb /\ v lb < 64} ->
    res:lbignum aLen{v count + v nw < v aLen} -> Stack unit
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))
let rec bn_lshift_ aLen a count nw lb res =
    if count >^ 0ul then begin
        let i = nw +^ count in
        let tmp = res.(i) in
        let count = count -^ 1ul in
        let t1 = a.(count) in
        let rb = 64ul -^ lb in
        assert(0 < v rb /\ v rb < 64);
        res.(i) <- U64.(tmp |^ U64.(t1 >>^ rb));
        res.(i -^ 1ul) <- U64.(t1 <<^ lb);
        bn_lshift_ aLen a count nw lb res end

(* res = a << n *)
val bn_lshift:
    aLen:U32.t -> a:lbignum aLen ->
    nCount:U32.t{v nCount > 0 /\ v aLen - (v nCount) / 64 - 1 > 0} ->
    res:lbignum aLen -> Stack unit
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))
let bn_lshift aLen a nCount res =
    let nw = nCount /^ 64ul in
    let lb = nCount %^ 64ul in
    (if lb =^ 0ul then
        blit a 0ul res nw (aLen -^ nw)
    else bn_lshift_ aLen a (aLen -^ nw -^ 1ul) nw lb res)


val bn_lshift1_:
    aLen:U32.t -> a:lbignum aLen ->
    carry:U64.t -> i:U32.t{v i < v aLen} ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))
let rec bn_lshift1_ aLen a carry i res =
    if i <^ aLen then begin
        let tmp = a.(i) in
        res.(i) <- U64.((tmp <<^ 1ul) |^ carry);
        let carry = if U64.((tmp &^ bn_tbit) =^ bn_tbit) then 1uL else 0uL in
        bn_lshift1_ aLen a carry (i +^ 1ul) res end

(* res = a << 1 *)
val bn_lshift1:
    aLen:U32.t -> a:lbignum aLen ->
    res:lbignum aLen -> Stack unit
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))

let bn_lshift1 aLen a res = bn_lshift1_ aLen a 0uL 0ul res


val bn_rshift_:
    aLen:U32.t -> a:lbignum aLen ->
    i:U32.t{v i > 0} -> nw:U32.t ->
    rb:U32.t{0 < v rb /\ v rb < 64} -> l:U64.t ->
    res:lbignum aLen{v i + v nw < v aLen} -> Stack unit
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))
let rec bn_rshift_ aLen a i nw rb l res =
    if (i <^ aLen -^ nw) then begin
        let tmp = U64.(l >>^ rb) in
        let l = a.(nw +^ i) in
        let lb = 64ul -^ rb in
        assert(0 < v lb /\ v lb < 64);
        res.(i -^ 1ul) <- U64.(tmp |^ U64.(l <<^ lb));
        bn_rshift_ aLen a (i +^ 1ul) nw rb l res end
    else res.(i -^ 1ul) <- U64.(l >>^ rb)

(* res = a >> n *)
val bn_rshift:
    aLen:U32.t -> a:lbignum aLen ->
    nCount:U32.t{v nCount > 0 /\ v aLen - (v nCount) / 64 - 1 > 0} ->
    res:lbignum aLen -> Stack unit
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))
let bn_rshift aLen a nCount res =
    let nw = nCount /^ 64ul in
    let rb = nCount %^ 64ul in
    (if rb =^ 0ul then
        blit a nw res 0ul (aLen -^ nw)
    else
        let l = a.(nw) in
        bn_rshift_ aLen a 1ul nw rb l res)


val bn_rshift1_:
    aLen:U32.t -> a:lbignum aLen ->
    carry:U64.t -> i:U32.t{v i < v aLen} ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))
let rec bn_rshift1_ aLen a carry i res =
    if i >^ 0ul then begin
        let i = i -^ 1ul in
        let tmp = a.(i) in
        res.(i) <- U64.((tmp >>^ 1ul) |^ carry);
        let carry = if U64.((tmp &^ 1uL) =^ 1uL) then bn_tbit else 0uL in
        bn_rshift1_ aLen a carry i res end

(* res = a >> 1 *)
val bn_rshift1:
    aLen:U32.t -> a:lbignum aLen ->
    res:lbignum aLen -> Stack unit
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))
let bn_rshift1 aLen a res =
    //if a is 0 then return 0
    let i = aLen -^ 1ul in
    let tmp = a.(i) in
    let carry = if U64.((tmp &^ 1uL) =^ 1uL) then bn_tbit else 0uL in
    let tmp = U64.(tmp >>^ 1ul) in
    //(if U64.(tmp >^ 0uL) then res.(i) <- tmp);
    res.(i) <- tmp;
    bn_rshift1_ aLen a carry i res

// res = a % (pow2 nCount)
val bn_mod_pow2_n:
    aLen:U32.t -> a:lbignum aLen ->
    nCount:U32.t ->
    resLen:U32.t -> res:lbignum resLen -> Stack unit
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))

let bn_mod_pow2_n aLen a nCount resLen res =
    let nw = nCount /^ 64ul in
    let nb = nCount %^ 64ul in
    blit a 0ul res 0ul resLen;

    let start_i =
        if (nb >^ 0ul) then begin
            res.(nw) <- U64.(res.(nw) &^ (0xffffffffffffffffuL >>^ U32.(64ul -^ nb)));
            nw +^ 1ul end
        else nw in

    let res' = Buffer.sub res start_i (resLen -^ start_i) in
    fill res' 0uL (resLen -^ start_i)