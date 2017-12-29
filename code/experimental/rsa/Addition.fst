module Addition

open FStar.HyperStack.All
open FStar.Buffer
open Lib

module U32 = FStar.UInt32
module U64 = FStar.UInt64
open U32

val bn_sub_:
    aLen:U32.t -> a:lbignum aLen ->
    bLen:U32.t -> b:lbignum bLen ->
    i:U32.t{v i <= v aLen} ->
    res:lbignum aLen -> Stack U64.t
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let rec bn_sub_ aLen a bLen b i res =
    if (i =^ 0ul) then 0uL
    else begin
        let i1 = i -^ 1ul in
        let carry' = bn_sub_ aLen a bLen b i1 res in
        let t1 = a.(i1) in 
        let t2 = if (i1 <^ bLen) then b.(i1) else 0uL in
        let res_i = U64.(t1 -%^ t2 -%^ carry') in
        res.(i1) <- res_i;
        (if U64.(carry' =^ 1uL) then
            (if U64.(t1 <=^ t2) then 1uL else 0uL)
        else
            (if U64.(t1 <^ t2) then 1uL else 0uL))
    end

(* a must be greater than b *)
(* ADD: isMore aLen bLen a b *)
(* res = a - b *)
val bn_sub:
    aLen:U32.t -> a:lbignum aLen ->
    bLen:U32.t{v bLen <= v aLen} -> b:lbignum bLen ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let bn_sub aLen a bLen b res =
    let _ = bn_sub_ aLen a bLen b aLen res in ()

val bn_add_:
    aLen:U32.t -> a:lbignum aLen ->
    bLen:U32.t -> b:lbignum bLen ->
    i:U32.t{v i <= v aLen} ->
    res:lbignum aLen -> Stack U64.t
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let rec bn_add_ aLen a bLen b i res =
    if (i =^ 0ul) then 0uL
    else begin
        let i1 = i -^ 1ul in
        let carry' = bn_add_ aLen a bLen b i1 res in
        let t1 = a.(i1) in 
        let t2 = if i1 <^ bLen then b.(i1) else 0uL in
        let res_i = U64.(t1 +%^ t2 +%^ carry') in
        res.(i1) <- res_i;
        (if U64.(res_i <^ t1) then 1uL else 0uL) 
    end

val bn_add:
    aLen:U32.t -> a:lbignum aLen ->
    bLen:U32.t{v bLen <= v aLen} -> b:lbignum bLen ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let bn_add aLen a bLen b res =
    let _ = bn_add_ aLen a bLen b aLen res in ()