module Addition

open FStar.HyperStack.All
open FStar.Buffer
open Lib

module U32 = FStar.UInt32
module U64 = FStar.UInt64

val bn_sub_:
    aLen:bnlen -> a:lbignum aLen ->
    bLen:bnlen -> b:lbignum bLen{disjoint a b} ->
    i:U32.t{U32.v i <= U32.v aLen} ->
    res:lbignum aLen{disjoint res a /\ disjoint res b} -> Stack U64.t
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h0 res /\
                             live h1 a /\ live h1 b /\ live h1 res /\ 
                             modifies_1 res h0 h1))

let rec bn_sub_ aLen a bLen b i res =
    if U32.(i =^ 0ul) then 0uL
    else begin
        let i1 = U32.(i -^ 1ul) in
        let carry' = bn_sub_ aLen a bLen b i1 res in
        let t1 = a.(i1) in 
        let t2 = if U32.(i1 <^ bLen) then b.(i1) else 0uL in
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
    aLen:bnlen -> a:lbignum aLen ->
    bLen:bnlen{U32.v bLen <= U32.v aLen} -> b:lbignum bLen{disjoint a b} ->
    res:lbignum aLen{disjoint res a /\ disjoint res b} -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h0 res /\
                             live h1 a /\ live h1 b /\ live h1 res /\
                             modifies_1 res h0 h1))

let bn_sub aLen a bLen b res =
    let _ = bn_sub_ aLen a bLen b aLen res in ()

val bn_add_:
    aLen:bnlen -> a:lbignum aLen ->
    bLen:bnlen -> b:lbignum bLen{disjoint a b} ->
    i:U32.t{U32.v i <= U32.v aLen} ->
    res:lbignum aLen{disjoint res a /\ disjoint res b} -> Stack U64.t
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h0 res /\
                             live h1 a /\ live h1 b /\ live h1 res /\
                             modifies_1 res h0 h1))

let rec bn_add_ aLen a bLen b i res =
    if U32.(i =^ 0ul) then 0uL
    else begin
        let i1 = U32.(i -^ 1ul) in
        let carry' = bn_add_ aLen a bLen b i1 res in
        let t1 = a.(i1) in 
        let t2 = if U32.(i1 <^ bLen) then b.(i1) else 0uL in
        let res_i = U64.(t1 +%^ t2 +%^ carry') in
        res.(i1) <- res_i;
        (if U64.(res_i <^ t1) then 1uL else 0uL) 
    end

val bn_add:
    aLen:bnlen -> a:lbignum aLen ->
    bLen:bnlen{U32.v bLen <= U32.v aLen} -> b:lbignum bLen{disjoint a b} ->
    res:lbignum aLen{disjoint res a /\ disjoint res b} -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h0 res /\
                             live h1 a /\ live h1 b /\ live h1 res /\
			     modifies_1 res h0 h1))

let bn_add aLen a bLen b res = 
    let _ = bn_add_ aLen a bLen b aLen res in ()