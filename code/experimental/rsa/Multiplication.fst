module Multiplication

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open Lib

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
open U32

val mult_by_limb_addj:
    aLen:bnlen -> a:lbignum aLen ->
    l:U64.t -> i:U32.t{v i <= v aLen} -> j:U32.t ->
    resLen:U32.t{v aLen + v j < v resLen} ->
    carry:U64.t -> res:lbignum resLen -> Stack unit
    (requires (fun h -> live h a /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 a /\ live h0 res /\
        live h1 a /\ live h1 res /\ modifies_1 res h0 h1))

let rec mult_by_limb_addj aLen a l i j resLen carry res =
    if U32.(i <^ aLen) then begin
        let res_ij = res.(i +^ j) in
        let carry = U128.uint64_to_uint128 carry in
        let res_ij = U128.uint64_to_uint128 res_ij in

        let ai_l = U128.mul_wide a.(i) l in
        let tmp = U128.add_mod ai_l carry in
        let res_ij = U128.add_mod res_ij tmp in

        let carry' = U128.shift_right res_ij 64ul in
        let res_ij = U128.uint128_to_uint64 res_ij in
        let carry' = U128.uint128_to_uint64 carry' in
        res.(i +^ j) <- res_ij;
        mult_by_limb_addj aLen a l (i +^ 1ul) j resLen carry' res end
    else
        res.(i +^ j) <- carry

val mult_loop:
    aLen:bnlen -> a:lbignum aLen ->
    bLen:bnlen -> b:lbignum bLen ->
    j:U32.t{U32.v j <= U32.v bLen} ->
    resLen:U32.t{v resLen = v aLen + v bLen} -> res:lbignum resLen -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h0 res /\
        live h1 a /\ live h1 b /\ live h1 res /\ modifies_1 res h0 h1))

let rec mult_loop aLen a bLen b j resLen res =
    if U32.(j <^ bLen) then begin
        mult_by_limb_addj aLen a b.(j) 0ul j resLen 0uL res;
        mult_loop aLen a bLen b (j +^ 1ul) resLen res
        end

(* res = a * b *)
val mult:
    aLen:bnlen -> a:lbignum aLen ->
    bLen:bnlen -> b:lbignum bLen ->
    res:lbignum U32.(aLen +^ bLen) -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h0 res /\
        live h1 a /\ live h1 b /\ live h1 res /\ modifies_1 res h0 h1))
        
let mult aLen a bLen b res =
    mult_loop aLen a bLen b 0ul (aLen +^ bLen) res

(* TODO: res = a * a *)
val sqr:
    aLen:bnlen -> a:lbignum aLen ->
    res:lbignum U32.(aLen +^ aLen) -> Stack unit
    (requires (fun h -> live h a /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 a /\ live h0 res /\ 
        live h1 a /\ live h1 res /\ modifies_1 res h0 h1))
        
let sqr aLen a res =
    mult aLen a aLen a res