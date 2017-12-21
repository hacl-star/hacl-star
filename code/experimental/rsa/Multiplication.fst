module Multiplication

open FStar.HyperStack.All
open FStar.Buffer
open Lib

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
open U32

val bn_mul_by_limb_addj_f:
    a_i:U64.t -> l:U64.t -> c:U64.t -> r_ij:U64.t -> Tot (tuple2 U64.t U64.t)
let bn_mul_by_limb_addj_f a_i l c r_ij =
    let res = U128.(mul_wide a_i l +^ uint64_to_uint128 c +^ uint64_to_uint128 r_ij) in
    let r = U128.uint128_to_uint64 res in
    let c' = U128.shift_right res 64ul in
    let c' = U128.uint128_to_uint64 c' in
    (c', r)

val bn_mul_by_limb_addj_:
    aLen:bnlen -> a:lbignum aLen ->
    l:U64.t -> i:U32.t{v i <= v aLen} -> j:U32.t ->
    resLen:U32.t{v aLen + v j < v resLen} ->
    res:lbignum resLen -> Stack U64.t
    (requires (fun h -> live h a /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 a /\ live h0 res /\
     			      live h1 a /\ live h1 res /\
			      modifies_1 res h0 h1))

let rec bn_mul_by_limb_addj_ aLen a l i j resLen res =
    if i =^ 0ul then 0uL
    else begin
        let i1 = i -^ 1ul in
        let c1 = bn_mul_by_limb_addj_ aLen a l i1 j resLen res in
        let (carry', res_ij) = bn_mul_by_limb_addj_f a.(i1) l c1 res.(i1 +^ j) in
        res.(i1 +^ j) <- res_ij;
        carry'
    end

val bn_mul_by_limb_addj:
    aLen:bnlen -> a:lbignum aLen -> l:U64.t -> j:U32.t ->
    resLen:U32.t{v aLen + v j < v resLen} ->
    res:lbignum resLen -> Stack U64.t
    (requires (fun h -> live h a /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 a /\ live h0 res /\
        		      live h1 a /\ live h1 res /\ 
			      modifies_1 res h0 h1))

let bn_mul_by_limb_addj aLen a l j resLen res =
    bn_mul_by_limb_addj_ aLen a l aLen j resLen res

val bn_mul_:
    aLen:bnlen -> a:lbignum aLen ->
    bLen:bnlen -> b:lbignum bLen ->
    j:U32.t{U32.v j <= U32.v bLen} ->
    resLen:U32.t{v resLen = v aLen + v bLen} -> 
    res:lbignum resLen -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h0 res /\
        		      live h1 a /\ live h1 b /\ live h1 res /\ 
			      modifies_1 res h0 h1))

let rec bn_mul_ aLen a bLen b j resLen res =
    if j =^ 0ul then ()
    else begin
        let j1 = j -^ 1ul in
        bn_mul_ aLen a bLen b j1 resLen res;
        let c' = bn_mul_by_limb_addj aLen a b.(j1) j1 resLen res in
        res.(aLen +^ j1) <- c'
    end

// res = a * b
val bn_mul:
    aLen:bnlen -> a:lbignum aLen ->
    bLen:bnlen -> b:lbignum bLen ->
    res:lbignum U32.(aLen +^ bLen) -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h0 res /\
        		      live h1 a /\ live h1 b /\ live h1 res /\ 
			      modifies_1 res h0 h1))
        
let bn_mul aLen a bLen b res = 
    bn_mul_ aLen a bLen b bLen (aLen +^ bLen) res