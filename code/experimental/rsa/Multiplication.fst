module Multiplication

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open FStar.Mul

open Lib

module Buffer = Spec.Lib.IntBuf

val bn_mul_by_limb_addj_f:
    a_i:uint64 -> l:uint64 -> c:uint64 -> r_ij:uint64 -> Tot (tuple2 uint64 uint64)
[@ "substitute"]    
let bn_mul_by_limb_addj_f a_i l c r_ij =
    assume (uint_v #U64 a_i * uint_v #U64 l + uint_v #U64 c + uint_v #U64 r_ij < pow2 128);
    let res = add #U128 (add #U128 (mul_wide a_i l) (to_u128 #U64 c)) (to_u128 #U64 r_ij) in
    let r = to_u64 res in
    let c' = to_u64 (res >>. u32 64) in
    (c', r)

val bn_mul_by_limb_addj_:
    #aLen:size_nat -> #resLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    l:uint64 -> i:size_t{v i <= aLen} -> j:size_t ->
    cresLen:size_t{aLen + v j < resLen} ->
    res:lbignum resLen -> Stack uint64
    (requires (fun h -> live h a /\ live h res /\ disjoint res a))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    
let rec bn_mul_by_limb_addj_ #aLen #resLen caLen a l i j cresLen res =
    if i =. size 0 then u64 0
    else begin
        let i1 = size_decr i in
        let c1 = bn_mul_by_limb_addj_ #aLen #resLen caLen a l i1 j cresLen res in
        let (carry', res_ij) = bn_mul_by_limb_addj_f a.(i1) l c1 res.(add #SIZE i1 j) in
        res.(add #SIZE i1 j) <- res_ij;
        carry'
    end

val bn_mul_by_limb_addj:
    #aLen:size_nat -> #resLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen -> l:uint64 -> j:size_t ->
    cresLen:size_t{aLen + v j < resLen} ->
    res:lbignum resLen -> Stack uint64
    (requires (fun h -> live h a /\ live h res /\ disjoint res a))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

[@ "substitute"]
let bn_mul_by_limb_addj #aLen #resLen caLen a l j cresLen res =
    bn_mul_by_limb_addj_ #aLen #resLen caLen a l caLen j cresLen res

val bn_mul_:
    #aLen:size_nat -> #bLen:size_nat -> #resLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    cbLen:size_t{v cbLen == bLen} -> b:lbignum bLen ->
    j:size_t{v j <= bLen} ->
    cresLen:size_t{v cresLen == resLen /\  resLen = aLen + bLen} ->
    res:lbignum resLen -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res /\ disjoint res a /\ disjoint res b))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

let rec bn_mul_ #aLen #bLen #resLen caLen a cbLen b j cresLen res =
    if j =. size 0 then ()
    else begin
        let j1 = size_decr j in
        bn_mul_ #aLen #bLen #resLen caLen a cbLen b j1 cresLen res;
        let c' = bn_mul_by_limb_addj #aLen #resLen caLen a b.(j1) j1 cresLen res in
        res.(add #SIZE caLen j1) <- c'
    end

// res = a * b
val bn_mul:
    #aLen:size_nat -> #bLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    cbLen:size_t{v cbLen == bLen /\ aLen + bLen < max_size_t} -> b:lbignum bLen ->
    res:lbignum (aLen + bLen) -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res /\ disjoint res a /\ disjoint res b))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
        
let bn_mul #aLen #bLen caLen a cbLen b res = 
    bn_mul_ #aLen #bLen #(aLen + bLen) caLen a cbLen b cbLen (add #SIZE caLen cbLen) res
