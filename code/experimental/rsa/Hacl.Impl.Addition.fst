module Hacl.Impl.Addition

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes

open Hacl.Impl.Lib

module Buffer = Spec.Lib.IntBuf

val bn_sub_:
    #aLen:size_nat -> #bLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    cbLen:size_t{v cbLen == bLen} -> b:lbignum bLen ->
    i:size_t{v i <= aLen} ->
    res:lbignum aLen -> Stack uint64
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    
let rec bn_sub_ #aLen #bLen caLen a cbLen b i res =
    if (i =. size 0) then u64 0
    else begin
        let i1 = size_decr i in
        let carry' = bn_sub_ #aLen #bLen caLen a cbLen b i1 res in
        let t1 = a.(i1) in 
        let t2 = if (i1 <. cbLen) then b.(i1) else u64 0 in
        let res_i = sub_mod #U64 (sub_mod #U64 t1 t2) carry' in
        res.(i1) <- res_i;
        (if (eq_u64 carry' (u64 1)) then
            (if (le_u64 t1 t2) then u64 1 else u64 0)
        else
            (if (lt_u64 t1 t2) then u64 1 else u64 0))
    end

(* a must be greater than b *)
(* ADD: isMore aLen bLen a b *)
(* res = a - b *)
val bn_sub:
    #aLen:size_nat -> #bLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    cbLen:size_t{v cbLen == bLen /\ bLen <= aLen} -> b:lbignum bLen ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    
let bn_sub #aLen #bLen caLen a cbLen b res =
    let _ = bn_sub_ #aLen #bLen caLen a cbLen b caLen res in ()


val bn_add_:
    #aLen:size_nat -> #bLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    cbLen:size_t{v cbLen == bLen} -> b:lbignum bLen ->
    i:size_t{v i <= aLen} ->
    res:lbignum aLen -> Stack uint64
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    
let rec bn_add_ #aLen #bLen caLen a cbLen b i res =
    if (i =. size 0) then u64 0
    else begin
        let i1 = size_decr i in
        let carry' = bn_add_ #aLen #bLen caLen a cbLen b i1 res in
        let t1 = a.(i1) in 
        let t2 = if (i1 <. cbLen) then b.(i1) else u64 0 in
        let res_i = add_mod #U64 (add_mod #U64 t1 t2) carry' in
        res.(i1) <- res_i;
        (if (lt_u64 res_i t1) then u64 1 else u64 0)
    end

val bn_add:
    #aLen:size_nat -> #bLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    cbLen:size_t{v cbLen == bLen /\ bLen <= aLen} -> b:lbignum bLen ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
let bn_add #aLen #bLen caLen a cbLen b res =
    let _ = bn_add_ #aLen #bLen caLen a cbLen b caLen res in ()

val bn_add_carry:
    #aLen:size_nat -> #bLen:size_nat ->
    caLen:size_t{v caLen == aLen /\ aLen + 1 < max_size_t} -> a:lbignum aLen ->
    cbLen:size_t{v cbLen == bLen /\ bLen <= aLen} -> b:lbignum bLen ->
    res:lbignum (aLen + 1) -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    
let bn_add_carry #aLen #bLen caLen a cbLen b res =
    let res' = Buffer.sub #uint64 #(aLen + 1) #aLen res (size 0) caLen in
    let carry = bn_add_ #aLen #bLen caLen a cbLen b caLen res' in
    res.(caLen) <- carry
