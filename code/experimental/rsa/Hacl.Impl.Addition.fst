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
    i:size_t{v i <= aLen} -> carry:uint64 ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    
let rec bn_sub_ #aLen #bLen caLen a cbLen b i carry res =
    if (i <. caLen) then begin
       let t1 = a.(i) in
       let t2 = if (i <. cbLen) then b.(i) else u64 0 in
       let res_i = sub_mod #U64 (sub_mod #U64 t1 t2) carry in
       res.(i) <- res_i;
       let carry =
           if (eq_u64 carry (u64 1)) then
              (if (le_u64 t1 t2) then u64 1 else u64 0)
           else
              (if (lt_u64 t1 t2) then u64 1 else u64 0) in
       bn_sub_ #aLen #bLen caLen a cbLen b (size_incr i) carry res
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
    bn_sub_ #aLen #bLen caLen a cbLen b (size 0) (u64 0) res

val bn_add_:
    #aLen:size_nat -> #bLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    cbLen:size_t{v cbLen == bLen} -> b:lbignum bLen ->
    i:size_t{v i <= aLen} -> carry:uint64 ->
    res:lbignum aLen -> Stack uint64
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    
let rec bn_add_ #aLen #bLen caLen a cbLen b i carry res =
    if (i <. caLen) then begin
       let t1 = a.(i) in
       let t2 = if (i <. cbLen) then b.(i) else u64 0 in
       let t1 = add_mod #U64 t1 carry in
       let carry = if (lt_u64 t1 carry) then u64 1 else u64 0 in
       let res_i = add_mod #U64 t1 t2 in
       res.(i) <- res_i;
       let carry = if (lt_u64 res_i t1) then add #U64 carry (u64 1) else carry in
       bn_add_ #aLen #bLen caLen a cbLen b (size_incr i) carry res end
    else carry

val bn_add:
    #aLen:size_nat -> #bLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    cbLen:size_t{v cbLen == bLen /\ bLen <= aLen} -> b:lbignum bLen ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

let bn_add #aLen #bLen caLen a cbLen b res =
    let _ = bn_add_ #aLen #bLen caLen a cbLen b (size 0) (u64 0) res in ()

val bn_add_carry:
    #aLen:size_nat -> #bLen:size_nat ->
    caLen:size_t{v caLen == aLen /\ aLen + 1 < max_size_t} -> a:lbignum aLen ->
    cbLen:size_t{v cbLen == bLen /\ bLen <= aLen} -> b:lbignum bLen ->
    res:lbignum (aLen + 1) -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    
let bn_add_carry #aLen #bLen caLen a cbLen b res =
    let res' = Buffer.sub #uint64 #(aLen + 1) #aLen res (size 0) caLen in
    let carry = bn_add_ #aLen #bLen caLen a cbLen b (size 0) (u64 0) res' in
    res.(caLen) <- carry
