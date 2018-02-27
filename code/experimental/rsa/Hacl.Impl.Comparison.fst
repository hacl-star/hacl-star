module Hacl.Impl.Comparison

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes

open Hacl.Impl.Lib

val bn_is_less_:
    #aLen:size_nat -> #bLen:size_nat ->
    aaLen:size_t{v aaLen == aLen} -> a:lbignum aLen ->
    bbLen:size_t{v bbLen == bLen /\ bLen <= aLen} -> b:lbignum bLen ->
    i:size_t{v i <= aLen} -> Stack bool
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ h0 == h1))
    [@"c_inline"]
let rec bn_is_less_ #aLen #bLen aaLen a bbLen b i =
    if (i >. size 0) then
        let i = size_decr i in
        let t1 = a.(i) in
        let t2 = bval bbLen b i in
        (if not (eq_u64 t1 t2) then
            if lt_u64 t1 t2 then true else false
        else bn_is_less_ aaLen a bbLen b i)
    else false

val bn_is_less:
    #aLen:size_nat -> #bLen:size_nat ->
    aaLen:size_t{v aaLen == aLen} -> a:lbignum aLen ->
    bbLen:size_t{v bbLen == bLen /\ bLen <= aLen} -> b:lbignum bLen -> Stack bool
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ h0 == h1))
    [@"c_inline"]
let bn_is_less #aLen #bLen aaLen a bbLen b = bn_is_less_ aaLen a bbLen b aaLen
