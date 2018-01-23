module Hacl.Impl.Comparison

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes

open Hacl.Impl.Lib

val bn_is_less_:
    #len:size_nat -> clen:size_t{v clen == len} ->
    a:lbignum len ->
    b:lbignum len ->
    i:size_t{v i <= len} -> Stack bool
    (requires (fun h -> live h a /\ live h b /\ disjoint a b))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ h0 == h1))

let rec bn_is_less_ #len clen a b i =
    if (i >. size 0) then
        let i = size_decr i in
        let t1 = a.(i) in
        let t2 = b.(i) in
        (if not (eq_u64 t1 t2) then
            if lt_u64 t1 t2 then true else false
        else bn_is_less_ #len clen a b i)
    else false

(* if a < b then true else false *)
val bn_is_less:
    #len:size_nat -> clen:size_t{v clen == len} ->
    a:lbignum len ->
    b:lbignum len -> Stack bool
    (requires (fun h -> live h a /\ live h b /\ disjoint a b))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ h0 == h1))
   
let bn_is_less #len clen a b = bn_is_less_ #len clen a b clen

val bn_is_less_ds_:
    #a0Len:size_nat -> #a1Len:size_nat ->
    aa0Len:size_t{v aa0Len == a0Len} -> a0:lbignum a0Len ->
    aa1Len:size_t{v aa1Len == a1Len /\ a1Len <= a0Len} -> a1:lbignum a1Len ->
    i:size_t{v i <= a0Len} -> Stack bool
    (requires (fun h -> live h a0 /\ live h a1))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ h0 == h1))

let rec bn_is_less_ds_ #a0Len #a1Len aa0Len a0 aa1Len a1 i =
    if (i >. size 0) then
        let i = size_decr i in
        let t1 = a0.(i) in
        let t2 = if (i <. aa1Len) then a1.(i) else u64 0 in
        (if not (eq_u64 t1 t2) then
            if lt_u64 t1 t2 then true else false
        else bn_is_less_ds_ aa0Len a0 aa1Len a1 i)
    else false

val bn_is_less_ds:
    #a0Len:size_nat -> #a1Len:size_nat ->
    aa0Len:size_t{v aa0Len == a0Len} -> a0:lbignum a0Len ->
    aa1Len:size_t{v aa1Len == a1Len /\ a1Len <= a0Len} -> a1:lbignum a1Len -> Stack bool
    (requires (fun h -> live h a0 /\ live h a1))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ h0 == h1))

let bn_is_less_ds #a0Len #a1len aa0Len a0 aa1Len a1 = bn_is_less_ds_ aa0Len a0 aa1Len a1 aa0Len
