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
[@ "substitute"]    
let bn_is_less #len clen a b = bn_is_less_ #len clen a b clen
