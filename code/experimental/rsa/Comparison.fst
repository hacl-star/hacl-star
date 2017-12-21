module Comparison

open FStar.HyperStack.All
open FStar.Buffer
open Lib

module U32 = FStar.UInt32
module U64 = FStar.UInt64

val bn_is_less_:
    len:bnlen -> a:lbignum len ->
    b:lbignum len{disjoint a b} ->
    i:U32.t{U32.v i <= U32.v len} -> Stack bool
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ 
			     live h1 a /\ live h1 b /\ h0 == h1))

let rec bn_is_less_ len a b i =
    if U32.(i >^ 0ul) then
        let i = U32.(i -^ 1ul) in
        let t1 = a.(i) in
        let t2 = b.(i) in
        (if not (U64.(t1 =^ t2)) then
            if U64.(t1 <^ t2) then true else false
        else bn_is_less_ len a b i)
    else false

(* if a < b then true else false *)
val bn_is_less:
    len:bnlen -> a:lbignum len ->
    b:lbignum len{disjoint a b} -> Stack bool
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ 
			     live h1 a /\ live h1 b /\ h0 == h1))

let bn_is_less len a b = bn_is_less_ len a b len