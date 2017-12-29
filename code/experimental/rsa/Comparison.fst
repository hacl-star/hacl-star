module Comparison

open FStar.HyperStack.All
open FStar.Buffer
open Lib

module U32 = FStar.UInt32
module U64 = FStar.UInt64
open U32

val bn_is_less_:
    len:U32.t ->
    a:lbignum len ->
    b:lbignum len ->
    i:U32.t{v i <= v len} -> Stack bool
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let rec bn_is_less_ len a b i =
    if (i >^ 0ul) then
        let i = i -^ 1ul in
        let t1 = a.(i) in
        let t2 = b.(i) in
        (if not (U64.(t1 =^ t2)) then
            if U64.(t1 <^ t2) then true else false
        else bn_is_less_ len a b i)
    else false

(* if a < b then true else false *)
val bn_is_less:
    len:U32.t ->
    a:lbignum len ->
    b:lbignum len -> Stack bool
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let bn_is_less len a b = bn_is_less_ len a b len