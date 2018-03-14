module Hacl.Impl.Shift

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes

open Hacl.Impl.Lib

module Buffer = Spec.Lib.IntBuf

inline_for_extraction
let bn_tbit = u64 0x8000000000000000

val bn_lshift1_:
    #aLen:size_nat -> aaLen:size_t{v aaLen == aLen} ->
    a:lbignum aLen -> carry:uint64 -> i:size_t{v i <= aLen} ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> live h a /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    [@"c_inline"]
let rec bn_lshift1_ #aLen aaLen a carry i res =
    if (i <. aaLen) then begin
        let tmp = a.(i) in
        res.(i) <- (shift_left #U64 tmp (u32 1)) |. carry;
        let carry = if (eq_u64 (logand #U64 tmp bn_tbit) bn_tbit) then u64 1 else u64 0 in
        bn_lshift1_ aaLen a carry (size_incr i) res
    end

// res = a << 1
val bn_lshift1:
    #aLen:size_nat -> aaLen:size_t{v aaLen == aLen} ->
    a:lbignum aLen -> res:lbignum aLen -> Stack unit
    (requires (fun h -> live h a /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    [@"c_inline"]
let bn_lshift1 #aLen aaLen a res = bn_lshift1_ aaLen a (u64 0) (size 0) res
