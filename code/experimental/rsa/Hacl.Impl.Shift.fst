module Hacl.Impl.Shift

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes

open Hacl.Impl.Lib

module Buffer = Spec.Lib.IntBuf

let bn_tbit = u64 0x8000000000000000

val bn_lshift1_:
    #aLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    carry:uint64 -> i:size_t{v i <= aLen} ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> live h a /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

let rec bn_lshift1_ #aLen caLen a carry i res =
    if (i <. caLen) then begin
        let tmp = a.(i) in
        res.(i) <- (shift_left #U64 tmp (u32 1)) |. carry;
        let carry = if (eq_u64 (logand #U64 tmp bn_tbit) bn_tbit) then u64 1 else u64 0 in
        bn_lshift1_ #aLen caLen a carry (size_incr i) res
    end

(* res = a << 1 *)
val bn_lshift1:
    #aLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> live h a /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

let bn_lshift1 #aLen caLen a res = bn_lshift1_ #aLen caLen a (u64 0) (size 0) res

val bn_rshift_:
    #aLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    i:size_t{v i > 0} -> nw:size_t ->
    rb:uint32{0 < uint_v #U32 rb /\ uint_v #U32 rb < 64} -> l:uint64 ->
    res:lbignum aLen{v i + v nw <= aLen} -> Stack unit
    (requires (fun h -> live h a /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

#reset-options "--z3rlimit 50 --max_fuel 0"

let rec bn_rshift_ #aLen caLen a i nw rb l res =
    if (i <. sub #SIZE caLen nw) then begin
        let tmp = l >>. rb in
        let l = a.(add #SIZE nw i) in
        let lb = u32 64 -. rb in
        assert(0 < uint_v #U32 lb /\ uint_v #U32 lb < 64);
        res.(size_decr i) <- tmp |. (shift_left #U64 l lb);
        bn_rshift_ #aLen caLen a (size_incr i) nw rb l res end
    else res.(size_decr i) <- shift_right #U64 l rb

(* res = a >> n *)
val bn_rshift:
    #aLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    nCount:size_t{v nCount > 0 /\ aLen - v nCount / 64 - 1 > 0} ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> live h a /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
	
let bn_rshift #aLen caLen a nCount res =
    let nw = nCount /. size 64 in
    let rb = nCount %. size 64 in
    (if rb =. size 0 then begin
	let a_Len = sub #SIZE caLen nw in
	let a_ = Buffer.sub #uint64 #aLen #(v a_Len) a nw a_Len in
	let res_ = Buffer.sub #uint64 #aLen #(v a_Len) res (size 0) a_Len in
	copy a_Len a_ res_ end
    else begin
        let l = a.(nw) in
        bn_rshift_ #aLen caLen a (size 1) nw (size_to_uint32 rb) l res end)

// res = a % (pow2 nCount)
val bn_mod_pow2_n:
    #aLen:size_nat -> #resLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    nCount:size_t ->
    cresLen:size_t{v cresLen == resLen /\ resLen <= aLen /\ resLen - v nCount / 64 - 1 >= 0} ->
    res:lbignum resLen -> Stack unit
    (requires (fun h -> live h a /\ live h res /\ disjoint res a))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

let bn_mod_pow2_n #aLen #resLen caLen a nCount cresLen res =
    let nw = nCount /. size 64 in
    let nb = nCount %. size 64 in
    let a_ = Buffer.sub a (size 0) cresLen in
    copy cresLen a_ res;

    let start_i:size_t =
        if (nb >. size 0) then begin
	    let lb = sub #U32 (u32 64) (size_to_uint32 nb) in
            res.(nw) <- res.(nw) &. (shift_right #U64 (u64 0xffffffffffffffff) lb);
            size_incr nw end
        else nw in

    if (start_i <. cresLen) then begin
       let res_Len = sub #SIZE cresLen start_i in
       let res_ = Buffer.sub #uint64 #resLen #(v res_Len) res start_i res_Len in
       fill res_Len res_ (u64 0) end
