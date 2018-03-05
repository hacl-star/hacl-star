module Hacl.Impl.Shift

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes

open Hacl.Impl.Lib

module Buffer = Spec.Lib.IntBuf

inline_for_extraction
let bn_tbit = u64 0x8000000000000000

val bn_lshift_:
    #aLen:size_nat -> aaLen:size_t{v aaLen == aLen} ->
    a:lbignum aLen -> count:size_t -> nw:size_t ->
    lb:uint32{0 < uint_v #U32 lb /\ uint_v #U32 lb < 64} ->
    res:lbignum aLen{v count + v nw < aLen} -> Stack unit
    (requires (fun h -> live h a /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    [@"c_inline"]
let rec bn_lshift_ #aLen aaLen a count nw lb res =
    if (count >. size 0) then begin
       let i = add #SIZE nw count in
       let tmp = res.(i) in
       let count = size_decr count in
       let t1 = a.(count) in
       let rb = u32 64 -. lb in
       assert (0 < uint_v #U32 rb /\ uint_v #U32 rb < 64);
       res.(i) <- tmp |. (shift_right #U64 t1 rb);
       res.(size_decr i) <- shift_left #U64 t1 lb;
       bn_lshift_ aaLen a count nw lb res end

// res = a << n
val bn_lshift:
    #aLen:size_nat -> aaLen:size_t{v aaLen == aLen} ->
    a:lbignum aLen -> nCount:size_t{aLen - (v nCount) / 64 > 0} ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> live h a /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    [@"c_inline"]
let bn_lshift #aLen aaLen a nCount res =
    if (nCount =. size 0) then
       copy aaLen a res
    else begin
       fill aaLen res (u64 0);
       let nw = nCount /. size 64 in
       let lb = nCount %. size 64 in
       if (lb =. size 0) then begin
          let aLen' = sub #SIZE aaLen nw in
          let a' = Buffer.sub #uint64 #aLen #(v aLen') a (size 0) aLen' in
          let res' = Buffer.sub #uint64 #aLen #(v aLen') res nw aLen' in
          copy aLen' a' res' end
       else begin
          let lb = size_to_uint32 lb in
          let count = size_decr (sub #SIZE aaLen nw) in
          let t1 = a.(count) in
          let i = add #SIZE nw count in
          res.(i) <- shift_left #U64 t1 lb;
          bn_lshift_ #aLen aaLen a count nw lb res end
    end
  
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

val bn_rshift_:
    #aLen:size_nat -> aaLen:size_t{v aaLen == aLen} ->
    a:lbignum aLen -> i:size_t{v i > 0} -> nw:size_t ->
    rb:uint32{0 < uint_v #U32 rb /\ uint_v #U32 rb < 64} -> l:uint64 ->
    res:lbignum aLen{v i + v nw <= aLen} -> Stack unit
    (requires (fun h -> live h a /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    [@"c_inline"]
let rec bn_rshift_ #aLen aaLen a i nw rb l res =
    if (i <. sub #SIZE aaLen nw) then begin
        let tmp = l >>. rb in
        let l = a.(add #SIZE nw i) in
        let lb = u32 64 -. rb in
        assert(0 < uint_v #U32 lb /\ uint_v #U32 lb < 64);
        res.(size_decr i) <- tmp |. (shift_left #U64 l lb);
        bn_rshift_ aaLen a (size_incr i) nw rb l res end
    else res.(size_decr i) <- shift_right #U64 l rb

// res = a >> n
val bn_rshift:
    #aLen:size_nat -> aaLen:size_t{v aaLen == aLen} ->
    a:lbignum aLen -> nCount:size_t{aLen - v nCount / 64 > 0} ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> live h a /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    [@"c_inline"]
let bn_rshift #aLen aaLen a nCount res =
    if (nCount =. size 0) then
      copy aaLen a res
    else begin
      let nw = nCount /. size 64 in
      let rb = nCount %. size 64 in
      (if rb =. size 0 then begin
          let aLen' = sub #SIZE aaLen nw in
          let a' = Buffer.sub #uint64 #aLen #(v aLen') a nw aLen' in
          let res' = Buffer.sub #uint64 #aLen #(v aLen') res (size 0) aLen' in
          copy aLen' a' res' end
      else begin
          let l = a.(nw) in
          bn_rshift_ aaLen a (size 1) nw (size_to_uint32 rb) l res end)
      end

// res = a % (pow2 nCount)
val bn_mod_pow2_n:
    #aLen:size_nat -> #resLen:size_nat ->
    aaLen:size_t{v aaLen == aLen} -> a:lbignum aLen -> nCount:size_t ->
    rresLen:size_t{v rresLen == resLen /\ resLen <= aLen /\ resLen - v nCount / 64 > 0} ->
    res:lbignum resLen -> Stack unit
    (requires (fun h -> live h a /\ live h res /\ disjoint res a))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    [@"c_inline"]
let bn_mod_pow2_n #aLen #resLen aaLen a nCount rresLen res =
    let nw = nCount /. size 64 in
    let nb = nCount %. size 64 in
    let a' = Buffer.sub a (size 0) rresLen in
    copy rresLen a' res;

    let start_i:size_t =
        if (nb >. size 0) then begin
           let lb = sub #U32 (u32 64) (size_to_uint32 nb) in
           res.(nw) <- res.(nw) &. (shift_right #U64 (u64 0xffffffffffffffff) lb);
           size_incr nw end
        else nw in

    if (start_i <. rresLen) then begin
       let resLen' = sub #SIZE rresLen start_i in
       let res' = Buffer.sub #uint64 #resLen #(v resLen') res start_i resLen' in
       fill resLen' res' (u64 0) end
