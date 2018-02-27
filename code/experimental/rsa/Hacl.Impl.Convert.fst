module Hacl.Impl.Convert

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open Spec.Lib.Endian
open FStar.Mul

open Hacl.Impl.Lib

module Buffer = Spec.Lib.IntBuf

val text_to_nat_:
    #len:size_nat ->
    clen:size_t{v clen == len} ->
    input:lbytes len ->
    resLen:size_t{len = 8 * v resLen} ->
    res:lbignum (v resLen) ->
    i:size_t{v i <= v resLen} -> Stack unit
    (requires (fun h -> live h input /\ live h res /\ disjoint res input))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    [@"c_inline"]
let rec text_to_nat_ #len clen input resLen res i =
    if (i <. resLen) then begin
        let inputi = uint64_from_bytes_be (Buffer.sub input (mul #SIZE (size 8) i) (size 8)) in
	let ind = sub #SIZE (sub #SIZE resLen i) (size 1) in
        res.(ind) <- inputi;
        text_to_nat_ #len clen input resLen res (size_incr i)
    end

val text_to_nat:
    #len:size_nat{len > 0} ->
    clen:size_t{v clen == len} ->
    input:lbytes len ->
    res:lbignum (v (get_size_nat clen)){8 * v (get_size_nat clen) < max_size_t} -> Stack unit
    (requires (fun h -> live h input /\ live h res /\ disjoint res input))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

#reset-options "--z3rlimit 50 --max_fuel 0"
    [@"c_inline"]
let text_to_nat #len clen input res =
    let num_words = get_size_nat clen in
    let tmpLen = mul #SIZE (size 8) num_words in
    let m = clen %. size 8 in
    let ind = if (m =. size 0) then size 0 else sub #SIZE (size 8) m in

    alloc #uint8 #unit #(v tmpLen) tmpLen (u8 0) [BufItem input] [BufItem res]
    (fun h0 _ h1 -> True)
    (fun tmp ->
      let tmp_Len = sub #SIZE tmpLen ind in
      assume (v tmp_Len = v clen);
      let tmp_:lbuffer uint8 len = Buffer.sub #uint8 #(v tmpLen) #(v tmp_Len) tmp ind tmp_Len in
      copy #uint8 #len clen input tmp_;
      text_to_nat_ tmpLen tmp num_words res (size 0)
    )
  

val nat_to_text_:
    #len:size_nat ->
    clen:size_t{v clen == len} ->
    input:lbignum len ->
    resLen:size_t{v resLen = 8 * len} ->
    res:lbytes (v resLen) ->
    i:size_t{v i <= len} -> Stack unit
    (requires (fun h -> live h input /\ live h res /\ disjoint res input))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    [@"c_inline"]
let rec nat_to_text_ #len clen input resLen res i =
    if (i <. clen) then begin
        let ind = sub #SIZE (sub #SIZE clen i) (size 1) in
        let tmp = input.(ind) in
	uint64_to_bytes_be (Buffer.sub res (mul #SIZE (size 8) i) (size 8)) tmp;
        nat_to_text_ #len clen input resLen res (size_incr i)
    end

val nat_to_text:
    #len:size_nat{len > 0} ->
    clen:size_t{v clen == len} ->
    input:lbignum (v (get_size_nat clen)){8 * v (get_size_nat clen) < max_size_t} ->
    res:lbytes len -> Stack unit
    (requires (fun h -> live h input /\ live h res /\ disjoint res input))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

#reset-options "--z3rlimit 50 --max_fuel 0"
    [@"c_inline"]
let nat_to_text #len clen input res =
    let num_words = get_size_nat clen in
    let tmpLen = mul #SIZE (size 8) num_words in
    let m = clen %. size 8 in
    let ind = if (m =. size 0) then size 0 else sub #SIZE (size 8) m in

    alloc #uint8 #unit #(v tmpLen) tmpLen (u8 0) [BufItem input] [BufItem res]
    (fun h0 _ h1 -> True)
    (fun tmp ->
      nat_to_text_ num_words input tmpLen tmp (size 0);
      let tmp_Len = sub #SIZE tmpLen ind in
      assume (v tmp_Len = v clen);
      let tmp_:lbuffer uint8 (v tmp_Len) = Buffer.sub tmp ind tmp_Len in
      copy #uint8 #len clen tmp_ res
    )

