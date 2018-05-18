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
  clen:size_t{v clen == len} -> input:lbytes len ->
  resLen:size_t{len = 8 * v resLen} -> res:lbignum (v resLen) -> Stack unit
  (requires (fun h -> live h input /\ live h res /\ disjoint res input))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@ "substitute"]
let text_to_nat_ #len clen input resLen res =
  iteri_simple #uint64 #(v resLen) resLen
  (fun i res ->
    let h = FStar.HyperStack.ST.get() in
    assume (live h input);
    res.(sub #SIZE (sub #SIZE resLen i) (size 1)) <- uint64_from_bytes_be (Buffer.sub #uint8 #len #8 input (mul #SIZE (size 8) i) (size 8))
  ) res

val text_to_nat:
  #len:size_nat{len > 0} ->
  clen:size_t{v clen == len} -> input:lbytes len ->
  res:lbignum (v (blocks clen (size 8))){8 * v (blocks clen (size 8)) < max_size_t} -> Stack unit
  (requires (fun h -> live h input /\ live h res /\ disjoint res input))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@"c_inline"]
let text_to_nat #len clen input res =
  let num_words = blocks clen (size 8) in
  let tmpLen = mul #SIZE (size 8) num_words in
  let m = clen %. size 8 in
  let ind = if (m =. size 0) then size 0 else sub #SIZE (size 8) m in

  alloc #uint8 #unit #(v tmpLen) tmpLen (u8 0) [BufItem input] [BufItem res]
  (fun h0 _ h1 -> True)
  (fun tmp ->
    let tmpLen1 = sub #SIZE tmpLen ind in
    let tmp1 = Buffer.sub #uint8 #(v tmpLen) #(v tmpLen1) tmp ind tmpLen1 in
    copy clen input tmp1;
    text_to_nat_ #(v tmpLen) tmpLen tmp num_words res
  )

val nat_to_text_:
  #len:size_nat ->
  clen:size_t{v clen == len} -> input:lbignum len ->
  resLen:size_t{v resLen = 8 * len} -> res:lbytes (v resLen) -> Stack unit
  (requires (fun h -> live h input /\ live h res /\ disjoint res input))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@ "substitute"]
let nat_to_text_ #len clen input resLen res =
  iteri_simple #uint8 #(v resLen) clen
  (fun i res ->
    let h = FStar.HyperStack.ST.get() in
    assume (live h input);
    let tmp = input.(sub #SIZE (sub #SIZE clen i) (size 1)) in
    uint64_to_bytes_be (Buffer.sub res (mul #SIZE (size 8) i) (size 8)) tmp
  ) res

val nat_to_text:
  #len:size_nat{len > 0} -> clen:size_t{v clen == len} ->
  input:lbignum (v (blocks clen (size 8))){8 * v (blocks clen (size 8)) < max_size_t} ->
  res:lbytes len -> Stack unit
  (requires (fun h -> live h input /\ live h res /\ disjoint res input))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  #reset-options "--z3rlimit 50 --max_fuel 0"
  [@"c_inline"]
let nat_to_text #len clen input res =
  let num_words = blocks clen (size 8) in
  let tmpLen = mul #SIZE (size 8) num_words in
  let m = clen %. size 8 in
  let ind = if (m =. size 0) then size 0 else sub #SIZE (size 8) m in

  alloc #uint8 #unit #(v tmpLen) tmpLen (u8 0) [BufItem input] [BufItem res]
  (fun h0 _ h1 -> True)
  (fun tmp ->
    nat_to_text_ num_words input tmpLen tmp;
    let tmpLen1 = sub #SIZE tmpLen ind in
    let tmp1 = Buffer.sub #uint8 #(v tmpLen) #(v tmpLen1) tmp ind tmpLen1 in
    copy clen tmp1 res
  )
