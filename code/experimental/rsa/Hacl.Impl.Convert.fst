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
  len:size_t -> input:lbytes len ->
  resLen:size_t{v len = 8 * v resLen} -> res:lbignum resLen -> Stack unit
  (requires (fun h -> live h input /\ live h res /\ disjoint res input))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@ "substitute"]
let text_to_nat_ len input resLen res =
  iteri_simple #uint64 #(v resLen) resLen
  (fun i res ->
    let h = FStar.HyperStack.ST.get() in
    assume (live h input);
    res.(sub #SIZE (sub #SIZE resLen i) (size 1)) <- uint64_from_bytes_be (Buffer.sub #uint8 #(v len) #8 input (mul #SIZE (size 8) i) (size 8))
  ) res

val text_to_nat:
  len:size_t{v len > 0} -> input:lbytes len ->
  res:lbignum (blocks len (size 8)){8 * v (blocks len (size 8)) < max_size_t} -> Stack unit
  (requires (fun h -> live h input /\ live h res /\ disjoint res input))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  #reset-options "--z3rlimit 50 --max_fuel 0"
  [@"c_inline"]
let text_to_nat len input res =
  let num_words = blocks len (size 8) in
  let tmpLen = mul #SIZE (size 8) num_words in
  let m = len %. size 8 in
  let ind = if (m =. size 0) then size 0 else sub #SIZE (size 8) m in

  let h0 = FStar.HyperStack.ST.get () in
  alloc1 #h0 tmpLen (u8 0) res
  (fun h -> (fun _ r -> True))
  (fun tmp ->
    let tmpLen1 = sub #SIZE tmpLen ind in
    assert (v tmpLen1 = v len);
    let tmp1 = Buffer.sub tmp ind tmpLen1 in
    copy tmp1 len input;
    text_to_nat_ tmpLen tmp num_words res
  )

val nat_to_text_:
  len:size_t -> input:lbignum len ->
  resLen:size_t{v resLen = 8 * v len} -> res:lbytes resLen -> Stack unit
  (requires (fun h -> live h input /\ live h res /\ disjoint res input))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@ "substitute"]
let nat_to_text_ len input resLen res =
  iteri_simple #uint8 #(v resLen) len
  (fun i res ->
    let h = FStar.HyperStack.ST.get() in
    assume (live h input);
    let tmp = input.(sub #SIZE (sub #SIZE len i) (size 1)) in
    uint64_to_bytes_be (Buffer.sub res (mul #SIZE (size 8) i) (size 8)) tmp
  ) res

val nat_to_text:
  len:size_t{v len > 0} ->
  input:lbignum (blocks len (size 8)){8 * v (blocks len (size 8)) < max_size_t} ->
  res:lbytes len -> Stack unit
  (requires (fun h -> live h input /\ live h res /\ disjoint res input))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  #reset-options "--z3rlimit 50 --max_fuel 0"
  [@"c_inline"]
let nat_to_text len input res =
  let num_words = blocks len (size 8) in
  let tmpLen = mul #SIZE (size 8) num_words in
  let m = len %. size 8 in
  let ind = if (m =. size 0) then size 0 else sub #SIZE (size 8) m in

  let h0 = FStar.HyperStack.ST.get () in
  alloc1 #h0 tmpLen (u8 0) res
  (fun h -> (fun _ r -> True))
  (fun tmp ->
    nat_to_text_ num_words input tmpLen tmp;
    let tmpLen1 = sub #SIZE tmpLen ind in
    assert (v tmpLen1 = v len);
    let tmp1 = Buffer.sub tmp ind tmpLen1 in
    copy res len tmp1
  )
