module Hacl.Impl.Shift

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes

open Hacl.Impl.Lib
open Hacl.Impl.Comparison
open Hacl.Impl.Addition

module Buffer = Spec.Lib.IntBuf

(* This file will be removed *)

inline_for_extraction
let bn_tbit = u64 0x8000000000000000

val bn_lshift1_:
  aLen:size_t ->
  a:lbignum aLen -> carry:uint64 -> i:size_t{v i <= v aLen} ->
  res:lbignum aLen -> Stack unit
  (requires (fun h -> live h a /\ live h res))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@"c_inline"]
let rec bn_lshift1_ aLen a carry i res =
  if (i <. aLen) then begin
    let tmp = a.(i) in
    res.(i) <- (shift_left #U64 tmp (u32 1)) |. carry;
    let carry = if (eq_u64 (logand #U64 tmp bn_tbit) bn_tbit) then u64 1 else u64 0 in
    bn_lshift1_ aLen a carry (add #SIZE i (size 1)) res
  end

// res = a << 1
val bn_lshift1:
  aLen:size_t ->
  a:lbignum aLen -> res:lbignum aLen -> Stack unit
  (requires (fun h -> live h a /\ live h res))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@"c_inline"]
let bn_lshift1 aLen a res = bn_lshift1_ aLen a (u64 0) (size 0) res

val bn_pow2_mod_n_:
  aLen:size_t -> a:lbignum aLen ->
  i:size_t -> p:size_t ->
  rLen:size_t{v aLen < v rLen} -> res:lbignum rLen ->
  Stack unit
    (requires (fun h -> live h a /\ live h res /\ disjoint res a))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@"c_inline"]
let rec bn_pow2_mod_n_ aLen a i p rLen res =
  if (i <. p) then begin
    bn_lshift1 rLen res res;
    (if not (bn_is_less rLen res aLen a) then
      let _ = bn_sub rLen res aLen a res in ());
    bn_pow2_mod_n_ aLen a (add #SIZE i (size 1)) p rLen res
  end

// res = 2 ^^ p % a
val bn_pow2_mod_n:
  aLen:size_t{v aLen + 1 < max_size_t} ->
  aBits:size_t -> a:lbignum aLen ->
  p:size_t{v aBits < v p} ->
  res:lbignum aLen ->
  Stack unit
    (requires (fun h -> live h a /\ live h res /\ disjoint res a))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@"c_inline"]
let bn_pow2_mod_n aLen aBits a p res =
  let rLen = add #SIZE aLen (size 1) in
  let h0 = FStar.HyperStack.ST.get () in
  alloc1 #h0 rLen (u64 0) res
  (fun h -> (fun _ r -> True))
  (fun tmp ->
    assume (v aBits / 64 < v rLen);
    bn_set_bit rLen tmp aBits;
    let _ = bn_sub rLen tmp aLen a tmp in // tmp = tmp - a
    bn_pow2_mod_n_ aLen a aBits p rLen tmp;
    let tmp' = Buffer.sub tmp (size 0) aLen in
    copy res aLen tmp'
  )
