module Hacl.Bignum.Lib

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Base
open Hacl.Bignum.Definitions

module S = Hacl.Spec.Bignum.Lib
module ST = FStar.HyperStack.ST
module Loops = Lib.LoopCombinators
module LSeq = Lib.Sequence


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///
///  Get and set i-th bit of a bignum
///

inline_for_extraction noextract
val bn_get_ith_bit:
    len:size_t
  -> b:lbignum len
  -> i:size_t{v i / 64 < v len} ->
  Stack uint64
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> h0 == h1 /\
    r == S.bn_get_ith_bit (as_seq h0 b) (v i))

let bn_get_ith_bit len input ind =
  let i = ind /. 64ul in
  let j = ind %. 64ul in
  let tmp = input.(i) in
  (tmp >>. j) &. u64 1


inline_for_extraction noextract
val bn_set_ith_bit:
    len:size_t
  -> b:lbignum len
  -> i:size_t{v i / 64 < v len} ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_seq h1 b == S.bn_set_ith_bit (as_seq h0 b) (v i))

let bn_set_ith_bit len input ind =
  let i = ind /. 64ul in
  let j = ind %. 64ul in
  input.(i) <- input.(i) |. (u64 1 <<. j)


inline_for_extraction noextract
val cswap2_st:
    len:size_t
  -> bit:uint64
  -> b1:lbuffer uint64 len
  -> b2:lbuffer uint64 len ->
  Stack unit
  (requires fun h -> live h b1 /\ live h b2 /\ disjoint b1 b2)
  (ensures  fun h0 _ h1 -> modifies (loc b1 |+| loc b2) h0 h1 /\
    (as_seq h1 b1, as_seq h1 b2) == S.cswap2 bit (as_seq h0 b1) (as_seq h0 b2))

let cswap2_st len bit b1 b2 =
  [@inline_let]
  let mask = u64 0 -. bit in
  [@inline_let]
  let spec h0 = S.cswap2_f mask in

  let h0 = ST.get () in
  loop2 h0 len b1 b2 spec
  (fun i ->
    Lib.LoopCombinators.unfold_repeati (v len) (spec h0) (as_seq h0 b1, as_seq h0 b2) (v i);
    let dummy = mask &. (b1.(i) ^. b2.(i)) in
    b1.(i) <- b1.(i) ^. dummy;
    b2.(i) <- b2.(i) ^. dummy
  )


inline_for_extraction noextract
val bn_leading_zero_index:
    len:size_t{0 < v len}
  -> b:lbignum len ->
  Stack uint64
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    v r == S.bn_leading_zero_index (as_seq h0 b))

let bn_leading_zero_index len b =
  push_frame ();
  let priv = create 1ul (u64 0) in

  let h0 = ST.get () in
  [@ inline_let]
  let refl h i = v (LSeq.index (as_seq h priv) 0) in
  [@ inline_let]
  let spec h0 = S.bn_leading_zero_index_f (as_seq h0 b) in

  [@ inline_let]
  let inv h (i:nat{i <= v len}) =
    modifies1 priv h0 h /\
    live h priv /\ live h b /\ disjoint priv b /\
    refl h i == Loops.repeat_gen i (S.bn_leading_zero_index_t (v len)) (spec h0) (refl h0 0) in

  Loops.eq_repeat_gen0 (v len) (S.bn_leading_zero_index_t (v len)) (spec h0) (refl h0 0);
  Lib.Loops.for 0ul len inv
  (fun i ->
    Loops.unfold_repeat_gen (v len) (S.bn_leading_zero_index_t (v len)) (spec h0) (refl h0 0) (v i);
    let mask = eq_mask b.(i) (zeros U64 SEC) in
    let h1 = ST.get () in
    priv.(0ul) <- mask_select mask priv.(0ul) (size_to_uint64 i);
    mask_select_lemma mask (LSeq.index (as_seq h1 priv) 0) (size_to_uint64 i));
  let res = priv.(0ul) in
  pop_frame ();
  res


inline_for_extraction noextract
val limb_leading_zero_index: a:uint64 ->
  Stack uint64
  (requires fun h -> True)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    v r == S.limb_leading_zero_index a)

let limb_leading_zero_index a =
  push_frame ();
  let priv = create 1ul (u64 0) in

  let h0 = ST.get () in
  [@ inline_let]
  let refl h i = v (LSeq.index (as_seq h priv) 0) in
  [@ inline_let]
  let spec h0 = S.limb_leading_zero_index_f a in

  [@ inline_let]
  let inv h (i:nat{i <= 64}) =
    modifies1 priv h0 h /\ live h priv /\
    refl h i == Loops.repeat_gen i S.limb_leading_zero_index_t (spec h0) (refl h0 0) in

  Loops.eq_repeat_gen0 64 S.limb_leading_zero_index_t (spec h0) (refl h0 0);
  Lib.Loops.for 0ul 64ul inv
  (fun i ->
    Loops.unfold_repeat_gen 64 S.limb_leading_zero_index_t (spec h0) (refl h0 0) (v i);
    let bit_i = (a >>. i) &. u64 1 in
    let mask = eq_mask bit_i (u64 1) in
    let h1 = ST.get () in
    priv.(0ul) <- mask_select mask (size_to_uint64 i) priv.(0ul);
    mask_select_lemma mask (size_to_uint64 i) (LSeq.index (as_seq h1 priv) 0));
  let res = priv.(0ul) in
  pop_frame ();
  res


inline_for_extraction noextract
val bn_get_num_bits:
    len:size_t{0 < v len /\ 64 * v len <= max_size_t}
  -> b:lbignum len ->
  Stack size_t
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    v r == S.bn_get_num_bits (as_seq h0 b))

let bn_get_num_bits len b =
  //TODO: call `limb_leading_zero_index` for each limb
  let ind = bn_leading_zero_index len b in
  let bits = limb_leading_zero_index b.(Lib.RawIntTypes.(size_from_UInt32 (u32_to_UInt32 (to_u32 ind)))) in
  Lib.RawIntTypes.(size_from_UInt32 (u32_to_UInt32 (to_u32 (u64 64 *! ind +! bits))))
