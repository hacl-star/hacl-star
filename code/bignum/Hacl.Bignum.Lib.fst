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
    #t:limb_t
  -> len:size_t
  -> b:lbignum t len
  -> i:size_t{v i / bits t < v len} ->
  Stack (limb t)
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> h0 == h1 /\
    r == S.bn_get_ith_bit (as_seq h0 b) (v i))

let bn_get_ith_bit #t len input ind =
  [@inline_let]
  let pbits = size (bits t) in
  let i = ind /. pbits in
  assert (v i == v ind / bits t);
  let j = ind %. pbits in
  assert (v j == v ind % bits t);
  let tmp = input.(i) in
  (tmp >>. j) &. uint #t 1


inline_for_extraction noextract
val bn_set_ith_bit:
    #t:limb_t
  -> len:size_t
  -> b:lbignum t len
  -> i:size_t{v i / bits t < v len} ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_seq h1 b == S.bn_set_ith_bit (as_seq h0 b) (v i))

let bn_set_ith_bit #t len input ind =
  [@inline_let]
  let pbits = size (bits t) in
  let i = ind /. pbits in
  assert (v i == v ind / bits t);
  let j = ind %. pbits in
  assert (v j == v ind % bits t);
  input.(i) <- input.(i) |. (uint #t 1 <<. j)


inline_for_extraction noextract
val cswap2_st:
    #t:limb_t
  -> len:size_t
  -> bit:limb t
  -> b1:lbignum t len
  -> b2:lbignum t len ->
  Stack unit
  (requires fun h -> live h b1 /\ live h b2 /\ disjoint b1 b2)
  (ensures  fun h0 _ h1 -> modifies (loc b1 |+| loc b2) h0 h1 /\
    (as_seq h1 b1, as_seq h1 b2) == S.cswap2 bit (as_seq h0 b1) (as_seq h0 b2))

let cswap2_st #t len bit b1 b2 =
  [@inline_let]
  let mask = uint #t 0 -. bit in
  [@inline_let]
  let spec h0 = S.cswap2_f mask in

  let h0 = ST.get () in
  loop2 h0 len b1 b2 spec
  (fun i ->
    Loops.unfold_repeati (v len) (spec h0) (as_seq h0 b1, as_seq h0 b2) (v i);
    let dummy = mask &. (b1.(i) ^. b2.(i)) in
    b1.(i) <- b1.(i) ^. dummy;
    b2.(i) <- b2.(i) ^. dummy
  )


inline_for_extraction noextract
val bn_leading_zero_index:
    #t:limb_t
  -> len:size_t{0 < v len}
  -> b:lbignum t len ->
  Stack (limb t)
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    v r == S.bn_leading_zero_index (as_seq h0 b))

let bn_leading_zero_index #t len b =
  push_frame ();
  let priv = create 1ul (uint #t 0) in

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
    let mask = eq_mask b.(i) (zeros t SEC) in
    let h1 = ST.get () in
    priv.(0ul) <- mask_select mask priv.(0ul) (size_to_limb i);
    mask_select_lemma mask (LSeq.index (as_seq h1 priv) 0) (size_to_limb i));
  let res = priv.(0ul) in
  pop_frame ();
  res


inline_for_extraction noextract
val limb_leading_zero_index: #t:limb_t -> a:limb t ->
  Stack (limb t)
  (requires fun h -> True)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    v r == S.limb_leading_zero_index a)

let limb_leading_zero_index #t a =
  push_frame ();
  let priv = create 1ul (uint #t 0) in

  let h0 = ST.get () in
  [@ inline_let]
  let refl h i = v (LSeq.index (as_seq h priv) 0) in
  [@ inline_let]
  let spec h0 = S.limb_leading_zero_index_f a in

  [@ inline_let]
  let inv h (i:nat{i <= bits t}) =
    modifies1 priv h0 h /\ live h priv /\
    refl h i == Loops.repeat_gen i (S.limb_leading_zero_index_t t) (spec h0) (refl h0 0) in

  Loops.eq_repeat_gen0 (bits t) (S.limb_leading_zero_index_t t) (spec h0) (refl h0 0);
  Lib.Loops.for 0ul (size (bits t)) inv
  (fun i ->
    Loops.unfold_repeat_gen (bits t) (S.limb_leading_zero_index_t t) (spec h0) (refl h0 0) (v i);
    let bit_i = (a >>. i) &. uint #t 1 in
    let mask = eq_mask bit_i (uint #t 1) in
    let h1 = ST.get () in
    priv.(0ul) <- mask_select mask (size_to_limb i) priv.(0ul);
    mask_select_lemma mask (size_to_limb i) (LSeq.index (as_seq h1 priv) 0));
  let res = priv.(0ul) in
  pop_frame ();
  res


inline_for_extraction noextract
val bn_get_num_bits:
    #t:limb_t
  -> len:size_t{0 < v len /\ bits t * v len <= max_size_t}
  -> b:lbignum t len ->
  Stack (limb t)
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    v r == S.bn_get_num_bits (as_seq h0 b))

let bn_get_num_bits #t len b =
  //TODO: call `limb_leading_zero_index` for each limb
  let ind = bn_leading_zero_index len b in
  let bs = limb_leading_zero_index b.(Lib.RawIntTypes.(size_from_UInt32 (u32_to_UInt32 (to_u32 ind)))) in
  uint #t (bits t) *! ind +! bs
