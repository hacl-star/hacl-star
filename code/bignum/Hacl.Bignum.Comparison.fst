module Hacl.Bignum.Comparison

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Base
open Hacl.Bignum.Definitions
open Hacl.Bignum.Lib

module S = Hacl.Spec.Bignum.Comparison
module ST = FStar.HyperStack.ST
module Loops = Lib.LoopCombinators


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///
///  Bignum comparison and test functions
///

inline_for_extraction noextract
val bn_is_odd:
    #t:limb_t
  -> len:size_t{v len > 0}
  -> a:lbignum t len ->
  Stack (limb t)
  (requires fun h -> live h a)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_is_odd (as_seq h0 a))

let bn_is_odd #t len a = a.(0ul) &. uint #t 1


inline_for_extraction noextract
val bn_eq_mask:
    #t:limb_t
  -> len:size_t
  -> a:lbignum t len
  -> b:lbignum t len ->
  Stack (limb t)
  (requires fun h -> live h a /\ live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_eq_mask (as_seq h0 a) (as_seq h0 b))

let bn_eq_mask #t len a b =
  push_frame ();
  let mask = create 1ul (ones t SEC) in
  let mask = Lib.ByteBuffer.buf_eq_mask a b len mask in
  pop_frame ();
  mask


inline_for_extraction noextract
val bn_is_zero_mask:
    #t:limb_t
  -> len:size_t{v len > 0}
  -> a:lbignum t len ->
  Stack (limb t)
  (requires fun h -> live h a)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_is_zero_mask (as_seq h0 a))

let bn_is_zero_mask #t len b =
  push_frame ();
  let bn_zero = create len (uint #t 0) in
  let res = bn_eq_mask len b bn_zero in
  pop_frame ();
  res


inline_for_extraction noextract
val bn_lt_mask:
    #t:limb_t
  -> len:size_t
  -> a:lbignum t len
  -> b:lbignum t len ->
  Stack (limb t)
  (requires fun h -> live h a /\ live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_lt_mask (as_seq h0 a) (as_seq h0 b))

let bn_lt_mask #t len a b =
  push_frame ();
  let acc = create 1ul (uint #t 0) in

  [@inline_let]
  let refl h i : GTot (limb t) = Lib.Sequence.index (as_seq h acc) 0 in
  [@inline_let]
  let footprint i = loc acc in
  [@inline_let]
  let spec h = S.bn_lt_mask_f (as_seq h a) (as_seq h b) in

  let h0 = ST.get () in
  loop h0 len (S.bn_lt_mask_t t (v len)) refl footprint spec
  (fun i ->
    Loops.unfold_repeat_gen (v len) (S.bn_lt_mask_t t (v len)) (spec h0) (refl h0 0) (v i);
    let beq = eq_mask a.(i) b.(i) in
    let blt = lt_mask a.(i) b.(i) in
    acc.(0ul) <- mask_select beq acc.(0ul) (mask_select blt (ones t SEC) (zeros t SEC))
  );
  let mask = acc.(0ul) in
  pop_frame ();
  mask


inline_for_extraction noextract
val bn_lt_pow2_mask:
    #t:limb_t
  -> len:size_t{0 < v len /\ bits t * v len <= max_size_t}
  -> b:lbignum t len
  -> x:size_t{v x < bits t * v len} ->
  Stack (limb t)
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_lt_pow2_mask (as_seq h0 b) (v x))

let bn_lt_pow2_mask #t len b x =
  push_frame ();
  let b2 = create len (uint #t 0) in
  bn_set_ith_bit len b2 x;
  let res = bn_lt_mask len b b2 in
  pop_frame ();
  res


inline_for_extraction noextract
val bn_gt_pow2_mask:
    #t:limb_t
  -> len:size_t{0 < v len /\ bits t * v len <= max_size_t}
  -> b:lbignum t len
  -> x:size_t{v x < bits t * v len} ->
  Stack (limb t)
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_gt_pow2_mask (as_seq h0 b) (v x))

let bn_gt_pow2_mask #t len b x =
  push_frame ();
  let b2 = create len (uint #t 0) in
  bn_set_ith_bit len b2 x;
  let res = bn_lt_mask len b2 b in
  pop_frame ();
  res
