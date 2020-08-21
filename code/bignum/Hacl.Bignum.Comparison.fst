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
    len:size_t{v len > 0}
  -> a:lbignum len ->
  Stack uint64
  (requires fun h -> live h a)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_is_odd #(v len) (as_seq h0 a))

let bn_is_odd len a = a.(0ul) &. u64 1


inline_for_extraction noextract
val bn_eq_mask:
    len:size_t
  -> a:lbignum len
  -> b:lbignum len ->
  Stack uint64
  (requires fun h -> live h a /\ live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_eq_mask #(v len) (as_seq h0 a) (as_seq h0 b))

let bn_eq_mask len a b =
  push_frame ();
  let mask = create 1ul (ones U64 SEC) in
  let mask = Lib.ByteBuffer.buf_eq_mask a b len mask in
  pop_frame ();
  mask


inline_for_extraction noextract
val bn_is_zero_mask:
    len:size_t{v len > 0}
  -> a:lbignum len ->
  Stack uint64
  (requires fun h -> live h a)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_is_zero_mask #(v len) (as_seq h0 a))

let bn_is_zero_mask len b =
  push_frame ();
  let bn_zero = create len (u64 0) in
  let res = bn_eq_mask len b bn_zero in
  pop_frame ();
  res


inline_for_extraction noextract
val bn_lt_mask:
    len:size_t
  -> a:lbignum len
  -> b:lbignum len ->
  Stack uint64
  (requires fun h -> live h a /\ live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    v r == v (S.bn_lt_mask (as_seq h0 a) (as_seq h0 b)))

let bn_lt_mask len a b =
  push_frame ();
  let acc = create 1ul (u64 0) in

  [@inline_let]
  let refl h i : GTot uint64 = Lib.Sequence.index (as_seq h acc) 0 in
  [@inline_let]
  let footprint i = loc acc in
  [@inline_let]
  let spec h = S.bn_lt_mask_f (as_seq h a) (as_seq h b) in

  let h0 = ST.get () in
  loop h0 len (S.bn_lt_mask_t (v len)) refl footprint spec
  (fun i ->
    Loops.unfold_repeat_gen (v len) (S.bn_lt_mask_t (v len)) (spec h0) (refl h0 0) (v i);
    let beq = eq_mask a.(i) b.(i) in
    let blt = lt_mask a.(i) b.(i) in
    acc.(0ul) <- mask_select beq acc.(0ul) (mask_select blt (ones U64 SEC) (zeros U64 SEC))
  );
  let mask = acc.(0ul) in
  pop_frame ();
  mask


inline_for_extraction noextract
val bn_lt_pow2_mask:
    len:size_t{0 < v len /\ 64 * v len <= max_size_t}
  -> b:lbignum len
  -> x:size_t{v x < 64 * v len} ->
  Stack uint64
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_lt_pow2_mask #(v len) (as_seq h0 b) (v x))

let bn_lt_pow2_mask len b x =
  push_frame ();
  let b2 = create len (u64 0) in
  bn_set_ith_bit len b2 x;
  let res = bn_lt_mask len b b2 in
  pop_frame ();
  res


inline_for_extraction noextract
val bn_gt_pow2_mask:
    len:size_t{0 < v len /\ 64 * v len <= max_size_t}
  -> b:lbignum len
  -> x:size_t{v x < 64 * v len} ->
  Stack uint64
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_gt_pow2_mask #(v len) (as_seq h0 b) (v x))

let bn_gt_pow2_mask len b x =
  push_frame ();
  let b2 = create len (u64 0) in
  bn_set_ith_bit len b2 x;
  let res = bn_lt_mask len b2 b in
  pop_frame ();
  res
