module Hacl.Impl.P256.Scalar

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum

module S = Spec.P256
module SM = Hacl.Spec.P256.Montgomery
module BSeq = Lib.ByteSequence

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

let qmont_as_nat (h:mem) (a:felem) = SM.from_qmont (as_nat h a)

///  Create one

val make_qone: f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f < S.order /\
    qmont_as_nat h1 f == 1)


///  Comparison

val bn_is_lt_order_mask4: f:felem -> Stack uint64
  (requires fun h -> live h f)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (if as_nat h0 f < S.order then v r = ones_v U64 else v r = 0))


val bn_is_lt_order_and_gt_zero_mask4: f:felem -> Stack uint64
  (requires fun h -> live h f)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (if 0 < as_nat h0 f && as_nat h0 f < S.order then v r = ones_v U64 else v r = 0))


inline_for_extraction noextract
val load_qelem_conditional: res:felem -> b:lbuffer uint8 32ul -> Stack uint64
  (requires fun h ->
    live h res /\ live h b /\ disjoint res b)
  (ensures fun h0 m h1 -> modifies (loc res) h0 h1 /\
   (let b_nat = BSeq.nat_from_bytes_be (as_seq h0 b) in
    let is_b_valid = 0 < b_nat && b_nat < S.order in
    (v m = ones_v U64 \/ v m = 0) /\ (v m = ones_v U64) = is_b_valid /\
    as_nat h1 res == (if is_b_valid then b_nat else 1)))


///  Field Arithmetic

val qmod_short: res:felem -> x:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == as_nat h0 x % S.order)


val qadd: res:felem -> x:felem -> y:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.order /\ as_nat h y < S.order)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == S.qadd (as_nat h0 x) (as_nat h0 y) /\
    qmont_as_nat h1 res == S.qadd (qmont_as_nat h0 x) (qmont_as_nat h0 y))


val from_qmont: res:felem -> x:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res /\
    as_nat h x < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.order /\
    as_nat h1 res == qmont_as_nat h0 x)


val qmul: res:felem -> x:felem -> y:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.order /\ as_nat h y < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = (as_nat h0 x * as_nat h0 y * SM.qmont_R_inv) % S.order /\
    qmont_as_nat h1 res = S.qmul (qmont_as_nat h0 x) (qmont_as_nat h0 y))


val qsqr: res:felem -> x:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res /\
    as_nat h x < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = (as_nat h0 x * as_nat h0 x * SM.qmont_R_inv) % S.order /\
    qmont_as_nat h1 res = S.qmul (qmont_as_nat h0 x) (qmont_as_nat h0 x))
