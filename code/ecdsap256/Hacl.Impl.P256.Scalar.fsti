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

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

let qmont_as_nat (h:mem) (a:felem) = SM.fromDomain_ (as_nat h a)

///  Create one

val make_qone: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == SM.toDomain_ 1 /\
    qmont_as_nat h1 n == 1)


///  Comparison

val bn_is_lt_order_mask4: f:felem -> Stack uint64
  (requires fun h -> live h f)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (if as_nat h0 f < S.order then v r = ones_v U64 else v r = 0))


val bn_is_lt_order_and_gt_zero_mask4: f:felem -> Stack uint64
  (requires fun h -> live h f)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (if 0 < as_nat h0 f && as_nat h0 f < S.order then v r = ones_v U64 else v r = 0))


///  Field Arithmetic

val qmod_short: x:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == as_nat h0 x % S.order)


val qadd: x:felem -> y:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.order /\ as_nat h y < S.order)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == S.qadd (as_nat h0 x) (as_nat h0 y) /\
    qmont_as_nat h1 res == S.qadd (qmont_as_nat h0 x) (qmont_as_nat h0 y))


val from_qmont: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint a res /\
    as_nat h a < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.order /\
    as_nat h1 res == qmont_as_nat h0 a)


val qmul: a:felem -> b:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    eq_or_disjoint a b /\ eq_or_disjoint a res /\ eq_or_disjoint b res /\
    as_nat h a < S.order /\ as_nat h b < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = (as_nat h0 a * as_nat h0 b * SM.qmont_R_inv) % S.order /\
    qmont_as_nat h1 res = S.qmul (qmont_as_nat h0 a) (qmont_as_nat h0 b))


val qsqr: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint a res /\
    as_nat h a < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = (as_nat h0 a * as_nat h0 a * SM.qmont_R_inv) % S.order /\
    qmont_as_nat h1 res = S.qmul (qmont_as_nat h0 a) (qmont_as_nat h0 a))
