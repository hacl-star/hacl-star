module Hacl.Impl.PCurves.Scalar

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Constants
open Hacl.Impl.PCurves.Bignum

module S = Spec.PCurves
module SM = Hacl.Spec.PCurves.Montgomery
module BSeq = Lib.ByteSequence
module CC = Hacl.Impl.PCurves.Constants

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

///  Comparison

inline_for_extraction noextract
let bn_is_lt_order_mask_t {| S.curve_params |} {| CC.curve_constants |} {| bn_ops |} =
  f:felem -> Stack uint64
  (requires fun h -> live h f)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (if as_nat h0 f < S.order then v r = ones_v U64 else v r = 0))

inline_for_extraction noextract
val bn_is_lt_order_mask_g {| S.curve_params |} {| CC.curve_constants |} {| bn_ops |}:
    bn_is_lt_order_mask_t

inline_for_extraction noextract
val bn_is_lt_order_and_gt_zero_mask {| S.curve_params |} {| CC.curve_constants |} {| bn_ops |}:
  f:felem -> Stack uint64
  (requires fun h -> live h f)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (if 0 < as_nat h0 f && as_nat h0 f < S.order then v r = ones_v U64 else v r = 0))

inline_for_extraction noextract
let load_qelem_conditional_t {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |} =
  res:felem -> b:lbuffer uint8 (size cp.bytes) -> Stack uint64
  (requires fun h ->
    live h res /\ live h b /\ disjoint res b)
  (ensures fun h0 m h1 -> modifies (loc res) h0 h1 /\
   (let b_nat = BSeq.nat_from_bytes_be (as_seq h0 b) in
    let is_b_valid = 0 < b_nat && b_nat < S.order in
    (v m = ones_v U64 \/ v m = 0) /\ (v m = ones_v U64) = is_b_valid /\
    as_nat h1 res == (if is_b_valid then b_nat else 1)))

inline_for_extraction noextract
val load_qelem_conditional_g {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |}: load_qelem_conditional_t


///  Field Arithmetic

inline_for_extraction noextract
let qmod_short_t {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |} =
  res:felem -> x:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == as_nat h0 x % S.order)

inline_for_extraction noextract
val qmod_short_g {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |}:
    qmod_short_t


inline_for_extraction noextract
let qadd_t {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |} =
  res:felem -> x:felem -> y:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.order /\ as_nat h y < S.order)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == S.qadd (as_nat h0 x) (as_nat h0 y) /\
    qmont_as_nat h1 res == S.qadd (qmont_as_nat h0 x) (qmont_as_nat h0 y))

inline_for_extraction noextract
val qadd_g {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |} :
  qadd_t

inline_for_extraction noextract
let from_qmont_t {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |} =
  res:felem -> x:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res /\
    as_nat h x < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.order /\
    as_nat h1 res == qmont_as_nat h0 x)

inline_for_extraction noextract
val from_qmont_g {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |}:
    from_qmont_t

inline_for_extraction noextract
let qmul_t {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |} =
  res:felem -> x:felem -> y:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.order /\ as_nat h y < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = (as_nat h0 x * as_nat h0 y * SM.qmont_R_inv) % S.order /\
    qmont_as_nat h1 res = S.qmul (qmont_as_nat h0 x) (qmont_as_nat h0 y))

inline_for_extraction noextract
val qmul_g {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |}:
    qmul_t

inline_for_extraction noextract
let qsqr_t {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |} =
  res:felem -> x:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res /\
    as_nat h x < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = (as_nat h0 x * as_nat h0 x * SM.qmont_R_inv) % S.order /\
    qmont_as_nat h1 res = S.qmul (qmont_as_nat h0 x) (qmont_as_nat h0 x))

inline_for_extraction noextract
val qsqr_g {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |}:
  qsqr_t

class order_ops {| S.curve_params |} {| CC.curve_constants |} {| bn:bn_ops |} = {
  bn_is_lt_order_mask: bn_is_lt_order_mask_t;
  load_qelem_conditional: load_qelem_conditional_t;
  qmod_short: qmod_short_t;
  qadd:qadd_t;
  qmul:qmul_t;
  qsqr:qsqr_t;
  from_qmont: from_qmont_t;
}
