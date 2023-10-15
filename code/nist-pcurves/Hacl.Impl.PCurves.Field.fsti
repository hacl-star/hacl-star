module Hacl.Impl.PCurves.Field

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Bignum

module S = Spec.PCurves
module SM = Hacl.Spec.PCurves.Montgomery
module CC = Hacl.Impl.PCurves.Constants

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Comparison


inline_for_extraction noextract
let bn_is_lt_prime_mask_t  {| S.curve_params |} {| bn:bn_ops |} {| CC.curve_constants |} =
    f:felem -> Stack uint64
  (requires fun h -> live h f)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (if as_nat h0 f < S.prime then v r = ones_v U64 else v r = 0))

[@(strict_on_arguments [0;1;2])]
inline_for_extraction noextract
val bn_is_lt_prime_mask_g {| S.curve_params |}  {| bn:bn_ops |} {| CC.curve_constants |}: bn_is_lt_prime_mask_t

[@(strict_on_arguments [0;1])]
inline_for_extraction noextract
val feq_mask {| S.curve_params |} {| bn:bn_ops |}:
  a:felem -> b:felem -> Stack uint64
  (requires fun h ->
    live h a /\ live h b /\ eq_or_disjoint a b /\
    as_nat h a < S.prime /\ as_nat h b < S.prime)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (if CC.fmont_as_nat h0 a = CC.fmont_as_nat h0 b then v r == ones_v U64 else v r = 0))


///  Field Arithmetic

inline_for_extraction noextract
let fadd_t {| S.curve_params |}  {| bn:bn_ops |} {| CC.curve_constants |} =
  res:felem -> x:felem -> y:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.prime /\ as_nat h y < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == S.fadd (as_nat h0 x) (as_nat h0 y) /\
    CC.fmont_as_nat h1 res == S.fadd (CC.fmont_as_nat h0 x) (CC.fmont_as_nat h0 y))

[@(strict_on_arguments [0;1;2])]
inline_for_extraction noextract
val fadd_g {| S.curve_params |}  {| bn:bn_ops |} {| CC.curve_constants |}:
  fadd_t


inline_for_extraction noextract
let fsub_t {| S.curve_params |}  {| bn:bn_ops |} {| CC.curve_constants |} =
  res:felem -> x:felem -> y:felem -> Stack unit
  (requires fun h ->
    live h res /\ live h x /\ live h y /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.prime /\ as_nat h y < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == S.fsub (as_nat h0 x) (as_nat h0 y) /\
    CC.fmont_as_nat h1 res == S.fsub (CC.fmont_as_nat h0 x) (CC.fmont_as_nat h0 y))

[@(strict_on_arguments [0;1;2])]
inline_for_extraction noextract
val fsub_g {| S.curve_params |}  {| bn:bn_ops |} {| CC.curve_constants |}:
  fsub_t

inline_for_extraction noextract
let fmul_t {| S.curve_params |}  {| bn:bn_ops |} {| CC.curve_constants |} =
  res:felem -> x:felem -> y:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.prime /\ as_nat h y < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = (as_nat h0 x * as_nat h0 y * SM.fmont_R_inv) % S.prime /\
    CC.fmont_as_nat h1 res = S.fmul (CC.fmont_as_nat h0 x) (CC.fmont_as_nat h0 y))

[@(strict_on_arguments [0;1;2])]
inline_for_extraction noextract
val fmul_g {| S.curve_params |}  {| bn:bn_ops |} {| CC.curve_constants |}:
  fmul_t

inline_for_extraction noextract
let fsqr_t {| S.curve_params |}  {| bn:bn_ops |} {| CC.curve_constants |} =
  res:felem -> x:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res /\
    as_nat h x < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = (as_nat h0 x * as_nat h0 x * SM.fmont_R_inv) % S.prime /\
    CC.fmont_as_nat h1 res = S.fmul (CC.fmont_as_nat h0 x) (CC.fmont_as_nat h0 x))

[@(strict_on_arguments [0;1;2])]
inline_for_extraction noextract
val fsqr_g {| S.curve_params |}  {| bn:bn_ops |} {| CC.curve_constants |}:
    fsqr_t

inline_for_extraction noextract
let from_mont_t {| S.curve_params |}  {| bn:bn_ops |} {| CC.curve_constants |} =
  res:felem -> x:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ as_nat h x < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = (as_nat h0 x * SM.fmont_R_inv) % S.prime /\
    as_nat h1 res = CC.fmont_as_nat h0 x)

[@(strict_on_arguments [0;1;2])]
inline_for_extraction noextract
val from_mont_g {| S.curve_params |}  {| bn:bn_ops |} {| CC.curve_constants |}:
  from_mont_t

inline_for_extraction noextract
let to_mont_t {| S.curve_params |}  {| bn:bn_ops |} {| CC.curve_constants |} =
  res:felem -> f:felem -> Stack unit
  (requires fun h ->
    live h f /\ live h res /\ eq_or_disjoint f res /\
    as_nat h f < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = SM.to_mont (as_nat h0 f))

[@(strict_on_arguments [0;1;2])]
inline_for_extraction noextract
val to_mont_g {| S.curve_params |}  {| bn:bn_ops |} {| CC.curve_constants |}:
    to_mont_t

///  Special cases of the above functions


[@(strict_on_arguments [0;1;2])]
inline_for_extraction
class field_ops {| S.curve_params |} {| bn:bn_ops |} {| CC.curve_constants |} = {
  bn_is_lt_prime_mask: bn_is_lt_prime_mask_t;
  fadd:fadd_t;
  fsub:fsub_t;
  fmul:fmul_t;
  fsqr:fsqr_t;
  from_mont: from_mont_t;
  to_mont: to_mont_t;
}

inline_for_extraction noextract
let fnegate_conditional_vartime_t {| S.curve_params |}  {| bn:bn_ops |} {| CC.curve_constants |} {| field_ops |} =
  f:felem -> is_negate:bool -> Stack unit
  (requires fun h -> live h f /\ as_nat h f < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\ as_nat h1 f < S.prime /\
    as_nat h1 f == (if is_negate then (S.prime - as_nat h0 f) % S.prime else as_nat h0 f))

[@(strict_on_arguments [0;1;2])]
inline_for_extraction noextract
val fnegate_conditional_vartime {| S.curve_params |}  {| bn:bn_ops |} {| CC.curve_constants |} {| field_ops |} : fnegate_conditional_vartime_t

[@(strict_on_arguments [0;1;2])]
inline_for_extraction noextract
val fdouble {| S.curve_params |}  {| bn:bn_ops |} {| CC.curve_constants |} {| field_ops |}:
  res:felem -> x:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res /\
    as_nat h x < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == (2 * as_nat h0 x) % S.prime /\
    CC.fmont_as_nat h1 res == (2 * CC.fmont_as_nat h0 x) % S.prime)

[@(strict_on_arguments [0;1;2])]
inline_for_extraction noextract
val fmul_by_b_coeff {| S.curve_params |}  {| bn:bn_ops |} {| CC.curve_constants |} {| field_ops |}:
  res:felem -> x:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res /\
    as_nat h x < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime /\
    CC.fmont_as_nat h1 res =
      S.fmul S.b_coeff (CC.fmont_as_nat h0 x))


[@(strict_on_arguments [0;1;2])]
inline_for_extraction noextract
val fcube {| S.curve_params |}  {| bn:bn_ops |} {| CC.curve_constants |} {| field_ops |}:
  res:felem -> x:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ disjoint x res /\
    as_nat h x < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime /\
    CC.fmont_as_nat h1 res =
      S.fmul (S.fmul (CC.fmont_as_nat h0 x) (CC.fmont_as_nat h0 x)) (CC.fmont_as_nat h0 x))


