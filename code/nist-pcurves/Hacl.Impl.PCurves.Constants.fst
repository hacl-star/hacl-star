module Hacl.Impl.PCurves.Constants

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Bignum

module S = Spec.PCurves
module SM = Hacl.Spec.PCurves.Montgomery

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

[@(strict_on_arguments [0])]
inline_for_extraction
let fmont_as_nat {| S.curve_params |} (h:mem) (a:felem) = SM.from_mont (as_nat h a)

[@(strict_on_arguments [0])]
inline_for_extraction
let qmont_as_nat {| c:S.curve_params |} (h:mem) (a:felem) = SM.from_qmont (as_nat h a)

[@(strict_on_arguments [0])]
inline_for_extraction
class curve_constants {| cp:S.curve_params |} = {
  make_prime : n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == cp.prime);
  make_order: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == S.order);
  make_a_coeff: a:felem -> Stack unit
  (requires fun h -> live h a)
  (ensures fun h0 _ h1 -> modifies (loc a) h0 h1 /\
    as_nat h1 a < S.prime /\
    SM.from_mont (as_nat h1 a) == S.a_coeff);
  make_b_coeff: b:felem -> Stack unit
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_nat h1 b < S.prime /\
    SM.from_mont (as_nat h1 b) == S.b_coeff);
  make_g_x: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n < S.prime /\
    SM.from_mont (as_nat h1 n) == S.basepoint_x);
  make_g_y: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n < S.prime /\
    SM.from_mont (as_nat h1 n) == S.basepoint_y);
  make_fmont_R2: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == SM.fmont_R * SM.fmont_R % S.prime);
  make_fzero: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n < S.prime /\
    fmont_as_nat h1 n == 0);
  make_fone: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n < S.prime /\
    fmont_as_nat h1 n == 1);
  make_qone: f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f < S.order /\
    qmont_as_nat h1 f == 1)
}
  
