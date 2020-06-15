module Hacl.Bignum.Exponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module S = Hacl.Spec.Bignum.Exponentiation

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let bn_mod_exp_st (modBits:size_t{v modBits > 0})
  (nLen:size_t{0 < v nLen /\ v nLen = v (blocks modBits 64ul) /\ 128 * (v nLen + 1) <= max_size_t})
=
    n:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_t{v bBits > 0}
  -> b:lbignum (blocks bBits 64ul)
  -> res:lbignum nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint n a)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mod_exp (v modBits) (v nLen) (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b))

// This version is fully run-time.
val bn_mod_exp: modBits:_ -> nLen:_ -> bn_mod_exp_st modBits nLen
