module Hacl.Bignum.Exponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module S = Hacl.Spec.Bignum.Exponentiation


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val bn_mod_exp:
    modBits:size_t{v modBits > 0}
  -> nLen:size_t{0 < v nLen /\ v nLen = v (blocks modBits 64ul) /\ 128 * (v nLen + 1) <= max_size_t}
  -> n:lbignum nLen
  -> r2:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_t{v bBits > 0}
  -> b:lbignum (blocks bBits 64ul)
  -> res:lbignum nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\ live h r2 /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint res r2 /\
    disjoint a r2 /\ disjoint a n /\ disjoint n r2)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mod_exp (v modBits) (v nLen) (as_seq h0 n) (as_seq h0 r2) (as_seq h0 a) (v bBits) (as_seq h0 b))
