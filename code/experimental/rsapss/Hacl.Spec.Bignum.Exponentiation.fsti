module Hacl.Spec.Bignum.Exponentiation

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"


val bn_mod_exp:
    modBits:size_pos
  -> nLen:size_pos{nLen = (blocks modBits 64) /\ 128 * (nLen + 1) <= max_size_t}
  -> n:lbignum nLen
  -> r2:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_pos
  -> b:lbignum (blocks bBits 64) ->
  lbignum nLen


val bn_mod_exp_lemma:
    modBits:size_pos
  -> nLen:size_pos{nLen = (blocks modBits 64) /\ 128 * (nLen + 1) <= max_size_t}
  -> n:lbignum nLen
  -> r2:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_pos
  -> b:lbignum (blocks bBits 64) -> Lemma
  (requires
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    0 < bn_v b /\ bn_v b < pow2 bBits /\ bn_v a < bn_v n /\
    bn_v r2 == pow2 (128 * (nLen + 1)) % bn_v n)
  (ensures
    bn_v (bn_mod_exp modBits nLen n r2 a bBits b) == Spec.RSAPSS.fpow #(bn_v n) (bn_v a) (bn_v b))
