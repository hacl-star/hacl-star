module Hacl.Bignum.AlmostMontgomery

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST
module S = Hacl.Spec.Bignum.AlmostMontgomery
module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Almost Montgomery Multiplication

inline_for_extraction noextract
let bn_almost_mont_reduction_st (t:limb_t) (len:size_t{0 < v len /\ v len + v len <= max_size_t}) =
    n:lbignum t len
  -> mu:limb t
  -> c:lbignum t (len +! len)
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h c /\ live h res /\
    disjoint res n /\ disjoint res c /\ disjoint n c)
  (ensures  fun h0 _ h1 -> modifies (loc res |+| loc c) h0 h1 /\
    as_seq h1 res == S.bn_almost_mont_reduction (as_seq h0 n) mu (as_seq h0 c))


inline_for_extraction noextract
val bn_almost_mont_reduction: #t:limb_t -> k:BN.bn t -> bn_almost_mont_reduction_st t k.BN.len


inline_for_extraction noextract
let bn_almost_mont_mul_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> mu:limb t
  -> aM:lbignum t len
  -> bM:lbignum t len
  -> resM:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h aM /\ live h bM /\ live h resM /\ live h n /\
    disjoint resM n /\ eq_or_disjoint aM bM /\
    eq_or_disjoint aM resM /\ eq_or_disjoint bM resM)
  (ensures  fun h0 _ h1 -> modifies (loc resM) h0 h1 /\
    as_seq h1 resM == S.bn_almost_mont_mul (as_seq h0 n) mu (as_seq h0 aM) (as_seq h0 bM))


inline_for_extraction noextract
val bn_almost_mont_mul:
    #t:limb_t
  -> k:BN.bn t
  -> mr:bn_almost_mont_reduction_st t k.BN.len ->
  bn_almost_mont_mul_st t k.BN.len


inline_for_extraction noextract
let bn_almost_mont_sqr_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> mu:limb t
  -> aM:lbignum t len
  -> resM:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h aM /\ live h resM /\ live h n /\
    disjoint resM n /\ eq_or_disjoint aM resM)
  (ensures  fun h0 _ h1 -> modifies (loc resM) h0 h1 /\
    as_seq h1 resM == S.bn_almost_mont_sqr (as_seq h0 n) mu (as_seq h0 aM))


inline_for_extraction noextract
val bn_almost_mont_sqr:
    #t:limb_t
  -> k:BN.bn t
  -> mr:bn_almost_mont_reduction_st t k.BN.len ->
  bn_almost_mont_sqr_st t k.BN.len


inline_for_extraction noextract
class almost_mont (t:limb_t) = {
  bn: BN.bn t;
  mont_check: BM.bn_check_modulus_st t bn.BN.len;
  precomp: BM.bn_precomp_r2_mod_n_st t bn.BN.len;
  reduction: bn_almost_mont_reduction_st t bn.BN.len;
  to: BM.bn_to_mont_st t bn.BN.len;
  from: BM.bn_from_mont_st t bn.BN.len;
  mul: bn_almost_mont_mul_st t bn.BN.len;
  sqr: bn_almost_mont_sqr_st t bn.BN.len;
}


inline_for_extraction noextract
val mk_runtime_almost_mont: #t:limb_t -> len:BN.meta_len t -> almost_mont t

val mk_runtime_almost_mont_len_lemma: #t:limb_t -> len:BN.meta_len t ->
  Lemma ((mk_runtime_almost_mont #t len).bn.BN.len == len) [SMTPat (mk_runtime_almost_mont #t len)]
