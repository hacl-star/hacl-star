module Hacl.Bignum.Montgomery

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions
module S = Hacl.Spec.Bignum.Montgomery
module BN = Hacl.Bignum

module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

include Hacl.Bignum.ModInvLimb

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"


inline_for_extraction noextract
let bn_check_modulus_st (t:limb_t) (len:BN.meta_len t) =
  n:lbignum t len ->
  Stack (limb t)
  (requires fun h -> live h n)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_check_modulus (as_seq h0 n))


inline_for_extraction noextract
val bn_check_modulus: #t:limb_t -> #len:BN.meta_len t -> bn_check_modulus_st t len


inline_for_extraction noextract
let bn_precomp_r2_mod_n_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h res /\ disjoint n res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_precomp_r2_mod_n (as_seq h0 n))


inline_for_extraction noextract
val bn_precomp_r2_mod_n: #t:limb_t -> #len:BN.meta_len t -> k:BN.bn t len -> bn_precomp_r2_mod_n_st t len


inline_for_extraction noextract
let new_bn_precomp_r2_mod_n_st (t:limb_t) =
    r:HS.rid
  -> nLen:size_t
  -> n:lbignum t nLen ->
  ST (B.buffer (limb t))
  (requires fun h -> live h n /\ ST.is_eternal_region r)
  (ensures  fun h0 res h1 ->
    B.(modifies loc_none h0 h1) /\
    not (B.g_is_null res) ==> (
      0 < v nLen /\ 2 * bits t * v nLen <= max_size_t /\
      1 < bn_v h0 n /\ bn_v h0 n % 2 = 1 /\
      B.len res == nLen /\
      B.(fresh_loc (loc_buffer res) h0 h1) /\
      B.(loc_includes (loc_region_only false r) (loc_buffer res)) /\
      as_seq h1 (res <: lbignum t nLen) == S.bn_precomp_r2_mod_n (as_seq h0 n) /\
      bn_v #t #nLen h1 res == pow2 (2 * bits t * v nLen) % bn_v h0 n))


inline_for_extraction noextract
val new_bn_precomp_r2_mod_n: #t:limb_t -> new_bn_precomp_r2_mod_n_st t


inline_for_extraction noextract
let bn_mont_reduction_st (t:limb_t) (len:size_t{0 < v len /\ v len + v len <= max_size_t}) =
    n:lbignum t len
  -> mu:limb t
  -> c:lbignum t (len +! len)
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h c /\ live h res /\
    disjoint res n /\ disjoint res c /\ disjoint n c)
  (ensures  fun h0 _ h1 -> modifies (loc res |+| loc c) h0 h1 /\
    as_seq h1 res == S.bn_mont_reduction (as_seq h0 n) mu (as_seq h0 c))


inline_for_extraction noextract
val bn_mont_reduction: #t:limb_t -> #len:BN.meta_len t -> k:BN.bn t len -> bn_mont_reduction_st t len


inline_for_extraction noextract
let bn_to_mont_st (t:limb_t) (nLen:BN.meta_len t) =
    n:lbignum t nLen
  -> mu:limb t
  -> r2:lbignum t nLen
  -> a:lbignum t nLen
  -> aM:lbignum t nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h r2 /\ live h a /\ live h aM /\
    disjoint a r2 /\ disjoint a n /\ disjoint a aM /\
    disjoint n r2 /\ disjoint n aM /\ disjoint r2 aM)
  (ensures  fun h0 _ h1 -> modifies (loc aM) h0 h1 /\
    as_seq h1 aM == S.bn_to_mont (as_seq h0 n) mu (as_seq h0 r2) (as_seq h0 a))


inline_for_extraction noextract
val bn_to_mont: #t:limb_t -> #len:BN.meta_len t -> k:BN.bn t len -> mr:bn_mont_reduction_st t len -> bn_to_mont_st t len


inline_for_extraction noextract
let bn_from_mont_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> mu:limb t
  -> aM:lbignum t len
  -> a:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h aM /\
    disjoint aM a /\ disjoint aM n /\ disjoint a n)
  (ensures  fun h0 _ h1 -> modifies (loc a) h0 h1 /\
    as_seq h1 a == S.bn_from_mont (as_seq h0 n) mu (as_seq h0 aM))


// This one just needs a specialized implementation of mont_reduction. No point
// in doing a type class for a single function , so we take it as a parameter.
inline_for_extraction noextract
val bn_from_mont: #t:limb_t -> #len:BN.meta_len t -> k:BN.bn t len -> mr:bn_mont_reduction_st t len -> bn_from_mont_st t len


inline_for_extraction noextract
let bn_mont_mul_st (t:limb_t) (len:BN.meta_len t) =
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
    as_seq h1 resM == S.bn_mont_mul (as_seq h0 n) mu (as_seq h0 aM) (as_seq h0 bM))


/// This one needs both the type class and a specialized montgomery reduction.
inline_for_extraction noextract
val bn_mont_mul: #t:limb_t -> #len:BN.meta_len t -> k:BN.bn t len -> mr:bn_mont_reduction_st t len -> bn_mont_mul_st t len


inline_for_extraction noextract
let bn_mont_sqr_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> mu:limb t
  -> aM:lbignum t len
  -> resM:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h aM /\ live h resM /\ live h n /\
    disjoint resM n /\ eq_or_disjoint aM resM)
  (ensures  fun h0 _ h1 -> modifies (loc resM) h0 h1 /\
    as_seq h1 resM == S.bn_mont_sqr (as_seq h0 n) mu (as_seq h0 aM))


/// This one needs both the type class and a specialized montgomery reduction.
inline_for_extraction noextract
val bn_mont_sqr: #t:limb_t -> #len:BN.meta_len t -> k:BN.bn t len -> mr:bn_mont_reduction_st t len -> bn_mont_sqr_st t len


inline_for_extraction noextract
class mont (t:limb_t) (len:BN.meta_len t) = {
  bn: BN.bn t len;
  mont_check: bn_check_modulus_st t len;
  precomp: bn_precomp_r2_mod_n_st t len;
  reduction: bn_mont_reduction_st t len;
  to: bn_to_mont_st t len;
  from: bn_from_mont_st t len;
  mul: bn_mont_mul_st t len;
  sqr: bn_mont_sqr_st t len;
}

/// Encoding type-class hierarchies via a hook for type class resolution.
inline_for_extraction noextract
instance bn_of_mont (t:limb_t) (len:BN.meta_len t) (x:mont t len) : BN.bn t len = x.bn

// A completely run-time-only instance where the functions above exist in the C code.
inline_for_extraction noextract
val mk_runtime_mont: t:limb_t -> len:BN.meta_len t -> mont t len
