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
let check_modulus_st (t:limb_t) (nLen:BN.meta_len) =
  n:lbignum t nLen ->
  Stack (limb t)
  (requires fun h -> live h n)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.check_modulus (as_seq h0 n))


inline_for_extraction noextract
val check_modulus:
    #t:limb_t
  -> #nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : BN.bn t nLen)
  -> check_modulus_st t nLen


inline_for_extraction noextract
let precomp_r2_mod_n_st (t:limb_t) (nLen:BN.meta_len) =
    n:lbignum t nLen
  -> res:lbignum t nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h res /\ disjoint n res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.precomp_r2_mod_n (as_seq h0 n))

// Not marking this one as noextract, since it legitimately can execute with
// nLen passed at run-time. It's just a little inefficient. (And it's helpful to
// keep a super-generic bignum implementation for any width.)
inline_for_extraction noextract
val precomp_r2_mod_n:
    #t:limb_t
  -> #nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : BN.bn t nLen)
  -> precomp_r2_mod_n_st t nLen


inline_for_extraction noextract
let new_precomp_r2_mod_n_st (t:limb_t) =
    r:HS.rid
  -> nLen:size_t
  -> n:lbignum t nLen ->
  ST (B.buffer (limb t))
  (requires fun h -> live h n /\ ST.is_eternal_region r)
  (ensures  fun h0 res h1 ->
    B.(modifies loc_none h0 h1) /\
    not (B.g_is_null res) ==> (
      0 < v nLen /\ 128 * v nLen <= max_size_t /\
      1 < bn_v h0 n /\ bn_v h0 n % 2 = 1 /\
      B.len res == nLen /\
      B.(fresh_loc (loc_buffer res) h0 h1) /\
      B.(loc_includes (loc_region_only false r) (loc_buffer res)) /\
      as_seq h1 (res <: lbignum t nLen) == S.precomp_r2_mod_n (as_seq h0 n) /\
      bn_v #t #nLen h1 res == pow2 (2 * bits t * v nLen) % bn_v h0 n))


inline_for_extraction noextract
val new_precomp_r2_mod_n: #t:limb_t -> new_precomp_r2_mod_n_st t


inline_for_extraction noextract
let mont_reduction_st (t:limb_t) (nLen:size_t{0 < v nLen /\ v nLen + v nLen <= max_size_t}) =
    n:lbignum t nLen
  -> mu:limb t
  -> c:lbignum t (nLen +! nLen)
  -> res:lbignum t nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h c /\ live h res /\
    disjoint res n /\ disjoint res c /\ disjoint n c)
  (ensures  fun h0 _ h1 -> modifies (loc res |+| loc c) h0 h1 /\
    as_seq h1 res == S.mont_reduction (as_seq h0 n) mu (as_seq h0 c))

inline_for_extraction noextract
val mont_reduction:
    #t:limb_t
  -> nLen:BN.meta_len
  -> mont_reduction_st t nLen


inline_for_extraction noextract
let to_mont_st (t:limb_t) (nLen:BN.meta_len) =
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
    as_seq h1 aM == S.to_mont (as_seq h0 n) mu (as_seq h0 r2) (as_seq h0 a))

inline_for_extraction noextract
val to_mont:
    #t:limb_t
  -> #nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : BN.bn t nLen)
  -> mr:mont_reduction_st t nLen
  -> to_mont_st t nLen


inline_for_extraction noextract
let from_mont_st (t:limb_t) (nLen:BN.meta_len) =
    n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen
  -> a:lbignum t nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h aM /\
    disjoint aM a /\ disjoint aM n /\ disjoint a n)
  (ensures  fun h0 _ h1 -> modifies (loc a) h0 h1 /\
    as_seq h1 a == S.from_mont (as_seq h0 n) mu (as_seq h0 aM))

// This one just needs a specialized implementation of mont_reduction. No point
// in doing a type class for a single function , so we take it as a parameter.
inline_for_extraction noextract
val from_mont:
    #t:limb_t
  -> #nLen:BN.meta_len
  -> mr:mont_reduction_st t nLen
  -> from_mont_st t nLen


inline_for_extraction noextract
let mont_mul_st (t:limb_t) (nLen:BN.meta_len) =
    n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen
  -> bM:lbignum t nLen
  -> resM:lbignum t nLen ->
  Stack unit
  (requires fun h ->
    live h aM /\ live h bM /\ live h resM /\ live h n /\
    disjoint resM n /\ eq_or_disjoint aM bM /\
    eq_or_disjoint aM resM /\ eq_or_disjoint bM resM)
  (ensures  fun h0 _ h1 -> modifies (loc resM) h0 h1 /\
    as_seq h1 resM == S.mont_mul (as_seq h0 n) mu (as_seq h0 aM) (as_seq h0 bM))

/// This one needs both the type class and a specialized montgomery reduction.
inline_for_extraction noextract
val mont_mul:
    #t:limb_t
  -> #nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : BN.bn t nLen)
  -> mr:mont_reduction_st t nLen
  -> mont_mul_st t nLen


inline_for_extraction noextract
let mont_sqr_st (t:limb_t) (nLen:BN.meta_len) =
    n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen
  -> resM:lbignum t nLen ->
  Stack unit
  (requires fun h ->
    live h aM /\ live h resM /\ live h n /\
    disjoint resM n /\ eq_or_disjoint aM resM)
  (ensures  fun h0 _ h1 -> modifies (loc resM) h0 h1 /\
    as_seq h1 resM == S.mont_sqr (as_seq h0 n) mu (as_seq h0 aM))

/// This one needs both the type class and a specialized montgomery reduction.
inline_for_extraction noextract
val mont_sqr:
    #t:limb_t
  -> #nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : BN.bn t nLen)
  -> mr:mont_reduction_st t nLen
  -> mont_sqr_st t nLen


/// A montgomery implementation specialized for a bignum length.
inline_for_extraction noextract
class mont (t:limb_t) (len: BN.meta_len)  = {
  bn: BN.bn t len;
  check: check_modulus_st t len;
  precomp: precomp_r2_mod_n_st t len;
  reduction: mont_reduction_st t len;
  to: to_mont_st t len;
  from: from_mont_st t len;
  mul: mont_mul_st t len;
  sqr: mont_sqr_st t len;
}

/// Encoding type-class hierarchies via a hook for type class resolution.
inline_for_extraction noextract
instance bn_of_mont (#t:limb_t) (#len:BN.meta_len) (x:mont t len): BN.bn t len = x.bn

// A completely run-time-only instance where the functions above exist in the C code.
inline_for_extraction noextract
val mk_runtime_mont (t:limb_t) (len: BN.meta_len): mont t len
