module Hacl.Bignum.GenericField

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module Euclid = FStar.Math.Euclid
module S = Hacl.Spec.Bignum.GenericField
module BE = Hacl.Bignum.Exponentiation
module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

//inline_for_extraction noextract
class bn_mont_ctx = {
  nBits: size_t;
  len: BN.meta_len U64;
  n: lbignum U64 len;
  mu: limb U64;
  r2: lbignum U64 len;
  }


inline_for_extraction noextract
let as_ctx (h:mem) (k:bn_mont_ctx) : GTot (S.bn_mont_ctx U64) = {
  S.nBits = v k.nBits;
  S.len = v k.len;
  S.n = as_seq h k.n;
  S.mu = k.mu;
  S.r2 = as_seq h k.r2;
  }


inline_for_extraction noextract
let bn_mont_ctx_inv (h:mem) (k:bn_mont_ctx) =
  live h k.n /\ live h k.r2 /\ disjoint k.n k.r2 /\
  S.bn_mont_ctx_inv (as_ctx h k)


inline_for_extraction noextract
let bn_field_get_len_st (k:bn_mont_ctx) = unit ->
  Stack (BN.meta_len U64)
  (requires fun h -> bn_mont_ctx_inv h k)
  (ensures  fun h0 r h1 -> h0 == h1 /\
    v r == S.bn_field_get_len (as_ctx h0 k))


inline_for_extraction noextract
val bn_field_get_len: k:bn_mont_ctx -> bn_field_get_len_st k


inline_for_extraction noextract
let bn_field_init_st (len:BN.meta_len U64) =
    r:HS.rid
  -> nBits:size_t
  -> n:lbignum U64 len ->
  ST (bn_mont_ctx)
  (requires fun h ->
    live h n /\ S.bn_mont_ctx_pre (v nBits) (v len) (as_seq h n) /\
    ST.is_eternal_region r)
  (ensures  fun h0 res h1 ->
    B.(modifies loc_none h0 h1) /\
    S.bn_mont_ctx_inv (as_ctx h1 res) /\
    B.(fresh_loc (loc_union (loc_buffer (res.n <: buffer (limb U64))) (loc_buffer (res.r2 <: buffer (limb U64)))) h0 h1) /\
    B.(loc_includes (loc_region_only false r) (loc_union (loc_buffer (res.n <: buffer (limb U64))) (loc_buffer (res.r2 <: buffer (limb U64))))) /\
    as_ctx h1 res == S.bn_field_init (v nBits) (as_seq h0 n))


inline_for_extraction noextract
val bn_field_init: km:BM.mont U64 -> bn_field_init_st km.BM.bn.BN.len


inline_for_extraction noextract
let bn_to_field_st (k:bn_mont_ctx) =
    a:lbignum U64 k.len
  -> aM:lbignum U64 k.len ->
  Stack unit
  (requires fun h ->
    bn_mont_ctx_inv h k /\ live h a /\ live h aM /\ disjoint a aM /\
    disjoint a k.r2 /\ disjoint a k.n /\
    disjoint aM k.r2 /\ disjoint aM k.n /\
    bn_v h a < bn_v h k.n)
  (ensures  fun h0 _ h1 -> modifies (loc aM) h0 h1 /\
    bn_v h1 aM < bn_v h0 k.n /\
    as_seq h1 aM == S.bn_to_field (as_ctx h0 k) (as_seq h0 a))


inline_for_extraction noextract
val bn_to_field: km:BM.mont U64 -> k:bn_mont_ctx{k.len == km.BM.bn.BN.len} -> bn_to_field_st k


inline_for_extraction noextract
let bn_from_field_st (k:bn_mont_ctx) =
    aM:lbignum U64 k.len
  -> a:lbignum U64 k.len ->
  Stack unit
  (requires fun h ->
    bn_mont_ctx_inv h k /\ live h a /\ live h aM /\ disjoint a aM /\
    disjoint a k.r2 /\ disjoint a k.n /\
    disjoint aM k.r2 /\ disjoint aM k.n /\
    bn_v h aM < bn_v h k.n)
  (ensures  fun h0 _ h1 -> modifies (loc a) h0 h1 /\
    bn_v h1 a < bn_v h0 k.n /\
    as_seq h1 a == S.bn_from_field (as_ctx h0 k) (as_seq h0 aM))


inline_for_extraction noextract
val bn_from_field: km:BM.mont U64 -> k:bn_mont_ctx{k.len == km.BM.bn.BN.len} -> bn_from_field_st k


inline_for_extraction noextract
let bn_field_add_st (k:bn_mont_ctx) =
    aM:lbignum U64 k.len
  -> bM:lbignum U64 k.len
  -> cM:lbignum U64 k.len ->
  Stack unit
  (requires fun h ->
    bn_mont_ctx_inv h k /\ live h aM /\ live h bM /\ live h cM /\
    eq_or_disjoint aM bM /\ eq_or_disjoint aM cM /\ eq_or_disjoint bM cM /\
    disjoint k.n aM /\ disjoint k.n bM /\ disjoint k.n cM /\
    bn_v h aM < bn_v h k.n /\ bn_v h bM < bn_v h k.n)
  (ensures  fun h0 _ h1 -> modifies (loc cM) h0 h1 /\
    bn_v h1 cM < bn_v h0 k.n /\
    as_seq h1 cM == S.bn_field_add (as_ctx h0 k) (as_seq h0 aM) (as_seq h0 bM))


inline_for_extraction noextract
val bn_field_add: km:BM.mont U64 -> k:bn_mont_ctx{k.len == km.BM.bn.BN.len} -> bn_field_add_st k


inline_for_extraction noextract
let bn_field_sub_st (k:bn_mont_ctx) =
    aM:lbignum U64 k.len
  -> bM:lbignum U64 k.len
  -> cM:lbignum U64 k.len ->
  Stack unit
  (requires fun h ->
    bn_mont_ctx_inv h k /\ live h aM /\ live h bM /\ live h cM /\
    eq_or_disjoint aM bM /\ eq_or_disjoint aM cM /\ eq_or_disjoint bM cM /\
    disjoint k.n aM /\ disjoint k.n bM /\ disjoint k.n cM /\
    bn_v h aM < bn_v h k.n /\ bn_v h bM < bn_v h k.n)
  (ensures  fun h0 _ h1 -> modifies (loc cM) h0 h1 /\
    bn_v h1 cM < bn_v h0 k.n /\
    as_seq h1 cM == S.bn_field_sub (as_ctx h0 k) (as_seq h0 aM) (as_seq h0 bM))


inline_for_extraction noextract
val bn_field_sub: km:BM.mont U64 -> k:bn_mont_ctx{k.len == km.BM.bn.BN.len} -> bn_field_sub_st k


inline_for_extraction noextract
let bn_field_mul_st (k:bn_mont_ctx) =
    aM:lbignum U64 k.len
  -> bM:lbignum U64 k.len
  -> cM:lbignum U64 k.len ->
  Stack unit
  (requires fun h ->
    bn_mont_ctx_inv h k /\ live h aM /\ live h bM /\ live h cM /\
    eq_or_disjoint aM bM /\ eq_or_disjoint aM cM /\ eq_or_disjoint bM cM /\
    disjoint cM k.n /\
    bn_v h aM < bn_v h k.n /\ bn_v h bM < bn_v h k.n)
  (ensures  fun h0 _ h1 -> modifies (loc cM) h0 h1 /\
    bn_v h1 cM < bn_v h0 k.n /\
    as_seq h1 cM == S.bn_field_mul (as_ctx h0 k) (as_seq h0 aM) (as_seq h0 bM))


inline_for_extraction noextract
val bn_field_mul: km:BM.mont U64 -> k:bn_mont_ctx{k.len == km.BM.bn.BN.len} -> bn_field_mul_st k


inline_for_extraction noextract
let bn_field_sqr_st (k:bn_mont_ctx) =
    aM:lbignum U64 k.len
  -> cM:lbignum U64 k.len ->
  Stack unit
  (requires fun h ->
    bn_mont_ctx_inv h k /\ live h aM /\ live h cM /\
    eq_or_disjoint aM cM /\ disjoint cM k.n /\
    bn_v h aM < bn_v h k.n)
  (ensures  fun h0 _ h1 -> modifies (loc cM) h0 h1 /\
    bn_v h1 cM < bn_v h0 k.n /\
    as_seq h1 cM == S.bn_field_sqr (as_ctx h0 k) (as_seq h0 aM))


inline_for_extraction noextract
val bn_field_sqr: km:BM.mont U64 -> k:bn_mont_ctx{k.len == km.BM.bn.BN.len} -> bn_field_sqr_st k


inline_for_extraction noextract
let bn_field_one_st (k:bn_mont_ctx) = oneM:lbignum U64 k.len ->
  Stack unit
  (requires fun h ->
    bn_mont_ctx_inv h k /\ live h oneM /\
    disjoint k.n oneM /\ disjoint k.r2 oneM)
  (ensures  fun h0 _ h1 -> modifies (loc oneM) h0 h1 /\
    bn_v h1 oneM < bn_v h0 k.n /\
    as_seq h1 oneM == S.bn_field_one (as_ctx h0 k))


inline_for_extraction noextract
val bn_field_one: km:BM.mont U64 -> k:bn_mont_ctx{k.len == km.BM.bn.BN.len} -> bn_field_one_st k


inline_for_extraction noextract
let bn_field_inv_st (k:bn_mont_ctx) =
    aM:lbignum U64 k.len
  -> aInvM:lbignum U64 k.len ->
  Stack unit
  (requires fun h ->
    bn_mont_ctx_inv h k /\ live h aM /\ live h aInvM /\
    disjoint aM aInvM /\ disjoint k.n aM /\
    disjoint k.n aInvM /\ disjoint k.r2 aInvM /\
    0 < bn_v h aM /\ bn_v h aM < bn_v h k.n)
  (ensures  fun h0 _ h1 -> modifies (loc aInvM) h0 h1 /\
    bn_v h1 aInvM < bn_v h0 k.n /\
    as_seq h1 aInvM == S.bn_field_inv (as_ctx h0 k) (as_seq h0 aM))


inline_for_extraction noextract
val bn_field_inv: km:BM.mont U64 -> k:bn_mont_ctx{k.len == km.BM.bn.BN.len} -> bn_field_inv_st k
