module Hacl.Bignum.MontArithmetic

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
module S = Hacl.Spec.Bignum.MontArithmetic
module BE = Hacl.Bignum.Exponentiation
module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// from Jonathan:
// type limb_t = U32 | U64
// let f (x: t) = match x with | U32 -> lbuffer UInt32.t | U64 -> lbuffer UInt64.t
// type ctx' (x: t) (a: Type0 { a == f x }) = {
//   r2: a;
// }
// let ctx (x: t) = ctx' x (f x)

inline_for_extraction noextract
let lb (t:limb_t) =
  match t with
  | U32 -> buffer uint32
  | U64 -> buffer uint64

inline_for_extraction noextract
let ll (t:limb_t) =
  match t with
  | U32 -> uint32
  | U64 -> uint64

inline_for_extraction// noextract
noeq
type bn_mont_ctx' (t:limb_t) (a:Type0{a == lb t}) (b:Type0{b == ll t}) = {
  len: BN.meta_len t;
  n: x:a{length #MUT #(limb t) x == v len};
  mu: b;
  r2: x:a{length #MUT #(limb t) x == v len};
  }

inline_for_extraction noextract
let bn_mont_ctx (t:limb_t) = bn_mont_ctx' t (lb t) (ll t)

let bn_mont_ctx_u32 = bn_mont_ctx' U32 (lb U32) (ll U32)
let bn_mont_ctx_u64 = bn_mont_ctx' U64 (lb U64) (ll U64)


inline_for_extraction noextract
let as_ctx (#t:limb_t) (h:mem) (k:bn_mont_ctx t) : GTot (S.bn_mont_ctx t) = {
  S.len = v k.len;
  S.n = as_seq h (k.n <: lbignum t k.len);
  S.mu = k.mu;
  S.r2 = as_seq h (k.r2 <: lbignum t k.len);
  }


inline_for_extraction noextract
let bn_mont_ctx_inv (#t:limb_t) (h:mem) (k:bn_mont_ctx t) =
  live h (k.n <: lbignum t k.len) /\ live h (k.r2 <: lbignum t k.len) /\
  disjoint (k.n <: lbignum t k.len) (k.r2 <: lbignum t k.len) /\
  S.bn_mont_ctx_inv (as_ctx h k)


inline_for_extraction noextract
let bn_field_get_len_st (#t:limb_t) (k:bn_mont_ctx t) = unit ->
  Stack (BN.meta_len t)
  (requires fun h -> bn_mont_ctx_inv h k)
  (ensures  fun h0 r h1 -> h0 == h1 /\
    v r == S.bn_field_get_len (as_ctx h0 k))


inline_for_extraction noextract
val bn_field_get_len: #t:limb_t -> k:bn_mont_ctx t -> bn_field_get_len_st k


inline_for_extraction noextract
let bn_field_check_modulus_st (t:limb_t) (len:BN.meta_len t) = n:lbignum t len ->
  Stack bool
  (requires fun h -> live h n)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_field_check_modulus (as_seq h0 n))


inline_for_extraction noextract
val bn_field_check_modulus: #t:limb_t -> len:BN.meta_len t -> bn_field_check_modulus_st t len


inline_for_extraction noextract
let bn_field_init_st (t:limb_t) (len:BN.meta_len t) =
    r:HS.rid
  -> n:lbignum t len ->
  ST (bn_mont_ctx t)
  (requires fun h ->
    live h n /\ ST.is_eternal_region r /\

    S.bn_mont_ctx_pre (as_seq h n))
  (ensures  fun h0 res h1 ->
    B.(modifies loc_none h0 h1) /\
    S.bn_mont_ctx_inv (as_ctx h1 res) /\
    B.(fresh_loc (loc_union (loc_buffer (res.n <: buffer (limb t))) (loc_buffer (res.r2 <: buffer (limb t)))) h0 h1) /\
    B.(loc_includes (loc_region_only false r) (loc_union (loc_buffer (res.n <: buffer (limb t))) (loc_buffer (res.r2 <: buffer (limb t))))) /\
    as_ctx h1 res == S.bn_field_init (as_seq h0 n))


inline_for_extraction noextract
val bn_field_init: #t:limb_t -> km:BM.mont t -> bn_field_init_st t km.BM.bn.BN.len


inline_for_extraction noextract
let bn_to_field_st (#t:limb_t) (k:bn_mont_ctx t) =
    a:lbignum t k.len
  -> aM:lbignum t k.len ->
  Stack unit
  (requires fun h ->
    bn_mont_ctx_inv h k /\

    live h a /\ live h aM /\ disjoint a aM /\
    disjoint a (k.r2 <: lbignum t k.len) /\ disjoint a (k.n <: lbignum t k.len) /\
    disjoint aM (k.r2 <: lbignum t k.len) /\ disjoint aM (k.n <: lbignum t k.len))
  (ensures  fun h0 _ h1 -> modifies (loc aM) h0 h1 /\
    bn_v h1 aM < bn_v #t #k.len h0 k.n /\
    as_seq h1 aM == S.bn_to_field (as_ctx h0 k) (as_seq h0 a))


inline_for_extraction noextract
val bn_to_field: #t:limb_t -> km:BM.mont t -> k:bn_mont_ctx t{k.len == km.BM.bn.BN.len} -> bn_to_field_st k


inline_for_extraction noextract
let bn_from_field_st (#t:limb_t) (k:bn_mont_ctx t) =
    aM:lbignum t k.len
  -> a:lbignum t k.len ->
  Stack unit
  (requires fun h ->
    bn_mont_ctx_inv h k /\ bn_v h aM < bn_v #t #k.len h k.n /\

    live h a /\ live h aM /\ disjoint a aM /\
    disjoint a (k.r2 <: lbignum t k.len) /\ disjoint a (k.n <: lbignum t k.len) /\
    disjoint aM (k.r2 <: lbignum t k.len) /\ disjoint aM (k.n <: lbignum t k.len))
  (ensures  fun h0 _ h1 -> modifies (loc a) h0 h1 /\
    bn_v h1 a < bn_v #t #k.len h0 k.n /\
    as_seq h1 a == S.bn_from_field (as_ctx h0 k) (as_seq h0 aM))


inline_for_extraction noextract
val bn_from_field: #t:limb_t -> km:BM.mont t -> k:bn_mont_ctx t{k.len == km.BM.bn.BN.len} -> bn_from_field_st k


inline_for_extraction noextract
let bn_field_add_st (#t:limb_t) (k:bn_mont_ctx t) =
    aM:lbignum t k.len
  -> bM:lbignum t k.len
  -> cM:lbignum t k.len ->
  Stack unit
  (requires fun h ->
    bn_mont_ctx_inv h k /\
    bn_v h aM < bn_v #t #k.len h k.n /\
    bn_v h bM < bn_v #t #k.len h k.n /\

    live h aM /\ live h bM /\ live h cM /\
    eq_or_disjoint aM bM /\ eq_or_disjoint aM cM /\ eq_or_disjoint bM cM /\
    disjoint (k.n <: lbignum t k.len) aM /\
    disjoint (k.n <: lbignum t k.len) bM /\
    disjoint (k.n <: lbignum t k.len) cM)
  (ensures  fun h0 _ h1 -> modifies (loc cM) h0 h1 /\
    bn_v h1 cM < bn_v #t #k.len h0 k.n /\
    as_seq h1 cM == S.bn_field_add (as_ctx h0 k) (as_seq h0 aM) (as_seq h0 bM))


inline_for_extraction noextract
val bn_field_add: #t:limb_t -> km:BM.mont t -> k:bn_mont_ctx t{k.len == km.BM.bn.BN.len} -> bn_field_add_st k


inline_for_extraction noextract
let bn_field_sub_st (#t:limb_t) (k:bn_mont_ctx t) =
    aM:lbignum t k.len
  -> bM:lbignum t k.len
  -> cM:lbignum t k.len ->
  Stack unit
  (requires fun h ->
    bn_mont_ctx_inv h k /\
    bn_v h aM < bn_v #t #k.len h k.n /\
    bn_v h bM < bn_v #t #k.len h k.n /\

    live h aM /\ live h bM /\ live h cM /\
    eq_or_disjoint aM bM /\ eq_or_disjoint aM cM /\ eq_or_disjoint bM cM /\
    disjoint (k.n <: lbignum t k.len) aM /\
    disjoint (k.n <: lbignum t k.len) bM /\
    disjoint (k.n <: lbignum t k.len) cM)
  (ensures  fun h0 _ h1 -> modifies (loc cM) h0 h1 /\
    bn_v h1 cM < bn_v #t #k.len h0 k.n /\
    as_seq h1 cM == S.bn_field_sub (as_ctx h0 k) (as_seq h0 aM) (as_seq h0 bM))


inline_for_extraction noextract
val bn_field_sub: #t:limb_t -> km:BM.mont t -> k:bn_mont_ctx t{k.len == km.BM.bn.BN.len} -> bn_field_sub_st k


inline_for_extraction noextract
let bn_field_mul_st (#t:limb_t) (k:bn_mont_ctx t) =
    aM:lbignum t k.len
  -> bM:lbignum t k.len
  -> cM:lbignum t k.len ->
  Stack unit
  (requires fun h ->
    bn_mont_ctx_inv h k /\
    bn_v h aM < bn_v #t #k.len h k.n /\
    bn_v h bM < bn_v #t #k.len h k.n /\

    live h aM /\ live h bM /\ live h cM /\
    eq_or_disjoint aM bM /\ eq_or_disjoint aM cM /\ eq_or_disjoint bM cM /\
    disjoint cM (k.n <: lbignum t k.len))
  (ensures  fun h0 _ h1 -> modifies (loc cM) h0 h1 /\
    bn_v h1 cM < bn_v #t #k.len h0 k.n /\
    as_seq h1 cM == S.bn_field_mul (as_ctx h0 k) (as_seq h0 aM) (as_seq h0 bM))


inline_for_extraction noextract
val bn_field_mul: #t:limb_t -> km:BM.mont t -> k:bn_mont_ctx t{k.len == km.BM.bn.BN.len} -> bn_field_mul_st k


inline_for_extraction noextract
let bn_field_sqr_st (#t:limb_t) (k:bn_mont_ctx t) =
    aM:lbignum t k.len
  -> cM:lbignum t k.len ->
  Stack unit
  (requires fun h ->
    bn_mont_ctx_inv h k /\
    bn_v h aM < bn_v #t #k.len h k.n /\

    live h aM /\ live h cM /\
    eq_or_disjoint aM cM /\ disjoint cM (k.n <: lbignum t k.len))
  (ensures  fun h0 _ h1 -> modifies (loc cM) h0 h1 /\
    bn_v h1 cM < bn_v #t #k.len h0 k.n /\
    as_seq h1 cM == S.bn_field_sqr (as_ctx h0 k) (as_seq h0 aM))


inline_for_extraction noextract
val bn_field_sqr: #t:limb_t -> km:BM.mont t -> k:bn_mont_ctx t{k.len == km.BM.bn.BN.len} -> bn_field_sqr_st k


inline_for_extraction noextract
let bn_field_one_st (#t:limb_t) (k:bn_mont_ctx t) = oneM:lbignum t k.len ->
  Stack unit
  (requires fun h ->
    bn_mont_ctx_inv h k /\

    live h oneM /\
    disjoint (k.n <: lbignum t k.len) oneM /\
    disjoint (k.r2 <: lbignum t k.len) oneM)
  (ensures  fun h0 _ h1 -> modifies (loc oneM) h0 h1 /\
    bn_v h1 oneM < bn_v #t #k.len h0 k.n /\
    as_seq h1 oneM == S.bn_field_one (as_ctx h0 k))


inline_for_extraction noextract
val bn_field_one: #t:limb_t -> km:BM.mont t -> k:bn_mont_ctx t{k.len == km.BM.bn.BN.len} -> bn_field_one_st k


inline_for_extraction noextract
let bn_field_exp_consttime_st (#t:limb_t) (k:bn_mont_ctx t) =
    aM:lbignum t k.len
  -> bBits:size_t{0 < v bBits}
  -> b:lbignum t (blocks bBits (size (bits t)))
  -> resM:lbignum t k.len ->
  Stack unit
  (requires fun h ->
    bn_mont_ctx_inv h k /\
    bn_v h aM < bn_v #t #k.len h k.n /\
    0 < bn_v h b /\ bn_v h b < pow2 (v bBits) /\

    live h aM /\ live h b /\ live h resM /\
    disjoint resM aM /\ disjoint resM b /\
    disjoint aM b /\
    disjoint (k.n <: lbignum t k.len) resM /\
    disjoint (k.n <: lbignum t k.len) aM /\
    disjoint (k.r2 <: lbignum t k.len) resM /\
    disjoint (k.r2 <: lbignum t k.len) aM)
  (ensures  fun h0 _ h1 -> modifies (loc resM) h0 h1 /\
    bn_v h1 resM < bn_v #t #k.len h0 k.n /\
    as_seq h1 resM == S.bn_field_exp_consttime (as_ctx h0 k) (as_seq h0 aM) (v bBits) (as_seq h0 b))


inline_for_extraction noextract
val bn_field_exp_consttime:
    #t:limb_t
  -> km:BM.mont t
  -> k:bn_mont_ctx t{k.len == km.BM.bn.BN.len} ->
  bn_field_exp_consttime_st k


inline_for_extraction noextract
let bn_field_exp_vartime_st (#t:limb_t) (k:bn_mont_ctx t) =
    aM:lbignum t k.len
  -> bBits:size_t{0 < v bBits}
  -> b:lbignum t (blocks bBits (size (bits t)))
  -> resM:lbignum t k.len ->
  Stack unit
  (requires fun h ->
    bn_mont_ctx_inv h k /\
    bn_v h aM < bn_v #t #k.len h k.n /\
    0 < bn_v h b /\ bn_v h b < pow2 (v bBits) /\

    live h aM /\ live h b /\ live h resM /\
    disjoint resM aM /\ disjoint resM b /\
    disjoint aM b /\
    disjoint (k.n <: lbignum t k.len) resM /\
    disjoint (k.n <: lbignum t k.len) aM /\
    disjoint (k.r2 <: lbignum t k.len) resM /\
    disjoint (k.r2 <: lbignum t k.len) aM)
  (ensures  fun h0 _ h1 -> modifies (loc resM) h0 h1 /\
    bn_v h1 resM < bn_v #t #k.len h0 k.n /\
    as_seq h1 resM == S.bn_field_exp_vartime (as_ctx h0 k) (as_seq h0 aM) (v bBits) (as_seq h0 b))


inline_for_extraction noextract
val bn_field_exp_vartime:
    #t:limb_t
  -> km:BM.mont t
  -> k:bn_mont_ctx t{k.len == km.BM.bn.BN.len} ->
  bn_field_exp_vartime_st k



inline_for_extraction noextract
let bn_field_inv_st (#t:limb_t) (k:bn_mont_ctx t) =
    aM:lbignum t k.len
  -> aInvM:lbignum t k.len ->
  Stack unit
  (requires fun h ->
    bn_mont_ctx_inv h k /\
    Euclid.is_prime (bn_v #t #k.len h k.n) /\
    0 < bn_v h aM /\ bn_v h aM < bn_v #t #k.len h k.n /\

    live h aM /\ live h aInvM /\
    disjoint aM aInvM /\
    disjoint (k.n <: lbignum t k.len) aM /\
    disjoint (k.n <: lbignum t k.len) aInvM /\
    disjoint (k.r2 <: lbignum t k.len) aM /\
    disjoint (k.r2 <: lbignum t k.len) aInvM)
  (ensures  fun h0 _ h1 -> modifies (loc aInvM) h0 h1 /\
    bn_v h1 aInvM < bn_v #t #k.len h0 k.n /\
    as_seq h1 aInvM == S.bn_field_inv (as_ctx h0 k) (as_seq h0 aM))


inline_for_extraction noextract
val bn_field_inv: #t:limb_t -> km:BM.mont t -> k:bn_mont_ctx t{k.len == km.BM.bn.BN.len} -> bn_field_inv_st k
