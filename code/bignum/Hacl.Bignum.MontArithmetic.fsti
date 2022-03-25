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

val _align_fsti : unit

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

inline_for_extraction
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
let pbn_mont_ctx (t:limb_t) = B.pointer (bn_mont_ctx t)

inline_for_extraction noextract
let pbn_mont_ctx_u32 = B.pointer bn_mont_ctx_u32
inline_for_extraction noextract
let pbn_mont_ctx_u64 = B.pointer bn_mont_ctx_u64

inline_for_extraction noextract
let as_ctx (#t:limb_t) (h:mem) (k:bn_mont_ctx t) : GTot (S.bn_mont_ctx t) = {
  S.len = v k.len;
  S.n = as_seq h (k.n <: lbignum t k.len);
  S.mu = k.mu;
  S.r2 = as_seq h (k.r2 <: lbignum t k.len);
  }

inline_for_extraction noextract
let bn_mont_ctx_inv (#t:limb_t) (h:mem) (k:bn_mont_ctx t) =
  let n : buffer (limb t) = k.n in
  let r2 : buffer (limb t) = k.r2 in
  live h n /\ live h r2 /\ disjoint n r2 /\
  S.bn_mont_ctx_inv (as_ctx h k)


inline_for_extraction noextract
let bn_v_n (#t:limb_t) (h:mem) (k:pbn_mont_ctx t) =
  let k1 = B.deref h k in
  let n : lbignum t k1.len = k1.n in
  bn_v h n

inline_for_extraction noextract
let freeable_s (#t:limb_t) (h:mem) (k:bn_mont_ctx t) =
  let n : buffer (limb t) = k.n in
  let r2 : buffer (limb t) = k.r2 in
  B.freeable n /\ B.freeable r2

inline_for_extraction noextract
let freeable (#t:limb_t) (h:mem) (k:pbn_mont_ctx t) =
  B.freeable k /\ freeable_s h (B.deref h k)

inline_for_extraction noextract
let footprint_s (#t:limb_t) (h:mem) (k:bn_mont_ctx t) =
  let n : buffer (limb t) = k.n in
  let r2 : buffer (limb t) = k.r2 in
  B.(loc_union (loc_addr_of_buffer n) (loc_addr_of_buffer r2))

inline_for_extraction noextract
let footprint (#t:limb_t) (h:mem) (k:pbn_mont_ctx t) =
  B.(loc_union (loc_addr_of_buffer k) (footprint_s h (B.deref h k)))

inline_for_extraction noextract
let as_pctx (#t:limb_t) (h:mem) (k:pbn_mont_ctx t) : GTot (S.bn_mont_ctx t) =
  as_ctx h (B.deref h k)

inline_for_extraction noextract
let pbn_mont_ctx_inv (#t:limb_t) (h:mem) (k:pbn_mont_ctx t) =
  B.live h k /\
  B.(loc_disjoint (loc_addr_of_buffer k) (footprint_s h (B.deref h k))) /\
  bn_mont_ctx_inv h (B.deref h k)


inline_for_extraction noextract
let bn_field_get_len_st (t:limb_t) = k:pbn_mont_ctx t ->
  Stack (BN.meta_len t)
  (requires fun h -> pbn_mont_ctx_inv h k)
  (ensures  fun h0 r h1 -> h0 == h1 /\
    r == (B.deref h0 k).len /\
    v r == S.bn_field_get_len (as_pctx h0 k))


inline_for_extraction noextract
val bn_field_get_len: #t:limb_t -> bn_field_get_len_st t


inline_for_extraction noextract
let bn_field_check_modulus_st (t:limb_t) (len:BN.meta_len t) = n:lbignum t len ->
  Stack bool
  (requires fun h -> live h n)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_field_check_modulus (as_seq h0 n))


inline_for_extraction noextract
val bn_field_check_modulus: #t:limb_t -> km:BM.mont t -> bn_field_check_modulus_st t km.BM.bn.BN.len


inline_for_extraction noextract
let bn_field_init_st (t:limb_t) (len:BN.meta_len t) =
    r:HS.rid
  -> n:lbignum t len ->
  ST (pbn_mont_ctx t)
  (requires fun h ->
    S.bn_mont_ctx_pre (as_seq h n) /\

    live h n /\ ST.is_eternal_region r)
  (ensures  fun h0 res h1 ->
    B.(modifies loc_none h0 h1) /\
    B.(fresh_loc (footprint h1 res) h0 h1) /\
    B.(loc_includes (loc_region_only true r) (footprint h1 res)) /\
    freeable h1 res /\
    (B.deref h1 res).len == len /\ bn_v_n h1 res == bn_v h0 n /\
    S.bn_mont_ctx_inv (as_pctx h1 res) /\
    as_pctx h1 res == S.bn_field_init (as_seq h0 n))


inline_for_extraction noextract
val bn_field_init:
    #t:limb_t
  -> len:BN.meta_len t
  -> precomp_r2:BM.bn_precomp_r2_mod_n_st t len ->
  bn_field_init_st t len


inline_for_extraction noextract
let bn_field_free_st (t:limb_t) = k:pbn_mont_ctx t ->
  ST unit
  (requires fun h ->
    freeable h k /\
    pbn_mont_ctx_inv h k)
  (ensures  fun h0 _ h1 ->
    B.(modifies (footprint h0 k) h0 h1))


inline_for_extraction noextract
val bn_field_free: #t:limb_t -> bn_field_free_st t


inline_for_extraction noextract
let bn_to_field_st (t:limb_t) (len:BN.meta_len t) =
    k:pbn_mont_ctx t
  -> a:lbignum t len
  -> aM:lbignum t len ->
  Stack unit
  (requires fun h ->
    (B.deref h k).len == len /\
    pbn_mont_ctx_inv h k /\

    live h a /\ live h aM /\ disjoint a aM /\
    B.(loc_disjoint (footprint h k) (loc_buffer (a <: buffer (limb t)))) /\
    B.(loc_disjoint (footprint h k) (loc_buffer (aM <: buffer (limb t)))))
  (ensures  fun h0 _ h1 -> modifies (loc aM) h0 h1 /\
    bn_v h1 aM < bn_v_n h0 k /\
    as_seq h1 aM == S.bn_to_field (as_pctx h0 k) (as_seq h0 a))


inline_for_extraction noextract
val bn_to_field: #t:limb_t -> km:BM.mont t -> bn_to_field_st t km.BM.bn.BN.len


inline_for_extraction noextract
let bn_from_field_st (t:limb_t) (len:BN.meta_len t) =
    k:pbn_mont_ctx t
  -> aM:lbignum t len
  -> a:lbignum t len ->
  Stack unit
  (requires fun h ->
    (B.deref h k).len == len /\
    pbn_mont_ctx_inv h k /\ bn_v h aM < bn_v_n h k /\

    live h a /\ live h aM /\ disjoint a aM /\
    B.(loc_disjoint (footprint h k) (loc_buffer (a <: buffer (limb t)))) /\
    B.(loc_disjoint (footprint h k) (loc_buffer (aM <: buffer (limb t)))))
  (ensures  fun h0 _ h1 -> modifies (loc a) h0 h1 /\
    bn_v h1 a < bn_v_n h0 k /\
    as_seq h1 a == S.bn_from_field (as_pctx h0 k) (as_seq h0 aM))


inline_for_extraction noextract
val bn_from_field: #t:limb_t -> km:BM.mont t -> bn_from_field_st t km.BM.bn.BN.len


inline_for_extraction noextract
let bn_field_add_st (t:limb_t) (len:BN.meta_len t) =
    k:pbn_mont_ctx t
  -> aM:lbignum t len
  -> bM:lbignum t len
  -> cM:lbignum t len ->
  Stack unit
  (requires fun h ->
    (B.deref h k).len == len /\
    pbn_mont_ctx_inv h k /\
    bn_v h aM < bn_v_n h k /\
    bn_v h bM < bn_v_n h k /\

    live h aM /\ live h bM /\ live h cM /\
    eq_or_disjoint aM bM /\ eq_or_disjoint aM cM /\ eq_or_disjoint bM cM /\
    B.(loc_disjoint (footprint h k) (loc_buffer (aM <: buffer (limb t)))) /\
    B.(loc_disjoint (footprint h k) (loc_buffer (bM <: buffer (limb t)))) /\
    B.(loc_disjoint (footprint h k) (loc_buffer (cM <: buffer (limb t)))))
  (ensures  fun h0 _ h1 -> modifies (loc cM) h0 h1 /\
    bn_v h1 cM < bn_v_n h0 k /\
    as_seq h1 cM == S.bn_field_add (as_pctx h0 k) (as_seq h0 aM) (as_seq h0 bM))


inline_for_extraction noextract
val bn_field_add: #t:limb_t -> km:BM.mont t -> bn_field_add_st t km.BM.bn.BN.len


inline_for_extraction noextract
let bn_field_sub_st (t:limb_t) (len:BN.meta_len t) =
    k:pbn_mont_ctx t
  -> aM:lbignum t len
  -> bM:lbignum t len
  -> cM:lbignum t len ->
  Stack unit
  (requires fun h ->
    (B.deref h k).len == len /\
    pbn_mont_ctx_inv h k /\
    bn_v h aM < bn_v_n h k /\
    bn_v h bM < bn_v_n h k /\

    live h aM /\ live h bM /\ live h cM /\
    eq_or_disjoint aM bM /\ eq_or_disjoint aM cM /\ eq_or_disjoint bM cM /\
    B.(loc_disjoint (footprint h k) (loc_buffer (aM <: buffer (limb t)))) /\
    B.(loc_disjoint (footprint h k) (loc_buffer (bM <: buffer (limb t)))) /\
    B.(loc_disjoint (footprint h k) (loc_buffer (cM <: buffer (limb t)))))
  (ensures  fun h0 _ h1 -> modifies (loc cM) h0 h1 /\
    bn_v h1 cM < bn_v_n h0 k /\
    as_seq h1 cM == S.bn_field_sub (as_pctx h0 k) (as_seq h0 aM) (as_seq h0 bM))


inline_for_extraction noextract
val bn_field_sub: #t:limb_t -> km:BM.mont t -> bn_field_sub_st t km.BM.bn.BN.len


inline_for_extraction noextract
let bn_field_mul_st (t:limb_t) (len:BN.meta_len t) =
    k:pbn_mont_ctx t
  -> aM:lbignum t len
  -> bM:lbignum t len
  -> cM:lbignum t len ->
  Stack unit
  (requires fun h ->
    (B.deref h k).len == len /\
    pbn_mont_ctx_inv h k /\
    bn_v h aM < bn_v_n h k /\
    bn_v h bM < bn_v_n h k /\

    live h aM /\ live h bM /\ live h cM /\
    eq_or_disjoint aM bM /\ eq_or_disjoint aM cM /\ eq_or_disjoint bM cM /\
    B.(loc_disjoint (footprint h k) (loc_buffer (aM <: buffer (limb t)))) /\
    B.(loc_disjoint (footprint h k) (loc_buffer (bM <: buffer (limb t)))) /\
    B.(loc_disjoint (footprint h k) (loc_buffer (cM <: buffer (limb t)))))
  (ensures  fun h0 _ h1 -> modifies (loc cM) h0 h1 /\
    bn_v h1 cM < bn_v_n h0 k /\
    as_seq h1 cM == S.bn_field_mul (as_pctx h0 k) (as_seq h0 aM) (as_seq h0 bM))


inline_for_extraction noextract
val bn_field_mul: #t:limb_t -> km:BM.mont t -> bn_field_mul_st t km.BM.bn.BN.len


inline_for_extraction noextract
let bn_field_sqr_st (t:limb_t) (len:BN.meta_len t) =
    k:pbn_mont_ctx t
  -> aM:lbignum t len
  -> cM:lbignum t len ->
  Stack unit
  (requires fun h ->
    (B.deref h k).len == len /\
    pbn_mont_ctx_inv h k /\
    bn_v h aM < bn_v_n h k /\

    live h aM /\ live h cM /\ eq_or_disjoint aM cM /\
    B.(loc_disjoint (footprint h k) (loc_buffer (aM <: buffer (limb t)))) /\
    B.(loc_disjoint (footprint h k) (loc_buffer (cM <: buffer (limb t)))))
  (ensures  fun h0 _ h1 -> modifies (loc cM) h0 h1 /\
    bn_v h1 cM < bn_v_n h0 k /\
    as_seq h1 cM == S.bn_field_sqr (as_pctx h0 k) (as_seq h0 aM))


inline_for_extraction noextract
val bn_field_sqr: #t:limb_t -> km:BM.mont t -> bn_field_sqr_st t km.BM.bn.BN.len


inline_for_extraction noextract
let bn_field_one_st (t:limb_t) (len:BN.meta_len t) =
    k:pbn_mont_ctx t
  -> oneM:lbignum t len ->
  Stack unit
  (requires fun h ->
    (B.deref h k).len == len /\
    pbn_mont_ctx_inv h k /\

    live h oneM /\
    B.(loc_disjoint (footprint h k) (loc_buffer (oneM <: buffer (limb t)))))
  (ensures  fun h0 _ h1 -> modifies (loc oneM) h0 h1 /\
    bn_v h1 oneM < bn_v_n h0 k /\
    as_seq h1 oneM == S.bn_field_one (as_pctx h0 k))


inline_for_extraction noextract
val bn_field_one: #t:limb_t -> km:BM.mont t -> bn_field_one_st t km.BM.bn.BN.len


inline_for_extraction noextract
let bn_field_exp_consttime_st (t:limb_t) (len:BN.meta_len t) =
    k:pbn_mont_ctx t
  -> aM:lbignum t len
  -> bBits:size_t
  -> b:lbignum t (blocks0 bBits (size (bits t)))
  -> resM:lbignum t len ->
  Stack unit
  (requires fun h ->
    (B.deref h k).len == len /\
    pbn_mont_ctx_inv h k /\
    bn_v h aM < bn_v_n h k /\
    bn_v h b < pow2 (v bBits) /\

    live h aM /\ live h b /\ live h resM /\
    disjoint resM aM /\ disjoint resM b /\ disjoint aM b /\
    B.(loc_disjoint (footprint h k) (loc_buffer (aM <: buffer (limb t)))) /\
    B.(loc_disjoint (footprint h k) (loc_buffer (resM <: buffer (limb t)))))
  (ensures  fun h0 _ h1 -> modifies (loc resM) h0 h1 /\
    bn_v h1 resM < bn_v_n h0 k /\
    as_seq h1 resM == S.bn_field_exp_consttime (as_pctx h0 k) (as_seq h0 aM) (v bBits) (as_seq h0 b))


inline_for_extraction noextract
val bn_field_exp_consttime: #t:limb_t -> km:BM.mont t -> bn_field_exp_consttime_st t km.BM.bn.BN.len


inline_for_extraction noextract
let bn_field_exp_vartime_st (t:limb_t) (len:BN.meta_len t) =
    k:pbn_mont_ctx t
  -> aM:lbignum t len
  -> bBits:size_t
  -> b:lbignum t (blocks0 bBits (size (bits t)))
  -> resM:lbignum t len ->
  Stack unit
  (requires fun h ->
    (B.deref h k).len == len /\
    pbn_mont_ctx_inv h k /\
    bn_v h aM < bn_v_n h k /\
    bn_v h b < pow2 (v bBits) /\

    live h aM /\ live h b /\ live h resM /\
    disjoint resM aM /\ disjoint resM b /\ disjoint aM b /\
    B.(loc_disjoint (footprint h k) (loc_buffer (aM <: buffer (limb t)))) /\
    B.(loc_disjoint (footprint h k) (loc_buffer (resM <: buffer (limb t)))))
  (ensures  fun h0 _ h1 -> modifies (loc resM) h0 h1 /\
    bn_v h1 resM < bn_v_n h0 k /\
    as_seq h1 resM == S.bn_field_exp_vartime (as_pctx h0 k) (as_seq h0 aM) (v bBits) (as_seq h0 b))


inline_for_extraction noextract
val bn_field_exp_vartime: #t:limb_t -> km:BM.mont t -> bn_field_exp_vartime_st t km.BM.bn.BN.len


inline_for_extraction noextract
let bn_field_inv_st (t:limb_t) (len:BN.meta_len t) =
    k:pbn_mont_ctx t
  -> aM:lbignum t len
  -> aInvM:lbignum t len ->
  Stack unit
  (requires fun h ->
    (B.deref h k).len == len /\
    pbn_mont_ctx_inv h k /\
    Euclid.is_prime (bn_v_n h k) /\
    0 < bn_v h aM /\ bn_v h aM < bn_v_n h k /\

    live h aM /\ live h aInvM /\ disjoint aM aInvM /\
    B.(loc_disjoint (footprint h k) (loc_buffer (aM <: buffer (limb t)))) /\
    B.(loc_disjoint (footprint h k) (loc_buffer (aInvM <: buffer (limb t)))))
  (ensures  fun h0 _ h1 -> modifies (loc aInvM) h0 h1 /\
    bn_v h1 aInvM < bn_v_n h0 k /\
    as_seq h1 aInvM == S.bn_field_inv (as_pctx h0 k) (as_seq h0 aM))


inline_for_extraction noextract
val bn_field_inv:
    #t:limb_t
  -> len:Ghost.erased _
  -> bn_field_exp_vartime:bn_field_exp_vartime_st t len ->
  bn_field_inv_st t len
