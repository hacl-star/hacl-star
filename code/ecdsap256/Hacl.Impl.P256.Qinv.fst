module Hacl.Impl.P256.Qinv

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Scalar
open Hacl.Impl.P256.Constants

module LSeq = Lib.Sequence

module M = Lib.NatMod
module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation

module S = Spec.P256
module SI = Hacl.Spec.P256.Qinv

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

unfold
let linv_ctx (a:LSeq.lseq uint64 0) : Type0 = True

unfold
let linv (a:LSeq.lseq uint64 4) : Type0 =
  let open Lib.Sequence in
  felem_seq_as_nat a < S.order

unfold
let refl (a:LSeq.lseq uint64 4{linv a}) : GTot S.qelem =
  fromDomain_ (felem_seq_as_nat a)


inline_for_extraction noextract
let mk_to_p256_order_comm_monoid : BE.to_comm_monoid U64 4ul 0ul = {
  BE.a_spec = S.qelem;
  BE.comm_monoid = SI.nat_mod_comm_monoid;
  BE.linv_ctx = linv_ctx;
  BE.linv = linv;
  BE.refl = refl;
}


val make_qone: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == toDomain_ 1 /\
    qmont_as_nat h1 n == 1)

[@CInline]
let make_qone n =
  [@inline_let] let n0 = u64 0xc46353d039cdaaf in
  [@inline_let] let n1 = u64 0x4319055258e8617b in
  [@inline_let] let n2 = u64 0x0 in
  [@inline_let] let n3 = u64 0xffffffff in
  assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 == toDomain_ 1);
  assert_norm (fromDomain_ (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192) == 1);
  bn_make_u64_4 n0 n1 n2 n3 n


inline_for_extraction noextract
val one_mod : BE.lone_st U64 4ul 0ul mk_to_p256_order_comm_monoid
let one_mod ctx one = make_qone one


inline_for_extraction noextract
val mul_mod : BE.lmul_st U64 4ul 0ul mk_to_p256_order_comm_monoid
let mul_mod ctx x y xy = qmul x y xy


inline_for_extraction noextract
val sqr_mod : BE.lsqr_st U64 4ul 0ul mk_to_p256_order_comm_monoid
let sqr_mod ctx x xx = qmul x x xx


inline_for_extraction noextract
let mk_p256_order_concrete_ops : BE.concrete_ops U64 4ul 0ul = {
  BE.to = mk_to_p256_order_comm_monoid;
  BE.lone = one_mod;
  BE.lmul = mul_mod;
  BE.lsqr = sqr_mod;
}


val fsquare_times (out a:felem) (b:size_t) : Stack unit
  (requires fun h ->
    live h out /\ live h a /\ disjoint out a /\
    as_nat h a < S.order)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    qmont_as_nat h1 out == SI.qsquare_times (qmont_as_nat h0 a) (v b))

[@CInline]
let fsquare_times out a b =
  let h0 = ST.get () in
  BE.lexp_pow2 4ul 0ul mk_p256_order_concrete_ops (null uint64) a b out;
  let h1 = ST.get () in
  assert (qmont_as_nat h1 out == LE.exp_pow2 SI.nat_mod_comm_monoid (qmont_as_nat h0 a) (v b));

  SE.exp_pow2_lemma SI.mk_nat_mod_concrete_ops (qmont_as_nat h0 a) (v b);
  assert (SI.qsquare_times (qmont_as_nat h0 a) (v b) ==
    LE.exp_pow2 SI.nat_mod_comm_monoid (qmont_as_nat h0 a) (v b))


// TODO: rm
val qexp_vartime (out a b:felem) : Stack unit
  (requires fun h ->
    live h out /\ live h a /\ live h b /\
    disjoint out a /\ disjoint out b /\
    as_nat h a < S.order)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out < S.order /\
    qmont_as_nat h1 out == M.pow_mod #S.order (qmont_as_nat h0 a) (as_nat h0 b))

[@CInline]
let qexp_vartime out a b =
  let h0 = ST.get () in
  assert_norm (pow2 5 = 32);
  as_nat_bound h0 b;
  bignum_bn_v_is_as_nat h0 b;
  BE.lexp_fw_vartime 4ul 0ul
    mk_p256_order_concrete_ops 5ul (null uint64) a 4ul 256ul b out;
  let h1 = ST.get () in
  SE.exp_fw_lemma SI.mk_nat_mod_concrete_ops (qmont_as_nat h0 a) 256 (as_nat h0 b) 5;
  LE.exp_fw_lemma SI.nat_mod_comm_monoid (qmont_as_nat h0 a) 256 (as_nat h0 b) 5;
  assert (qmont_as_nat h1 out == LE.pow SI.nat_mod_comm_monoid (qmont_as_nat h0 a) (as_nat h0 b));
  M.lemma_pow_nat_mod_is_pow #S.order (qmont_as_nat h0 a) (as_nat h0 b);
  assert (qmont_as_nat h1 out == M.pow (qmont_as_nat h0 a) (as_nat h0 b) % S.order);
  M.lemma_pow_mod #S.order (qmont_as_nat h0 a) (as_nat h0 b)


//--------------------------------
// TODO: use an addition chain from Hacl.Spec.P256.Qinv
inline_for_extraction noextract
val make_order_minus_2: b:felem -> Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_nat h1 b == S.order - 2)

let make_order_minus_2 b =
  // 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254f
  [@inline_let] let b0 = u64 0xf3b9cac2fc63254f in
  [@inline_let] let b1 = u64 0xbce6faada7179e84 in
  [@inline_let] let b2 = u64 0xffffffffffffffff in
  [@inline_let] let b3 = u64 0xffffffff00000000 in
  assert_norm (v b0 + v b1 * pow2 64 + v b2 * pow2 128 + v b3 * pow2 192 = S.order - 2);
  bn_make_u64_4 b0 b1 b2 b3 b


[@CInline]
let qinv res r =
  push_frame ();
  let b = create_felem () in
  let tmp = create_felem () in
  copy tmp r;
  make_order_minus_2 b;
  qexp_vartime res tmp b;
  pop_frame ()

//--------------------------

[@CInline]
let multPowerPartial s a b res =
  let h0 = ST.get() in
  push_frame ();
  let buffFromDB = create (size 4) (u64 0) in
  fromDomainImpl b buffFromDB;
  fromDomainImpl buffFromDB buffFromDB;
  qmul a buffFromDB res;
  let h1 = ST.get () in
  assume (as_nat h1 res = (S.pow (as_nat h0 s) (S.order - 2) * (as_nat h0 b)) % S.order);
  pop_frame ()
