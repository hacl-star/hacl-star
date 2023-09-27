module Hacl.Impl.P256.Group

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module BE = Hacl.Impl.Exponentiation.Definitions

module S = Spec.P256
module SL = Spec.P256.Lemmas

open Hacl.Impl.P256.Point

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

unfold
let linv_ctx (a:LSeq.lseq uint64 0) : Type0 = True

unfold
let refl (p:LSeq.lseq uint64 12{point_inv_seq p}) : GTot S.aff_point =
  S.to_aff_point (from_mont_point (as_point_nat_seq p))

inline_for_extraction noextract
let mk_to_p256_comm_monoid : BE.to_comm_monoid U64 12ul 0ul = {
  BE.a_spec = S.aff_point;
  BE.comm_monoid = S.mk_p256_comm_monoid;
  BE.linv_ctx = linv_ctx;
  BE.linv = point_inv_seq;
  BE.refl = refl;
}


inline_for_extraction noextract
val point_add : BE.lmul_st U64 12ul 0ul mk_to_p256_comm_monoid
let point_add ctx x y xy =
  let h0 = ST.get () in
  SL.to_aff_point_add_lemma
    (from_mont_point (as_point_nat h0 x)) (from_mont_point (as_point_nat h0 y));
  Hacl.Impl.P256.PointAdd.point_add xy x y


inline_for_extraction noextract
val point_double : BE.lsqr_st U64 12ul 0ul mk_to_p256_comm_monoid
let point_double ctx x xx =
  let h0 = ST.get () in
  SL.to_aff_point_double_lemma (from_mont_point (as_point_nat h0 x));
  Hacl.Impl.P256.PointDouble.point_double xx x


inline_for_extraction noextract
val point_zero : BE.lone_st U64 12ul 0ul mk_to_p256_comm_monoid
let point_zero ctx one =
  let h0 = ST.get () in
  SL.to_aff_point_at_infinity_lemma ();
  make_point_at_inf one


inline_for_extraction noextract
let mk_p256_concrete_ops : BE.concrete_ops U64 12ul 0ul = {
  BE.to = mk_to_p256_comm_monoid;
  BE.lone = point_zero;
  BE.lmul = point_add;
  BE.lsqr = point_double;
}
