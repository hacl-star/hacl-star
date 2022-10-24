module Hacl.Impl.K256.Group

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module BE = Hacl.Impl.Exponentiation.Definitions

module S = Spec.K256
module SL = Spec.K256.Lemmas

open Hacl.Impl.K256.Point

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

unfold
let linv_ctx (a:LSeq.lseq uint64 0) : Type0 = True

unfold
let refl (p:LSeq.lseq uint64 15{point_inv_lseq p}) : GTot S.aff_point =
  S.to_aff_point (point_eval_lseq p)

inline_for_extraction noextract
let mk_to_k256_comm_monoid : BE.to_comm_monoid U64 15ul 0ul = {
  BE.a_spec = S.aff_point;
  BE.comm_monoid = S.mk_k256_comm_monoid;
  BE.linv_ctx = linv_ctx;
  BE.linv = point_inv_lseq;
  BE.refl = refl;
}


inline_for_extraction noextract
val point_add : BE.lmul_st U64 15ul 0ul mk_to_k256_comm_monoid
let point_add ctx x y xy =
  let h0 = ST.get () in
  SL.to_aff_point_add_lemma (point_eval h0 x) (point_eval h0 y);
  Hacl.Impl.K256.PointAdd.point_add xy x y


inline_for_extraction noextract
val point_double : BE.lsqr_st U64 15ul 0ul mk_to_k256_comm_monoid
let point_double ctx x xx =
  let h0 = ST.get () in
  SL.to_aff_point_double_lemma (point_eval h0 x);
  Hacl.Impl.K256.PointDouble.point_double xx x


inline_for_extraction noextract
val point_zero : BE.lone_st U64 15ul 0ul mk_to_k256_comm_monoid
let point_zero ctx one = make_point_at_inf one


inline_for_extraction noextract
let mk_k256_concrete_ops : BE.concrete_ops U64 15ul 0ul = {
  BE.to = mk_to_k256_comm_monoid;
  BE.lone = point_zero;
  BE.lmul = point_add;
  BE.lsqr = point_double;
}
