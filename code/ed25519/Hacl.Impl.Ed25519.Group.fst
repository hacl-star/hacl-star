module Hacl.Impl.Ed25519.Group

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519
open Hacl.Impl.Ed25519.PointConstants

module LSeq = Lib.Sequence
module F51 = Hacl.Impl.Ed25519.Field51
module BE = Hacl.Impl.Exponentiation.Definitions
module S = Spec.Ed25519

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

unfold
let a_spec = S.aff_point_c

unfold
let refl (a:LSeq.lseq uint64 20{F51.linv a}) : GTot a_spec =
  S.to_aff_point (F51.refl_ext_point a)

unfold
let linv_ctx (a:LSeq.lseq uint64 0) : Type0 = True

inline_for_extraction noextract
let mk_to_ed25519_comm_monoid : BE.to_comm_monoid U64 20ul 0ul = {
  BE.a_spec = a_spec;
  BE.comm_monoid = S.mk_ed25519_comm_monoid;
  BE.linv_ctx = linv_ctx;
  BE.linv = F51.linv;
  BE.refl = refl;
}


inline_for_extraction noextract
val point_add : BE.lmul_st U64 20ul 0ul mk_to_ed25519_comm_monoid
let point_add ctx x y xy =
  let h0 = ST.get () in
  Spec.Ed25519.Lemmas.to_aff_point_add_lemma
    (F51.refl_ext_point (as_seq h0 x)) (F51.refl_ext_point (as_seq h0 y));
  Hacl.Impl.Ed25519.PointAdd.point_add xy x y


inline_for_extraction noextract
val point_double : BE.lsqr_st U64 20ul 0ul mk_to_ed25519_comm_monoid
let point_double ctx x xx =
  let h0 = ST.get () in
  Spec.Ed25519.Lemmas.to_aff_point_double_lemma (F51.refl_ext_point (as_seq h0 x));
  Hacl.Impl.Ed25519.PointDouble.point_double xx x


inline_for_extraction noextract
val point_zero : BE.lone_st U64 20ul 0ul mk_to_ed25519_comm_monoid
let point_zero ctx one = make_point_inf one


inline_for_extraction noextract
let mk_ed25519_concrete_ops : BE.concrete_ops U64 20ul 0ul = {
  BE.to = mk_to_ed25519_comm_monoid;
  BE.lone = point_zero;
  BE.lmul = point_add;
  BE.lsqr = point_double;
}
