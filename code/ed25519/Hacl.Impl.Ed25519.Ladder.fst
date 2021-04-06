module Hacl.Impl.Ed25519.Ladder

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519
module F51 = Hacl.Impl.Ed25519.Field51

module LSeq = Lib.Sequence
module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation
module ME = Hacl.Impl.MultiExponentiation

module BD = Hacl.Bignum.Definitions
module BN = Hacl.Bignum
module SN = Hacl.Spec.Bignum

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

////////////////////////////////////////////////////
unfold
let a_spec = Spec.Ed25519.aff_point_c

unfold
let lseq_as_felem (a:LSeq.lseq uint64 5) : GTot Hacl.Spec.Curve25519.Field51.Definition.felem5 =
  let s0 = LSeq.index a 0 in
  let s1 = LSeq.index a 1 in
  let s2 = LSeq.index a 2 in
  let s3 = LSeq.index a 3 in
  let s4 = LSeq.index a 4 in
  (s0, s1, s2, s3, s4)

unfold
let refl_ext_point (a:LSeq.lseq uint64 20) : GTot Spec.Ed25519.ext_point =
  let open Hacl.Spec.Curve25519.Field51.Definition in
  let x = feval (lseq_as_felem (LSeq.sub a 0 5)) in
  let y = feval (lseq_as_felem (LSeq.sub a 5 5)) in
  let z = feval (lseq_as_felem (LSeq.sub a 10 5)) in
  let t = feval (lseq_as_felem (LSeq.sub a 15 5)) in
  (x, y, z, t)

unfold
let inv_ext_point (a:LSeq.lseq uint64 20) : Type0 =
  Spec.Ed25519.point_inv (refl_ext_point a)


unfold
let linv (a:LSeq.lseq uint64 20) : Type0 =
  let open Hacl.Spec.Curve25519.Field51 in
  mul_inv_t (lseq_as_felem (LSeq.sub a 0 5)) /\
  mul_inv_t (lseq_as_felem (LSeq.sub a 5 5)) /\
  mul_inv_t (lseq_as_felem (LSeq.sub a 10 5)) /\
  mul_inv_t (lseq_as_felem (LSeq.sub a 15 5)) /\
  inv_ext_point a


unfold
let refl (a:LSeq.lseq uint64 20{linv a}) : GTot a_spec =
  Spec.Ed25519.to_aff_point (refl_ext_point a)

unfold
let linv_ctx (a:LSeq.lseq uint64 0) : Type0 = True


inline_for_extraction noextract
let mk_to_ed25519_comm_monoid : BE.to_comm_monoid U64 20ul 0ul = {
  BE.a_spec = a_spec;
  BE.comm_monoid = Spec.Ed25519.mk_ed25519_comm_monoid;
  BE.linv_ctx = linv_ctx;
  BE.linv = linv;
  BE.refl = refl;
  }


inline_for_extraction noextract
val point_add : BE.lmul_st U64 20ul 0ul mk_to_ed25519_comm_monoid
let point_add ctx x y xy =
  let h0 = ST.get () in
  Spec.Ed25519.Lemmas.to_aff_point_add_lemma (refl_ext_point (as_seq h0 x)) (refl_ext_point (as_seq h0 y));
  Hacl.Impl.Ed25519.PointAdd.point_add xy x y


inline_for_extraction noextract
val point_double : BE.lsqr_st U64 20ul 0ul mk_to_ed25519_comm_monoid
let point_double ctx x xx =
  let h0 = ST.get () in
  Spec.Ed25519.Lemmas.to_aff_point_double_lemma (refl_ext_point (as_seq h0 x));
  Hacl.Impl.Ed25519.PointDouble.point_double xx x


inline_for_extraction noextract
let mk_ed25519_concrete_ops : BE.concrete_ops U64 20ul 0ul = {
  BE.to = mk_to_ed25519_comm_monoid;
  BE.lmul = point_add;
  BE.lsqr = point_double;
}

//////////////////////////////////////////////

inline_for_extraction noextract
val make_point_inf:
  b:lbuffer uint64 20ul ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    F51.point_inv_t h1 b /\ inv_ext_point (as_seq h1 b) /\
    Spec.Ed25519.to_aff_point (F51.point_eval h1 b) ==
    Spec.Ed25519.aff_point_at_infinity)

let make_point_inf b =
  let x = sub b 0ul 5ul in
  let y = sub b 5ul 5ul in
  let z = sub b 10ul 5ul in
  let t = sub b 15ul 5ul in
  make_zero x;
  make_one y;
  make_one z;
  make_zero t;
  let h1 = ST.get () in
  assert (F51.point_eval h1 b == Spec.Ed25519.point_at_infinity);
  Spec.Ed25519.Lemmas.to_aff_point_at_infinity_lemma ()


inline_for_extraction noextract
val make_g:
  g:point ->
  Stack unit
  (requires fun h -> live h g)
  (ensures fun h0 _ h1 -> modifies (loc g) h0 h1 /\
    F51.point_inv_t h1 g /\
    F51.point_eval h1 g == Spec.Ed25519.g)

let make_g g =
  let gx = getx g in
  let gy = gety g in
  let gz = getz g in
  let gt = gett g in
  make_u64_5 gx (u64 0x00062d608f25d51a) (u64 0x000412a4b4f6592a) (u64 0x00075b7171a4b31d) (u64 0x0001ff60527118fe) (u64 0x000216936d3cd6e5);
  make_u64_5 gy (u64 0x0006666666666658) (u64 0x0004cccccccccccc) (u64 0x0001999999999999) (u64 0x0003333333333333) (u64 0x0006666666666666);
  make_one gz;
  make_u64_5 gt (u64 0x00068ab3a5b7dda3) (u64 0x00000eea2a5eadbb) (u64 0x0002af8df483c27e) (u64 0x000332b375274732) (u64 0x00067875f0fd78b7);

  (**) assert_norm (Spec.Ed25519.g_x ==
    Hacl.Spec.Curve25519.Field51.Definition.as_nat5 (u64 0x00062d608f25d51a, u64 0x000412a4b4f6592a, u64 0x00075b7171a4b31d, u64 0x0001ff60527118fe, u64 0x000216936d3cd6e5) % Spec.Curve25519.prime);
  (**) assert_norm (Spec.Ed25519.g_y ==
    Hacl.Spec.Curve25519.Field51.Definition.as_nat5 (u64 0x0006666666666658, u64 0x0004cccccccccccc, u64 0x0001999999999999, u64 0x0003333333333333, u64 0x0006666666666666) %
      Spec.Curve25519.prime);
  (**) assert_norm (Mktuple4?._4 Spec.Ed25519.g ==
    Hacl.Spec.Curve25519.Field51.Definition.as_nat5 (u64 0x00068ab3a5b7dda3, u64 0x00000eea2a5eadbb, u64 0x0002af8df483c27e, u64 0x000332b375274732, u64 0x00067875f0fd78b7) % Spec.Curve25519.prime)


val point_mul:
    result:point
  -> scalar:lbuffer uint8 32ul
  -> q:point ->
  Stack unit
  (requires fun h ->
    live h scalar /\ live h q /\ live h result /\
    disjoint q result /\ disjoint q scalar /\
    F51.point_inv_t h q /\ inv_ext_point (as_seq h q))
  (ensures  fun h0 _ h1 -> modifies (loc result |+| loc q) h0 h1 /\
    F51.point_inv_t h1 result /\ inv_ext_point (as_seq h1 result) /\
    Spec.Ed25519.to_aff_point (F51.point_eval h1 result) ==
    Spec.Ed25519.to_aff_point (Spec.Ed25519.point_mul (as_seq h0 scalar) (F51.point_eval h0 q)))

let point_mul result scalar q =
  let h0 = ST.get () in
  push_frame ();
  let bscalar = create 4ul (u64 0) in
  BN.bn_from_bytes_le 32ul scalar bscalar;
  SN.bn_from_bytes_le_lemma #U64 32 (as_seq h0 scalar);

  make_point_inf result;
  BE.lexp_fw_consttime 20ul 0ul mk_ed25519_concrete_ops (null uint64) q 4ul 256ul bscalar result 4ul;
  pop_frame ()


val point_mul_g:
    result:point
  -> scalar:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h ->
    live h scalar /\ live h result /\ disjoint result scalar)
  (ensures  fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    F51.point_inv_t h1 result /\ inv_ext_point (as_seq h1 result) /\
    Spec.Ed25519.to_aff_point (F51.point_eval h1 result) ==
    Spec.Ed25519.to_aff_point (Spec.Ed25519.point_mul_g (as_seq h0 scalar)))

[@CInline]
let point_mul_g result scalar =
  push_frame ();
  let g = create 20ul (u64 0) in
  make_g g;
  Spec.Ed25519.Lemmas.g_is_on_curve ();
  point_mul result scalar g;
  pop_frame ()


#push-options "--z3rlimit 150"
val point_mul_double_vartime:
    result:point
  -> scalar1:lbuffer uint8 32ul
  -> q1:point
  -> scalar2:lbuffer uint8 32ul
  -> q2:point ->
  Stack unit
  (requires fun h ->
    live h result /\ live h scalar1 /\ live h q1 /\
    live h scalar2 /\ live h q2 /\
    disjoint q1 result /\ disjoint q2 result /\
    disjoint q1 q2 /\
    F51.point_inv_t h q1 /\ inv_ext_point (as_seq h q1) /\
    F51.point_inv_t h q2 /\ inv_ext_point (as_seq h q2))
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    F51.point_inv_t h1 result /\ inv_ext_point (as_seq h1 result) /\
    Spec.Ed25519.to_aff_point (F51.point_eval h1 result) ==
    Spec.Ed25519.to_aff_point (Spec.Ed25519.point_mul_double
      (as_seq h0 scalar1) (F51.point_eval h0 q1)
      (as_seq h0 scalar2) (F51.point_eval h0 q2)))

[@CInline]
let point_mul_double_vartime result scalar1 q1 scalar2 q2 =
  let h0 = ST.get () in
  push_frame ();
  let bscalar1 = create 4ul (u64 0) in
  BN.bn_from_bytes_le 32ul scalar1 bscalar1;
  SN.bn_from_bytes_le_lemma #U64 32 (as_seq h0 scalar1);

  let bscalar2 = create 4ul (u64 0) in
  BN.bn_from_bytes_le 32ul scalar2 bscalar2;
  SN.bn_from_bytes_le_lemma #U64 32 (as_seq h0 scalar2);

  make_point_inf result;
  ME.lexp_double_fw_vartime 20ul 0ul mk_ed25519_concrete_ops (null uint64) q1 4ul 256ul bscalar1 q2 bscalar2 result 4ul;
  pop_frame ()
#pop-options


val point_mul_g_double_vartime:
    result:point
  -> scalar1:lbuffer uint8 32ul
  -> scalar2:lbuffer uint8 32ul
  -> q2:point ->
  Stack unit
  (requires fun h ->
    live h result /\ live h scalar1 /\
    live h scalar2 /\ live h q2 /\
    disjoint q2 result /\
    F51.point_inv_t h q2 /\ inv_ext_point (as_seq h q2))
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    F51.point_inv_t h1 result /\ inv_ext_point (as_seq h1 result) /\
    Spec.Ed25519.to_aff_point (F51.point_eval h1 result) ==
    Spec.Ed25519.to_aff_point (Spec.Ed25519.point_mul_double_g
      (as_seq h0 scalar1) (as_seq h0 scalar2) (F51.point_eval h0 q2)))

[@CInline]
let point_mul_g_double_vartime result scalar1 scalar2 q2 =
  push_frame ();
  let g = create 20ul (u64 0) in
  make_g g;
  Spec.Ed25519.Lemmas.g_is_on_curve ();
  point_mul_double_vartime result scalar1 g scalar2 q2;
  pop_frame ()
