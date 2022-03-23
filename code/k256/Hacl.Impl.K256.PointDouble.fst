module Hacl.Impl.K256.PointDouble

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST

module S = Spec.K256
module BL = Hacl.Spec.K256.Field52.Lemmas

open Hacl.K256.Field
open Hacl.Impl.K256.Point

#set-options "--z3rlimit 300 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val calc_z3 (y1 z1 z3 yy tmp:felem) : Stack unit
  (requires fun h ->
    live h y1 /\ live h z1 /\ live h z3 /\
    live h yy /\ live h tmp /\
    disjoint y1 z1 /\ disjoint y1 z3 /\ disjoint y1 yy /\
    disjoint y1 tmp /\ eq_or_disjoint z1 z3 /\ disjoint z1 yy /\
    disjoint z1 tmp /\ disjoint z3 yy /\ disjoint z3 tmp /\ disjoint yy tmp /\

    inv_lazy_reduced2 h y1 /\ inv_lazy_reduced2 h z1 /\ inv_lazy_reduced2 h yy)
  (ensures  fun h0 _ h1 -> modifies (loc tmp |+| loc z3) h0 h1 /\
    feval h1 z3 = S.fmul (S.fmul (S.fmul (feval h0 yy) (feval h0 y1)) (feval h0 z1)) 8 /\
    inv_lazy_reduced2 h1 z3)

let calc_z3 y1 z1 z3 yy tmp =
  fmul tmp yy y1; //tmp = yy*y
  fmul z3 tmp z1; //z3 = tmp*z = yy*y*z
  let h1 = ST.get () in
  //assert (inv_lazy_reduced2 h1 x3);
  //assert (inv_lazy_reduced2 h1 tmp);
  //assert (inv_lazy_reduced2 h1 z3);

  fmul_8_normalize_weak z3 z3 //z3 = z3*8=yy*y*z*8


inline_for_extraction noextract
val calc_bzz9_tmp (yy zz bzz3 bzz9 tmp:felem) : Stack unit
  (requires fun h ->
    live h yy /\ live h zz /\ live h bzz3 /\ live h bzz9 /\ live h tmp /\
    disjoint yy zz /\ disjoint yy bzz3 /\ disjoint yy bzz9 /\
    disjoint yy tmp /\ disjoint zz bzz3 /\ disjoint zz bzz9 /\
    disjoint zz tmp /\ disjoint bzz3 bzz9 /\ disjoint bzz3 tmp /\
    disjoint bzz9 tmp /\
    inv_lazy_reduced2 h yy /\ inv_lazy_reduced2 h zz)
  (ensures  fun h0 _ h1 ->
    modifies (loc bzz3 |+| loc bzz9 |+| loc tmp) h0 h1 /\
    (let bzz3 = S.fmul (S.fmul 3 S.b) (feval h0 zz) in
     feval h1 bzz9 = S.fsub (feval h0 yy) (S.fmul 3 bzz3) /\
     feval h1 tmp = S.fmul (feval h1 bzz9) (S.fadd (feval h0 yy) bzz3) /\
     inv_lazy_reduced2 h1 tmp /\ felem_fits5 (as_felem5 h1 bzz9) (13,13,13,13,14)))

let calc_bzz9_tmp yy zz bzz3 bzz9 tmp =
  fmul_3b_normalize_weak bzz3 zz; //bzz3 = (3*b)*zz
  let h1 = ST.get () in
  //assert (inv_lazy_reduced2 h1 bzz3);

  fmul_small_num bzz9 bzz3 (u64 3); //bzz9 = 3*bzz3
  let h2 = ST.get () in
  BL.fmul15_lemma (1,1,1,1,2) 3 (as_felem5 h1 bzz3) (u64 3);
  //assert (felem_fits5 (as_felem5 h2 bzz9) (3,3,3,3,6));

  BL.fsub5_lemma (1,1,1,1,2) (3,3,3,3,6) (as_felem5 h1 yy) (as_felem5 h2 bzz9) (u64 6);
  fsub bzz9 yy bzz9 (u64 6); //bzz9 = yy_m_bzz9 = yy-bzz9
  let h3 = ST.get () in
  //assert (felem_fits5 (as_felem5 h3 bzz9) (13,13,13,13,14));

  fadd tmp yy bzz3; //tmp = yy_p_bzz3 = yy+bzz3
  let h4 = ST.get () in
  BL.fadd5_lemma (1,1,1,1,2) (1,1,1,1,2) (as_felem5 h1 yy) (as_felem5 h1 bzz3);
  //assert (felem_fits5 (as_felem5 h4 tmp) (2,2,2,2,4));

  fmul tmp bzz9 tmp //tmp = bzz9*tmp = yy_m_bzz9*yy_p_bzz3


inline_for_extraction noextract
val calc_y3 (y3 tmp: felem) : Stack unit
  (requires fun h ->
    live h y3 /\ live h tmp /\ disjoint y3 tmp /\
    inv_lazy_reduced2 h y3 /\ inv_lazy_reduced2 h tmp)
  (ensures  fun h0 _ h1 -> modifies (loc y3) h0 h1 /\
    feval h1 y3 = S.fadd (feval h0 tmp) (S.fmul (S.fmul 24 S.b) (feval h0 y3))/\
    inv_lazy_reduced2 h1 y3)

let calc_y3 y3 tmp =
  let h0 = ST.get () in
  fmul_small_num y3 y3 (u64 168); //y3 = t = (24*b)*y3 = (24*b)*yy_zz
  let h1 = ST.get () in
  BL.fmul15_lemma (1,1,1,1,2) 168 (as_felem5 h0 y3) (u64 168);
  //assert (felem_fits5 (as_felem5 h1 y3) (168,168,168,168,336));

  fadd y3 tmp y3;  //y3 = tmp+y3 = yy_m_bzz9*yy_p_bzz3+t
  let h2 = ST.get () in
  BL.fadd5_lemma (1,1,1,1,2) (168,168,168,168,336) (as_felem5 h0 tmp) (as_felem5 h1 y3);
  //assert (felem_fits5 (as_felem5 h2 y3) (169,169,169,169,338));
  fnormalize_weak y3 y3;
  BL.normalize_weak5_lemma (169,169,169,169,338) (as_felem5 h2 y3)


inline_for_extraction noextract
val point_double_no_alloc (out p:point) (tmp:lbuffer uint64 (5ul *! nlimb)) : Stack unit
  (requires fun h ->
    live h out /\ live h p /\ live h tmp /\
    eq_or_disjoint out p /\ disjoint out tmp /\ disjoint p tmp /\
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc out |+| loc tmp) h0 h1 /\ point_inv h1 out /\
    point_eval h1 out == S.point_double (point_eval h0 p))

let point_double_no_alloc out p tmp =
  let x1, y1, z1 = getx p, gety p, getz p in
  let x3, y3, z3 = getx out, gety out, getz out in

  let yy = sub tmp 0ul nlimb in
  let zz = sub tmp nlimb nlimb in
  let bzz3 = sub tmp (2ul *! nlimb) nlimb in
  let bzz9 = sub tmp (3ul *! nlimb) nlimb in
  let tmp = sub tmp (4ul *! nlimb) nlimb in

  let h0 = ST.get () in
  fsqr yy y1; //yy = y*y
  fsqr zz z1; //zz = z*z
  let h1 = ST.get () in
  //assert (inv_lazy_reduced2 h1 yy);
  //assert (inv_lazy_reduced2 h1 zz);

  fmul_small_num x3 x1 (u64 2); //x3 = 2*x
  let h2 = ST.get () in
  BL.fmul15_lemma (1,1,1,1,2) 2 (as_felem5 h1 x1) (u64 2);
  //assert (felem_fits5 (as_felem5 h2 x3) (2,2,2,2,4));

  fmul x3 x3 y1; //x3 = xy2 = x3*y = (2*x)*y
  calc_z3 y1 z1 z3 yy tmp;
  calc_bzz9_tmp yy zz bzz3 bzz9 tmp;

  fmul y3 yy zz; //y3 = yy_zz = yy*zz
  fmul x3 x3 bzz9; //x3 = x3*bzz9 = xy2*yy_m_bzz9
  calc_y3 y3 tmp


val point_double (out p:point) : Stack unit
  (requires fun h ->
    live h out /\ live h p /\ eq_or_disjoint out p /\
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ point_inv h1 out /\
    point_eval h1 out == S.point_double (point_eval h0 p))

let point_double out p =
  push_frame ();
  let tmp = create (5ul *! nlimb) (u64 0) in
  point_double_no_alloc out p tmp;
  pop_frame ()
