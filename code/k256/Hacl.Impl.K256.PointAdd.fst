module Hacl.Impl.K256.PointAdd

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.K256
module BI = Hacl.Spec.K256.Field52
module BL = Hacl.Spec.K256.Field52.Lemmas

open Hacl.K256.Field
open Hacl.Impl.K256.Point

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"


inline_for_extraction noextract
val point_add_xy_pairs (x1 y1 x2 y2 xx yy tmp xy_pairs:felem) : Stack unit
  (requires fun h ->
    live h x1 /\ live h y1 /\ live h x2 /\ live h y2 /\
    live h xx /\ live h yy /\ live h tmp /\ live h xy_pairs /\
    eq_or_disjoint x1 y1 /\ eq_or_disjoint x2 y2 /\ eq_or_disjoint xx yy /\
    disjoint x1 xy_pairs /\ disjoint y1 xy_pairs /\ disjoint x2 xy_pairs /\ disjoint y2 xy_pairs /\
    disjoint x1 tmp /\ disjoint y1 tmp /\ disjoint x2 tmp /\ disjoint y2 tmp /\
    disjoint xx xy_pairs /\ disjoint yy xy_pairs /\ disjoint xx tmp /\ disjoint yy tmp /\
    disjoint xy_pairs tmp /\

    inv_lazy_reduced2 h x1 /\ inv_lazy_reduced2 h y1 /\ inv_lazy_reduced2 h x2 /\ inv_lazy_reduced2 h y2 /\
    inv_lazy_reduced2 h xx /\ inv_lazy_reduced2 h yy)
  (ensures  fun h0 _ h1 -> modifies (loc xy_pairs |+| loc tmp) h0 h1 /\
    feval h1 xy_pairs =
      S.fsub
	(S.fmul (S.fadd (feval h0 x1) (feval h0 y1)) (S.fadd (feval h0 x2) (feval h0 y2)))
	(S.fadd (feval h0 xx) (feval h0 yy)) /\
    felem_fits5 (as_felem5 h1 xy_pairs) (9,9,9,9,10))

let point_add_xy_pairs x1 y1 x2 y2 xx yy tmp xy_pairs =
  let h0 = ST.get () in
  BL.fadd5_lemma (1,1,1,1,2) (1,1,1,1,2) (as_felem5 h0 x1) (as_felem5 h0 y1);
  BL.fadd5_lemma (1,1,1,1,2) (1,1,1,1,2) (as_felem5 h0 x2) (as_felem5 h0 y2);
  fadd xy_pairs x1 y1;
  fadd tmp x2 y2;
  let h1 = ST.get () in
  assert (felem_fits5 (as_felem5 h1 xy_pairs) (2,2,2,2,4));
  assert (felem_fits5 (as_felem5 h1 tmp) (2,2,2,2,4));
  fmul xy_pairs xy_pairs tmp;
  let h2 = ST.get () in
  assert (felem_fits5 (as_felem5 h2 xy_pairs) (1,1,1,1,2));
  BL.fadd5_lemma (1,1,1,1,2) (1,1,1,1,2) (as_felem5 h2 xx) (as_felem5 h2 yy);
  fadd tmp xx yy;
  let h3 = ST.get () in
  assert (felem_fits5 (as_felem5 h3 tmp) (2,2,2,2,4));

  fsub xy_pairs xy_pairs tmp (u64 4);
  let h4 = ST.get () in
  BL.fsub5_lemma (1,1,1,1,2) (2,2,2,2,4) (as_felem5 h3 xy_pairs) (as_felem5 h3 tmp) (u64 4);
  assert (felem_fits5 (as_felem5 h4 xy_pairs) (9,9,9,9,10))


inline_for_extraction noextract
val ab_plus_cd (a b c d tmp:felem) : Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h c /\ live h d /\ live h tmp /\
    disjoint a b /\ disjoint c d /\ eq_or_disjoint a b /\ eq_or_disjoint a d /\
    disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp /\ disjoint d tmp /\

    felem_fits5 (as_felem5 h a) (9,9,9,9,10) /\
    felem_fits5 (as_felem5 h b) (5,5,5,5,6) /\
    felem_fits5 (as_felem5 h c) (3,3,3,3,6) /\
    felem_fits5 (as_felem5 h d) (9,9,9,9,10))
  (ensures fun h0 _ h1 -> modifies (loc c |+| loc tmp) h0 h1 /\
    feval h1 c ==
      S.fadd
	(S.fmul (feval h0 a) (feval h0 b))
	(S.fmul (feval h0 c) (feval h0 d)) /\
    inv_lazy_reduced2 h1 c)

let ab_plus_cd a b c d tmp =
  fmul tmp a b;
  fmul c c d;
  let h1 = ST.get () in
  assert (inv_lazy_reduced2 h1 tmp);
  assert (inv_lazy_reduced2 h1 c);
  BL.fadd5_lemma (1,1,1,1,2) (1,1,1,1,2) (as_felem5 h1 tmp) (as_felem5 h1 c);
  fadd c tmp c;
  let h2 = ST.get () in
  assert (felem_fits5 (as_felem5 h2 c) (2,2,2,2,4));
  fnormalize_weak c c;
  BL.normalize_weak5_lemma (2,2,2,2,4) (as_felem5 h2 c)


inline_for_extraction noextract
val ab_minus_cd (a b c d tmp:felem) : Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h c /\ live h d /\ live h tmp /\
    disjoint a b /\ disjoint c d /\ eq_or_disjoint a b /\ eq_or_disjoint a d /\
    disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp /\ disjoint d tmp /\

    felem_fits5 (as_felem5 h a) (9,9,9,9,10) /\
    felem_fits5 (as_felem5 h b) (5,5,5,5,6) /\
    felem_fits5 (as_felem5 h c) (1,1,1,1,2) /\
    felem_fits5 (as_felem5 h d) (9,9,9,9,10))
  (ensures fun h0 _ h1 -> modifies (loc c |+| loc tmp) h0 h1 /\
    feval h1 c ==
      S.fsub
	(S.fmul (feval h0 a) (feval h0 b))
	(S.fmul (feval h0 c) (feval h0 d)) /\
    inv_lazy_reduced2 h1 c)

let ab_minus_cd a b c d tmp =
  fmul tmp a b;
  fmul c c d;
  let h1 = ST.get () in
  assert (inv_lazy_reduced2 h1 tmp);
  assert (inv_lazy_reduced2 h1 c);
  BL.fsub5_lemma (1,1,1,1,2) (1,1,1,1,2) (as_felem5 h1 tmp) (as_felem5 h1 c) (u64 2);
  fsub c tmp c (u64 2);
  let h2 = ST.get () in
  assert (felem_fits5 (as_felem5 h2 c) (5,5,5,5,6));
  fnormalize_weak c c;
  BL.normalize_weak5_lemma (5,5,5,5,6) (as_felem5 h2 c)


#set-options "--z3rlimit 300"

inline_for_extraction noextract
val point_add_no_alloc (out p q:point) (tmp:lbuffer uint64 (9ul *! nlimb)) : Stack unit
  (requires fun h ->
    live h out /\ live h p /\ live h q /\ live h tmp /\
    eq_or_disjoint out p /\ eq_or_disjoint out q /\ eq_or_disjoint p q /\
    disjoint p tmp /\ disjoint q tmp /\ disjoint out tmp /\
    point_inv h p /\ point_inv h q)
  (ensures fun h0 _ h1 -> modifies (loc out |+| loc tmp) h0 h1 /\ point_inv h1 out /\
    point_eval h1 out == S.point_add (point_eval h0 p) (point_eval h0 q))

let point_add_no_alloc out p q tmp =
  let x1, y1, z1 = getx p, gety p, getz p in
  let x2, y2, z2 = getx q, gety q, getz q in
  let x3, y3, z3 = getx out, gety out, getz out in

  let xx = sub tmp 0ul nlimb in
  let yy = sub tmp nlimb nlimb in
  let zz = sub tmp (2ul *! nlimb) nlimb in

  let xy_pairs = sub tmp (3ul *! nlimb) nlimb in
  let yz_pairs = sub tmp (4ul *! nlimb) nlimb in
  let xz_pairs = sub tmp (5ul *! nlimb) nlimb in

  let yy_m_bzz3 = sub tmp (6ul *! nlimb) nlimb in
  let yy_p_bzz3 = sub tmp (7ul *! nlimb) nlimb in
  let tmp1 = sub tmp (8ul *! nlimb) nlimb in

  let h0 = ST.get () in

  fmul xx x1 x2; //xx = x1*x2
  fmul yy y1 y2; //yy = y1*y2
  fmul zz z1 z2; //zz = z1*z2
  let h1 = ST.get () in
  // assert (inv_lazy_reduced2 h1 xx);
  // assert (inv_lazy_reduced2 h1 yy);
  // assert (inv_lazy_reduced2 h1 zz);

  point_add_xy_pairs x1 y1 x2 y2 xx yy tmp1 xy_pairs; //xy_pairs = (x1+y1)*(x2+y2)-(xx+yy)
  point_add_xy_pairs y1 z1 y2 z2 yy zz tmp1 yz_pairs; //yz_pairs = (y1+z1)*(y2+z2)-(yy+zz)
  point_add_xy_pairs x1 z1 x2 z2 xx zz tmp1 xz_pairs; //xz_pairs = (x1+z1)*(x2+z2)-(xx+zz)

  let h2 = ST.get () in
  // assert (felem_fits5 (as_felem5 h2 xy_pairs) (9,9,9,9,10));
  // assert (felem_fits5 (as_felem5 h2 yz_pairs) (9,9,9,9,10));
  // assert (felem_fits5 (as_felem5 h2 xz_pairs) (9,9,9,9,10));

  fmul_3b_normalize_weak tmp1 zz; //tmp1 = bzz3 = (3*b)*zz
  let h3 = ST.get () in
  // assert (felem_fits5 (as_felem5 h3 tmp1) (1,1,1,1,2));

  fsub yy_m_bzz3 yy tmp1 (u64 2); //yy_m_bzz3 = yy-bzz3
  let h5 = ST.get () in
  BL.fsub5_lemma (1,1,1,1,2) (1,1,1,1,2) (as_felem5 h3 yy) (as_felem5 h3 tmp1) (u64 2);
  // assert (felem_fits5 (as_felem5 h5 yy_m_bzz3) (5,5,5,5,6));

  fadd yy_p_bzz3 yy tmp1; //yy_p_bzz3 = yy+bzz3
  let h6 = ST.get () in
  BL.fadd5_lemma (1,1,1,1,2) (1,1,1,1,2) (as_felem5 h3 yy) (as_felem5 h3 tmp1);
  // assert (felem_fits5 (as_felem5 h6 yy_p_bzz3) (2,2,2,2,4));

  fmul_3b_normalize_weak x3 yz_pairs; //x3 = byz3 = (3*b)*yz_pairs
  let h7 = ST.get () in
  // assert (felem_fits5 (as_felem5 h7 x3) (1,1,1,1,2));

  fmul_small_num z3 xx (u64 3); //z3 = xx3 = 3*xx
  let h8 = ST.get () in
  BL.fmul15_lemma (1,1,1,1,2) 3 (as_felem5 h7 xx) (u64 3);
  // assert (felem_fits5 (as_felem5 h8 z3) (3,3,3,3,6));

  fmul_3b_normalize_weak y3 z3; //y3 = bxx9 = (3*b)*xx3
  let h9 = ST.get () in
  // assert (felem_fits5 (as_felem5 h9 y3) (1,1,1,1,2));
  ab_minus_cd xy_pairs yy_m_bzz3 x3 xz_pairs tmp1; //x3 = (xy_pairs*yy_m_bzz3-byz3*xz_pairs)
  ab_plus_cd yy_p_bzz3 yy_m_bzz3 y3 xz_pairs tmp1; //y3 = (yy_p_bzz3*yy_m_bzz3+bxx9*xz_pairs)
  ab_plus_cd yz_pairs yy_p_bzz3 z3 xy_pairs tmp1 //z3 = (yz_pairs*yy_p_bzz3+xx3*xy_pairs)


val point_add (out p q:point) : Stack unit
  (requires fun h ->
    live h out /\ live h p /\ live h q /\
    eq_or_disjoint out p /\ eq_or_disjoint out q /\ eq_or_disjoint p q /\
    point_inv h p /\ point_inv h q)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ point_inv h1 out /\
    point_eval h1 out == S.point_add (point_eval h0 p) (point_eval h0 q))

[@CInline]
let point_add out p q =
  push_frame ();
  let tmp = create (9ul *! nlimb) (u64 0) in
  point_add_no_alloc out p q tmp;
  pop_frame ()
