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

    fe_lt_prime h x1 /\ fe_lt_prime h y1 /\ fe_lt_prime h x2 /\ fe_lt_prime h y2 /\
    fe_lt_prime h xx /\ fe_lt_prime h yy)
  (ensures  fun h0 _ h1 -> modifies (loc xy_pairs |+| loc tmp) h0 h1 /\
    as_nat h1 xy_pairs =
      S.fsub
	(S.fmul (S.fadd (as_nat h0 x1) (as_nat h0 y1)) (S.fadd (as_nat h0 x2) (as_nat h0 y2)))
	(S.fadd (as_nat h0 xx) (as_nat h0 yy)) /\
    fe_lt_prime h1 xy_pairs)

let point_add_xy_pairs x1 y1 x2 y2 xx yy tmp xy_pairs =
  //let h0 = ST.get () in
  fadd xy_pairs x1 y1;
  fadd tmp x2 y2;
  //let h1 = ST.get () in
  //assert (as_nat h1 xy_pairs == S.fadd (as_nat h0 x1) (as_nat h0 y1));
  //assert (as_nat h1 tmp == S.fadd (as_nat h0 x2) (as_nat h0 y2));
  fmul xy_pairs xy_pairs tmp;
  fadd tmp xx yy;
  //let h2 = ST.get () in
  //assert (as_nat h2 xy_pairs == S.fmul (as_nat h1 xy_pairs) (as_nat h1 tmp));
  //assert (as_nat h2 tmp = S.fadd (as_nat h0 xx) (as_nat h0 yy));
  fsub xy_pairs xy_pairs tmp
  //let h3 = ST.get () in
  //assert (as_nat h3 xy_pairs == S.fsub (as_nat h2 xy_pairs) (as_nat h2 tmp));
  //assert (as_nat h3 xy_pairs ==
    // S.fsub
    //   (S.fmul (S.fadd (as_nat h0 x1) (as_nat h0 y1)) (S.fadd (as_nat h0 x2) (as_nat h0 y2)))
    //   (S.fadd (as_nat h0 xx) (as_nat h0 yy)))


inline_for_extraction noextract
val ab_plus_cd (a b c d tmp:felem) : Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h c /\ live h d /\ live h tmp /\
    disjoint a b /\ disjoint c d /\ eq_or_disjoint a b /\ eq_or_disjoint a d /\
    disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp /\ disjoint d tmp /\

    fe_lt_prime h a /\ fe_lt_prime h b /\ fe_lt_prime h c /\ fe_lt_prime h d)
  (ensures fun h0 _ h1 -> modifies (loc c |+| loc tmp) h0 h1 /\
    as_nat h1 c ==
      S.fadd
	(S.fmul (as_nat h0 a) (as_nat h0 b))
	(S.fmul (as_nat h0 c) (as_nat h0 d)) /\
    fe_lt_prime h1 c)

let ab_plus_cd a b c d tmp =
  fmul tmp a b;
  fmul c c d;
  fadd c tmp c


inline_for_extraction noextract
val ab_minus_cd (a b c d tmp:felem) : Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h c /\ live h d /\ live h tmp /\
    disjoint a b /\ disjoint c d /\ eq_or_disjoint a b /\ eq_or_disjoint a d /\
    disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp /\ disjoint d tmp /\

    fe_lt_prime h a /\ fe_lt_prime h b /\ fe_lt_prime h c /\ fe_lt_prime h d)
  (ensures fun h0 _ h1 -> modifies (loc c |+| loc tmp) h0 h1 /\
    as_nat h1 c ==
      S.fsub
	(S.fmul (as_nat h0 a) (as_nat h0 b))
	(S.fmul (as_nat h0 c) (as_nat h0 d)) /\
    fe_lt_prime h1 c)

let ab_minus_cd a b c d tmp =
  fmul tmp a b;
  fmul c c d;
  fsub c tmp c


inline_for_extraction noextract
val point_add_no_alloc (out p q:point) (tmp:lbuffer uint64 (9ul *! nlimb)) : Stack unit
  (requires fun h ->
    live h out /\ live h p /\ live h q /\ live h tmp /\
    eq_or_disjoint out p /\ eq_or_disjoint out q /\ eq_or_disjoint p q /\
    disjoint p tmp /\ disjoint q tmp /\ disjoint out tmp /\
    point_inv h p /\ point_inv h q)
  (ensures fun h0 _ h1 -> modifies (loc out |+| loc tmp) h0 h1 /\ point_inv h1 out /\
    point_as_nat3_proj h1 out == S.point_add (point_as_nat3_proj h0 p) (point_as_nat3_proj h0 q))

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

  // let h1 = ST.get () in
  // assert (as_nat h1 xx == S.fmul (as_nat h0 x1) (as_nat h0 x2));
  // assert (as_nat h1 yy == S.fmul (as_nat h0 y1) (as_nat h0 y2));
  // assert (as_nat h1 zz == S.fmul (as_nat h0 z1) (as_nat h0 z2));

  point_add_xy_pairs x1 y1 x2 y2 xx yy tmp1 xy_pairs; //xy_pairs = (x1+y1)*(x2+y2)-(xx+yy)
  point_add_xy_pairs y1 z1 y2 z2 yy zz tmp1 yz_pairs; //yz_pairs = (y1+z1)*(y2+z2)-(yy+zz)
  point_add_xy_pairs x1 z1 x2 z2 xx zz tmp1 xz_pairs; //xz_pairs = (x1+z1)*(x2+z2)-(xx+zz)

  // let h2 = ST.get () in
  // assert (as_nat h2 xy_pairs ==
  //   S.fsub
  //     (S.fmul (S.fadd (as_nat h0 x1) (as_nat h0 y1)) (S.fadd (as_nat h0 x2) (as_nat h0 y2)))
  //     (S.fadd (as_nat h1 xx) (as_nat h1 yy)));

  // assert (as_nat h2 yz_pairs ==
  //   S.fsub
  //     (S.fmul (S.fadd (as_nat h0 y1) (as_nat h0 z1)) (S.fadd (as_nat h0 y2) (as_nat h0 z2)))
  //     (S.fadd (as_nat h1 yy) (as_nat h1 zz)));

  // assert (as_nat h2 xz_pairs ==
  //   S.fsub
  //     (S.fmul (S.fadd (as_nat h0 x1) (as_nat h0 z1)) (S.fadd (as_nat h0 x2) (as_nat h0 z2)))
  //     (S.fadd (as_nat h1 xx) (as_nat h1 zz)));

  fmul_3b tmp1 zz; //tmp1 = bzz3 = (3*b)*zz
  fsub yy_m_bzz3 yy tmp1; //yy_m_bzz3 = yy-bzz3
  fadd yy_p_bzz3 yy tmp1; //yy_p_bzz3 = yy+bzz3

  // let h3 = ST.get () in
  // assert (as_nat h3 tmp1 = S.fmul (S.fmul 3 S.b) (as_nat h1 zz));
  // assert (as_nat h3 yy_m_bzz3 = S.fsub (as_nat h1 yy) (as_nat h3 tmp1));
  // assert (as_nat h3 yy_p_bzz3 = S.fadd (as_nat h1 yy) (as_nat h3 tmp1));

  fmul_3b x3 yz_pairs; //x3 = byz3 = (3*b)*yz_pairs
  fmul_small_num z3 xx (u64 3); //z3 = xx3 = 3*xx
  fmul_3b y3 z3; //y3 = bxx9 = (3*b)*xx3

  // let h4 = ST.get () in
  // assert (as_nat h4 x3 = S.fmul (S.fmul 3 S.b) (as_nat h2 yz_pairs));
  // assert (as_nat h4 z3 = S.fmul 3 (as_nat h1 xx));
  // assert (as_nat h4 y3 = S.fmul (S.fmul 3 S.b) (as_nat h4 z3));

  ab_minus_cd xy_pairs yy_m_bzz3 x3 xz_pairs tmp1; //x3 = (xy_pairs*yy_m_bzz3-byz3*xz_pairs)
  ab_plus_cd yy_p_bzz3 yy_m_bzz3 y3 xz_pairs tmp1; //y3 = (yy_p_bzz3*yy_m_bzz3+bxx9*xz_pairs)
  ab_plus_cd yz_pairs yy_p_bzz3 z3 xy_pairs tmp1 //z3 = (yz_pairs*yy_p_bzz3+xx3*xy_pairs)

  // let h5 = ST.get () in
  // assert (as_nat h5 x3 =
  //   S.fsub
  //     (S.fmul (as_nat h2 xy_pairs) (as_nat h3 yy_m_bzz3))
  //     (S.fmul (as_nat h4 x3) (as_nat h2 xz_pairs)));

  // assert (as_nat h5 y3 =
  //   S.fadd
  //     (S.fmul (as_nat h3 yy_p_bzz3) (as_nat h3 yy_m_bzz3))
  //     (S.fmul (as_nat h4 y3) (as_nat h2 xz_pairs)));

  // assert (as_nat h5 z3 =
  //   S.fadd
  //     (S.fmul (as_nat h2 yz_pairs) (as_nat h3 yy_p_bzz3))
  //     (S.fmul (as_nat h4 z3) (as_nat h2 xy_pairs)))


val point_add (out p q:point) : Stack unit
  (requires fun h ->
    live h out /\ live h p /\ live h q /\
    eq_or_disjoint out p /\ eq_or_disjoint out q /\ eq_or_disjoint p q /\
    point_inv h p /\ point_inv h q)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ point_inv h1 out /\
    point_as_nat3_proj h1 out == S.point_add (point_as_nat3_proj h0 p) (point_as_nat3_proj h0 q))

[@CInline]
let point_add out p q =
  push_frame ();
  let tmp = create (9ul *! nlimb) (u64 0) in
  point_add_no_alloc out p q tmp;
  pop_frame ()
