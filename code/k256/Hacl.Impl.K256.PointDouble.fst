module Hacl.Impl.K256.PointDouble

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
val point_double_no_alloc (out p:point) (tmp:lbuffer uint64 (5ul *! nlimb)) : Stack unit
  (requires fun h ->
    live h out /\ live h p /\ live h tmp /\
    eq_or_disjoint out p /\ disjoint out tmp /\ disjoint p tmp /\
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc out |+| loc tmp) h0 h1 /\ point_inv h1 out /\
    point_as_nat3_proj h1 out == S.point_double (point_as_nat3_proj h0 p))

let point_double_no_alloc out p tmp =
  let x1, y1, z1 = getx p, gety p, getz p in
  let x3, y3, z3 = getx out, gety out, getz out in

  let yy = sub tmp 0ul nlimb in
  let zz = sub tmp nlimb nlimb in
  let bzz3 = sub tmp (2ul *! nlimb) nlimb in
  let bzz9 = sub tmp (3ul *! nlimb) nlimb in
  let tmp = sub tmp (4ul *! nlimb) nlimb in

  fsqr yy y1; //yy = y*y
  fsqr zz z1; //zz = z*z

  fmul_small_num x3 x1 (u64 2); //x3 = 2*x
  fmul x3 x3 y1; //x3 = xy2 = x3*y = (2*x)*y

  fmul tmp yy y1; //tmp = yy*y
  fmul z3 tmp z1; //z3 = tmp*z = yy*y*z
  fmul_small_num z3 z3 (u64 8); //z3 = z3*8=yy*y*z*8

  fmul_3b bzz3 zz; //bzz3 = (3*b)*zz
  fmul_small_num bzz9 bzz3 (u64 3); //bzz9 = 3*bzz3

  fsub bzz9 yy bzz9; //bzz9 = yy_m_bzz9 = yy-bzz9
  fadd tmp yy bzz3; //tmp = yy_p_bzz3 = yy+bzz3

  fmul y3 yy zz; //y3 = yy_zz = yy*zz
  fmul_24b y3 y3; //y3 = t = (24*b)*y3 = (24*b)*yy_zz

  fmul x3 x3 bzz9; //x3 = x3*bzz9 = xy2*yy_m_bzz9

  fmul tmp bzz9 tmp; //tmp = bzz9*tmp = yy_m_bzz9*yy_p_bzz3
  fadd y3 tmp y3  //y3 = tmp+y3 = yy_m_bzz9*yy_p_bzz3+t


val point_double (out p:point) : Stack unit
  (requires fun h ->
    live h out /\ live h p /\ eq_or_disjoint out p /\
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ point_inv h1 out /\
    point_as_nat3_proj h1 out == S.point_double (point_as_nat3_proj h0 p))

[@CInline]
let point_double out p =
  push_frame ();
  let tmp = create (5ul *! nlimb) (u64 0) in
  point_double_no_alloc out p tmp;
  pop_frame ()
