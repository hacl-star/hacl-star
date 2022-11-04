module Hacl.Impl.K256.GLV.Constants

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST

module S = Spec.K256
module SG = Hacl.Spec.K256.GLV

open Hacl.K256.Field
open Hacl.K256.Scalar
open Hacl.Impl.K256.Point

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(**
 Fast computation of [lambda]P as (beta * px, py, pz) in projective coordinates
*)

// [lambda]P = (beta * px, py, pz)
val point_mul_lambda: res:point -> p:point -> Stack unit
  (requires fun h ->
    live h res /\ live h p /\ eq_or_disjoint res p /\
    point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
    point_eval h1 res == SG.point_mul_lambda (point_eval h0 p))


// [lambda]P = (beta * px, py, pz)
val point_mul_lambda_inplace: res:point -> Stack unit
  (requires fun h ->
    live h res /\ point_inv h res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
    point_eval h1 res == SG.point_mul_lambda (point_eval h0 res))


val ecmult_endo_split:
    r1:qelem -> r2:qelem
  -> q1:point -> q2:point
  -> scalar:qelem -> q:point -> Stack (bool & bool)
  (requires fun h ->
    live h r1 /\ live h r2 /\ live h q1 /\
    live h q2 /\ live h scalar /\ live h q /\
    disjoint r1 r2 /\ disjoint r1 q1 /\ disjoint r1 q2 /\
    disjoint r1 scalar /\ disjoint r1 q /\ disjoint r2 q1 /\
    disjoint r2 q2 /\ disjoint r2 scalar /\ disjoint r2 q /\
    disjoint q1 q2 /\ disjoint q1 scalar /\ disjoint q1 q /\
    disjoint q2 scalar /\ disjoint q2 q /\
    point_inv h q /\ qas_nat h scalar < S.q)
  (ensures fun h0 (is_high1, is_high2) h1 ->
    modifies (loc r1 |+| loc r2 |+| loc q1 |+| loc q2) h0 h1 /\
    point_inv h1 q1 /\ point_inv h1 q2 /\
   (let r1_s0, r2_s0 = SG.scalar_split_lambda (qas_nat h0 scalar) in
    let r1_s, q1_s, r2_s, q2_s = SG.ecmult_endo_split (qas_nat h0 scalar) (point_eval h0 q) in
    qas_nat h1 r1 == r1_s /\ qas_nat h1 r2 == r2_s /\
    point_eval h1 q1 == q1_s /\ point_eval h1 q2 == q2_s /\
    is_high1 == S.scalar_is_high r1_s0 /\
    is_high2 == S.scalar_is_high r2_s0))
