module Spec.Ed25519.Lemmas

open FStar.Mul

open Spec.Curve25519
open Spec.Ed25519.PointOps

module LM = Lib.NatMod

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

val aff_point_add_lemma: p:aff_point -> q:aff_point -> Lemma
  (requires is_on_curve p /\ is_on_curve q)
  (ensures  is_on_curve (aff_point_add p q))

val aff_point_add_assoc_lemma: p:aff_point -> q:aff_point -> s:aff_point ->
  Lemma (aff_point_add (aff_point_add p q) s == aff_point_add p (aff_point_add q s))

val aff_point_at_infinity_lemma: p:aff_point ->
  Lemma (aff_point_add p aff_point_at_infinity == p)

val aff_point_add_comm_lemma: p:aff_point -> q:aff_point ->
  Lemma (aff_point_add p q == aff_point_add q p)

val aff_point_double_lemma: p:aff_point{is_on_curve p} ->
  Lemma (aff_point_double p == aff_point_add p p)

val aff_point_negate_lemma: p:aff_point -> Lemma
  (requires is_on_curve p)
  (ensures  is_on_curve (aff_point_negate p))


val to_aff_point_at_infinity_lemma: unit ->
  Lemma (to_aff_point point_at_infinity == aff_point_at_infinity)

val to_aff_point_add_lemma: p:ext_point -> q:ext_point -> Lemma
  (requires point_inv p /\ point_inv q)
  (ensures (let r = point_add p q in point_inv r /\
    to_aff_point r == aff_point_add (to_aff_point p) (to_aff_point q)))

val to_aff_point_double_lemma: p:ext_point -> Lemma
  (requires point_inv p)
  (ensures (let r = point_double p in point_inv r /\
    to_aff_point r == aff_point_double (to_aff_point p) /\
    to_aff_point r == aff_point_add (to_aff_point p) (to_aff_point p)))

val to_aff_point_negate: p:ext_point -> Lemma
  (requires point_inv p)
  (ensures (let r = point_negate p in point_inv r /\
    to_aff_point r == aff_point_negate (to_aff_point p)))


val aff_g_is_on_curve: unit -> Lemma (is_on_curve aff_g)
val g_is_on_curve: unit -> Lemma (point_inv g /\ to_aff_point g == aff_g)

val point_decompress_lemma: s:Lib.ByteSequence.lbytes 32 ->
  Lemma (let p = point_decompress s in Some? p ==> point_inv (Some?.v p))
