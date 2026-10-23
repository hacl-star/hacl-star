module Spec.K256.Lemmas

open FStar.Mul

open Spec.K256.PointOps

(** The group-law lemmas hold only for valid points: `aff_point_inv` and
    `point_inv` (Spec.K256.PointOps). For points off the curve, they are
    false (github.com/hacl-star/hacl-star/issues/1079). *)

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

val lemma_aff_is_point_at_inf: p:proj_point ->
  Lemma (let px, py, pz = p in
    is_aff_point_at_inf (to_aff_point p) == (pz = 0 || (px = 0 && py = 0)))


val lemma_proj_aff_id (p:aff_point) :
  Lemma (to_aff_point (to_proj_point p) == p)


/// Valid points

val point_inv_lemma (p:proj_point) : Lemma
  (point_inv p <==>
    (let (x, y, z) = p in
     if z = 0 then x = 0 /\ y <> 0 else is_on_curve (to_aff_point p)))


val aff_point_at_inf_inv: unit -> Lemma (aff_point_inv aff_point_at_inf)


val point_at_inf_inv: unit -> Lemma (point_inv point_at_inf)


val g_inv: unit ->
  Lemma (point_inv g /\ to_aff_point g == (g_x, g_y) /\ aff_point_inv (g_x, g_y))


val to_aff_point_inv (p:proj_point) : Lemma
  (requires point_inv p)
  (ensures  aff_point_inv (to_aff_point p))


val to_proj_point_inv (p:aff_point) : Lemma
  (requires is_on_curve p)
  (ensures  point_inv (to_proj_point p))


val load_point_inv (b:Lib.ByteSequence.lbytes 64) :
  Lemma (Some? (load_point b) ==> point_inv (Some?.v (load_point b)))


val aff_point_negate_inv (p:aff_point) : Lemma
  (requires aff_point_inv p)
  (ensures  aff_point_inv (aff_point_negate p))


val point_negate_inv (p:proj_point) : Lemma
  (requires point_inv p)
  (ensures  point_inv (point_negate p))


// Multiplying the x-coordinate by a cube root of unity (the GLV endomorphism) keeps points valid
val aff_point_mul_x_inv (c:felem) (p:aff_point) : Lemma
  (requires c *% c *% c == one /\ aff_point_inv p)
  (ensures  aff_point_inv (let (x, y) = p in (c *% x, y)))


val point_mul_x_inv (c:felem) (p:proj_point) : Lemma
  (requires c *% c *% c == one /\ point_inv p)
  (ensures  point_inv (let (x, y, z) = p in (c *% x, y, z)))


/// Affine group law

val aff_point_at_inf_lemma (p:aff_point) :
  Lemma (aff_point_add p aff_point_at_inf = p)


val aff_point_add_inv_lemma (p q:aff_point) : Lemma
  (requires aff_point_inv p /\ aff_point_inv q)
  (ensures  aff_point_inv (aff_point_add p q))


val aff_point_add_assoc_lemma (p q s:aff_point) : Lemma
  (requires aff_point_inv p /\ aff_point_inv q /\ aff_point_inv s)
  (ensures  aff_point_add (aff_point_add p q) s == aff_point_add p (aff_point_add q s))


val aff_point_add_comm_lemma (p q:aff_point) :
  Lemma (aff_point_add p q = aff_point_add q p)


val aff_point_negate_lemma (p:aff_point) :
  Lemma (aff_point_add (aff_point_negate p) p == aff_point_at_inf)


val to_aff_point_at_infinity_lemma: unit ->
  Lemma (to_aff_point point_at_inf == aff_point_at_inf)


val to_aff_point_add_lemma (p q:proj_point) : Lemma
  (requires point_inv p /\ point_inv q)
  (ensures (let r = point_add p q in point_inv r /\
    to_aff_point r == aff_point_add (to_aff_point p) (to_aff_point q)))


val to_aff_point_double_lemma (p:proj_point) : Lemma
  (requires point_inv p)
  (ensures (let r = point_double p in point_inv r /\
    to_aff_point r == aff_point_add (to_aff_point p) (to_aff_point p)))


val to_aff_point_negate_lemma (p:proj_point) :
  Lemma (to_aff_point (point_negate p) == aff_point_negate (to_aff_point p))


// works when q < prime /\ prime < 2 * q
val ecdsa_verify_avoid_finv: p:proj_point{not (is_proj_point_at_inf p)} -> r:nat{0 < r /\ r < q} ->
  Lemma (let _X, _Y, _Z = p in
    (_X /% _Z % q = r) <==> ((r *% _Z = _X) || (r + q < prime && (r + q) *% _Z = _X)))
