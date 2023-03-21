module Hacl.Impl.P256.PointDouble

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Field

module S = Spec.P256
module SM = Hacl.Spec.P256.MontgomeryMultiplication
module SL = Hacl.Spec.P256.Math

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

inline_for_extraction noextract
val point_double_a_b_g_d:
    p:point
  -> alpha:felem -> beta:felem -> gamma:felem -> delta:felem
  -> tmp:felem ->
  Stack unit
  (requires fun h ->
    live h p /\ live h alpha /\ live h beta /\
    live h gamma /\ live h delta /\ live h tmp /\
    LowStar.Monotonic.Buffer.all_disjoint
      [loc p; loc alpha; loc beta; loc gamma; loc delta; loc tmp] /\
    point_inv h p)
  (ensures fun h0 _ h1 ->
    modifies (loc alpha |+| loc beta |+| loc gamma |+| loc delta |+| loc tmp) h0 h1 /\
    as_nat h1 alpha < S.prime /\ as_nat h1 beta < S.prime /\
    as_nat h1 gamma < S.prime /\ as_nat h1 delta < S.prime /\
   (let x, y, z = SM.from_mont_point (as_point_nat h0 p) in
    fmont_as_nat h1 delta = S.fmul z z /\
    fmont_as_nat h1 gamma = S.fmul y y /\
    fmont_as_nat h1 beta = S.fmul x (fmont_as_nat h1 gamma) /\
    fmont_as_nat h1 alpha =
      S.fmul (S.fmul 3 (S.fsub x (fmont_as_nat h1 delta))) (S.fadd x (fmont_as_nat h1 delta))))

let point_double_a_b_g_d p alpha beta gamma delta tmp =
  let px = getx p in
  let py = gety p in
  let pz = getz p in

  let h0 = ST.get () in
  fsqr pz delta;      // delta = z * z
  fsqr py gamma;      // gamma = y * y
  fmul px gamma beta; // beta = x * gamma
  let h1 = ST.get () in
  assert (fmont_as_nat h1 delta = S.fmul (fmont_as_nat h0 pz) (fmont_as_nat h0 pz));
  assert (fmont_as_nat h1 gamma = S.fmul (fmont_as_nat h0 py) (fmont_as_nat h0 py));
  assert (fmont_as_nat h1 beta = S.fmul (fmont_as_nat h0 px) (fmont_as_nat h1 gamma));

  fsub px delta alpha;   // a0 = x - delta
  let h2 = ST.get () in
  assert (fmont_as_nat h2 alpha = S.fsub (fmont_as_nat h0 px) (fmont_as_nat h1 delta));
  fmul_by_3 alpha tmp;
  let h3 = ST.get () in
  assert (fmont_as_nat h3 tmp = S.fmul 3 (fmont_as_nat h2 alpha));
  fadd px delta alpha;   // a1 = x + delta
  let h4 = ST.get () in
  assert (fmont_as_nat h4 alpha = S.fadd (fmont_as_nat h0 px) (fmont_as_nat h1 delta));
  fmul tmp alpha alpha


inline_for_extraction noextract
val point_double_x3: x3:felem -> alpha:felem -> beta:felem -> tmp:felem ->
  Stack unit
  (requires fun h ->
    live h x3 /\ live h alpha /\ live h beta /\ live h tmp /\
    LowStar.Monotonic.Buffer.all_disjoint
      [loc x3; loc alpha; loc beta; loc tmp] /\
    as_nat h alpha < S.prime /\ as_nat h beta < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc x3 |+| loc beta |+| loc tmp) h0 h1 /\
    as_nat h1 beta < S.prime /\ as_nat h1 x3 < S.prime /\
    fmont_as_nat h1 beta == S.fmul 4 (fmont_as_nat h0 beta) /\
    fmont_as_nat h1 x3 == S.fsub (S.fmul (fmont_as_nat h0 alpha) (fmont_as_nat h0 alpha))
      (S.fmul 8 (fmont_as_nat h0 beta)))

let point_double_x3 x3 alpha beta tmp =
  let h0 = ST.get () in
  fsqr alpha x3;          // x3 = alpha * alpha
  fmul_by_4 beta beta;    // beta = 4 * beta
  let h1 = ST.get () in
  assert (fmont_as_nat h1 x3 = S.fmul (fmont_as_nat h0 alpha) (fmont_as_nat h0 alpha));
  assert (fmont_as_nat h1 beta = S.fmul 4 (fmont_as_nat h0 beta));
  fdouble beta tmp;      // tmp = 8 * beta
  let h2 = ST.get () in
  assert (fmont_as_nat h2 tmp = S.fmul 2 (S.fmul 4 (fmont_as_nat h0 beta)));
  Math.Lemmas.lemma_mod_mul_distr_r 2 (4 * fmont_as_nat h0 beta) S.prime;
  assert (fmont_as_nat h2 tmp = S.fmul 8 (fmont_as_nat h0 beta));
  fsub x3 tmp x3         // x3 = alpha * alpha - 8 * beta


inline_for_extraction noextract
val point_double_z3: z3:felem -> py:felem -> pz:felem -> gamma:felem -> delta:felem ->
  Stack unit
  (requires fun h ->
    live h z3 /\ live h py /\ live h pz /\ live h gamma /\ live h delta /\
    eq_or_disjoint pz z3 /\ disjoint z3 gamma /\ disjoint z3 delta /\
    disjoint py z3 /\ disjoint py pz /\
    as_nat h gamma < S.prime /\ as_nat h delta < S.prime /\
    as_nat h py < S.prime /\ as_nat h pz < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc z3) h0 h1 /\
    as_nat h1 z3 < S.prime /\
   (let yz = S.fadd (fmont_as_nat h0 py) (fmont_as_nat h0 pz) in
    fmont_as_nat h1 z3 =
      S.fsub (S.fsub (S.fmul yz yz) (fmont_as_nat h0 delta)) (fmont_as_nat h0 gamma)))

let point_double_z3 z3 py pz gamma delta =
  let h0 = ST.get () in
  fadd py pz z3;  // z3 = py + pz
  fsqr z3 z3;     // z3 = (py + pz) * (py + pz)
  let h1 = ST.get () in
  assert (let yz = S.fadd (fmont_as_nat h0 py) (fmont_as_nat h0 pz) in
    fmont_as_nat h1 z3 = S.fmul yz yz);

  fsub z3 delta z3;  // z3 = (py + pz) ** 2 - delta
  fsub z3 gamma z3   // z3 = (py + pz) ** 2 - delta - gamma


inline_for_extraction noextract
val point_double_y3: y3:felem -> x3:felem -> alpha:felem -> gamma:felem -> beta:felem ->
  Stack unit
  (requires fun h ->
    live h y3 /\ live h x3 /\ live h alpha /\ live h gamma /\ live h beta /\
    LowStar.Monotonic.Buffer.all_disjoint
      [loc y3; loc x3; loc alpha; loc gamma; loc beta] /\
    as_nat h x3 < S.prime /\ as_nat h alpha < S.prime /\
    as_nat h gamma < S.prime /\ as_nat h beta < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc y3 |+| loc gamma) h0 h1 /\
    as_nat h1 y3 < S.prime /\
    fmont_as_nat h1 y3 ==
    S.fsub
      (S.fmul (fmont_as_nat h0 alpha) (S.fsub (fmont_as_nat h0 beta) (fmont_as_nat h0 x3)))
      (S.fmul (S.fmul 8 (fmont_as_nat h0 gamma)) (fmont_as_nat h0 gamma)))

let point_double_y3 y3 x3 alpha gamma beta =
  let h0 = ST.get () in
  fsub beta x3 y3;      // y3 = beta - x3
  fmul alpha y3 y3;     // y3 = alpha * (beta - x3)
  let h1 = ST.get () in
  assert (fmont_as_nat h1 y3 =
    S.fmul (fmont_as_nat h0 alpha) (S.fsub (fmont_as_nat h0 beta) (fmont_as_nat h0 x3)));

  fsqr gamma gamma;
  fmul_by_8 gamma gamma; // gamma = 8 * gamma * gamma
  let h2 = ST.get () in
  assert (let g = fmont_as_nat h0 gamma in
    fmont_as_nat h2 gamma == S.fmul 8 (S.fmul g g));
  Lib.NatMod.lemma_mul_mod_assoc #S.prime 8 (fmont_as_nat h0 gamma) (fmont_as_nat h0 gamma);
  fsub y3 gamma y3       // y3 = alpha * (beta - x3) - 8 * gamma * gamma


[@CInline]
let point_double p res tmp =
  let px = getx p in
  let py = gety p in
  let pz = getz p in

  let x3 = getx res in
  let y3 = gety res in
  let z3 = getz res in

  let delta = sub tmp 0ul 4ul in
  let gamma = sub tmp 4ul 4ul in
  let beta  = sub tmp 8ul 4ul in
  let alpha = sub tmp 12ul 4ul in
  let ftmp  = sub tmp 16ul 4ul in

  point_double_a_b_g_d p alpha beta gamma delta ftmp;
  point_double_x3 x3 alpha beta ftmp;
  point_double_z3 z3 py pz gamma delta;
  point_double_y3 y3 x3 alpha gamma beta
