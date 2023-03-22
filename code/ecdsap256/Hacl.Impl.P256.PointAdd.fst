module Hacl.Impl.P256.PointAdd

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Field

module S = Spec.P256
module SM = Hacl.Spec.P256.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val point_add_u12_s12: u1:felem -> u2:felem -> s1:felem -> s2:felem -> p:point -> q:point ->
  Stack unit
  (requires fun h ->
    live h u1 /\ live h u2 /\ live h s1 /\ live h s2 /\ live h p /\ live h q /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc u1; loc u2; loc s1; loc s2] /\
    point_inv h p /\ point_inv h q)
  (ensures fun h0 _ h1 ->
    modifies (loc u1 |+| loc u2 |+| loc s1 |+| loc s2) h0 h1 /\
    as_nat h1 u1 < S.prime /\ as_nat h1 u2 < S.prime /\
    as_nat h1 s1 < S.prime /\ as_nat h1 s2 < S.prime /\
    (let px, py, pz = SM.from_mont_point (as_point_nat h0 p) in
    let qx, qy, qz = SM.from_mont_point (as_point_nat h0 q) in
    let z2z2 = S.fmul qz qz in
    let z1z1 = S.fmul pz pz in
    fmont_as_nat h1 u1 == S.fmul px z2z2 /\
    fmont_as_nat h1 u2 == S.fmul qx z1z1 /\
    fmont_as_nat h1 s1 == S.fmul (S.fmul py qz) z2z2 /\
    fmont_as_nat h1 s2 == S.fmul (S.fmul qy pz) z1z1))

let point_add_u12_s12 u1 u2 s1 s2 p q =
  let px = getx p in
  let py = gety p in
  let pz = getz p in

  let qx = getx q in
  let qy = gety q in
  let qz = getz q in

  let h0 = ST.get () in
  fsqr s1 qz;           // s1 = z2z2 = qz * qz
  fsqr s2 pz;           // s2 = z1z1 = pz * pz
  let h1 = ST.get () in
  assert (fmont_as_nat h1 s1 == S.fmul (fmont_as_nat h0 qz) (fmont_as_nat h0 qz));
  assert (fmont_as_nat h1 s2 == S.fmul (fmont_as_nat h0 pz) (fmont_as_nat h0 pz));

  fmul u1 px s1;        // u1 = px * z2z2
  fmul u2 qx s2;        // u2 = qx * z1z1
  let h2 = ST.get () in
  assert (fmont_as_nat h2 u1 == S.fmul (fmont_as_nat h0 px) (fmont_as_nat h1 s1));
  assert (fmont_as_nat h2 u2 == S.fmul (fmont_as_nat h0 qx) (fmont_as_nat h1 s2));

  fmul s1 qz s1;
  fmul s1 py s1;
  let h3 = ST.get () in
  assert (fmont_as_nat h3 s1 ==
    S.fmul (fmont_as_nat h0 py) (S.fmul (fmont_as_nat h0 qz) (fmont_as_nat h1 s1)));
  Lib.NatMod.lemma_mul_mod_assoc #S.prime
    (fmont_as_nat h0 py) (fmont_as_nat h0 qz) (fmont_as_nat h1 s1);

  fmul s2 pz s2;
  fmul s2 qy s2;
  let h4 = ST.get () in
  assert (fmont_as_nat h4 s2 ==
    S.fmul (fmont_as_nat h0 qy) (S.fmul (fmont_as_nat h0 pz) (fmont_as_nat h1 s2)));
  Lib.NatMod.lemma_mul_mod_assoc #S.prime
    (fmont_as_nat h0 qy) (fmont_as_nat h0 pz) (fmont_as_nat h1 s2)


inline_for_extraction noextract
val point_add_hhh_uhh_h_r:
    h:felem -> r:felem -> hhh:felem
  -> u1:felem -> u2:felem -> s1:felem -> s2:felem ->
  Stack unit
  (requires fun h0 ->
    live h0 h /\ live h0 r /\ live h0 hhh /\
    live h0 u1 /\ live h0 u2 /\ live h0 s1 /\ live h0 s2 /\
    LowStar.Monotonic.Buffer.all_disjoint
      [loc u1; loc u2; loc s1; loc s2; loc h; loc r; loc hhh] /\
    as_nat h0 u1 < S.prime /\ as_nat h0 u2 < S.prime /\
    as_nat h0 s1 < S.prime /\ as_nat h0 s2 < S.prime)
  (ensures fun h0 _ h1 ->
    modifies (loc h |+| loc r |+| loc u1 |+| loc hhh) h0 h1 /\
    as_nat h1 h < S.prime /\ as_nat h1 r < S.prime /\
    as_nat h1 u1 < S.prime /\ as_nat h1 hhh < S.prime /\
    fmont_as_nat h1 h == S.fsub (fmont_as_nat h0 u2) (fmont_as_nat h0 u1) /\
    fmont_as_nat h1 r == S.fsub (fmont_as_nat h0 s2) (fmont_as_nat h0 s1) /\
    fmont_as_nat h1 u1 ==
      S.fmul (fmont_as_nat h0 u1) (S.fmul (fmont_as_nat h1 h) (fmont_as_nat h1 h)) /\
    fmont_as_nat h1 hhh ==
      S.fmul (S.fmul (fmont_as_nat h1 h) (fmont_as_nat h1 h)) (fmont_as_nat h1 h))

let point_add_hhh_uhh_h_r h r hhh u1 u2 s1 s2 =
  let h0 = ST.get () in
  fsub h u2 u1;     // h = u2 - u1
  fsub r s2 s1;     // r = s2 - s1
  let h1 = ST.get () in
  assert (fmont_as_nat h1 h == S.fsub (fmont_as_nat h0 u2) (fmont_as_nat h0 u1));
  assert (fmont_as_nat h1 r == S.fsub (fmont_as_nat h0 s2) (fmont_as_nat h0 s1));

  fsqr hhh h;      // hh = h * h
  fmul u1 hhh u1;  // u1hh = u1 * hh
  fmul hhh h hhh   // hhh = hh * h


inline_for_extraction noextract
val point_add_x3: x3:felem -> hhh:felem -> u1:felem -> r:felem -> tmp:felem ->
  Stack unit
  (requires fun h0 ->
    live h0 x3 /\ live h0 hhh /\ live h0 u1 /\ live h0 r /\ live h0 tmp /\
    LowStar.Monotonic.Buffer.all_disjoint [loc x3; loc hhh; loc u1; loc r; loc tmp] /\
    as_nat h0 hhh < S.prime /\ as_nat h0 u1 < S.prime /\ as_nat h0 r < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc x3 |+| loc tmp) h0 h1 /\
    as_nat h1 x3 < S.prime /\
    fmont_as_nat h1 x3 ==
      S.fsub
        (S.fsub (S.fmul (fmont_as_nat h0 r) (fmont_as_nat h0 r)) (fmont_as_nat h0 hhh))
        (S.fmul 2 (fmont_as_nat h0 u1)))

let point_add_x3 x3 hhh u1 r tmp =
  fsqr x3 r;       // rr = r * r
  fsub x3 x3 hhh;  // rr - hhh
  fdouble tmp u1;  // 2 * u1
  fsub x3 x3 tmp   // rr - hhh - 2 * u1


inline_for_extraction noextract
val point_add_y3: y3:felem -> s1:felem -> hhh:felem -> u1:felem -> x3:felem -> r:felem ->
  Stack unit
  (requires fun h ->
    live h y3 /\ live h s1 /\ live h hhh /\ live h u1 /\ live h x3 /\ live h r /\
    LowStar.Monotonic.Buffer.all_disjoint [loc y3; loc s1; loc hhh; loc u1; loc x3; loc r] /\
    as_nat h s1 < S.prime /\ as_nat h hhh < S.prime /\
    as_nat h u1 < S.prime /\ as_nat h x3 < S.prime /\ as_nat h r < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc y3 |+| loc u1) h0 h1 /\
    as_nat h1 y3 < S.prime /\
    fmont_as_nat h1 y3 =
      S.fsub
        (S.fmul (fmont_as_nat h0 r) (S.fsub (fmont_as_nat h0 u1) (fmont_as_nat h0 x3)))
        (S.fmul (fmont_as_nat h0 s1) (fmont_as_nat h0 hhh)))

let point_add_y3 y3 s1 hhh u1 x3 r =
  fmul y3 s1 hhh;  // s1 * hhh
  fsub u1 u1 x3;   // u1 - x3
  fmul u1 r u1;    // r * (u1 - x3)
  fsub y3 u1 y3    // r * (u1 - x3) - s1 * hhh


inline_for_extraction noextract
val point_add_z3: z3:felem -> z1:felem -> z2:felem -> h:felem -> Stack unit
  (requires fun h0 ->
    live h0 z3 /\ live h0 z1 /\ live h0 z2 /\ live h0 h /\
    eq_or_disjoint z1 z3 /\ eq_or_disjoint z2 z3 /\ eq_or_disjoint z1 z2 /\
    disjoint h z1 /\ disjoint h z2 /\ disjoint h z3 /\
    as_nat h0 z1 < S.prime /\ as_nat h0 z2 < S.prime /\ as_nat h0 h < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc z3 |+| loc h) h0 h1 /\
    as_nat h1 z3 < S.prime /\
    fmont_as_nat h1 z3 ==
      S.fmul (S.fmul (fmont_as_nat h0 h) (fmont_as_nat h0 z1)) (fmont_as_nat h0 z2))

let point_add_z3 z3 z1 z2 h =
  fmul h z1 h;
  fmul z3 h z2


inline_for_extraction noextract
val point_add_no_point_at_inf:
  p:point -> q:point -> res:point -> tmp:lbuffer uint64 32ul -> Stack unit
  (requires fun h ->
    live h p /\ live h q /\ live h res /\ live h tmp /\
    eq_or_disjoint q res /\ disjoint p q /\ disjoint p tmp /\
    disjoint q tmp /\ disjoint p res /\ disjoint res tmp /\
    point_inv h p /\ point_inv h q)
  (ensures fun h0 _ h1 -> modifies (loc tmp |+| loc res) h0 h1 /\
    point_inv h1 res /\
    SM.from_mont_point (as_point_nat h1 res) == S.point_add_no_point_at_inf
      (SM.from_mont_point (as_point_nat h0 p)) (SM.from_mont_point (as_point_nat h0 q)))

let point_add_no_point_at_inf p q res tmp =
  let z1 = getz p in
  let z2 = getz q in

  let u1 = sub tmp 0ul 4ul in
  let u2 = sub tmp 4ul 4ul in
  let s1 = sub tmp 8ul 4ul in
  let s2 = sub tmp 12ul 4ul in

  let h = sub tmp 16ul 4ul in
  let r = sub tmp 20ul 4ul in
  let hhh = sub tmp 24ul 4ul in
  let ftmp = sub tmp 28ul 4ul in

  let x3 = getx res in
  let y3 = gety res in
  let z3 = getz res in

  point_add_u12_s12 u1 u2 s1 s2 p q;
  point_add_hhh_uhh_h_r h r hhh u1 u2 s1 s2;
  point_add_x3 x3 hhh u1 r ftmp;
  point_add_y3 y3 s1 hhh u1 x3 r;
  point_add_z3 z3 z1 z2 h


inline_for_extraction noextract
val point_add_condional_branch: p:point -> q:point -> res:point -> Stack unit
  (requires fun h ->
    live h p /\ live h q /\ live h res /\
    disjoint p res /\ disjoint q res /\ disjoint p q /\
    point_inv h p /\ point_inv h q /\ point_inv h res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
   (let p = SM.from_mont_point (as_point_nat h0 p) in
    let q = SM.from_mont_point (as_point_nat h0 q) in
    let r = SM.from_mont_point (as_point_nat h0 res) in
    SM.from_mont_point (as_point_nat h1 res) ==
      (if S.is_point_at_inf q then p else if S.is_point_at_inf p then q else r)))

let point_add_condional_branch p q res =
  copy_point_conditional res q p;
  copy_point_conditional res p q


[@CInline]
let point_add p q res tmp =
  point_add_no_point_at_inf p q res tmp;
  point_add_condional_branch p q res
