module Hacl.Impl.PCurves.PointAdd

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Field

module S = Spec.PCurves

#reset-options "--z3rlimit 100 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val point_add_1 {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} (t0 t1 t2 t3 t4:felem) (p q:point) : Stack unit
  (requires fun h ->
    live h t0 /\ live h t1 /\ live h t2 /\
    live h t3 /\ live h t4 /\ live h p /\ live h q /\
    LowStar.Monotonic.Buffer.all_disjoint
      [loc t0; loc t1; loc t2; loc t3; loc t4 ] /\
    eq_or_disjoint p q /\ disjoint p t0 /\ disjoint p t1 /\
    disjoint p t2 /\ disjoint p t3 /\ disjoint p t4 /\
    disjoint q t0 /\ disjoint q t1 /\ disjoint q t2 /\
    disjoint q t3 /\ disjoint q t4 /\
    point_inv h p /\ point_inv h q)
  (ensures fun h0 _ h1 -> modifies (loc t0 |+| loc t1 |+| loc t2 |+| loc t3 |+| loc t4) h0 h1 /\
    as_nat h1 t0 < S.prime /\ as_nat h1 t1 < S.prime /\
    as_nat h1 t2 < S.prime /\ as_nat h1 t3 < S.prime /\
    as_nat h1 t4 < S.prime /\
    (let x1, y1, z1 = from_mont_point (as_point_nat h0 p) in
    let x2, y2, z2 = from_mont_point (as_point_nat h0 q) in
    let t0_s = S.fmul x1 x2 in
    let t1_s = S.fmul y1 y2 in
    let t2_s = S.fmul z1 z2 in
    let t3_s = S.fadd x1 y1 in
    let t4_s = S.fadd x2 y2 in
    let t3_s = S.fmul t3_s t4_s in
    let t4_s = S.fadd t0_s t1_s in

    fmont_as_nat h1 t0 == t0_s /\ fmont_as_nat h1 t1 == t1_s /\
    fmont_as_nat h1 t2 == t2_s /\ fmont_as_nat h1 t3 == t3_s /\
    fmont_as_nat h1 t4 == t4_s))

let point_add_1 {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} t0 t1 t2 t3 t4 p q =
  let x1, y1, z1 = getx p, gety p, getz p in
  let x2, y2, z2 = getx q, gety q, getz q in
  f.fmul t0 x1 x2;
  f.fmul t1 y1 y2;
  f.fmul t2 z1 z2;
  f.fadd t3 x1 y1;
  f.fadd t4 x2 y2;
  f.fmul t3 t3 t4;
  f.fadd t4 t0 t1


inline_for_extraction noextract
val point_add_2 {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} (t1 t2 t3 t4 t5:felem) (p q:point) : Stack unit
  (requires fun h ->
    live h t1 /\ live h t2 /\ live h t3 /\ live h t4 /\ live h t5 /\
    live h p /\ live h q /\
    LowStar.Monotonic.Buffer.all_disjoint [ loc t1; loc t2; loc t3; loc t4; loc t5 ] /\
    eq_or_disjoint p q /\ disjoint p t1 /\ disjoint p t2 /\
    disjoint p t3 /\ disjoint p t4 /\ disjoint p t5 /\
    disjoint q t1 /\ disjoint q t2 /\ disjoint q t3 /\
    disjoint q t4 /\ disjoint q t5 /\
    point_inv h p /\ point_inv h q /\
    as_nat h t1 < S.prime /\ as_nat h t2 < S.prime /\
    as_nat h t3 < S.prime /\ as_nat h t4 < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc t3 |+| loc t4 |+| loc t5) h0 h1 /\
    as_nat h1 t3 < S.prime /\ as_nat h1 t4 < S.prime /\ as_nat h1 t5 < S.prime /\
    (let x1, y1, z1 = from_mont_point (as_point_nat h0 p) in
    let x2, y2, z2 = from_mont_point (as_point_nat h0 q) in
    let t1_s = fmont_as_nat h0 t1 in
    let t2_s = fmont_as_nat h0 t2 in
    let t3_s = fmont_as_nat h0 t3 in
    let t4_s = fmont_as_nat h0 t4 in
    let t3_s = S.fsub t3_s t4_s in
    let t4_s = S.fadd y1 z1 in
    let t5_s = S.fadd y2 z2 in
    let t4_s = S.fmul t4_s t5_s in
    let t5_s = S.fadd t1_s t2_s in
    let t4_s = S.fsub t4_s t5_s in

    fmont_as_nat h1 t3 == t3_s /\ fmont_as_nat h1 t4 == t4_s /\
    fmont_as_nat h1 t5 == t5_s))

let point_add_2 {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} t1 t2 t3 t4 t5 p q =
  let y1, z1 = gety p, getz p in
  let y2, z2 = gety q, getz q in
  f.fsub t3 t3 t4;
  f.fadd t4 y1 z1;
  f.fadd t5 y2 z2;
  f.fmul t4 t4 t5;
  f.fadd t5 t1 t2;
  f.fsub t4 t4 t5


inline_for_extraction noextract
val point_add_3 {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} (x3 y3 t0 t2:felem) (p q:point) : Stack unit
  (requires fun h ->
    live h x3 /\ live h y3 /\ live h t0 /\ live h t2 /\
    live h p /\ live h q /\
    LowStar.Monotonic.Buffer.all_disjoint [ loc x3; loc y3; loc t0; loc t2 ] /\
    eq_or_disjoint p q /\ disjoint p x3 /\ disjoint p y3 /\
    disjoint p t0 /\ disjoint p t2 /\ disjoint q x3 /\
    disjoint q y3 /\ disjoint q t0 /\ disjoint q t2 /\
    point_inv h p /\ point_inv h q /\
    as_nat h t0 < S.prime /\ as_nat h t2 < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc x3 |+| loc y3) h0 h1 /\
    as_nat h1 x3 < S.prime /\ as_nat h1 y3 < S.prime /\
    (let x1, y1, z1 = from_mont_point (as_point_nat h0 p) in
    let x2, y2, z2 = from_mont_point (as_point_nat h0 q) in
    let t0_s = fmont_as_nat h0 t0 in
    let t2_s = fmont_as_nat h0 t2 in
    let x3_s = S.fadd x1 z1 in
    let y3_s = S.fadd x2 z2 in
    let x3_s = S.fmul x3_s y3_s in
    let y3_s = S.fadd t0_s t2_s in
    let y3_s = S.fsub x3_s y3_s in
    fmont_as_nat h1 x3 == x3_s /\ fmont_as_nat h1 y3 == y3_s))

let point_add_3 {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} x3 y3 t0 t2 p q =
  let x1, z1 = getx p, getz p in
  let x2, z2 = getx q, getz q in
  f.fadd x3 x1 z1;
  f.fadd y3 x2 z2;
  f.fmul x3 x3 y3;
  f.fadd y3 t0 t2;
  f.fsub y3 x3 y3


inline_for_extraction noextract
val point_add_4 {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} (x3 y3 z3 t1 t2:felem) : Stack unit
  (requires fun h ->
    live h x3 /\ live h y3 /\ live h z3 /\ live h t1 /\ live h t2 /\
    LowStar.Monotonic.Buffer.all_disjoint [ loc x3; loc y3; loc z3; loc t1; loc t2 ] /\
    as_nat h t1 < S.prime /\ as_nat h t2 < S.prime /\ as_nat h y3 < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc x3 |+| loc y3 |+| loc z3) h0 h1 /\
    as_nat h1 x3 < S.prime /\ as_nat h1 y3 < S.prime /\ as_nat h1 z3 < S.prime /\
    (let t1_s = fmont_as_nat h0 t1 in
    let t2_s = fmont_as_nat h0 t2 in
    let y3_s = fmont_as_nat h0 y3 in
    let z3_s = S.fmul S.b_coeff t2_s in
    let x3_s = S.fsub y3_s z3_s in
    let z3_s = S.fadd x3_s x3_s in
    let x3_s = S.fadd x3_s z3_s in
    let z3_s = S.fsub t1_s x3_s in
    let x3_s = S.fadd t1_s x3_s in
    let y3_s = S.fmul S.b_coeff y3_s in
    fmont_as_nat h1 x3 == x3_s /\ fmont_as_nat h1 y3 == y3_s /\ fmont_as_nat h1 z3 == z3_s))

let point_add_4 {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} x3 y3 z3 t1 t2 =
  fmul_by_b_coeff z3 t2;
  f.fsub x3 y3 z3;
  fdouble z3 x3;
  f.fadd x3 x3 z3;
  f.fsub z3 t1 x3;
  f.fadd x3 t1 x3;
  fmul_by_b_coeff y3 y3


inline_for_extraction noextract
val point_add_5 {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} (x3 y3 z3 t0 t1 t2:felem) : Stack unit
  (requires fun h ->
    live h x3 /\ live h y3 /\ live h z3 /\
    live h t0 /\ live h t1 /\ live h t2 /\
    LowStar.Monotonic.Buffer.all_disjoint [ loc x3; loc y3; loc z3; loc t0; loc t1; loc t2 ] /\
    as_nat h y3 < S.prime /\ as_nat h t0 < S.prime /\
    as_nat h t1 < S.prime /\ as_nat h t2 < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc y3 |+| loc t1 |+| loc t2) h0 h1 /\
    as_nat h1 t1 < S.prime /\ as_nat h1 t2 < S.prime /\ as_nat h1 y3 < S.prime /\
    (let t0_s = fmont_as_nat h0 t0 in
    let t1_s = fmont_as_nat h0 t1 in
    let t2_s = fmont_as_nat h0 t2 in
    let y3_s = fmont_as_nat h0 y3 in
    let t1_s = S.fadd t2_s t2_s in
    let t2_s = S.fadd t1_s t2_s in
    let y3_s = S.fsub y3_s t2_s in
    let y3_s = S.fsub y3_s t0_s in
    let t1_s = S.fadd y3_s y3_s in
    fmont_as_nat h1 t1 == t1_s /\ fmont_as_nat h1 t2 == t2_s /\ fmont_as_nat h1 y3 == y3_s))

let point_add_5 {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} x3 y3 z3 t0 t1 t2 =
  fdouble t1 t2;
  f.fadd t2 t1 t2;
  f.fsub y3 y3 t2;
  f.fsub y3 y3 t0;
  fdouble t1 y3


inline_for_extraction noextract
val point_add_6 {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} (x3 y3 z3 t0 t1 t2 t4:felem) : Stack unit
  (requires fun h ->
    live h x3 /\ live h y3 /\ live h z3 /\
    live h t0 /\ live h t1 /\ live h t2 /\ live h t4 /\
    LowStar.Monotonic.Buffer.all_disjoint
      [ loc x3; loc y3; loc z3; loc t0; loc t1; loc t2; loc t4 ] /\
    as_nat h y3 < S.prime /\ as_nat h t0 < S.prime /\
    as_nat h t1 < S.prime /\ as_nat h t2 < S.prime /\
    as_nat h t4 < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc y3 |+| loc t0 |+| loc t1 |+| loc t2) h0 h1 /\
    as_nat h1 t0 < S.prime /\ as_nat h1 t1 < S.prime /\
    as_nat h1 t2 < S.prime /\ as_nat h1 y3 < S.prime /\
    (let t0_s = fmont_as_nat h0 t0 in
    let t1_s = fmont_as_nat h0 t1 in
    let t2_s = fmont_as_nat h0 t2 in
    let t4_s = fmont_as_nat h0 t4 in
    let y3_s = fmont_as_nat h0 y3 in
    let y3_s = S.fadd t1_s y3_s in
    let t1_s = S.fadd t0_s t0_s in
    let t0_s = S.fadd t1_s t0_s in
    let t0_s = S.fsub t0_s t2_s in
    let t1_s = S.fmul t4_s y3_s in
    let t2_s = S.fmul t0_s y3_s in
    fmont_as_nat h1 t0 == t0_s /\ fmont_as_nat h1 t1 == t1_s /\
    fmont_as_nat h1 t2 == t2_s /\ fmont_as_nat h1 y3 == y3_s))

let point_add_6 {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} x3 y3 z3 t0 t1 t2 t4 =
  f.fadd y3 t1 y3;
  fdouble t1 t0;
  f.fadd t0 t1 t0;
  f.fsub t0 t0 t2;
  f.fmul t1 t4 y3;
  f.fmul t2 t0 y3


inline_for_extraction noextract
val point_add_7 {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} (x3 y3 z3 t0 t1 t2 t3 t4:felem) : Stack unit
  (requires fun h ->
    live h x3 /\ live h y3 /\ live h z3 /\
    live h t0 /\ live h t1 /\ live h t2 /\ live h t3 /\ live h t4 /\
    LowStar.Monotonic.Buffer.all_disjoint
      [ loc x3; loc y3; loc z3; loc t0; loc t1; loc t2; loc t3; loc t4 ] /\
    as_nat h x3 < S.prime /\ as_nat h z3 < S.prime /\
    as_nat h t0 < S.prime /\ as_nat h t1 < S.prime /\
    as_nat h t2 < S.prime /\ as_nat h t3 < S.prime /\ as_nat h t4 < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc x3 |+| loc y3 |+| loc z3 |+| loc t1) h0 h1 /\
    as_nat h1 x3 < S.prime /\ as_nat h1 y3 < S.prime /\
    as_nat h1 z3 < S.prime /\ as_nat h1 t1 < S.prime /\
    (let x3_s = fmont_as_nat h0 x3 in
    let z3_s = fmont_as_nat h0 z3 in
    let t0_s = fmont_as_nat h0 t0 in
    let t1_s = fmont_as_nat h0 t1 in
    let t2_s = fmont_as_nat h0 t2 in
    let t3_s = fmont_as_nat h0 t3 in
    let t4_s = fmont_as_nat h0 t4 in
    let y3_s = S.fmul x3_s z3_s in
    let y3_s = S.fadd y3_s t2_s in
    let x3_s = S.fmul t3_s x3_s in
    let x3_s = S.fsub x3_s t1_s in
    let z3_s = S.fmul t4_s z3_s in
    let t1_s = S.fmul t3_s t0_s in
    let z3_s = S.fadd z3_s t1_s in
    fmont_as_nat h1 x3 == x3_s /\ fmont_as_nat h1 y3 == y3_s /\
    fmont_as_nat h1 z3 == z3_s /\ fmont_as_nat h1 t1 == t1_s))

let point_add_7 {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} x3 y3 z3 t0 t1 t2 t3 t4 =
  f.fmul y3 x3 z3;
  f.fadd y3 y3 t2;
  f.fmul x3 t3 x3;
  f.fsub x3 x3 t1;
  f.fmul z3 t4 z3;
  f.fmul t1 t3 t0;
  f.fadd z3 z3 t1


inline_for_extraction noextract
val point_add_noalloc {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} :
  tmp:lbuffer uint64 (6ul *! cp.bn_limbs) -> res:point -> p:point -> q:point -> Stack unit
  (requires fun h ->
    live h p /\ live h q /\ live h res /\ live h tmp /\
    eq_or_disjoint p q /\ disjoint q res /\ disjoint p res /\
    disjoint tmp p /\ disjoint tmp q /\ disjoint tmp res /\
    point_inv h p /\ point_inv h q)
  (ensures fun h0 _ h1 -> modifies (loc res |+| loc tmp) h0 h1 /\
    point_inv h1 res /\
    from_mont_point (as_point_nat h1 res) ==
    S.point_add (from_mont_point (as_point_nat h0 p)) (from_mont_point (as_point_nat h0 q)))

#push-options "--split_queries always"
let point_add_noalloc {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} tmp res p q =
  let x3, y3, z3 = getx res, gety res, getz res in
  let t0 = sub tmp 0ul cp.bn_limbs in
  let t1 = sub tmp cp.bn_limbs cp.bn_limbs in
  assert (v (2ul *! cp.bn_limbs) = 2 * v cp.bn_limbs);
  assert (v (3ul *! cp.bn_limbs) = 3 * v cp.bn_limbs);
  assert (v (4ul *! cp.bn_limbs) = 4 * v cp.bn_limbs);
  assert (v (5ul *! cp.bn_limbs) = 5 * v cp.bn_limbs);
  assert (v (6ul *! cp.bn_limbs) = 6 * v cp.bn_limbs);
  let t2 = sub tmp (2ul *! cp.bn_limbs) cp.bn_limbs in
  let t3 = sub tmp (3ul *! cp.bn_limbs) cp.bn_limbs in
  let t4 = sub tmp (4ul *! cp.bn_limbs) cp.bn_limbs in
  let t5 = sub tmp (5ul *! cp.bn_limbs) cp.bn_limbs in
  point_add_1 t0 t1 t2 t3 t4 p q;
  point_add_2 t1 t2 t3 t4 t5 p q;
  point_add_3 x3 y3 t0 t2 p q;
  point_add_4 x3 y3 z3 t1 t2;
  point_add_5 x3 y3 z3 t0 t1 t2;
  point_add_6 x3 y3 z3 t0 t1 t2 t4;
  point_add_7 x3 y3 z3 t0 t1 t2 t3 t4
#pop-options

let point_add {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} res p q =
  push_frame ();
  let tmp = create (9ul *! cp.bn_limbs) (u64 0) in
  let t0 = sub tmp 0ul (6ul *! cp.bn_limbs) in
  let t1 = sub tmp (6ul *! cp.bn_limbs) (3ul *! cp.bn_limbs) in
  point_add_noalloc t0 t1 p q;
  copy res t1;
  pop_frame ()
