module Hacl.Impl.P256.PointDouble

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Field

module S = Spec.P256

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

inline_for_extraction noextract
val point_double_1 (t0 t1 t2 t3 t4:felem) (p:point) : Stack unit
  (requires fun h ->
    live h t0 /\ live h t1 /\ live h t2 /\
    live h t3 /\ live h t4 /\ live h p /\
    LowStar.Monotonic.Buffer.all_disjoint
      [loc t0; loc t1; loc t2; loc t3; loc t4; loc p ] /\
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc t0 |+| loc t1 |+| loc t2 |+| loc t3 |+| loc t4) h0 h1 /\
    as_nat h1 t0 < S.prime /\ as_nat h1 t1 < S.prime /\
    as_nat h1 t2 < S.prime /\ as_nat h1 t3 < S.prime /\
    as_nat h1 t4 < S.prime /\
    (let x, y, z = from_mont_point (as_point_nat h0 p) in
    let t0_s = S.fmul x x in
    let t1_s = S.fmul y y in
    let t2_s = S.fmul z z in
    let t3_s = S.fmul x y in
    let t3_s = S.fadd t3_s t3_s in
    let t4_s = S.fmul y z in
    fmont_as_nat h1 t0 == t0_s /\ fmont_as_nat h1 t1 == t1_s /\
    fmont_as_nat h1 t2 == t2_s /\ fmont_as_nat h1 t3 == t3_s /\
    fmont_as_nat h1 t4 == t4_s))

let point_double_1 t0 t1 t2 t3 t4 p =
  let x, y, z = getx p, gety p, getz p in
  fsqr t0 x;
  fsqr t1 y;
  fsqr t2 z;
  fmul t3 x y;
  fdouble t3 t3;
  fmul t4 y z


inline_for_extraction noextract
val point_double_2 (x3 y3 z3 t2:felem) : Stack unit
  (requires fun h ->
    live h x3 /\ live h y3 /\ live h z3 /\ live h t2 /\
    LowStar.Monotonic.Buffer.all_disjoint [ loc x3; loc y3; loc z3; loc t2 ] /\
    as_nat h z3 < S.prime /\ as_nat h t2 < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc x3 |+| loc y3 |+| loc z3) h0 h1 /\
    as_nat h1 x3 < S.prime /\ as_nat h1 y3 < S.prime /\ as_nat h1 z3 < S.prime /\
    (let z3_s = fmont_as_nat h0 z3 in
    let t2_s = fmont_as_nat h0 t2 in
    let z3_s = S.fadd z3_s z3_s in
    let y3_s = S.fmul S.b_coeff t2_s in
    let y3_s = S.fsub y3_s z3_s in
    let x3_s = S.fadd y3_s y3_s in
    let y3_s = S.fadd x3_s y3_s in
    fmont_as_nat h1 x3 == x3_s /\ fmont_as_nat h1 y3 == y3_s /\
    fmont_as_nat h1 z3 == z3_s))

let point_double_2 x3 y3 z3 t2 =
  fdouble z3 z3;
  fmul_by_b_coeff y3 t2;
  fsub y3 y3 z3;
  fdouble x3 y3;
  fadd y3 x3 y3


inline_for_extraction noextract
val point_double_3 (x3 y3 t1 t2 t3:felem) : Stack unit
  (requires fun h ->
    live h x3 /\ live h y3 /\ live h t1 /\ live h t2 /\ live h t3 /\
    LowStar.Monotonic.Buffer.all_disjoint [ loc x3; loc y3; loc t1; loc t2; loc t3 ] /\
    as_nat h t1 < S.prime /\ as_nat h t2 < S.prime /\
    as_nat h t3 < S.prime /\ as_nat h y3 < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc x3 |+| loc y3 |+| loc t2 |+| loc t3) h0 h1 /\
    as_nat h1 x3 < S.prime /\ as_nat h1 y3 < S.prime /\
    as_nat h1 t2 < S.prime /\ as_nat h1 t3 < S.prime /\
    (let t1_s = fmont_as_nat h0 t1 in
    let t2_s = fmont_as_nat h0 t2 in
    let t3_s = fmont_as_nat h0 t3 in
    let y3_s = fmont_as_nat h0 y3 in
    let x3_s = S.fsub t1_s y3_s in
    let y3_s = S.fadd t1_s y3_s in
    let y3_s = S.fmul x3_s y3_s in
    let x3_s = S.fmul x3_s t3_s in
    let t3_s = S.fadd t2_s t2_s in
    let t2_s = S.fadd t2_s t3_s in

    fmont_as_nat h1 x3 == x3_s /\ fmont_as_nat h1 y3 == y3_s /\
    fmont_as_nat h1 t2 == t2_s /\ fmont_as_nat h1 t3 == t3_s))

let point_double_3 x3 y3 t1 t2 t3 =
  fsub x3 t1 y3;
  fadd y3 t1 y3;
  fmul y3 x3 y3;
  fmul x3 x3 t3;
  fdouble t3 t2;
  fadd t2 t2 t3


inline_for_extraction noextract
val point_double_4 (z3 t0 t2 t3:felem) : Stack unit
  (requires fun h ->
    live h z3 /\ live h t0 /\ live h t2 /\ live h t3 /\
    LowStar.Monotonic.Buffer.all_disjoint [ loc z3; loc t0; loc t2; loc t3 ] /\
    as_nat h z3 < S.prime /\ as_nat h t0 < S.prime /\ as_nat h t2 < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc z3 |+| loc t3) h0 h1 /\
    as_nat h1 z3 < S.prime /\ as_nat h1 t3 < S.prime /\
    (let z3_s = fmont_as_nat h0 z3 in
    let t0_s = fmont_as_nat h0 t0 in
    let t2_s = fmont_as_nat h0 t2 in
    let z3_s = S.fmul S.b_coeff z3_s in
    let z3_s = S.fsub z3_s t2_s in
    let z3_s = S.fsub z3_s t0_s in
    let t3_s = S.fadd z3_s z3_s in
    let z3_s = S.fadd z3_s t3_s in
    fmont_as_nat h1 z3 == z3_s /\ fmont_as_nat h1 t3 == t3_s))

let point_double_4 z3 t0 t2 t3 =
  fmul_by_b_coeff z3 z3;
  fsub z3 z3 t2;
  fsub z3 z3 t0;
  fdouble t3 z3;
  fadd z3 z3 t3


inline_for_extraction noextract
val point_double_5 (y3 z3 t0 t2 t3:felem) : Stack unit
  (requires fun h ->
    live h y3 /\ live h z3 /\ live h t0 /\ live h t2 /\ live h t3 /\
    LowStar.Monotonic.Buffer.all_disjoint [ loc y3; loc z3; loc t0; loc t2; loc t3 ] /\
    as_nat h y3 < S.prime /\ as_nat h z3 < S.prime /\
    as_nat h t0 < S.prime /\ as_nat h t2 < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc y3 |+| loc t0 |+| loc t3) h0 h1 /\
    as_nat h1 y3 < S.prime /\ as_nat h1 t3 < S.prime /\
    (let t0_s = fmont_as_nat h0 t0 in
    let t2_s = fmont_as_nat h0 t2 in
    let y3_s = fmont_as_nat h0 y3 in
    let z3_s = fmont_as_nat h0 z3 in
    let t3_s = S.fadd t0_s t0_s in
    let t0_s = S.fadd t3_s t0_s in
    let t0_s = S.fsub t0_s t2_s in
    let t0_s = S.fmul t0_s z3_s in
    let y3_s = S.fadd y3_s t0_s in
    fmont_as_nat h1 y3 == y3_s /\ fmont_as_nat h1 t0 == t0_s /\ fmont_as_nat h1 t3 == t3_s))

let point_double_5 y3 z3 t0 t2 t3 =
  fdouble t3 t0;
  fadd t0 t3 t0;
  fsub t0 t0 t2;
  fmul t0 t0 z3;
  fadd y3 y3 t0


inline_for_extraction noextract
val point_double_6 (x3 z3 t0 t1 t4:felem) : Stack unit
  (requires fun h ->
    live h x3 /\ live h z3 /\ live h t0 /\ live h t1 /\ live h t4 /\
    LowStar.Monotonic.Buffer.all_disjoint [ loc x3; loc z3; loc t0; loc t1; loc t4 ] /\
    as_nat h x3 < S.prime /\ as_nat h z3 < S.prime /\
    as_nat h t1 < S.prime /\ as_nat h t4 < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc x3 |+| loc z3 |+| loc t0) h0 h1 /\
    as_nat h1 x3 < S.prime /\ as_nat h1 z3 < S.prime /\ as_nat h1 t0 < S.prime /\
    (let t1_s = fmont_as_nat h0 t1 in
    let t4_s = fmont_as_nat h0 t4 in
    let x3_s = fmont_as_nat h0 x3 in
    let z3_s = fmont_as_nat h0 z3 in
    let t0_s = S.fadd t4_s t4_s in
    let z3_s = S.fmul t0_s z3_s in
    let x3_s = S.fsub x3_s z3_s in
    let z3_s = S.fmul t0_s t1_s in
    let z3_s = S.fadd z3_s z3_s in
    let z3_s = S.fadd z3_s z3_s in
    fmont_as_nat h1 z3 == z3_s /\ fmont_as_nat h1 x3 == x3_s /\ fmont_as_nat h1 t0 == t0_s))

let point_double_6 x3 z3 t0 t1 t4 =
  fdouble t0 t4;
  fmul z3 t0 z3;
  fsub x3 x3 z3;
  fmul z3 t0 t1;
  fdouble z3 z3;
  fdouble z3 z3


inline_for_extraction noextract
val point_double_noalloc: tmp:lbuffer uint64 20ul -> res:point -> p:point -> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ live h tmp /\
    eq_or_disjoint p res /\ disjoint tmp res /\ disjoint tmp p /\
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc res |+| loc tmp)  h0 h1 /\
    point_inv h1 res /\
    from_mont_point (as_point_nat h1 res) ==
      S.point_double (from_mont_point (as_point_nat h0 p)))

let point_double_noalloc tmp res p =
  let x, z = getx p, getz p in
  let x3, y3, z3 = getx res, gety res, getz res in
  let t0 = sub tmp 0ul 4ul in
  let t1 = sub tmp 4ul 4ul in
  let t2 = sub tmp 8ul 4ul in
  let t3 = sub tmp 12ul 4ul in
  let t4 = sub tmp 16ul 4ul in
  point_double_1 t0 t1 t2 t3 t4 p;
  fmul z3 x z;
  point_double_2 x3 y3 z3 t2;
  point_double_3 x3 y3 t1 t2 t3;
  point_double_4 z3 t0 t2 t3;
  point_double_5 y3 z3 t0 t2 t3;
  point_double_6 x3 z3 t0 t1 t4


[@CInline]
let point_double res p =
  push_frame ();
  let tmp = create 20ul (u64 0) in
  point_double_noalloc tmp res p;
  pop_frame ()
