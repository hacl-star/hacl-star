module Hacl.Impl.P256.PointDouble

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Tactics
open FStar.Tactics.Canon

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Field
open Hacl.Spec.P256.Math
open Hacl.Spec.P256.MontgomeryMultiplication

module S = Spec.P256

#set-options "--z3rlimit 300 --ifuel 0 --fuel 0"

val lemma_x3_0: x: int -> y: int -> z: int -> Lemma (
  ((3 * (x - (z * z % S.prime)) * (x + (z * z % S.prime)) % S.prime) * (3 * (x - (z * z % S.prime)) * (x + (z * z % S.prime)) % S.prime)  - 8 * (x * (y * y % S.prime) % S.prime)) % S.prime ==  ((3 * (x - (z * z % S.prime)) * (x + (z * z % S.prime)) % S.prime) * (3 * (x - (z * z % S.prime)) * (x + (z * z % S.prime)) % S.prime) - 8 * x * y * y) % S.prime)

let lemma_x3_0 x y z =
  let t0 = (3 * (x - (z * z % S.prime)) * (x + (z * z % S.prime)) % S.prime) in
  calc (==)
  {
    (t0 * t0 - 8 * (x * (y * y % S.prime) % S.prime)) % S.prime;
    (==) {lemma_mod_mul_distr_r x (y * y) S.prime}
    (t0 * t0 - 8 * ((x * (y * y)) % S.prime)) % S.prime;
    (==) {assert_by_tactic (x * (y * y) == x * y * y) canon}
    (t0 * t0 - 8 * (x * y * y % S.prime)) % S.prime;
    (==) {lemma_mod_sub_distr (t0 * t0) (8 * (x * y * y % S.prime)) S.prime}
    (t0 * t0 - (8 * (x * y * y % S.prime)) % S.prime) % S.prime;
    (==) {lemma_mod_mul_distr_r 8 (x * y * y) S.prime}
    (t0 * t0 - (8 * (x * y * y)) % S.prime) % S.prime;
    (==) {assert_by_tactic (8 * (x * y * y) == 8 * x * y * y) canon}
    (t0 * t0 - (8 * x * y * y) % S.prime) % S.prime;
    (==) {lemma_mod_sub_distr (t0 * t0) (8 * x * y * y) S.prime}
    (t0 * t0 - 8 * x * y * y) % S.prime;

  }


val lemma_x3_1: a: int -> b: int -> Lemma (((a % S.prime) * (a % S.prime) - b) % S.prime == (a * a - b) % S.prime)

let lemma_x3_1 a b =
  calc (==)
  {
    ((a % S.prime) * (a % S.prime) - b) % S.prime;
    (==) {lemma_mod_add_distr (- b) ((a % S.prime) * (a % S.prime)) S.prime}
    ((a % S.prime) * (a % S.prime) % S.prime - b) % S.prime;
    (==) {lemma_mod_mul_distr_l a (a % S.prime) S.prime; lemma_mod_mul_distr_r a a S.prime}
    (a * a % S.prime - b) % S.prime;
    (==) {lemma_mod_add_distr (- b) (a * a) S.prime}
    (a * a - b) % S.prime;
  }


val lemma_x3: x: int -> y: int -> z: int -> Lemma (
  ((3 * (x - (z * z % S.prime)) * (x + (z * z % S.prime)) % S.prime) * (3 * (x - (z * z % S.prime)) * (x + (z * z % S.prime)) % S.prime) - 8 * (x * (y * y % S.prime) % S.prime)) % S.prime ==
  ((3 * (x - z * z) * (x + z * z)) * (3 * (x - z * z) * (x + z * z)) - 8 * x * (y * y)) % S.prime
)

let lemma_x3 x y z =
  lemma_x3_0 x y z;

  calc (==)
  {
    (
      (3 * (x - (z * z % S.prime)) * (x + (z * z % S.prime)) % S.prime) *
      (3 * (x - (z * z % S.prime)) * (x + (z * z % S.prime)) % S.prime) - 8 * x * y * y) % S.prime;

    (==) {lemma_mod_mul_distr_l (3 * (x - (z * z % S.prime))) (x + (z * z % S.prime)) S.prime}

    (
      (3 * (x - (z * z % S.prime)) % S.prime * (x + (z * z % S.prime)) % S.prime) *
      (3 * (x - (z * z % S.prime)) % S.prime * (x + (z * z % S.prime)) % S.prime) - 8 * x * y * y) % S.prime;

  (==) {lemma_mod_mul_distr_r 3 (x - (z * z % S.prime)) S.prime}

     (
       (3 * ((x - (z * z % S.prime)) % S.prime) % S.prime * (x + (z * z % S.prime)) % S.prime) *
       (3 * ((x - (z * z % S.prime)) % S.prime) % S.prime * (x + (z * z % S.prime)) % S.prime) - 8 * x * y * y) % S.prime;

   (==) {lemma_mod_sub_distr x (z * z) S.prime}

     (
       (3 * ((x - z * z) % S.prime) % S.prime * (x + (z * z % S.prime)) % S.prime) *
       (3 * ((x - z * z) % S.prime) % S.prime * (x + (z * z % S.prime)) % S.prime) - 8 * x * y * y) % S.prime;

  (==) {lemma_mod_mul_distr_r 3 (x - (z * z)) S.prime}

     (
       (3 * ((x - z * z)) % S.prime * (x + (z * z % S.prime)) % S.prime) *
       (3 * ((x - z * z)) % S.prime * (x + (z * z % S.prime)) % S.prime) - 8 * x * y * y) % S.prime;

  (==) {lemma_mod_mul_distr_l (3 * (x - z * z)) (x + (z * z % S.prime)) S.prime}

     (
       (3 * (x - z * z) * (x + (z * z % S.prime)) % S.prime) *
       (3 * (x - z * z) * (x + (z * z % S.prime)) % S.prime) - 8 * x * y * y) % S.prime;

  (==) {lemma_mod_mul_distr_r (3 * (x - z * z)) (x + (z * z % S.prime)) S.prime;
       lemma_mod_add_distr x (z * z) S.prime;
       lemma_mod_mul_distr_r (3 * (x - z * z)) (x + z * z) S.prime}

    (
      (3 * (x - z * z) * (x + (z * z)) % S.prime) *
      (3 * (x - z * z) * (x + (z * z)) % S.prime) - 8 * x * y * y) % S.prime;

  (==) {lemma_x3_1 (3 * (x - z * z) * (x + (z * z))) (8 * x * y * y)}

    (
      (3 * (x - z * z) * (x + z * z)) *
      (3 * (x - z * z) * (x + z * z)) - 8 * x * y * y) % S.prime;

 (==) {assert_by_tactic (8 * x * y * y == 8 * x * (y * y)) canon}
     (
      (3 * (x - z * z) * (x + z * z)) *
      (3 * (x - z * z) * (x + z * z)) - 8 * x * (y * y)) % S.prime;
}


val y3_lemma_0: x: int ->  y: int -> z: int ->  t0: int -> Lemma (
   (t0 - 8 * (y * y % S.prime) * (y * y % S.prime)) % S.prime == (t0 - 8 * y * y * y * y) % S.prime)

let y3_lemma_0 x y z t0 =
  calc (==) {
    (t0 - 8 * (y * y % S.prime) * (y * y % S.prime)) % S.prime;
  (==) {lemma_mod_sub_distr t0 (8 * (y * y % S.prime) * (y * y % S.prime)) S.prime}
    (t0 - (8 * (y * y % S.prime) * (y * y % S.prime)) % S.prime) % S.prime;
  (==) {lemma_mod_mul_distr_r (8 * (y * y % S.prime)) (y * y) S.prime}
    (t0 - (8 * (y * y % S.prime) * (y * y)) % S.prime) % S.prime;
  (==) {lemma_mod_mul_distr_r (8 * (y * y)) (y * y) S.prime}
    (t0 - (8 * (y * y) * (y * y)) % S.prime) % S.prime;
  (==) {assert_by_tactic (8 * (y * y) * (y * y) == 8 * y * y * y * y) canon}
    (t0 - (8 * y * y * y * y) % S.prime) % S.prime;
  (==) {lemma_mod_sub_distr t0 (8 * y * y * y * y) S.prime}
    (t0 - (8 * y * y * y * y)) % S.prime;
  (==) {assert_by_tactic (t0 - (8 * y * y * y * y) == t0 - 8 * y * y * y * y) canon}
    (t0 - 8 * y * y * y * y) % S.prime;
  }


val y3_lemma_1: x: int ->  y: int -> z: int ->
  Lemma (3 * (x - (z * z % S.prime)) * (x + (z * z % S.prime)) % S.prime == 3 * (x + z * z) * (x - z * z)  % S.prime)

let sym_decidable (#a:eqtype) (x y:a) : Lemma (requires y = x) (ensures x == y) = ()

let y3_lemma_1 x y z =
  calc (==)
  {
    3 * (x - (z * z % S.prime)) * (x + (z * z % S.prime)) % S.prime;
    (==) {lemma_mod_mul_distr_r (3 * (x - (z * z % S.prime))) (x + (z * z % S.prime)) S.prime}
      3 * (x - (z * z % S.prime)) * ((x + (z * z % S.prime)) % S.prime) % S.prime;
    (==) {lemma_mod_add_distr x (z * z) S.prime}
      3 * (x - (z * z % S.prime)) * ((x + z * z) % S.prime) % S.prime;
    (==) {lemma_mod_mul_distr_r (3 * (x - (z * z % S.prime))) (x + z * z) S.prime}
      3 * (x - (z * z % S.prime)) * (x + z * z) % S.prime;
    (==) {assert_by_tactic (3 * (x - (z * z % S.prime)) * (x + z * z) == 3 * (x + z * z) * (x - (z * z % S.prime))) canon}
      3 * (x + z * z) * (x - (z * z % S.prime)) % S.prime;
    (==) {lemma_mod_mul_distr_r (3 * (x + z * z)) (x - (z * z % S.prime)) S.prime}
      3 * (x + z * z) * ((x - (z * z % S.prime))  % S.prime)  % S.prime;
    (==) {lemma_mod_sub_distr x (z * z) S.prime}
      3 * (x + z * z) * ((x - z * z) % S.prime)  % S.prime;
    (==) { _ by FStar.Tactics.(mapply (`sym_decidable); mapply (`lemma_mod_mul_distr_r)) }
      3 * (x + z * z) * (x - z * z)  % S.prime;
    }


val lemma_y3: x: int -> y: int -> z: int -> x3: int -> Lemma (
  ((3 * (x - (z * z % S.prime)) * (x + (z * z % S.prime)) % S.prime) *  ((4 * (x * (y * y % S.prime) % S.prime) % S.prime) - x3) - 8 * (y * y % S.prime) * (y * y % S.prime)) % S.prime == (3 * (x - z * z) * (x + z * z) *  (4 * x * (y * y) - x3) - 8 * (y * y) * (y * y)) % S.prime)


let lemma_y3 x y z x3 =
  let t = ((3 * (x - (z * z % S.prime)) * (x + (z * z % S.prime)) % S.prime) *  ((4 * (x * (y * y % S.prime) % S.prime) % S.prime) - x3) - 8 * (y * y % S.prime) * (y * y % S.prime)) % S.prime in
  let t0 = (3 * (x - (z * z % S.prime)) * (x + (z * z % S.prime)) % S.prime) *  ((4 * (x * (y * y % S.prime) % S.prime) % S.prime) - x3) in
  assert(t == (t0 - 8 * (y * y % S.prime) * (y * y % S.prime)) % S.prime);

  y3_lemma_0 x y z t0;
  y3_lemma_1 x y z;


  calc (==)
  {
      4 * (x * (y * y % S.prime) % S.prime) % S.prime;
    (==) {lemma_mod_mul_distr_r x (y * y) S.prime}
       4 * ((x * (y * y)) % S.prime) % S.prime;
    (==) {assert_by_tactic (x * (y * y) == x * y * y) canon}
      (4 * ((x * y * y) % S.prime)) % S.prime;
    (==) {lemma_mod_mul_distr_r 4 (x * y * y) S.prime}
      (4 * (x * y * y)) % S.prime;
    (==) {assert_by_tactic (4 * (x * y * y) == 4 * x * y * y) canon}
      4 * x * y * y % S.prime;

   };

  calc (==)
  {
    ((3 * (x + z * z) * (x - z * z)  % S.prime) *  (4 * x * y * y % S.prime - x3) - 8 * y * y * y * y) % S.prime;
    (==) {lemma_mod_add_distr (- 8 * y * y * y * y) ((3 * (x + z * z) * (x - z * z)  % S.prime) *  (4 * x * y * y % S.prime - x3)) S.prime}
    ((((3 * (x + z * z) * (x - z * z)) % S.prime) *  (4 * x * y * y % S.prime - x3)) % S.prime - 8 * y * y * y * y) % S.prime;
    (==) {lemma_mod_mul_distr_l (3 * (x + z * z) * (x - z * z))  (4 * x * y * y % S.prime - x3) S.prime}
    (((3 * (x + z * z) * (x - z * z)) *  (4 * x * y * y % S.prime - x3)) % S.prime - 8 * y * y * y * y) % S.prime;
    (==) {lemma_mod_mul_distr_r (3 * (x + z * z) * (x - z * z)) (4 * x * y * y % S.prime - x3) S.prime}
    (((3 * (x + z * z) * (x - z * z)) *  ((4 * x * y * y % S.prime - x3) % S.prime)) % S.prime - 8 * y * y * y * y) % S.prime;
    (==) {lemma_mod_add_distr (- x3) (4 * x * y * y) S.prime}
    (((3 * (x + z * z) * (x - z * z)) *  ((4 * x * y * y - x3) % S.prime)) % S.prime - 8 * y * y * y * y) % S.prime;
    (==) {lemma_mod_mul_distr_r (3 * (x + z * z) * (x - z * z)) (4 * x * y * y - x3) S.prime}
    ((3 * (x + z * z) * (x - z * z) *  (4 * x * y * y - x3)) % S.prime - 8 * y * y * y * y) % S.prime;
    (==) {lemma_mod_add_distr (- 8 * y * y * y * y) (3 * (x + z * z) * (x - z * z) *  (4 * x * y * y - x3)) S.prime}
    (3 * (x + z * z) * (x - z * z) *  (4 * x * y * y - x3) - 8 * y * y * y * y) % S.prime;
    (==) {assert_by_tactic (8 * y * y * y * y == 8 * (y * y) * (y * y)) canon}
    (3 * (x + z * z) * (x - z * z) *  (4 * x * y * y - x3) - 8 * (y * y) * (y * y)) % S.prime;
    (==) {assert_by_tactic (4 * x * y * y == 4 * x * (y * y)) canon}
    (3 * (x + z * z) * (x - z * z) *  (4 * x * (y * y) - x3) - 8 * (y * y) * (y * y)) % S.prime;
    (==) {assert_by_tactic ((3 * (x + z * z) * (x - z * z) *  (4 * x * (y * y) - x3) - 8 * (y * y) * (y * y)) == (3 * (x - z * z) * (x + z * z) *  (4 * x * (y * y) - x3) - 8 * (y * y) * (y * y))) canon}
    (3 * (x - z * z) * (x + z * z) *  (4 * x * (y * y) - x3) - 8 * (y * y) * (y * y)) % S.prime;

  }


val lemma_z3: x: int -> y: int -> z: int -> Lemma
  (((y + z) * (y + z) - (y * y % S.prime) - (z * z % S.prime)) % S.prime == ((y + z) * (y + z) - z * z - y * y) % S.prime)


let lemma_z3 x y z =
  let t = ((y + z) * (y + z) - (y * y % S.prime) - (z * z % S.prime)) % S.prime in

  calc (==)
    {
      ((y + z) * (y + z) - (y * y % S.prime) - (z * z % S.prime)) % S.prime;
      (==) {lemma_mod_sub_distr ((y + z) * (y + z) - (y * y % S.prime)) (z * z) S.prime}
      ((y + z) * (y + z) - (y * y % S.prime) - z * z) % S.prime;
      (==) {lemma_mod_sub_distr ((y + z) * (y + z) - z * z) (y * y) S.prime}
      ((y + z) * (y + z) - z * z - y * y) % S.prime;}


val point_double_a_b_g: p: point -> alpha: felem -> beta: felem -> gamma: felem -> delta: felem -> tempBuffer: lbuffer uint64 (size 12) ->
  Stack unit
    (requires fun h ->
      live h p /\ live h alpha /\ live h beta /\ live h gamma /\ live h delta /\ live h tempBuffer /\
      LowStar.Monotonic.Buffer.all_disjoint [loc p; loc alpha; loc beta; loc gamma; loc delta; loc tempBuffer] /\
      as_nat h (gsub p (size 8) (size 4)) < S.prime /\
      as_nat h (gsub p (size 0) (size 4)) < S.prime /\
      as_nat h (gsub p (size 4) (size 4)) < S.prime
    )
    (ensures fun h0 _ h1 -> modifies (loc alpha |+| loc beta |+| loc gamma |+| loc delta |+| loc tempBuffer) h0 h1 /\
      (
	let x = fromDomain_ (as_nat h0 (gsub p (size 0) (size 4))) in
	let y = fromDomain_ (as_nat h0 (gsub p (size 4) (size 4))) in
	let z = fromDomain_ (as_nat h0 (gsub p (size 8) (size 4))) in
	as_nat h1 delta = toDomain_ (z * z % S.prime) /\
	as_nat h1 gamma = toDomain_ (y * y % S.prime) /\
	as_nat h1 beta = toDomain_ (x * fromDomain_(as_nat h1 gamma) % S.prime) /\
	as_nat h1 alpha = toDomain_ (3 * (x - fromDomain_ (as_nat h1 delta)) * (x + fromDomain_ (as_nat h1 delta)) % S.prime)
      )
    )

val lemma_point_abd: xD: int -> dlt: int ->
  Lemma (3 * (xD - dlt) * (xD + dlt) == 3 * ((xD - dlt) * (xD + dlt)))

let lemma_point_abd xD dlt = ()


let point_double_a_b_g p alpha beta gamma delta tempBuffer =
  let pX = sub p (size 0) (size 4) in
  let pY = sub p (size 4) (size 4) in
  let pZ = sub p (size 8) (size 4) in

  let a0 = sub tempBuffer (size 0) (size 4) in
  let a1 = sub tempBuffer (size 4) (size 4) in
  let alpha0 = sub tempBuffer (size 8) (size 4) in

  fsqr pZ delta; (* delta = z * z*)
  fsqr pY gamma; (* gamma = y * y *)
  fmul pX gamma beta; (* beta = x * gamma *)

  let h0 = ST.get() in

  fsub pX delta a0; (* a0 = x - delta *)
  fadd pX delta a1; (* a1 = x + delta *)
  fmul a0 a1 alpha0; (* alpha = (x - delta) * (x + delta) *)
  fmul_by_3 alpha0 alpha;

    let xD = fromDomain_ (as_nat h0 pX) in
    let dlt = fromDomain_ (as_nat h0 delta) in

    calc (==)
    {
      (3 * (((xD - dlt) % S.prime) *  ((xD + dlt) % S.prime) % S.prime) % S.prime);
    (==) {lemma_mod_mul_distr_l (xD - dlt) ((xD + dlt) % S.prime) S.prime; lemma_mod_mul_distr_r (xD - dlt) (xD + dlt) S.prime}
      (3 * ((xD - dlt) *  (xD + dlt) % S.prime) % S.prime);
    (==) {lemma_mod_mul_distr_r 3 ((xD - dlt) * (xD + dlt)) S.prime}
      (3 * ((xD - dlt) * (xD + dlt)) % S.prime);
    (==) {lemma_point_abd xD dlt}
      (3 * (xD - dlt) * (xD + dlt)) % S.prime;
  }

val point_double_x3: x3: felem -> alpha: felem -> fourBeta: felem -> beta: felem -> eightBeta: felem ->
  Stack unit
    (requires fun h -> live h x3 /\ live h alpha /\ live h fourBeta /\ live h beta /\ live h eightBeta /\
      LowStar.Monotonic.Buffer.all_disjoint [loc x3; loc alpha; loc fourBeta; loc beta; loc eightBeta] /\
      as_nat h alpha < S.prime /\
      as_nat h beta < S.prime
    )
    (ensures fun h0 _ h1 -> modifies (loc x3 |+| loc fourBeta |+| loc eightBeta) h0 h1 /\
      as_nat h1 fourBeta = toDomain_ (4 * fromDomain_ (as_nat h0 beta) % S.prime) /\
      as_nat h1 x3 = toDomain_ ((fromDomain_ (as_nat h0 alpha) * fromDomain_ (as_nat h0 alpha) - 8 * (fromDomain_ (as_nat h0 beta))) % S.prime)
    )

let point_double_x3 x3 alpha fourBeta beta eightBeta  =
    let h0 = ST.get() in
  fsqr alpha x3; (* x3 = alpha ** 2 *)
  fmul_by_4 beta fourBeta; (*  fourBeta = beta * 4 *)
  fdouble fourBeta eightBeta; (* eightBeta = beta * 8 *)
  fsub x3 eightBeta x3 (* x3 = alpha ** 2 - beta * 8 *);

  calc(==)
  {
     toDomain_ (((fromDomain_ (as_nat h0 alpha) * fromDomain_ (as_nat h0 alpha) % S.prime) - (2 *  (4 * fromDomain_ (as_nat h0 beta) % S.prime) % S.prime)) % S.prime);
  (==) {lemma_mod_mul_distr_r 2 (4 * fromDomain_ (as_nat h0 beta)) S.prime}
  toDomain_ (((fromDomain_ (as_nat h0 alpha) * fromDomain_ (as_nat h0 alpha) % S.prime) - (8 * fromDomain_ (as_nat h0 beta)) % S.prime) % S.prime);
  (==) {lemma_mod_sub_distr (fromDomain_ (as_nat h0 alpha) * fromDomain_ (as_nat h0 alpha) % S.prime) (8 * fromDomain_ (as_nat h0 beta)) S.prime}
    toDomain_ (((fromDomain_ (as_nat h0 alpha) * fromDomain_ (as_nat h0 alpha) % S.prime) - (8 * fromDomain_ (as_nat h0 beta))) % S.prime);
  (==) {lemma_mod_add_distr (- 8 * fromDomain_ (as_nat h0 beta)) (fromDomain_ (as_nat h0 alpha) * fromDomain_ (as_nat h0 alpha)) S.prime}
    toDomain_ ((fromDomain_ (as_nat h0 alpha) * fromDomain_ (as_nat h0 alpha) - 8 * fromDomain_ (as_nat h0 beta)) % S.prime);
  }


val point_double_z3: z3: felem -> pY: felem -> pZ: felem -> gamma: felem -> delta: felem ->
  Stack unit
    (requires fun h -> live h z3 /\ live h pY /\ live h pZ /\ live h gamma /\ live h delta /\
      eq_or_disjoint pZ z3 /\ disjoint z3 gamma /\ disjoint z3 delta /\ disjoint pY z3 /\
      as_nat h gamma < S.prime /\
      as_nat h delta < S.prime /\
      as_nat h pY < S.prime /\
      as_nat h pZ < S.prime
    )
    (ensures fun h0 _ h1 -> modifies (loc z3) h0 h1 /\
      (
	let y = fromDomain_ (as_nat h0 pY) in
	let z = fromDomain_ (as_nat h0 pZ) in
	as_nat h1 z3 = toDomain_ (((y + z) * (y + z) - fromDomain_ (as_nat h0 gamma) - fromDomain_ (as_nat h0 delta)) % S.prime)
      )
    )

let point_double_z3 z3 pY pZ gamma delta  =
    let h0 = ST.get() in

  fadd pY pZ z3; (* z3 = py + pz *)
  fsqr z3 z3; (* z3 = (py + pz) ** 2 *)
  fsub z3 gamma z3; (* z3 =  (py + pz) ** 2 - gamma  *)
  fsub z3 delta z3 (* z3 = (py + pz) ** 2 - gamma - delta *);

    let pyD = fromDomain_ (as_nat h0 pY) in
    let pzD = fromDomain_ (as_nat h0 pZ) in

  calc (==)
  {
    toDomain_ (((((( ((pyD + pzD) % S.prime) * ((pyD + pzD) % S.prime) % S.prime)) - fromDomain_ (as_nat h0 gamma)) % S.prime) - fromDomain_ (as_nat h0 delta)) % S.prime);
  (==) {lemma_mod_mul_distr_l (pyD + pzD) ((pyD + pzD) % S.prime) S.prime; lemma_mod_mul_distr_r (pyD + pzD) (pyD + pzD) S.prime}
    toDomain_ ((((((pyD + pzD) * (pyD + pzD) % S.prime) - fromDomain_ (as_nat h0 gamma)) % S.prime) - fromDomain_ (as_nat h0 delta)) % S.prime);
  (==) {lemma_mod_add_distr (- fromDomain_ (as_nat h0 gamma)) ((pyD + pzD) * (pyD + pzD)) S.prime }
    toDomain_ (((((pyD + pzD) * (pyD + pzD) - fromDomain_ (as_nat h0 gamma)) % S.prime) - fromDomain_ (as_nat h0 delta)) % S.prime);
  (==) {lemma_mod_add_distr (- fromDomain_ (as_nat h0 delta)) ((pyD + pzD) * (pyD + pzD) - fromDomain_ (as_nat h0 gamma)) S.prime}
    toDomain_ (((pyD + pzD) * (pyD + pzD) - fromDomain_ (as_nat h0 gamma) - fromDomain_ (as_nat h0 delta)) % S.prime);
  }


val point_double_y3: y3: felem -> x3: felem -> alpha: felem -> gamma: felem -> eightGamma: felem -> fourBeta: felem ->
  Stack unit
  (requires fun h -> live h y3 /\ live h x3 /\ live h alpha /\ live h gamma /\ live h eightGamma /\ live h fourBeta /\
    LowStar.Monotonic.Buffer.all_disjoint [loc y3; loc x3; loc alpha; loc gamma; loc eightGamma; loc fourBeta] /\
    as_nat h x3 < S.prime /\
    as_nat h alpha < S.prime /\
    as_nat h gamma < S.prime /\
    as_nat h fourBeta < S.prime
  )
  (ensures fun h0 _ h1 -> modifies (loc y3 |+| loc gamma |+| loc eightGamma) h0 h1 /\
    (
      let alphaD = fromDomain_ (as_nat h0 alpha) in
      let gammaD = fromDomain_ (as_nat h0 gamma) in
      as_nat h1 y3 == toDomain_ ((alphaD *  (fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3)) - 8 * gammaD * gammaD) % S.prime)
    )
  )



let point_double_y3 y3 x3 alpha gamma eightGamma fourBeta =
    let h0 = ST.get() in
  fsub fourBeta x3 y3; (* y3 = 4 * beta - x3 *)
  fmul alpha y3 y3; (* y3 = alpha * (4 * beta - x3) *)
  fsqr gamma gamma; (* gamma = gamma ** 2 *)
  fmul_by_8 gamma eightGamma; (* gamma = 8 * gamma ** 2 *)
  fsub y3 eightGamma y3; (* y3 = alpha * y3 - 8 * gamma **2 *)


  let alphaD = fromDomain_ (as_nat h0 alpha) in
  let gammaD = fromDomain_ (as_nat h0 gamma) in

  calc(==)
  {
     toDomain_ (((fromDomain_ (as_nat h0 alpha) *  ((fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3)) % S.prime) % S.prime) - (8 *  (fromDomain_ (as_nat h0 gamma) * fromDomain_ (as_nat h0 gamma) % S.prime) % S.prime)) % S.prime);
  (==) {lemma_mod_mul_distr_r (fromDomain_ (as_nat h0 alpha)) (((fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3)))) S.prime}
    toDomain_ (((fromDomain_ (as_nat h0 alpha) *  (fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3)) % S.prime) - (8 *  (fromDomain_ (as_nat h0 gamma) * fromDomain_ (as_nat h0 gamma) % S.prime) % S.prime)) % S.prime);
  (==) {lemma_mod_mul_distr_r 8 (fromDomain_ (as_nat h0 gamma) * (fromDomain_ (as_nat h0 gamma))) S.prime}
    toDomain_ (((alphaD *  (fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3)) % S.prime) - (8 * (gammaD * gammaD) % S.prime)) % S.prime);
  (==) {lemma_mod_add_distr (-(8 * (gammaD * gammaD) % S.prime)) (alphaD *  (fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3))) S.prime  }
      toDomain_ (((alphaD *  (fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3))) - (8 * (gammaD * gammaD) % S.prime)) % S.prime);
  (==) {lemma_mod_sub_distr (alphaD *  (fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3))) (8 * (gammaD * gammaD)) S.prime}
       toDomain_ (((alphaD *  (fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3))) - (8 * (gammaD * gammaD))) % S.prime);
  (==) {assert_by_tactic (8 * (gammaD * gammaD) == 8 * gammaD * gammaD) canon}
    toDomain_ ((alphaD *  (fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3)) - 8 * gammaD * gammaD) % S.prime);
}


val lemma_pd_to_spec: x: nat -> y: nat -> z: nat -> x3: nat -> y3: nat -> z3: nat ->  Lemma
  (requires (
    let xD, yD, zD = fromDomain_ x, fromDomain_ y, fromDomain_ z in
    x3 == toDomain_ (((3 * (xD - zD * zD) * (xD + zD * zD)) * (3 * (xD - zD * zD) * (xD + zD * zD)) - 8 * xD * (yD * yD)) % S.prime) /\
    y3 == toDomain_ ((3 * (xD - zD * zD) * (xD + zD * zD) *  (4 * xD * (yD * yD) - fromDomain_ x3) - 8 * (yD * yD) * (yD * yD)) % S.prime) /\
    z3 = toDomain_ (((yD + zD) * (yD + zD) - zD * zD - yD * yD) % S.prime)
  )
)
 (ensures(
   let xD, yD, zD = fromDomain_ x, fromDomain_ y, fromDomain_ z in
   let x3D, y3D, z3D = fromDomain_ x3, fromDomain_ y3, fromDomain_ z3 in
   let xN, yN, zN = S.point_double (xD, yD, zD) in
   x3D == xN /\ y3D == yN /\ z3D == zN))

let lemma_pd_to_spec x y z x3 y3 z3 =
  let xD, yD, zD = fromDomain_ x, fromDomain_ y, fromDomain_ z in
  let x3D, y3D, z3D = fromDomain_ x3, fromDomain_ y3, fromDomain_ z3 in
  assert(let xN, yN, zN = S.point_double (xD, yD, zD) in
      x3D == xN /\ y3D == yN /\ z3D == zN)



let point_double p result tempBuffer =
  let pX = sub p (size 0) (size 4) in
  let pY = sub p (size 4) (size 4) in
  let pZ = sub p (size 8) (size 4) in

  let x3 = sub result (size 0) (size 4) in
  let y3 = sub result (size 4) (size 4) in
  let z3 = sub result (size 8) (size 4) in

  let delta = sub tempBuffer (size 0) (size 4) in
  let gamma = sub tempBuffer (size 4) (size 4) in
  let beta = sub tempBuffer (size 8) (size 4) in
  let alpha = sub tempBuffer (size 16) (size 4) in

  let fourBeta = sub tempBuffer (size 20) (size 4) in
  let eightBeta = sub tempBuffer (size 24) (size 4) in
  let eightGamma = sub tempBuffer (size 28) (size 4) in

  let tmp = sub tempBuffer (size 32) (size 12) in


  let h0 = ST.get() in
    point_double_a_b_g p alpha beta gamma delta tmp;
    point_double_x3 x3 alpha fourBeta beta eightBeta;
    point_double_z3 z3 pY pZ gamma delta;
    point_double_y3 y3 x3 alpha gamma eightGamma fourBeta;

  let h4 = ST.get() in

  let x = fromDomain_ (as_nat h0 (gsub p (size 0) (size 4))) in
  let y = fromDomain_ (as_nat h0 (gsub p (size 4) (size 4))) in
  let z = fromDomain_ (as_nat h0 (gsub p (size 8) (size 4))) in

  lemma_x3 x y z;
  lemma_z3 x y z;
  lemma_y3 x y z (fromDomain_ (as_nat h4 x3));
  lemma_pd_to_spec
    (as_nat h0 (gsub p (size 0) (size 4)))
      (as_nat h0 (gsub p (size 4) (size 4)))
	(as_nat h0 (gsub p (size 8) (size 4)))
    (as_nat h4 (gsub result (size 0) (size 4)))
      (as_nat h4 (gsub result (size 4) (size 4)))
	(as_nat h4 (gsub result (size 8) (size 4)))
