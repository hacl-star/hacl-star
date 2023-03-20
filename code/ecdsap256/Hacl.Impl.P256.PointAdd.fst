module Hacl.Impl.P256.PointAdd

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Tactics
open FStar.Tactics.Canon

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Field
open Hacl.Spec.P256.Math

module S = Spec.P256
module SM = Hacl.Spec.P256.MontgomeryMultiplication

#reset-options "--z3rlimit 300 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val move_from_jacobian_coordinates: u1: felem -> u2: felem -> s1: felem -> s2: felem ->  p: point -> q: point ->
  tempBuffer16: lbuffer uint64 (size 16) ->
  Stack unit (requires fun h -> live h u1 /\ live h u2 /\ live h s1 /\ live h s2 /\ live h p /\ live h q /\ live h tempBuffer16 /\
   LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer16; loc p; loc q; loc u1; loc u2; loc s1; loc s2] /\
    as_nat h (gsub p (size 8) (size 4)) < S.prime /\
    as_nat h (gsub p (size 0) (size 4)) < S.prime /\
    as_nat h (gsub p (size 4) (size 4)) < S.prime /\
    as_nat h (gsub q (size 8) (size 4)) < S.prime /\
    as_nat h (gsub q (size 0) (size 4)) < S.prime /\
    as_nat h (gsub q (size 4) (size 4)) < S.prime
    )
  (ensures fun h0 _ h1 ->
    modifies (loc u1 |+| loc u2 |+| loc s1 |+| loc s2 |+| loc tempBuffer16) h0 h1 /\
    as_nat h1 u1 < S.prime /\ as_nat h1 u2 < S.prime /\ as_nat h1 s1 < S.prime /\ as_nat h1 s2 < S.prime  /\
    (
      let pX, pY, pZ = as_nat h0 (gsub p (size 0) (size 4)), as_nat h0 (gsub p (size 4) (size 4)), as_nat h0 (gsub p (size 8) (size 4)) in
      let qX, qY, qZ = as_nat h0 (gsub q (size 0) (size 4)), as_nat h0 (gsub q (size 4) (size 4)), as_nat h0 (gsub q (size 8) (size 4)) in

      let pxD, pyD, pzD = SM.from_mont_point (pX, pY, pZ) in
      let qxD, qyD, qzD = SM.from_mont_point (qX, qY, qZ) in

      as_nat h1 u1 == SM.to_mont (qzD * qzD * pxD % S.prime) /\
      as_nat h1 u2 == SM.to_mont (pzD * pzD * qxD % S.prime) /\
      as_nat h1 s1 == SM.to_mont (qzD * qzD * qzD * pyD % S.prime) /\
      as_nat h1 s2 == SM.to_mont (pzD * pzD * pzD * qyD % S.prime)
)
)

let move_from_jacobian_coordinates u1 u2 s1 s2 p q tempBuffer =
    let h0 = ST.get() in
   let pX = sub p (size 0) (size 4) in
   let pY = sub p (size 4) (size 4) in
   let pZ = sub p (size 8) (size 4) in

   let qX = sub q (size 0) (size 4) in
   let qY = sub q (size 4) (size 4) in
   let qZ = sub q (size 8) (size 4) in

   let z2Square = sub tempBuffer (size 0) (size 4) in
   let z1Square = sub tempBuffer (size 4) (size 4) in
   let z2Cube = sub tempBuffer (size 8) (size 4) in
   let z1Cube = sub tempBuffer (size 12) (size 4) in

   fsqr qZ z2Square;
   fsqr pZ z1Square;
   fmul z2Square qZ z2Cube;

   fmul z1Square pZ z1Cube;
   fmul z2Square pX u1;
   fmul z1Square qX u2;

   fmul z2Cube pY s1;
   fmul z1Cube qY s2;


     lemma_mod_mul_distr_l (SM.from_mont (as_nat h0 qZ) * SM.from_mont (as_nat h0 qZ)) (SM.from_mont (as_nat h0 qZ)) S.prime;
     lemma_mod_mul_distr_l (SM.from_mont (as_nat h0 pZ) * SM.from_mont (as_nat h0 pZ)) (SM.from_mont (as_nat h0 pZ)) S.prime;
     lemma_mod_mul_distr_l (SM.from_mont (as_nat h0 qZ) * SM.from_mont (as_nat h0 qZ)) (SM.from_mont (as_nat h0 pX)) S.prime;

     lemma_mod_mul_distr_l (SM.from_mont (as_nat h0 pZ) * SM.from_mont (as_nat h0 pZ)) (SM.from_mont (as_nat h0 qX)) S.prime;
     lemma_mod_mul_distr_l (SM.from_mont (as_nat h0 qZ) * SM.from_mont (as_nat h0 qZ) * SM.from_mont (as_nat h0 qZ)) (SM.from_mont (as_nat h0 pY)) S.prime;
     lemma_mod_mul_distr_l (SM.from_mont (as_nat h0 pZ) * SM.from_mont (as_nat h0 pZ) * SM.from_mont (as_nat h0 pZ)) (SM.from_mont (as_nat h0 qY)) S.prime



inline_for_extraction noextract
val compute_common_params_point_add: h: felem -> r: felem -> uh: felem -> hCube: felem ->
  u1: felem -> u2: felem -> s1: felem -> s2: felem -> tempBuffer: lbuffer uint64 (size 16) ->
  Stack unit
    (requires fun h0 -> live h0 h /\ live h0 r /\ live h0 uh /\ live h0 hCube /\ live h0 u1 /\ live h0 u2 /\ live h0 s1 /\ live h0 s2 /\ live h0 tempBuffer /\
      LowStar.Monotonic.Buffer.all_disjoint [loc u1; loc u2; loc s1; loc s2; loc h; loc r; loc uh; loc hCube; loc tempBuffer] /\ as_nat h0 u1 < S.prime /\ as_nat h0 u2 < S.prime /\ as_nat h0 s1 < S.prime /\ as_nat h0 s2 < S.prime)
    (ensures fun h0 _ h1 ->
      modifies (loc h |+| loc r |+| loc uh |+| loc hCube |+| loc tempBuffer) h0 h1 /\
      as_nat h1 h < S.prime /\ as_nat h1 r < S.prime /\ as_nat h1 uh < S.prime /\ as_nat h1 hCube < S.prime /\
      (
	let u1D = SM.from_mont (as_nat h0 u1) in
	let u2D = SM.from_mont (as_nat h0 u2) in
	let s1D = SM.from_mont (as_nat h0 s1) in
	let s2D = SM.from_mont (as_nat h0 s2) in

	let hD = SM.from_mont (as_nat h1 h) in

	as_nat h1 h == SM.to_mont ((u2D - u1D) % S.prime) /\
	as_nat h1 r == SM.to_mont ((s2D - s1D) % S.prime) /\
	as_nat h1 uh == SM.to_mont (hD * hD * u1D % S.prime) /\
	as_nat h1 hCube == SM.to_mont (hD * hD * hD % S.prime)
  )
)


let compute_common_params_point_add h r uh hCube u1 u2 s1 s2 tempBuffer =
    let h0 = ST.get() in
  let temp = sub tempBuffer (size 0) (size 4) in
  fsub u2 u1 h;
    let h1 = ST.get() in
  fsub s2 s1 r;
    let h2 = ST.get() in
  fsqr h temp;
    let h3 = ST.get() in
  fmul temp u1 uh;
  fmul temp h hCube;

    lemma_mod_mul_distr_l (SM.from_mont (as_nat h2 h) * SM.from_mont (as_nat h2 h)) (SM.from_mont (as_nat h3 u1)) S.prime;
    lemma_mod_mul_distr_l (SM.from_mont (as_nat h2 h) * SM.from_mont (as_nat h2 h)) (SM.from_mont (as_nat h1 h)) S.prime


inline_for_extraction noextract
val computeX3_point_add: x3: felem -> hCube: felem -> uh: felem -> r: felem -> tempBuffer: lbuffer uint64 (size 16)->  Stack unit
  (requires fun h0 -> live h0 x3 /\ live h0 hCube /\ live h0 uh /\ live h0 r /\ live h0 tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc x3; loc hCube; loc uh; loc r; loc tempBuffer] /\
    as_nat h0 hCube < S.prime /\as_nat h0 uh < S.prime /\ as_nat h0 r < S.prime
  )
  (ensures fun h0 _ h1 -> modifies (loc x3 |+| loc tempBuffer) h0 h1 /\ as_nat h1 x3 < S.prime /\
    (
      let hCubeD = SM.from_mont (as_nat h0 hCube) in
      let uhD = SM.from_mont (as_nat h0 uh) in
      let rD = SM.from_mont (as_nat h0 r) in
      as_nat h1 x3 == SM.to_mont ((rD * rD - hCubeD - 2 * uhD) % S.prime)
    )
  )

let computeX3_point_add x3 hCube uh r tempBuffer =
    let h0 = ST.get() in
  let rSquare = sub tempBuffer (size 0) (size 4) in
  let rH = sub tempBuffer (size 4) (size 4) in
  let twoUh = sub tempBuffer (size 8) (size 4) in
  fsqr r rSquare;
    let h1 = ST.get() in
  fsub rSquare hCube rH;
    let h2 = ST.get() in
  fdouble uh twoUh;
    let h3 = ST.get() in
  fsub rH twoUh x3;

    lemma_mod_add_distr (-SM.from_mont (as_nat h1 hCube)) (SM.from_mont (as_nat h0 r) * SM.from_mont (as_nat h0 r)) S.prime;
    lemma_mod_add_distr (-SM.from_mont (as_nat h3 twoUh)) (SM.from_mont (as_nat h0 r) * SM.from_mont (as_nat h0 r) - SM.from_mont (as_nat h1 hCube)) S.prime;
    lemma_mod_sub_distr (SM.from_mont (as_nat h0 r) * SM.from_mont (as_nat h0 r) - SM.from_mont (as_nat h1 hCube)) (2 * SM.from_mont (as_nat h2 uh)) S.prime


inline_for_extraction noextract
val computeY3_point_add:y3: felem -> s1: felem -> hCube: felem -> uh: felem -> x3_out: felem -> r: felem -> tempBuffer: lbuffer uint64 (size 16) ->
  Stack unit
    (requires fun h -> live h y3 /\ live h s1 /\ live h hCube /\ live h uh /\ live h x3_out /\ live h r /\ live h tempBuffer /\
      LowStar.Monotonic.Buffer.all_disjoint [loc y3; loc s1; loc hCube; loc uh; loc x3_out; loc r; loc tempBuffer] /\
      as_nat h s1 < S.prime /\ as_nat h hCube < S.prime /\ as_nat h uh < S.prime /\ as_nat h x3_out <S.prime /\ as_nat h r < S.prime)
    (ensures fun h0 _ h1 ->
      modifies (loc y3 |+| loc tempBuffer) h0 h1 /\ as_nat h1 y3 < S.prime /\
      (
	let s1D = SM.from_mont (as_nat h0 s1) in
	let hCubeD = SM.from_mont (as_nat h0 hCube) in
	let uhD = SM.from_mont (as_nat h0 uh) in
	let x3D = SM.from_mont (as_nat h0 x3_out) in
	let rD = SM.from_mont (as_nat h0 r) in
	as_nat h1 y3 = SM.to_mont (((uhD - x3D) * rD - s1D * hCubeD) % S.prime)
    )
)


let computeY3_point_add y3 s1 hCube uh x3 r tempBuffer =
    let h0 = ST.get() in
  let s1hCube = sub tempBuffer (size 0) (size 4) in
  let u1hx3 = sub tempBuffer (size 4) (size 4) in
  let ru1hx3 = sub tempBuffer (size 8) (size 4) in

  fmul s1 hCube s1hCube;
  fsub uh x3 u1hx3;
  fmul u1hx3 r ru1hx3;

    let h3 = ST.get() in
    lemma_mod_mul_distr_l (SM.from_mont (as_nat h0 uh) - SM.from_mont (as_nat h0 x3)) (SM.from_mont (as_nat h0 r)) S.prime;
  fsub ru1hx3 s1hCube y3;
    lemma_mod_add_distr (-(SM.from_mont (as_nat h3 s1hCube)))  ((SM.from_mont (as_nat h0 uh) - SM.from_mont (as_nat h0 x3)) * SM.from_mont (as_nat h0 r))  S.prime;
    lemma_mod_sub_distr ((SM.from_mont (as_nat h0 uh) - SM.from_mont (as_nat h0 x3)) * SM.from_mont (as_nat h0 r)) (SM.from_mont (as_nat h0 s1) * SM.from_mont (as_nat h0 hCube)) S.prime



inline_for_extraction noextract
val computeZ3_point_add: z3: felem ->  z1: felem -> z2: felem -> h: felem -> tempBuffer: lbuffer uint64 (size 16) ->
  Stack unit (requires fun h0 -> live h0 z3 /\ live h0 z1 /\ live h0 z2 /\ live h0 h /\ live h0 tempBuffer /\ live h0 z3 /\
  LowStar.Monotonic.Buffer.all_disjoint [loc z1; loc z2; loc h; loc tempBuffer; loc z3] /\
  as_nat h0 z1 < S.prime /\ as_nat h0 z2 < S.prime /\ as_nat h0 h < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc z3 |+| loc tempBuffer) h0 h1 /\ as_nat h1 z3 < S.prime /\
    (
      let z1D = SM.from_mont (as_nat h0 z1) in
      let z2D = SM.from_mont (as_nat h0 z2) in
      let hD = SM.from_mont (as_nat h0 h) in
      as_nat h1 z3 == SM.to_mont (z1D * z2D * hD % S.prime)
    )
  )

let computeZ3_point_add z3 z1 z2 h tempBuffer =
    let h0 = ST.get() in
  let z1z2 = sub tempBuffer (size 0) (size 4) in
  fmul z1 z2 z1z2;
  fmul z1z2 h z3;
    lemma_mod_mul_distr_l (SM.from_mont (as_nat h0 z1) * SM.from_mont (as_nat h0 z2)) (SM.from_mont (as_nat h0 h)) S.prime


inline_for_extraction noextract
val point_add_if_second_branch_impl: result: point -> p: point -> q: point -> u1: felem -> u2: felem -> s1: felem ->
  s2: felem -> r: felem -> h: felem -> uh: felem -> hCube: felem -> tempBuffer28 : lbuffer uint64 (size 28) ->
  Stack unit
    (requires fun h0 -> live h0 result /\ live h0 p /\ live h0 q /\ live h0 u1 /\ live h0 u2 /\ live h0 s1 /\ live h0 s2 /\ live h0 r /\ live h0 h /\ live h0 uh /\ live h0 hCube /\ live h0 tempBuffer28 /\

    as_nat h0 u1 < S.prime  /\ as_nat h0 u2 < S.prime  /\ as_nat h0 s1 < S.prime /\ as_nat h0 s2 < S.prime /\ as_nat h0 r < S.prime /\
    as_nat h0 h < S.prime /\ as_nat h0 uh < S.prime /\ as_nat h0 hCube < S.prime /\

    eq_or_disjoint p result /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc u1; loc u2; loc s1; loc s2; loc r; loc h; loc uh; loc hCube; loc tempBuffer28] /\
    disjoint result tempBuffer28 /\

    as_nat h0 (gsub p (size 8) (size 4)) < S.prime /\
    as_nat h0 (gsub p (size 0) (size 4)) < S.prime /\
    as_nat h0 (gsub p (size 4) (size 4)) < S.prime /\
    as_nat h0 (gsub q (size 8) (size 4)) < S.prime /\
    as_nat h0 (gsub q (size 0) (size 4)) < S.prime /\
    as_nat h0 (gsub q (size 4) (size 4)) < S.prime /\

    (
      let pX, pY, pZ = as_nat h0 (gsub p (size 0) (size 4)), as_nat h0 (gsub p (size 4) (size 4)), as_nat h0 (gsub p (size 8) (size 4)) in
      let qX, qY, qZ = as_nat h0 (gsub q (size 0) (size 4)), as_nat h0 (gsub q (size 4) (size 4)), as_nat h0 (gsub q (size 8) (size 4)) in
      let pxD, pyD, pzD = SM.from_mont pX, SM.from_mont pY, SM.from_mont pZ in
      let qxD, qyD, qzD = SM.from_mont qX, SM.from_mont qY, SM.from_mont qZ in

      let u1D = SM.from_mont (as_nat h0 u1) in
      let u2D = SM.from_mont (as_nat h0 u2) in
      let s1D = SM.from_mont (as_nat h0 s1) in
      let s2D = SM.from_mont (as_nat h0 s2) in

      let hD = SM.from_mont (as_nat h0 h) in

      as_nat h0 u1 == SM.to_mont (qzD * qzD * pxD % S.prime) /\
      as_nat h0 u2 == SM.to_mont (pzD * pzD * qxD % S.prime) /\
      as_nat h0 s1 == SM.to_mont (qzD * qzD * qzD * pyD % S.prime) /\
      as_nat h0 s2 == SM.to_mont (pzD * pzD * pzD * qyD % S.prime) /\

      as_nat h0 h == SM.to_mont ((u2D - u1D) % S.prime) /\
      as_nat h0 r == SM.to_mont ((s2D - s1D) % S.prime) /\
      as_nat h0 uh == SM.to_mont (hD * hD * u1D % S.prime) /\
      as_nat h0 hCube == SM.to_mont (hD * hD * hD % S.prime)
  )
)
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer28 |+| loc result) h0 h1 /\
    as_nat h1 (gsub result (size 8) (size 4)) < S.prime /\
    as_nat h1 (gsub result (size 0) (size 4)) < S.prime /\
    as_nat h1 (gsub result (size 4) (size 4)) < S.prime /\
    (
      let pX, pY, pZ = as_nat h0 (gsub p (size 0) (size 4)), as_nat h0 (gsub p (size 4) (size 4)), as_nat h0 (gsub p (size 8) (size 4)) in
      let qX, qY, qZ = as_nat h0 (gsub q (size 0) (size 4)), as_nat h0 (gsub q (size 4) (size 4)), as_nat h0 (gsub q (size 8) (size 4)) in
      let x3, y3, z3 = as_nat h1 (gsub result (size 0) (size 4)), as_nat h1 (gsub result (size 4) (size 4)), as_nat h1 (gsub result (size 8) (size 4)) in

      let pxD, pyD, pzD = SM.from_mont pX, SM.from_mont pY, SM.from_mont pZ in
      let qxD, qyD, qzD = SM.from_mont qX, SM.from_mont qY, SM.from_mont qZ in
      let x3D, y3D, z3D = SM.from_mont x3, SM.from_mont y3, SM.from_mont z3 in

      let rD = SM.from_mont (as_nat h0 r) in
      let hD = SM.from_mont (as_nat h0 h) in
      let s1D = SM.from_mont (as_nat h0 s1) in
      let u1D = SM.from_mont (as_nat h0 u1) in

  if qzD = 0 then
    x3D == pxD /\ y3D == pyD /\ z3D == pzD
   else if pzD = 0 then
    x3D == qxD /\  y3D == qyD /\ z3D == qzD
   else
    x3 == SM.to_mont ((rD * rD - hD * hD * hD - 2 * hD * hD * u1D) % S.prime) /\
    y3 == SM.to_mont (((hD * hD * u1D - SM.from_mont (x3)) * rD - s1D * hD * hD * hD) % S.prime) /\
    z3 == SM.to_mont (pzD * qzD * hD % S.prime)
  )
)


let point_add_if_second_branch_impl result p q u1 u2 s1 s2 r h uh hCube tempBuffer28 =
    let h0 = ST.get() in
  let pZ = sub p (size 8) (size 4) in
  let qZ = sub q (size 8) (size 4) in

  let tempBuffer16 = sub tempBuffer28 (size 0) (size 16) in

  let xyz_out = Lib.Buffer.sub tempBuffer28 16ul 12ul in
  let x3_out = Lib.Buffer.sub tempBuffer28 (size 16) (size 4) in
  let y3_out = Lib.Buffer.sub tempBuffer28 (size 20) (size 4) in
  let z3_out = Lib.Buffer.sub tempBuffer28 (size 24) (size 4) in

  computeX3_point_add x3_out hCube uh r tempBuffer16;
    let h1 = ST.get() in
  computeY3_point_add y3_out s1 hCube uh x3_out r tempBuffer16;
  computeZ3_point_add z3_out pZ qZ h tempBuffer16;
  copy_point_conditional xyz_out q p;

  copy_point_conditional xyz_out p q;
  concat3 (size 4) x3_out (size 4) y3_out (size 4) z3_out result;

    let hEnd = ST.get() in

  let rD = SM.from_mont (as_nat h0 r) in
  let hD = SM.from_mont (as_nat h0 h) in
  let u1D = SM.from_mont (as_nat h0 u1) in
  let uhD = SM.from_mont (as_nat h0 uh) in

  let s1D = SM.from_mont (as_nat h0 s1) in
  let x3D = SM.from_mont (as_nat h1 x3_out) in

  //lemma_point_add_0 (rD * rD) (hD * hD * hD) (hD * hD * u1D);
  lemma_mod_sub_distr (rD * rD - 2 * uhD) (hD * hD * hD) S.prime;
  assert_by_tactic (2 * (hD * hD * u1D) == 2 * hD * hD * u1D) canon;

  //lemma_point_add_1 (hD * hD * u1D) x3D rD s1D (hD * hD * hD);
  assert_by_tactic (s1D * (hD * hD * hD) == s1D * hD * hD * hD) canon;

  assert_norm (S.modp_inv2_prime (pow2 256) S.prime > 0);
  assert_norm (S.modp_inv2_prime (pow2 256) S.prime % S.prime <> 0);

  lemma_multiplication_not_mod_prime (as_nat h0 pZ);
  lemma_multiplication_not_mod_prime (as_nat h0 qZ)


let point_add p q result tempBuffer =
    let h0 = ST.get() in

  let z1 = sub p (size 8) (size 4) in
  let z2 = sub q (size 8) (size 4) in

  let tempBuffer16 = sub tempBuffer (size 0) (size 16) in

  let u1 = sub tempBuffer (size 16) (size 4) in
  let u2 = sub tempBuffer (size 20) (size 4) in
  let s1 = sub tempBuffer (size 24) (size 4) in
  let s2 = sub tempBuffer (size 28) (size 4) in

  let h = sub tempBuffer (size 32) (size 4) in
  let r = sub tempBuffer (size 36) (size 4) in
  let uh = sub tempBuffer (size 40) (size 4) in

  let hCube = sub tempBuffer (size 44) (size 4) in

  let x3_out = sub tempBuffer (size 48) (size 4) in
  let y3_out = sub tempBuffer (size 52) (size 4) in
  let z3_out = sub tempBuffer (size 56) (size 4) in

  let tempBuffer28 = sub tempBuffer (size 60) (size 28) in

  move_from_jacobian_coordinates u1 u2 s1 s2 p q tempBuffer16;
  compute_common_params_point_add h r uh hCube u1 u2 s1 s2 tempBuffer16;
  point_add_if_second_branch_impl result p q u1 u2 s1 s2 r h uh hCube tempBuffer28;
    let h1 = ST.get() in
      let pxD = SM.from_mont (as_nat h0 (gsub p (size 0) (size 4))) in
      let pyD = SM.from_mont (as_nat h0 (gsub p (size 4) (size 4))) in
      let pzD = SM.from_mont (as_nat h0 (gsub p (size 8) (size 4))) in
      let qxD = SM.from_mont (as_nat h0 (gsub q (size 0) (size 4))) in
      let qyD = SM.from_mont (as_nat h0 (gsub q (size 4) (size 4))) in
      let qzD = SM.from_mont (as_nat h0 (gsub q (size 8) (size 4))) in
      let x3 = as_nat h1 (gsub result (size 0) (size 4)) in
      let y3 = as_nat h1 (gsub result (size 4) (size 4)) in
      let z3 = as_nat h1 (gsub result (size 8) (size 4)) in
      ()
      //lemma_pointAddToSpecification pxD pyD pzD qxD qyD qzD x3 y3 z3 (as_nat h1 u1) (as_nat h1 u2) (as_nat h1 s1) (as_nat h1 s2) (as_nat h1 h) (as_nat h1 r)
