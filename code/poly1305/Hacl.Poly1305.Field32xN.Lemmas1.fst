module Hacl.Poly1305.Field32xN.Lemmas1

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence
open FStar.Mul
open FStar.Calc

open Hacl.Spec.Poly1305.Vec
include Hacl.Spec.Poly1305.Field32xN


#reset-options "--z3rlimit 50 --using_facts_from '* -FStar.Seq' --max_fuel 0 --max_ifuel 0"

val lemma_prime: unit -> Lemma (pow2 130 % prime = 5)
let lemma_prime () =
  assert_norm (pow2 130 % prime = 5 % prime);
  assert_norm (5 < prime);
  FStar.Math.Lemmas.modulo_lemma 5 prime

noextract
val carry26_wide_zero: #w:lanes -> l:uint64xN w -> uint64xN w & uint64xN w
let carry26_wide_zero #w l = (vec_and l (mask26 w), vec_shift_right l 26ul)

val carry26_wide_zero_eq: #w:lanes -> f:uint64xN w -> Lemma
  (carry26_wide_zero f == carry26_wide f (zero w))
let carry26_wide_zero_eq #w f =
  let l1 = vec_add_mod f (zero w) in
  assert (vec_v l1 == map2 ( +. ) (vec_v f) (vec_v (zero w)));
  assert (forall (i:nat{i < w}). uint_v (vec_v l1).[i] == uint_v (vec_v f).[i]);
  assert (forall (i:nat{i < w}). (vec_v l1).[i] == (vec_v f).[i]);
  eq_intro (vec_v l1) (vec_v f);
  assert (vec_v l1 == vec_v f);
  vecv_extensionality l1 f

val vec_smul_mod_five_i: #w:lanes -> f:uint64xN w{uint64xN_fits f (4096 * max26)} -> i:nat{i < w} -> Lemma
  (u64 5 *. (vec_v f).[i] == (vec_v f).[i] +. ((vec_v f).[i] <<. 2ul))
let vec_smul_mod_five_i #w f i =
  let f = (vec_v f).[i] in
  assert (v (f <<. 2ul) == (v f * pow2 2) % pow2 64);
  Math.Lemmas.small_mod (v f * pow2 2) (pow2 64);
  Math.Lemmas.small_mod (v f + v f * pow2 2) (pow2 64);
  Math.Lemmas.small_mod (5 * v f) (pow2 64);
  assert (5 * v f == v f + v f * 4);
  v_injective (u64 5 *. f);
  v_injective (f +. (f <<. 2ul))

val vec_smul_mod_five: #w:lanes -> f:uint64xN w{uint64xN_fits f (4096 * max26)} -> Lemma
  (vec_smul_mod f (u64 5) == vec_add_mod f (vec_shift_left f 2ul))
let vec_smul_mod_five #w f =
  let r1 = vec_smul_mod f (u64 5) in
  let r2 = vec_add_mod f (vec_shift_left f 2ul) in
  Classical.forall_intro (vec_smul_mod_five_i #w f);
  eq_intro (vec_v r1) (vec_v r2);
  vecv_extensionality r1 r2


noextract
val carry_wide_felem5_compact: #w:lanes -> inp:felem_wide5 w -> out:felem5 w
let carry_wide_felem5_compact #w (x0, x1, x2, x3, x4) =
  // m_i <= 4096, x_i <= m_i * max26 * max26
  // felem_wide_fits5 (x0, x1, x2, x3, x4) (m0, m1, m2, m3, m4)
  let t0, c0 = carry26_wide_zero x0 in
  // t0 <= max26 /\ c0 <= (m0 + 1) * max26
  let t1, c1 = carry26_wide x1 c0 in
  // t1 <= max26 /\ c1 <= (m1 + 1) * max26
  let t2, c2 = carry26_wide x2 c1 in
  // t2 <= max26 /\ c2 <= (m2 + 1) * max26
  let t3, c3 = carry26_wide_zero x3 in
  // t3 <= max26 /\ c3 <= (m3 + 1) * max26
  let t3', c6 = carry26 t3 c2 in
  // t3' <= max26 /\ c6 <= m2 + 2

  let t4, c4 = carry26_wide x4 c3 in
  // t4 <= max26 /\ c4 <= (m4 + 1) * max26
  let t4' = vec_add_mod t4 c6 in
  // t4' <= 2 * max26

  let t0', c5 = carry26 t0 (vec_smul_mod c4 (u64 5)) in
  // t0' <= max26 /\ c5 <= 5 * (m4 + 1) + 1
  let t1' = vec_add_mod t1 c5 in
  // t1' <= 2 * max26
  (t0', t1', t2, t3', t4')
  // felem_fits5 (t0', t1', t2, t3', t4') (1, 2, 1, 1, 2)

val carry26_wide_lemma_i:
    #w:lanes
  -> #m:scale64
  -> l:uint64xN w{felem_wide_fits1 l m}
  -> cin:uint64xN w{uint64xN_fits cin (4096 * max26)}
  -> i:nat{i < w} ->
  Lemma
  (let (l0, l1) = carry26 #w l cin in
   (uint64xN_v l0).[i] <= max26 /\ (uint64xN_v l1).[i] <= (m + 1) * max26 /\
   (uint64xN_v l).[i] + (uint64xN_v cin).[i] == (uint64xN_v l1).[i] * pow2 26 + (uint64xN_v l0).[i])

let carry26_wide_lemma_i #w #m l cin i =
  let l = (vec_v l).[i] in
  let cin = (vec_v cin).[i] in
  let mask26 = u64 0x3ffffff in
  assert_norm (0x3ffffff = pow2 26 - 1);
  FStar.Math.Lemmas.modulo_lemma (v l + v cin) (pow2 64);
  let l' = l +! cin in
  let l0 = l' &. mask26 in
  let l1 = l' >>. 26ul in
  mod_mask_lemma l' 26ul;
  assert (v (mod_mask #U64 #SEC 26ul) == v mask26);
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v l') 26 32;
  FStar.Math.Lemmas.euclidean_division_definition (v l') (pow2 26)


val carry26_wide_fits_lemma:
    #w:lanes
  -> #m:scale64
  -> l:uint64xN w{felem_wide_fits1 l m}
  -> cin:uint64xN w{uint64xN_fits cin (4096 * max26)} ->
  Lemma
  (let (l0, l1) = carry26 #w l cin in
  felem_fits1 l0 1 /\ uint64xN_fits l1 ((m + 1) * max26))

let carry26_wide_fits_lemma #w #m l cin =
  match w with
  | 1 ->
    carry26_wide_lemma_i #w #m l cin 0
  | 2 ->
    carry26_wide_lemma_i #w #m l cin 0;
    carry26_wide_lemma_i #w #m l cin 1
  | 4 ->
    carry26_wide_lemma_i #w #m l cin 0;
    carry26_wide_lemma_i #w #m l cin 1;
    carry26_wide_lemma_i #w #m l cin 2;
    carry26_wide_lemma_i #w #m l cin 3


val carry26_wide_eval_lemma:
    #w:lanes
  -> #m:scale64
  -> l:uint64xN w{felem_wide_fits1 l m}
  -> cin:uint64xN w{uint64xN_fits cin (4096 * max26)} ->
  Lemma
  (let (l0, l1) = carry26 #w l cin in
  //felem_fits1 l0 1 /\
  uint64xN_fits l1 ((m + 1) * max26) /\
  (forall (i:nat). i < w ==> (uint64xN_v l).[i] + (uint64xN_v cin).[i] ==
    (uint64xN_v l1).[i] * pow2 26 + (uint64xN_v l0).[i]))

let carry26_wide_eval_lemma #w #m l cin =
  carry26_wide_fits_lemma #w #m l cin;
  match w with
  | 1 ->
    carry26_wide_lemma_i #w #m l cin 0
  | 2 ->
    carry26_wide_lemma_i #w #m l cin 0;
    carry26_wide_lemma_i #w #m l cin 1
  | 4 ->
    carry26_wide_lemma_i #w #m l cin 0;
    carry26_wide_lemma_i #w #m l cin 1;
    carry26_wide_lemma_i #w #m l cin 2;
    carry26_wide_lemma_i #w #m l cin 3

val carry26_lemma_i:
    #w:lanes
  -> m:scale64
  -> ml:scale32
  -> l:uint64xN w{felem_fits1 l ml}
  -> cin:uint64xN w{uint64xN_fits cin (m * max26)}
  -> i:nat{i < w} ->
  Lemma
  (let (l0, l1) = carry26 #w l cin in
   (uint64xN_v l0).[i] <= max26 /\ (uint64xN_v l1).[i] < m + ml /\
   (uint64xN_v l).[i] + (uint64xN_v cin).[i] == (uint64xN_v l1).[i] * pow2 26 + (uint64xN_v l0).[i])

let carry26_lemma_i #w m ml l cin i =
  let l = (vec_v l).[i] in
  let cin = (vec_v cin).[i] in
  let mask26 = u64 0x3ffffff in
  assert_norm (0x3ffffff = pow2 26 - 1);
  FStar.Math.Lemmas.modulo_lemma (v l + v cin) (pow2 64);
  let l' = l +! cin in
  let l0 = l' &. mask26 in
  let l1 = l' >>. 26ul in
  mod_mask_lemma l' 26ul;
  assert (v (mod_mask #U64 #SEC 26ul) == v mask26);
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v l') 26 32;
  FStar.Math.Lemmas.pow2_minus 32 26


val carry26_fits_lemma:
    #w:lanes
  -> m:scale64
  -> ml:scale32
  -> l:uint64xN w{felem_fits1 l ml}
  -> cin:uint64xN w{uint64xN_fits cin (m * max26)} ->
  Lemma
  (let (l0, l1) = carry26 #w l cin in
   felem_fits1 l0 1 /\ uint64xN_fits l1 (m + ml))

let carry26_fits_lemma #w m ml l cin =
  match w with
  | 1 ->
    carry26_lemma_i #w m ml l cin 0
  | 2 ->
    carry26_lemma_i #w m ml l cin 0;
    carry26_lemma_i #w m ml l cin 1
  | 4 ->
    carry26_lemma_i #w m ml l cin 0;
    carry26_lemma_i #w m ml l cin 1;
    carry26_lemma_i #w m ml l cin 2;
    carry26_lemma_i #w m ml l cin 3


val carry26_eval_lemma:
    #w:lanes
  -> m:scale64
  -> ml:scale32
  -> l:uint64xN w{felem_fits1 l ml}
  -> cin:uint64xN w{uint64xN_fits cin (m * max26)} ->
  Lemma
  (let (l0, l1) = carry26 #w l cin in
   felem_fits1 l0 1 /\ uint64xN_fits l1 (m + ml) /\
  (forall (i:nat). i < w ==> (uint64xN_v l).[i] + (uint64xN_v cin).[i] ==
   (uint64xN_v l1).[i] * pow2 26 + (uint64xN_v l0).[i]))

let carry26_eval_lemma #w m ml l cin =
  match w with
  | 1 ->
    carry26_lemma_i #w m ml l cin 0
  | 2 ->
    carry26_lemma_i #w m ml l cin 0;
    carry26_lemma_i #w m ml l cin 1
  | 4 ->
    carry26_lemma_i #w m ml l cin 0;
    carry26_lemma_i #w m ml l cin 1;
    carry26_lemma_i #w m ml l cin 2;
    carry26_lemma_i #w m ml l cin 3


val carry_wide_felem5_fits_lemma0:
    #w:lanes
  -> inp:felem_wide5 w{felem_wide_fits5 inp (126, 102, 78, 54, 30)} ->
  Lemma (let (x0, x1, x2, x3, x4) = inp in
  let t0, c0 = carry26_wide_zero x0 in
  let t1, c1 = carry26_wide x1 c0 in
  let t2, c2 = carry26_wide x2 c1 in
  let t3, c3 = carry26_wide_zero x3 in
  let t3', c6 = carry26 t3 c2 in
  let t4, c4 = carry26_wide x4 c3 in
  let t4' = vec_add_mod t4 c6 in
  let tmp = (t0, t1, t2, t3', t4') in
  felem_fits5 tmp (1, 1, 1, 1, 2) /\ felem_fits1 c4 31)

let carry_wide_felem5_fits_lemma0 #w inp =
  let (x0, x1, x2, x3, x4) = inp in
  let t0, c0 = carry26_wide_zero x0 in
  carry26_wide_zero_eq x0;
  carry26_wide_fits_lemma #w #126 x0 (zero w);
  let t1, c1 = carry26_wide x1 c0 in
  carry26_wide_fits_lemma #w #102 x1 c0;
  let t2, c2 = carry26_wide x2 c1 in
  carry26_wide_fits_lemma #w #78 x2 c1;
  let t3, c3 = carry26_wide_zero x3 in
  carry26_wide_zero_eq x3;
  carry26_wide_fits_lemma #w #54 x3 (zero w);
  let t3', c6 = carry26 t3 c2 in
  carry26_fits_lemma 79 1 t3 c2;
  let t4, c4 = carry26_wide x4 c3 in
  carry26_wide_fits_lemma #w #30 x4 c3


val carry_wide_felem5_fits_lemma:
    #w:lanes
  -> inp:felem_wide5 w ->
  Lemma
  (requires felem_wide_fits5 inp (126, 102, 78, 54, 30))
  (ensures  felem_fits5 (carry_wide_felem5 inp) (1, 2, 1, 1, 2))

let carry_wide_felem5_fits_lemma #w inp =
  let (x0, x1, x2, x3, x4) = inp in
  let t0, c0 = carry26_wide_zero x0 in
  let t1, c1 = carry26_wide x1 c0 in
  let t2, c2 = carry26_wide x2 c1 in
  let t3, c3 = carry26_wide_zero x3 in
  let t3', c6 = carry26 t3 c2 in
  let t4, c4 = carry26_wide x4 c3 in
  let t4' = vec_add_mod t4 c6 in
  carry_wide_felem5_fits_lemma0 #w inp;
  vec_smul_mod_five c4;
  let t0', c5 = carry26 t0 (vec_smul_mod c4 (u64 5)) in
  carry26_fits_lemma 155 1 t0 (vec_smul_mod c4 (u64 5))


val carry_wide_felem5_eval_lemma_i0:
    inp:tup64_5
  -> tmp:tup64_5
  -> vc0:nat -> vc1:nat -> vc2:nat -> vc3:nat -> vc4:nat -> vc6:nat ->
  Lemma
  (requires
   (let (t0, t1, t2, t3, t4) = tmp in
    let (xi0, xi1, xi2, xi3, xi4) = inp in
    v xi0 == vc0 * pow2 26 + v t0 /\
    v xi1 + vc0 == vc1 * pow2 26 + v t1 /\
    v xi2 + vc1 == vc2 * pow2 26 + v t2 /\
    v xi3 + vc2 == vc3 * pow2 26 + vc6 * pow2 26 + v t3 /\
    v xi4 + vc3 == vc4 * pow2 26 + v t4 - vc6))
  (ensures
   (let (t0, t1, t2, t3, t4) = tmp in
    let (ti0, ti1, ti2, ti3, ti4) = inp in
    as_nat5 inp % prime ==
    (v t0 + vc4 * 5 + v t1 * pow26 + v t2 * pow52 + v t3 * pow78 + v t4 * pow104) % prime))

let carry_wide_felem5_eval_lemma_i0 inp tmp vc0 vc1 vc2 vc3 vc4 vc6 =
  let (t0, t1, t2, t3, t4) = tmp in
  let (xi0, xi1, xi2, xi3, xi4) = inp in
  let tmp_n = v t0 + v t1 * pow26 + v t2 * pow52 + v t3 * pow78 + v t4 * pow104 in

  calc (==) {
    as_nat5 inp % prime;
    (==) { }
    (v xi0 + v xi1 * pow26 + v xi2 * pow52 + v xi3 * pow78 + v xi4 * pow104) % prime;
    (==) { }
    (vc0 * pow2 26 + v t0 +
    (vc1 * pow2 26 + v t1 - vc0) * pow26 +
    (vc2 * pow2 26 + v t2 - vc1) * pow52 +
    (vc3 * pow2 26 + vc6 * pow2 26 + v t3 - vc2) * pow78 +
    (vc4 * pow2 26 + v t4 - vc6 - vc3) * pow104) % prime;
    (==) {
      assert_norm (pow2 26 * pow26 = pow52);
      assert_norm (pow2 26 * pow52 = pow78);
      assert_norm (pow2 26 * pow78 = pow104);
      assert_norm (pow2 26 * pow104 = pow2 130)}
    (v t0 + v t1 * pow26 + v t2 * pow52 + v t3 * pow78 + v t4 * pow104 + vc4 * pow2 130) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r tmp_n (vc4 * pow2 130) prime }
    (tmp_n + (vc4 * pow2 130 % prime)) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_r (vc4) (pow2 130) prime }
    (tmp_n + (vc4 * (pow2 130 % prime) % prime)) % prime;
    (==) { lemma_prime () }
    (tmp_n + (vc4 * 5 % prime)) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r tmp_n (vc4 * 5) prime }
    (tmp_n + vc4 * 5) % prime;
  };
  assert (as_nat5 inp % prime == (tmp_n + vc4 * 5) % prime)


val carry_wide_felem5_eval_lemma_i1:
    #w:lanes
  -> inp:felem_wide5 w{felem_wide_fits5 inp (126, 102, 78, 54, 30)}
  -> i:nat{i < w} ->
  Lemma (let (x0, x1, x2, x3, x4) = inp in
    let t0, c0 = carry26_wide_zero x0 in
    let t1, c1 = carry26_wide x1 c0 in
    let t2, c2 = carry26_wide x2 c1 in
    let t3, c3 = carry26_wide_zero x3 in
    let t3', c6 = carry26 t3 c2 in
    let t4, c4 = carry26_wide x4 c3 in
    let t4' = vec_add_mod t4 c6 in
    let tmp = (t0, t1, t2, t3', t4') in
    let (t0, t1, t2, t3, t4) = as_tup64_i tmp i in
    let vc4 = (uint64xN_v c4).[i] in
    (feval5 inp).[i] == (v t0 + vc4 * 5 + v t1 * pow26 + v t2 * pow52 + v t3 * pow78 + v t4 * pow104) % prime)

let carry_wide_felem5_eval_lemma_i1 #w inp i =
  let (x0, x1, x2, x3, x4) = inp in
  let t0, c0 = carry26_wide_zero x0 in
  let t1, c1 = carry26_wide x1 c0 in
  let t2, c2 = carry26_wide x2 c1 in
  let t3, c3 = carry26_wide_zero x3 in
  carry26_wide_zero_eq x3;
  carry26_wide_fits_lemma #w #54 x3 (zero w);
  let t3', c6 = carry26 t3 c2 in
  carry26_eval_lemma 79 1 t3 c2;
  carry26_fits_lemma 79 1 t3 c2;

  let t4, c4 = carry26_wide x4 c3 in
  let t4' = vec_add_mod t4 c6 in
  let tmp = (t0, t1, t2, t3, t4) in
  let tmp' = (t0, t1, t2, t3', t4') in
  let (t0, t1, t2, t3, t4) = as_tup64_i tmp i in
  let (t0, t1, t2, t3', t4') = as_tup64_i tmp' i in
  let (xi0, xi1, xi2, xi3, xi4) = as_tup64_i inp i in
  let vc0 = (uint64xN_v c0).[i] in
  let vc1 = (uint64xN_v c1).[i] in
  let vc2 = (uint64xN_v c2).[i] in
  let vc3 = (uint64xN_v c3).[i] in
  let vc4 = (uint64xN_v c4).[i] in
  let vc6 = (uint64xN_v c6).[i] in

  carry26_wide_zero_eq x0;
  carry26_wide_eval_lemma #w #126 x0 (zero w);
  assert (v xi0 == vc0 * pow2 26 + v t0);
  carry26_wide_eval_lemma #w #102 x1 c0;
  assert (v xi1 + vc0 == vc1 * pow2 26 + v t1);
  carry26_wide_eval_lemma #w #78 x2 c1;
  assert (v xi2 + vc1 == vc2 * pow2 26 + v t2);
  carry26_wide_zero_eq x3;
  carry26_wide_eval_lemma #w #54 x3 (zero w);
  assert (v xi3 == vc3 * pow2 26 + v t3);
  assert (v t3 + vc2 == vc6 * pow2 26 + v t3');

  carry26_wide_eval_lemma #w #30 x4 c3;
  assert (v xi4 + vc3 == vc4 * pow2 26 + v t4);
  carry26_wide_fits_lemma #w #30 x4 c3;
  Math.Lemmas.small_mod (v t4 + vc6) (pow2 64);
  assert (v t4' == v t4 + vc6);

  carry_wide_felem5_eval_lemma_i0 (xi0, xi1, xi2, xi3, xi4) (t0, t1, t2, t3', t4') vc0 vc1 vc2 vc3 vc4 vc6;
  assert ((feval5 inp).[i] == (v t0 + vc4 * 5 + v t1 * pow26 + v t2 * pow52 + v t3' * pow78 + v t4' * pow104) % prime)


val carry_wide_felem5_eval_lemma_i:
    #w:lanes
  -> inp:felem_wide5 w{felem_wide_fits5 inp (126, 102, 78, 54, 30)}
  -> i:nat{i < w} ->
  Lemma ((feval5 (carry_wide_felem5 #w inp)).[i] == (feval5 inp).[i])

let carry_wide_felem5_eval_lemma_i #w inp i =
  let (x0, x1, x2, x3, x4) = inp in
  let tmp0, c0 = carry26_wide_zero x0 in
  let tmp1, c1 = carry26_wide x1 c0 in
  let tmp2, c2 = carry26_wide x2 c1 in
  let tmp3, c3 = carry26_wide_zero x3 in
  let tmp3', c6 = carry26 tmp3 c2 in
  let tmp4, c4 = carry26_wide x4 c3 in
  let tmp4' = vec_add_mod tmp4 c6 in

  carry_wide_felem5_fits_lemma0 #w inp;
  Math.Lemmas.small_mod ((uint64xN_v c4).[i] * 5) (pow2 64);
  let tmp0', c5 = carry26 tmp0 (vec_smul_mod c4 (u64 5)) in
  carry26_eval_lemma 155 1 tmp0 (vec_smul_mod c4 (u64 5));
  assert ((uint64xN_v tmp0).[i] + (uint64xN_v c4).[i] * 5 == (uint64xN_v c5).[i] * pow2 26 + (uint64xN_v tmp0').[i]);
  let tmp1' = vec_add_mod tmp1 c5 in
  Math.Lemmas.small_mod ((uint64xN_v tmp1).[i] + (uint64xN_v c5).[i]) (pow2 64);
  assert ((uint64xN_v tmp1').[i] == (uint64xN_v tmp1).[i] + (uint64xN_v c5).[i]);

  let out = (tmp0', tmp1', tmp2, tmp3', tmp4') in
  let tmp = (tmp0, tmp1, tmp2, tmp3', tmp4') in
  let (o0, o1, o2, o3, o4) = as_tup64_i out i in
  let (t0, t1, t2, t3, t4) = as_tup64_i tmp i in
  let vc4 = (uint64xN_v c4).[i] in
  let vc5 = (uint64xN_v c5).[i] in

  calc (==) {
    (feval5 out).[i];
    (==) { }
    (v o0 + v o1 * pow26 + v o2 * pow52 + v o3 * pow78 + v o4 * pow104) % prime;
    (==) { }
    (v t0 + vc4 * 5 + (v t1 + vc5) * pow26 - vc5 * pow26 + v t2 * pow52 + v t3 * pow78 + v t4 * pow104) % prime;
    };
  Math.Lemmas.distributivity_add_left (v t1) vc5 pow26;
  assert ((feval5 out).[i] == (v t0 + vc4 * 5 + v t1 * pow26 + v t2 * pow52 + v t3 * pow78 + v t4 * pow104) % prime);
  carry_wide_felem5_eval_lemma_i1 #w inp i;
  assert ((feval5 inp).[i] == (v t0 + vc4 * 5 + v t1 * pow26 + v t2 * pow52 + v t3 * pow78 + v t4 * pow104) % prime);
  assert ((feval5 out).[i] == (feval5 inp).[i]);
  vec_smul_mod_five c4


val carry_wide_felem5_eval_lemma:
    #w:lanes
  -> inp:felem_wide5 w
  -> Lemma
    (requires felem_wide_fits5 inp (126, 102, 78, 54, 30))
    (ensures feval5 (carry_wide_felem5 #w inp) == feval5 inp)

let carry_wide_felem5_eval_lemma #w inp =
  let o = carry_wide_felem5 #w inp in
  FStar.Classical.forall_intro (carry_wide_felem5_eval_lemma_i #w inp);
  eq_intro (feval5 o) (feval5 inp)



val lemma_subtract_p5_0:
    f:tup64_5{tup64_fits5 f (1, 1, 1, 1, 1)}
  -> f':tup64_5 ->
  Lemma
  (requires
   (let (f0, f1, f2, f3, f4) = f in
    let (f0', f1', f2', f3', f4') = f' in
    (v f4 <> 0x3ffffff || v f3 <> 0x3ffffff || v f2 <> 0x3ffffff || v f1 <> 0x3ffffff || v f0 < 0x3fffffb) /\
    (v f0' = v f0 && v f1' = v f1 && v f2' = v f2 && v f3' = v f3 && v f4' = v f4)))
  (ensures as_nat5 f' == as_nat5 f % prime)

let lemma_subtract_p5_0 f f' =
  let (f0, f1, f2, f3, f4) = f in
  let (f0', f1', f2', f3', f4') = f' in
  assert_norm (max26 = pow2 26 - 1);
  assert_norm (0x3ffffff = max26);
  assert_norm (0x3fffffb = max26 - 4);
  assert (as_nat5 f == v f0 + v f1 * pow26 + v f2 * pow52 + v f3 * pow78 + v f4 * pow104);
  assert (as_nat5 f <= pow26 - 5 + (pow2 26 - 1) * pow26 + (pow2 26 - 1) * pow52 + (pow2 26 - 1) * pow78 + (pow2 26 - 1) * pow104);
  assert_norm (pow2 26 * pow104 = pow2 130);
  assert (as_nat5 f < pow2 130 - 5);
  assert (as_nat5 f == as_nat5 f');
  FStar.Math.Lemmas.modulo_lemma (as_nat5 f') prime


val lemma_subtract_p5_1:
    f:tup64_5{tup64_fits5 f (1, 1, 1, 1, 1)}
  -> f':tup64_5 ->
  Lemma
  (requires
   (let (f0, f1, f2, f3, f4) = f in
    let (f0', f1', f2', f3', f4') = f' in
    (v f4 = 0x3ffffff && v f3 = 0x3ffffff && v f2 = 0x3ffffff && v f1 = 0x3ffffff && v f0 >= 0x3fffffb) /\
    (v f0' = v f0 - 0x3fffffb && v f1' = v f1 - 0x3ffffff && v f2' = v f2 - 0x3ffffff && v f3' = v f3 - 0x3ffffff && v f4' = v f4 - 0x3ffffff)))
  (ensures as_nat5 f' == as_nat5 f % prime)

let lemma_subtract_p5_1 f f' =
  let (f0, f1, f2, f3, f4) = f in
  let (f0', f1', f2', f3', f4') = f' in
  //assert_norm (max26 = pow2 26 - 1);
  assert_norm (0x3ffffff = pow2 26 - 1);
  assert_norm (0x3fffffb = pow2 26 - 5);
  assert (as_nat5 f' < prime);
  calc (==) {
    as_nat5 f' % prime;
    (==) { }
    (v f0' + v f1' * pow26 + v f2' * pow52 + v f3' * pow78 + v f4' * pow104) % prime;
    (==) { }
    (v f0 - (pow2 26 - 5) + (v f1 - (pow2 26 - 1)) * pow26 + (v f2 - (pow2 26 - 1)) * pow52 +
    (v f3 - (pow2 26 - 1)) * pow78 + (v f4 - (pow2 26 - 1)) * pow104) % prime;
    (==) {
      assert_norm (pow2 26 * pow26 = pow52);
      assert_norm (pow2 26 * pow52 = pow78);
      assert_norm (pow2 26 * pow78 = pow104);
      assert_norm (pow2 26 * pow104 = pow2 130) }
    (v f0 + v f1 * pow26 + v f2 * pow52 + v f3 * pow78 + v f4 * pow104 - prime) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_sub (v f0 + v f1 * pow26 + v f2 * pow52 + v f3 * pow78 + v f4 * pow104) prime 1 }
    (v f0 + v f1 * pow26 + v f2 * pow52 + v f3 * pow78 + v f4 * pow104) % prime;
    (==) { }
    as_nat5 f % prime;
    };
  assert (as_nat5 f' % prime == as_nat5 f % prime);
  FStar.Math.Lemmas.modulo_lemma (as_nat5 f') prime


val lemma_subtract_p5:
    f:tup64_5{tup64_fits5 f (1, 1, 1, 1, 1)}
  -> f':tup64_5 ->
  Lemma
  (requires
    (let (f0, f1, f2, f3, f4) = f in
     let (f0', f1', f2', f3', f4') = f' in
     ((v f4 = 0x3ffffff && v f3 = 0x3ffffff && v f2 = 0x3ffffff && v f1 = 0x3ffffff && v f0 >= 0x3fffffb) /\
     (v f0' = v f0 - 0x3fffffb && v f1' = v f1 - 0x3ffffff && v f2' = v f2 - 0x3ffffff && v f3' = v f3 - 0x3ffffff && v f4' = v f4 - 0x3ffffff)) \/
     ((v f4 <> 0x3ffffff || v f3 <> 0x3ffffff || v f2 <> 0x3ffffff || v f1 <> 0x3ffffff || v f0 < 0x3fffffb) /\
     (v f0' = v f0 && v f1' = v f1 && v f2' = v f2 && v f3' = v f3 && v f4' = v f4))))
  (ensures as_nat5 f' == as_nat5 f % prime)

let lemma_subtract_p5 f f' =
  let (f0, f1, f2, f3, f4) = f in
  let (f0', f1', f2', f3', f4') = f' in
  assert_norm (max26 = pow2 26 - 1);
  if ((v f4 <> 0x3ffffff || v f3 <> 0x3ffffff || v f2 <> 0x3ffffff || v f1 <> 0x3ffffff || v f0 < 0x3fffffb) &&
     (v f0' = v f0 && v f1' = v f1 && v f2' = v f2 && v f3' = v f3 && v f4' = v f4))
  then lemma_subtract_p5_0 f f'
  else lemma_subtract_p5_1 f f'


noextract
val subtract_p5_s:
    #w:lanes
  -> f:felem5 w{felem_fits5 f (1, 1, 1, 1, 1)}
  -> i:nat{i < w} ->
  Pure tup64_5
  (requires True)
  (ensures  fun out ->
    tup64_fits5 out (1, 1, 1, 1, 1) /\
    as_nat5 out == as_nat5 (as_tup64_i f i) % prime)

let subtract_p5_s #w f i =
  let (f0, f1, f2, f3, f4) = as_tup64_i f i in
  let mask0 = eq_mask f4 (u64 0x3ffffff) in
  let mask1 = mask0 &. eq_mask f3 (u64 0x3ffffff) in
  let mask2 = mask1 &. eq_mask f2 (u64 0x3ffffff) in
  let mask3 = mask2 &. eq_mask f1 (u64 0x3ffffff) in
  let mask4 = mask3 &. gte_mask f0 (u64 0x3fffffb) in

  let p0 = mask4 &. u64 0x3fffffb in
  logand_lemma mask4 (u64 0x3fffffb);
  let p1 = mask4 &. u64 0x3ffffff in
  logand_lemma mask4 (u64 0x3ffffff);
  let p2 = mask4 &. u64 0x3ffffff in
  let p3 = mask4 &. u64 0x3ffffff in
  let p4 = mask4 &. u64 0x3ffffff in

  let f0' = f0 -. p0 in
  let f1' = f1 -. p1 in
  let f2' = f2 -. p2 in
  let f3' = f3 -. p3 in
  let f4' = f4 -. p4 in
  lemma_subtract_p5 (f0, f1, f2, f3, f4) (f0', f1', f2', f3', f4');
  (f0', f1', f2', f3', f4')

#push-options "--max_ifuel 1"
val subtract_p5_felem5_lemma_i:
    #w:lanes
  -> f:felem5 w{felem_fits5 f (1, 1, 1, 1, 1)}
  -> i:nat{i < w} ->
  Lemma
  (tup64_fits5 (as_tup64_i (subtract_p5 #w f) i) (1, 1, 1, 1, 1) /\
   as_nat5 (as_tup64_i (subtract_p5 #w f) i) == as_nat5 (as_tup64_i f i) % prime)

let subtract_p5_felem5_lemma_i #w f i =
  assert (subtract_p5_s #w f i == as_tup64_i (subtract_p5 #w f) i)
#pop-options

val subtract_p5_felem5_lemma:
    #w:lanes
  -> f:felem5 w{felem_fits5 f (1, 1, 1, 1, 1)} ->
  Lemma
  (felem_fits5 (subtract_p5 f) (1, 1, 1, 1, 1) /\
  (fas_nat5 (subtract_p5 f)).[0] == (feval5 f).[0])

let subtract_p5_felem5_lemma #w f =
  match w with
  | 1 ->
    subtract_p5_felem5_lemma_i #w f 0
  | 2 ->
    subtract_p5_felem5_lemma_i #w f 0;
    subtract_p5_felem5_lemma_i #w f 1
  | 4 ->
    subtract_p5_felem5_lemma_i #w f 0;
    subtract_p5_felem5_lemma_i #w f 1;
    subtract_p5_felem5_lemma_i #w f 2;
    subtract_p5_felem5_lemma_i #w f 3


noextract
let acc_inv_t (#w:lanes) (acc:felem5 w) : Type0 =
  let (o0, o1, o2, o3, o4) = acc in
  forall (i:nat). i < w ==>
   (if uint_v (vec_v o0).[i] >= pow2 26 then
      tup64_fits5 (as_tup64_i acc i) (2, 1, 1, 1, 1) /\
      uint_v (vec_v o0).[i] % pow2 26 < 47
    else tup64_fits5 (as_tup64_i acc i) (1, 1, 1, 1, 1))

val acc_inv_lemma_i:
    #w:lanes
  -> acc:felem5 w{felem_fits5 acc (1, 1, 1, 1, 1)}
  -> cin:uint64xN w{uint64xN_fits cin 45}
  -> i:nat{i < w} ->
  Lemma
  (let (i0, i1, i2, i3, i4) = acc in
   let i0' = vec_add_mod i0 cin in
   let acc1 = (i0', i1, i2, i3, i4) in
  (if (uint64xN_v i0').[i] >= pow2 26 then
    tup64_fits5 (as_tup64_i acc1 i) (2, 1, 1, 1, 1) /\
    (uint64xN_v i0').[i] % pow2 26 < 47
  else tup64_fits5 (as_tup64_i acc1 i) (1, 1, 1, 1, 1)))

let acc_inv_lemma_i #w acc cin i =
  let (i0, i1, i2, i3, i4) = acc in
  let i0' = vec_add_mod i0 cin in
  assert ((vec_v i0').[i] == (vec_v i0).[i] +. (vec_v cin).[i]);
  assert ((uint64xN_v i0).[i] + (uint64xN_v cin).[i] <= max26 + 46);
  assert_norm (max26 = pow2 26 - 1);
  FStar.Math.Lemmas.euclidean_division_definition ((uint64xN_v i0).[i] + (uint64xN_v cin).[i]) (pow2 26)

val acc_inv_lemma:
    #w:lanes
  -> acc:felem5 w{felem_fits5 acc (1, 1, 1, 1, 1)}
  -> cin:uint64xN w{uint64xN_fits cin 45} ->
  Lemma
  (let (i0, i1, i2, i3, i4) = acc in
   let i0' = vec_add_mod i0 cin in
   acc_inv_t (i0', i1, i2, i3, i4))

let acc_inv_lemma #w acc cin =
  match w with
  | 1 ->
    acc_inv_lemma_i #w acc cin 0
  | 2 ->
    acc_inv_lemma_i #w acc cin 0;
    acc_inv_lemma_i #w acc cin 1
  | 4 ->
    acc_inv_lemma_i #w acc cin 0;
    acc_inv_lemma_i #w acc cin 1;
    acc_inv_lemma_i #w acc cin 2;
    acc_inv_lemma_i #w acc cin 3

val carry_full_felem5_fits_lemma0: #w:lanes -> f:felem5 w{felem_fits5 f (8, 8, 8, 8, 8)} ->
  Lemma (let (f0, f1, f2, f3, f4) = f in
    let tmp0,c0 = carry26 f0 (zero w) in
    let tmp1,c1 = carry26 f1 c0 in
    let tmp2,c2 = carry26 f2 c1 in
    let tmp3,c3 = carry26 f3 c2 in
    let tmp4,c4 = carry26 f4 c3 in
    felem_fits5 (tmp0, tmp1, tmp2, tmp3, tmp4) (1, 1, 1, 1, 1) /\ uint64xN_fits c4 9)
let carry_full_felem5_fits_lemma0 #w (f0, f1, f2, f3, f4) =
  let tmp0,c0 = carry26 f0 (zero w) in
  carry26_fits_lemma 1 8 f0 (zero w);
  let tmp1,c1 = carry26 f1 c0 in
  carry26_fits_lemma 1 8 f1 c0;
  let tmp2,c2 = carry26 f2 c1 in
  carry26_fits_lemma 1 8 f2 c1;
  let tmp3,c3 = carry26 f3 c2 in
  carry26_fits_lemma 1 8 f3 c2;
  let tmp4,c4 = carry26 f4 c3 in
  carry26_fits_lemma 1 8 f4 c3;
  assert (felem_fits5 (tmp0, tmp1, tmp2, tmp3, tmp4) (1, 1, 1, 1, 1));
  assert (uint64xN_fits c4 9)


val carry_full_felem5_fits_lemma: #w:lanes -> f:felem5 w{felem_fits5 f (8, 8, 8, 8, 8)} ->
  Lemma (acc_inv_t (carry_full_felem5 f))
let carry_full_felem5_fits_lemma #w f =
  let (f0, f1, f2, f3, f4) = f in
  let tmp0,c0 = carry26 f0 (zero w) in
  let tmp1,c1 = carry26 f1 c0 in
  let tmp2,c2 = carry26 f2 c1 in
  let tmp3,c3 = carry26 f3 c2 in
  let tmp4,c4 = carry26 f4 c3 in
  carry_full_felem5_fits_lemma0 #w f;
  assert (felem_fits1 tmp0 1 /\ uint64xN_fits c4 9);
  let tmp0' = vec_add_mod tmp0 (vec_smul_mod c4 (u64 5)) in
  acc_inv_lemma (tmp0, tmp1, tmp2, tmp3, tmp4) (vec_smul_mod c4 (u64 5))


val carry_full_felem5_eval_lemma_i0:
    inp:tup64_5
  -> tmp:tup64_5
  -> vc0:nat -> vc1:nat -> vc2:nat -> vc3:nat -> vc4:nat ->
  Lemma
  (requires
   (let (t0, t1, t2, t3, t4) = tmp in
    let (ti0, ti1, ti2, ti3, ti4) = inp in
    v ti0 == vc0 * pow2 26 + v t0 /\
    v ti1 + vc0 == vc1 * pow2 26 + v t1 /\
    v ti2 + vc1 == vc2 * pow2 26 + v t2 /\
    v ti3 + vc2 == vc3 * pow2 26 + v t3 /\
    v ti4 + vc3 == vc4 * pow2 26 + v t4))
  (ensures
   (let (t0, t1, t2, t3, t4) = tmp in
    let (ti0, ti1, ti2, ti3, ti4) = inp in
    as_nat5 inp % prime ==
    (v t0 + vc4 * 5 + v t1 * pow26 + v t2 * pow52 + v t3 * pow78 + v t4 * pow104) % prime))

let carry_full_felem5_eval_lemma_i0 inp tmp vc0 vc1 vc2 vc3 vc4 =
  let (t0, t1, t2, t3, t4) = tmp in
  let (ti0, ti1, ti2, ti3, ti4) = inp in
  let tmp_n = v t0 + v t1 * pow26 + v t2 * pow52 + v t3 * pow78 + v t4 * pow104 in

  calc (==) {
    as_nat5 inp % prime;
    (==) { }
    (v ti0 + v ti1 * pow26 + v ti2 * pow52 + v ti3 * pow78 + v ti4 * pow104) % prime;
    (==) { }
    (vc0 * pow2 26 + v t0 +
    (vc1 * pow2 26 + v t1 - vc0) * pow26 +
    (vc2 * pow2 26 + v t2 - vc1) * pow52 +
    (vc3 * pow2 26 + v t3 - vc2) * pow78 +
    (vc4 * pow2 26 + v t4 - vc3) * pow104) % prime;
    (==) {
      assert_norm (pow2 26 * pow26 = pow52);
      assert_norm (pow2 26 * pow52 = pow78);
      assert_norm (pow2 26 * pow78 = pow104);
      assert_norm (pow2 26 * pow104 = pow2 130)}
    (v t0 + v t1 * pow26 + v t2 * pow52 + v t3 * pow78 + v t4 * pow104 + vc4 * pow2 130) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r tmp_n (vc4 * pow2 130) prime }
    (tmp_n + (vc4 * pow2 130 % prime)) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_r (vc4) (pow2 130) prime }
    (tmp_n + (vc4 * (pow2 130 % prime) % prime)) % prime;
    (==) { lemma_prime () }
    (tmp_n + (vc4 * 5 % prime)) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r tmp_n (vc4 * 5) prime }
    (tmp_n + vc4 * 5) % prime;
  };
  assert (as_nat5 inp % prime == (tmp_n + vc4 * 5) % prime)


val carry_full_felem5_eval_lemma_i1:
    #w:lanes
  -> inp:felem_wide5 w{felem_fits5 inp (8, 8, 8, 8, 8)}
  -> i:nat{i < w} ->
  Lemma
  (let (i0, i1, i2, i3, i4) = inp in
   let tmp0,c0 = carry26 i0 (zero w) in
   let tmp1,c1 = carry26 i1 c0 in
   let tmp2,c2 = carry26 i2 c1 in
   let tmp3,c3 = carry26 i3 c2 in
   let tmp4,c4 = carry26 i4 c3 in

   let tmp = (tmp0, tmp1, tmp2, tmp3, tmp4) in
   let (t0, t1, t2, t3, t4) = as_tup64_i tmp i in
   let vc4 = (uint64xN_v c4).[i] in
   (feval5 inp).[i] == (v t0 + vc4 * 5 + v t1 * pow26 + v t2 * pow52 + v t3 * pow78 + v t4 * pow104) % prime)

let carry_full_felem5_eval_lemma_i1 #w inp i =
  let (i0, i1, i2, i3, i4) = inp in
  let tmp0,c0 = carry26 i0 (zero w) in
  let tmp1,c1 = carry26 i1 c0 in
  let tmp2,c2 = carry26 i2 c1 in
  let tmp3,c3 = carry26 i3 c2 in
  let tmp4,c4 = carry26 i4 c3 in

  let tmp = (tmp0, tmp1, tmp2, tmp3, tmp4) in
  let (t0, t1, t2, t3, t4) = as_tup64_i tmp i in
  let (ti0, ti1, ti2, ti3, ti4) = as_tup64_i inp i in
  let vc0 = (uint64xN_v c0).[i] in
  let vc1 = (uint64xN_v c1).[i] in
  let vc2 = (uint64xN_v c2).[i] in
  let vc3 = (uint64xN_v c3).[i] in
  let vc4 = (uint64xN_v c4).[i] in

  carry26_eval_lemma 1 8 i0 (zero w);
  assert (v ti0 == vc0 * pow2 26 + v t0);
  carry26_eval_lemma 1 8 i1 c0;
  assert (v ti1 + vc0 == vc1 * pow2 26 + v t1);
  carry26_eval_lemma 1 8 i2 c1;
  assert (v ti2 + vc1 == vc2 * pow2 26 + v t2);
  carry26_eval_lemma 1 8 i3 c2;
  assert (v ti3 + vc2 == vc3 * pow2 26 + v t3);
  carry26_eval_lemma 1 8 i4 c3;
  assert (v ti4 + vc3 == vc4 * pow2 26 + v t4);

  carry_full_felem5_eval_lemma_i0 (ti0, ti1, ti2, ti3, ti4) (t0, t1, t2, t3, t4) vc0 vc1 vc2 vc3 vc4;
  assert ((feval5 inp).[i] ==
   (v t0 + vc4 * 5 + v t1 * pow26 + v t2 * pow52 + v t3 * pow78 + v t4 * pow104) % prime)


val carry_full_felem5_eval_lemma_i:
    #w:lanes
  -> inp:felem_wide5 w{felem_fits5 inp (8, 8, 8, 8, 8)}
  -> i:nat{i < w} ->
  Lemma ((feval5 (carry_full_felem5 #w inp)).[i] == (feval5 inp).[i])

let carry_full_felem5_eval_lemma_i #w inp i =
  let (i0, i1, i2, i3, i4) = inp in
  let tmp0,c0 = carry26 i0 (zero w) in
  let tmp1,c1 = carry26 i1 c0 in
  let tmp2,c2 = carry26 i2 c1 in
  let tmp3,c3 = carry26 i3 c2 in
  let tmp4,c4 = carry26 i4 c3 in

  let tmp = (tmp0, tmp1, tmp2, tmp3, tmp4) in
  let (t0, t1, t2, t3, t4) = as_tup64_i tmp i in
  let (ti0, ti1, ti2, ti3, ti4) = as_tup64_i inp i in
  let vc4 = (uint64xN_v c4).[i] in
  carry_full_felem5_fits_lemma0 #w inp;

  let cin = vec_smul_mod c4 (u64 5) in
  assert ((uint64xN_v cin).[i] == vc4 * 5);
  let tmp0' = vec_add_mod tmp0 cin in
  Math.Lemmas.small_mod ((uint64xN_v tmp0).[i] + vc4 * 5) (pow2 64);
  assert ((uint64xN_v tmp0').[i] == (uint64xN_v tmp0).[i] + vc4 * 5);

  let out = (tmp0', tmp1, tmp2, tmp3, tmp4) in
  let (o0, o1, o2, o3, o4) = as_tup64_i out i in
  assert ((feval5 out).[i] == (v t0 + vc4 * 5 + v t1 * pow26 + v t2 * pow52 + v t3 * pow78 + v t4 * pow104) % prime);
  carry_full_felem5_eval_lemma_i1 #w inp i;
  assert ((feval5 out).[i] == (feval5 inp).[i])


val carry_full_felem5_eval_lemma:
    #w:lanes
  -> inp:felem_wide5 w
  -> Lemma
    (requires felem_fits5 inp (8, 8, 8, 8, 8))
    (ensures  feval5 (carry_full_felem5 #w inp) == feval5 inp)

let carry_full_felem5_eval_lemma #w inp =
  let o = carry_full_felem5 #w inp in
  FStar.Classical.forall_intro (carry_full_felem5_eval_lemma_i #w inp);
  eq_intro (feval5 o) (feval5 inp)


val carry_full_felem5_lemma:
    #w:lanes
  -> f:felem5 w{felem_fits5 f (8, 8, 8, 8, 8)} ->
  Lemma
  (felem_fits5 (carry_full_felem5 f) (2, 1, 1, 1, 1) /\
   feval5 (carry_full_felem5 f) == feval5 f)
let carry_full_felem5_lemma #w f =
  carry_full_felem5_eval_lemma f;
  carry_full_felem5_fits_lemma f


val carry_reduce_lemma_i:
    #w:lanes
  -> l:uint64xN w
  -> cin:uint64xN w
  -> i:nat{i < w} ->
  Lemma
  (requires
    (uint64xN_v l).[i] <= 2 * max26 /\
    (uint64xN_v cin).[i] <= 62 * max26)
  (ensures
    (let (l0, l1) = carry26 #w l cin in
    (uint64xN_v l0).[i] <= max26 /\ (uint64xN_v l1).[i] <= 63 /\
   (uint64xN_v l).[i] + (uint64xN_v cin).[i] ==
     (uint64xN_v l1).[i] * pow2 26 + (uint64xN_v l0).[i]))

let carry_reduce_lemma_i #w l cin i =
  let li = (vec_v l).[i] in
  let cini = (vec_v cin).[i] in
  let mask26 = u64 0x3ffffff in
  assert_norm (0x3ffffff = pow2 26 - 1);
  FStar.Math.Lemmas.modulo_lemma (v li + v cini) (pow2 64);
  let li' = li +! cini in
  let li0 = li' &. mask26 in
  let li1 = li' >>. 26ul in
  mod_mask_lemma li' 26ul;
  assert (v (mod_mask #U64 #SEC 26ul) == v mask26);
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v li') 26 32;
  FStar.Math.Lemmas.pow2_minus 32 26


#push-options "--z3rlimit 150"
val carry_reduce_felem5_fits_lemma_i0:
    #w:lanes
  -> f:felem5 w{acc_inv_t f}
  -> i:nat{i < w} ->
  Lemma
  (let (f0, f1, f2, f3, f4) = f in
   let tmp0,c0 = carry26 f0 (zero w) in
   let tmp1,c1 = carry26 f1 c0 in
   let tmp2,c2 = carry26 f2 c1 in
   let tmp3,c3 = carry26 f3 c2 in
   let tmp4,c4 = carry26 f4 c3 in
   let res = (tmp0, tmp1, tmp2, tmp3, tmp4) in
   (if (uint64xN_v f0).[i] < pow2 26 then (uint64xN_v tmp0).[i] < pow2 26 else (uint64xN_v tmp0).[i] <= 46) /\
   (if (uint64xN_v f0).[i] < pow2 26 then (uint64xN_v c4).[i] = 0 else (uint64xN_v c4).[i] <= 63) /\
   (uint64xN_v c4).[i] <= 63 /\
   tup64_fits5 (as_tup64_i res i) (1, 1, 1, 1, 1))

let carry_reduce_felem5_fits_lemma_i0 #w f i =
  let (f0, f1, f2, f3, f4) = f in
  let tmp0,c0 = carry26 f0 (zero w) in
  carry_reduce_lemma_i f0 (zero w) i;
  assert (if (uint64xN_v f0).[i] < pow2 26 then (uint64xN_v tmp0).[i] < pow2 26 else (uint64xN_v tmp0).[i] <= 46);
  assert (if (uint64xN_v f0).[i] < pow2 26 then (uint64xN_v c0).[i] = 0 else (uint64xN_v c0).[i] <= 63);
  let tmp1,c1 = carry26 f1 c0 in
  carry_reduce_lemma_i f1 c0 i;
  assert (if (uint64xN_v c0).[i] = 0 then (uint64xN_v c1).[i] = 0 else (uint64xN_v c1).[i] <= 63);
  let tmp2,c2 = carry26 f2 c1 in
  carry_reduce_lemma_i f2 c1 i;
  assert (if (uint64xN_v c0).[i] = 0 then (uint64xN_v c2).[i] = 0 else (uint64xN_v c2).[i] <= 63);
  let tmp3,c3 = carry26 f3 c2 in
  carry_reduce_lemma_i f3 c2 i;
  assert (if (uint64xN_v c0).[i] = 0 then (uint64xN_v c3).[i] = 0 else (uint64xN_v c3).[i] <= 63);
  let tmp4,c4 = carry26 f4 c3 in
  carry_reduce_lemma_i f4 c3 i;
  assert (if (uint64xN_v c0).[i] = 0 then (uint64xN_v c4).[i] = 0 else (uint64xN_v c4).[i] <= 63);
  assert (if (uint64xN_v f0).[i] < pow2 26 then (uint64xN_v c0).[i] = 0 /\ (uint64xN_v c4).[i] = 0 else (uint64xN_v c4).[i] <= 63);
  let res = (tmp0, tmp1, tmp2, tmp3, tmp4) in
  assert (tup64_fits5 (as_tup64_i res i) (1, 1, 1, 1, 1))


val carry_reduce_felem5_fits_lemma_i:
    #w:lanes
  -> f:felem5 w{acc_inv_t f}
  -> i:nat{i < w} ->
  Lemma (tup64_fits5 (as_tup64_i (carry_full_felem5 f) i) (1, 1, 1, 1, 1))

let carry_reduce_felem5_fits_lemma_i #w f i =
  assert_norm (max26 == pow2 26 - 1);
  let (f0, f1, f2, f3, f4) = f in
  let tmp0,c0 = carry26 f0 (zero w) in
  let tmp1,c1 = carry26 f1 c0 in
  let tmp2,c2 = carry26 f2 c1 in
  let tmp3,c3 = carry26 f3 c2 in
  let tmp4,c4 = carry26 f4 c3 in
  carry_reduce_felem5_fits_lemma_i0 #w f i;

  FStar.Math.Lemmas.modulo_lemma ((uint64xN_v c4).[i] * 5) (pow2 64);
  assert ((uint64xN_v (vec_smul_mod c4 (u64 5))).[i] == (uint64xN_v c4).[i] * 5);
  let tmp0' = vec_add_mod tmp0 (vec_smul_mod c4 (u64 5)) in
  carry_reduce_felem5_fits_lemma_i0 #w f i;
  let res = (tmp0', tmp1, tmp2, tmp3, tmp4) in
  assert (tup64_fits5 (as_tup64_i res i) (1, 1, 1, 1, 1))
#pop-options


val carry_reduce_felem5_fits_lemma:
    #w:lanes
  -> f:felem5 w{acc_inv_t f} ->
  Lemma (felem_fits5 (carry_full_felem5 f) (1, 1, 1, 1, 1))

let carry_reduce_felem5_fits_lemma #w f =
  match w with
  | 1 ->
    carry_reduce_felem5_fits_lemma_i #w f 0
  | 2 ->
    carry_reduce_felem5_fits_lemma_i #w f 0;
    carry_reduce_felem5_fits_lemma_i #w f 1
  | 4 ->
    carry_reduce_felem5_fits_lemma_i #w f 0;
    carry_reduce_felem5_fits_lemma_i #w f 1;
    carry_reduce_felem5_fits_lemma_i #w f 2;
    carry_reduce_felem5_fits_lemma_i #w f 3


val carry_reduce_felem5_lemma:
    #w:lanes
  -> f:felem5 w{acc_inv_t f} ->
  Lemma
  (felem_fits5 (carry_full_felem5 f) (1, 1, 1, 1, 1) /\
   feval5 (carry_full_felem5 f) == feval5 f)

let carry_reduce_felem5_lemma #w f =
  carry_reduce_felem5_fits_lemma #w f;
  carry_full_felem5_eval_lemma f
