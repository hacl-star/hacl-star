module Hacl.Spec.Poly1305.Field32.Lemmas

open Lib.Sequence
open Lib.IntTypes
open FStar.Mul
open NatPrime

open Hacl.Spec.Poly1305.Field32.Definition

#reset-options "--z3rlimit 50 --max_fuel 0 --using_facts_from '* -FStar.Seq'"

(* Move the following lemmas to Lib.IntTypes *)
val eq_mask_logand_lemma: a:uint32 -> b:uint32 -> c:uint32 ->
  Lemma
  (requires True)
  (ensures
    (if v a = v b then
      v (c `logand` (eq_mask a b)) == v c
    else
      v (c `logand` (eq_mask a b)) == 0))
  [SMTPat (c `logand` (eq_mask a b))]
let eq_mask_logand_lemma a b c = admit()

val gte_mask_logand_lemma: a:uint32 -> b:uint32 -> c:uint32 ->
  Lemma
  (requires True)
  (ensures
    (if v a >= v b then
      v (c `logand` (gte_mask a b)) == v c
    else
      v (c `logand` (gte_mask a b)) == 0))
  [SMTPat (c `logand` (gte_mask a b))]
let gte_mask_logand_lemma a b c = admit()

val eq_mask_lemma: a:uint32 -> b:uint32 ->
  Lemma
  (requires True)
  (ensures
  (if v a = v b then
    v (eq_mask a b) == pow2 32 - 1
  else
    v (eq_mask a b) == 0))
  [SMTPat (eq_mask a b)]
let eq_mask_lemma a b = admit()

val gte_mask_lemma: a:uint32 -> b:uint32 ->
  Lemma
  (requires True)
  (ensures
    (if v a >= v b then
      v (gte_mask a b) == pow2 32 - 1
    else
      v (gte_mask a b) == 0))
  [SMTPat (gte_mask a b)]
let gte_mask_lemma a b = admit()

val logand_lemma: a:uint32 -> b:uint32 ->
  Lemma
  (requires v a = 0 \/ v a = pow2 32 - 1)
  (ensures
    (if v a = 0 then
      v (a `logand` b) == 0
    else
      v (a `logand` b) == v b))
  [SMTPat (a `logand` b)]
let logand_lemma a b = admit()
(* end *)

val lemma_mul5_distr_l:
  a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> f:nat ->
  Lemma (a * (b + c + d + e + f) == a * b + a * c + a * d + a * e + a * f)
let lemma_mul5_distr_l a b c d e f = ()

val lemma_mul_assos_6:
  a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> f:nat ->
  Lemma (a * b * c * d * e * f == a * (b * c * d * e * f))
let lemma_mul_assos_6 a b c d e f = ()

val lemma_prime: unit ->
  Lemma (pow2 130 % prime = 5)
let lemma_prime () =
  assert_norm (pow2 130 % prime = 5 % prime);
  assert_norm (5 < prime);
  FStar.Math.Lemmas.modulo_lemma 5 prime

val lemma_acc_inv:
    acc:felem5{felem_fits5 acc (1, 1, 1, 1, 1)}
  -> cin:uint32{v cin < pow2 26}
  -> Lemma
    (let (i0, i1, i2, i3, i4) = acc in
     let i1' = i1 +! cin in
     let out = (i0, i1', i2, i3, i4) in
     if (v i1 + v cin) / pow2 26 > 0 then
       felem_fits5 out (1, 2, 1, 1, 1) /\ (v i1 + v cin) % pow2 26 < v cin
     else felem_fits5 out (1, 1, 1, 1, 1))
let lemma_acc_inv acc cin = ()

//#set-options "--z3rlimit 150"

val lemma_carry26:
    l:uint32
  -> cin:uint32
  -> Lemma
    (requires felem_fits1 l 2 /\ felem_fits1 cin 62)
    (ensures
     (let l0 = (l +! cin) &. mask26 in
      let l1 = (l +! cin) >>. 26ul in
      v l + v cin == v l1 * pow2 26 + v l0 /\
      felem_fits1 l0 1 /\ v l1 <= 64))
let lemma_carry26 l cin =
  let l' = l +! cin in
  let l0 = l' &. mask26 in
  let l1 = l' >>. 26ul in
  mod_mask_lemma (to_u64 l') 26ul;
  uintv_extensionality (mod_mask #U32 #SEC 26ul) mask26;
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v l') 26 32;
  FStar.Math.Lemmas.euclidean_division_definition (v l') (pow2 26);
  FStar.Math.Lemmas.pow2_minus 32 26

val lemma_carry26_wide:
    #m:scale64{m < 64}
  -> l:uint64{felem_wide_fits1 l m}
  -> cin:uint32{felem_fits1 cin 64}
  -> Lemma (
      let l' = l +! to_u64 cin in
      let l0 = (to_u32 l') &. mask26 in
      let l1 = to_u32 (l' >>. 26ul) in
      v l + v cin == v l1 * pow2 26 + v l0 /\
      felem_fits1 l0 1 /\ felem_fits1 l1 (m + 1))
let lemma_carry26_wide #m l cin =
  let l' = l +! to_u64 cin in
  let l0 = (to_u32 l') &. mask26 in
  let l1 = to_u32 (l' >>. 26ul) in
  mod_mask_lemma (to_u32 l') 26ul;
  uintv_extensionality (mod_mask #U32 #SEC 26ul) mask26;
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v l') 26 32;
  FStar.Math.Lemmas.euclidean_division_definition (v l') (pow2 26)

val lemma_carry_wide5_simplify:
  inp:felem_wide5{felem_wide_fits5 inp (47, 35, 27, 19, 11)} ->
  c0:uint32 -> c1:uint32 -> c2:uint32 -> c3:uint32 -> c4:uint32 ->
  t0:uint32 -> t1:uint32 -> t2:uint32 -> t3:uint32 -> t4:uint32 ->
  Lemma
    (requires
    feval_wide inp ==
    (v c0 * pow2 26 + v t0 +
    (v c1 * pow2 26 + v t1 - v c0) * pow26 +
    (v c2 * pow2 26 + v t2 - v c1) * pow26 * pow26 +
    (v c3 * pow2 26 + v t3 - v c2) * pow26 * pow26 * pow26 +
    (v c4 * pow2 26 + v t4 - v c3) * pow26 * pow26 * pow26 * pow26) % prime)
   (ensures
    feval_wide inp ==
    (v t0 + v c4 * 5 + v t1 * pow26 + v t2 * pow26 * pow26 +
     v t3 * pow26 * pow26 * pow26 + v t4 * pow26 * pow26 * pow26 * pow26) % prime)
let lemma_carry_wide5_simplify inp c0 c1 c2 c3 c4 t0 t1 t2 t3 t4 =
  assert (
    v c0 * pow2 26 + v t0 +
    (v c1 * pow2 26 + v t1 - v c0) * pow26 +
    (v c2 * pow2 26 + v t2 - v c1) * pow26 * pow26 +
    (v c3 * pow2 26 + v t3 - v c2) * pow26 * pow26 * pow26 +
    (v c4 * pow2 26 + v t4 - v c3) * pow26 * pow26 * pow26 * pow26 ==
    v t0 + v t1 * pow26 + v t2 * pow26 * pow26 + v t3 * pow26 * pow26 * pow26 +
    v t4 * pow26 * pow26 * pow26 * pow26 + v c4 * pow2 26 * pow26 * pow26 * pow26 * pow26);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
   (v t0 + v t1 * pow26 +
    v t2 * pow26 * pow26 +
    v t3 * pow26 * pow26 * pow26 +
    v t4 * pow26 * pow26 * pow26 * pow26)
   (v c4 * pow2 26 * pow26 * pow26 * pow26 * pow26) prime;
  lemma_mul_assos_6 (v c4) (pow2 26) pow26 pow26 pow26 pow26;
  assert_norm (pow2 26 * pow26 * pow26 * pow26 * pow26 = pow2 130);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v c4) (pow2 130) prime;
  lemma_prime ();
  assert_norm ((v c4 * pow2 130) % prime == (v c4 * 5) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
   (v t0 + v t1 * pow26 +
    v t2 * pow26 * pow26 +
    v t3 * pow26 * pow26 * pow26 +
    v t4 * pow26 * pow26 * pow26 * pow26)
   (v c4 * 5) prime

(* the same proof as for lemma_carry_wide5_simplify *)
val lemma_carry_felem5_full_simplify:
  inp:felem5 ->
  c0:uint32 -> c1:uint32 -> c2:uint32 -> c3:uint32 -> c4:uint32 ->
  t0:uint32 -> t1:uint32 -> t2:uint32 -> t3:uint32 -> t4:uint32 ->
  Lemma
    (requires
    feval inp ==
    (v c0 * pow2 26 + v t0 +
    (v c1 * pow2 26 + v t1 - v c0) * pow26 +
    (v c2 * pow2 26 + v t2 - v c1) * pow26 * pow26 +
    (v c3 * pow2 26 + v t3 - v c2) * pow26 * pow26 * pow26 +
    (v c4 * pow2 26 + v t4 - v c3) * pow26 * pow26 * pow26 * pow26) % prime)
   (ensures
    feval inp ==
    (v t0 + v c4 * 5 + v t1 * pow26 + v t2 * pow26 * pow26 +
     v t3 * pow26 * pow26 * pow26 + v t4 * pow26 * pow26 * pow26 * pow26) % prime)
let lemma_carry_felem5_full_simplify inp c0 c1 c2 c3 c4 t0 t1 t2 t3 t4 =
  assert (
    v c0 * pow2 26 + v t0 +
    (v c1 * pow2 26 + v t1 - v c0) * pow26 +
    (v c2 * pow2 26 + v t2 - v c1) * pow26 * pow26 +
    (v c3 * pow2 26 + v t3 - v c2) * pow26 * pow26 * pow26 +
    (v c4 * pow2 26 + v t4 - v c3) * pow26 * pow26 * pow26 * pow26 ==
    v t0 + v t1 * pow26 + v t2 * pow26 * pow26 + v t3 * pow26 * pow26 * pow26 +
    v t4 * pow26 * pow26 * pow26 * pow26 + v c4 * pow2 26 * pow26 * pow26 * pow26 * pow26);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
   (v t0 + v t1 * pow26 +
    v t2 * pow26 * pow26 +
    v t3 * pow26 * pow26 * pow26 +
    v t4 * pow26 * pow26 * pow26 * pow26)
   (v c4 * pow2 26 * pow26 * pow26 * pow26 * pow26) prime;
  lemma_mul_assos_6 (v c4) (pow2 26) pow26 pow26 pow26 pow26;
  assert_norm (pow2 26 * pow26 * pow26 * pow26 * pow26 = pow2 130);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v c4) (pow2 130) prime;
  lemma_prime ();
  assert_norm ((v c4 * pow2 130) % prime == (v c4 * 5) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
   (v t0 + v t1 * pow26 +
    v t2 * pow26 * pow26 +
    v t3 * pow26 * pow26 * pow26 +
    v t4 * pow26 * pow26 * pow26 * pow26)
   (v c4 * 5) prime

val lemma_smul_felem5:
    #m1:scale32
  -> #m2:scale32_5
  -> u1:uint32{felem_fits1 u1 m1}
  -> f2:felem5{felem_fits5 f2 m2 /\ m1 *^ m2 <=* s64x5 4096}
  -> Lemma (let (f20, f21, f22, f23, f24) = f2 in
      v u1 * as_nat5 f2 == v u1 * v f20 + v u1 * v f21 * pow26 +
      v u1 * v f22 * pow26 * pow26 + v u1 * v f23 * pow26 * pow26 * pow26 +
      v u1 * v f24 * pow26 * pow26 * pow26 * pow26)
let lemma_smul_felem5 #m1 #m2 u1 f2 =
  let (f20, f21, f22, f23, f24) = f2 in
  assert (v u1 * as_nat5 f2 == v u1 * (v f20 + v f21 * pow26 + v f22 * pow26 * pow26 +
    v f23 * pow26 * pow26 * pow26 + v f24 * pow26 * pow26 * pow26 * pow26))

#set-options "--z3rlimit 100"

val lemma_smul_add_felem5:
    #m1:scale32
  -> #m2:scale32_5
  -> #m3:scale64_5
  -> u1:uint32{felem_fits1 u1 m1}
  -> f2:felem5{felem_fits5 f2 m2}
  -> acc1:felem_wide5{felem_wide_fits5 acc1 m3 /\ m3 +* m1 *^ m2 <=* s64x5 4096}
  -> Lemma (let (f20, f21, f22, f23, f24) = f2 in
      let (o0, o1, o2, o3, o4) = acc1 in
      wide_as_nat5 acc1 + uint_v u1 * as_nat5 f2 ==
      v o0 + v o1 * pow26 + v o2 * pow26 * pow26 +
      v o3 * pow26 * pow26 * pow26 + v o4 * pow26 * pow26 * pow26 * pow26 +
      v u1 * v f20 + v u1 * v f21 * pow26 +
      v u1 * v f22 * pow26 * pow26 + v u1 * v f23 * pow26 * pow26 * pow26 +
      v u1 * v f24 * pow26 * pow26 * pow26 * pow26)
let lemma_smul_add_felem5 #m1 #m2 #m3 u1 f2 acc1 =
  let (f20, f21, f22, f23, f24) = f2 in
  let (o0, o1, o2, o3, o4) = acc1 in
  assert (wide_as_nat5 acc1 + uint_v u1 * as_nat5 f2 ==
    v o0 + v o1 * pow26 + v o2 * pow26 * pow26 +
    v o3 * pow26 * pow26 * pow26 + v o4 * pow26 * pow26 * pow26 * pow26 +
    v u1 * (v f20 + v f21 * pow26 + v f22 * pow26 * pow26 +
    v f23 * pow26 * pow26 * pow26 + v f24 * pow26 * pow26 * pow26 * pow26));
  lemma_mul5_distr_l (v u1) (v f20) (v f21 * pow26) (v f22 * pow26 * pow26)
    (v f23 * pow26 * pow26 * pow26) (v f24 * pow26 * pow26 * pow26 * pow26)

val lemma_subtract_p5_0: f:felem5{felem_fits5 f (1, 1, 1, 1, 1)} -> f':felem5 ->
  Lemma
  (requires
    (let (f0, f1, f2, f3, f4) = f in
     let (f0', f1', f2', f3', f4') = f' in
     (v f4 <> 0x3ffffff || v f3 <> 0x3ffffff || v f2 <> 0x3ffffff || v f1 <> 0x3ffffff || v f0 < 0x3fffffb) /\
     (v f0' = v f0 && v f1' = v f1 && v f2' = v f2 && v f3' = v f3 && v f4' = v f4)))
  (ensures as_nat5 f' == feval f)
let lemma_subtract_p5_0 f f' =
  let (f0, f1, f2, f3, f4) = f in
  let (f0', f1', f2', f3', f4') = f' in
  assert_norm (0x3ffffff = max26);
  assert_norm (0x3fffffb = max26 - 4);
  assert (as_nat5 f == v f0 + v f1 * pow26 + v f2 * pow26 * pow26 +
    v f3 * pow26 * pow26 * pow26 + v f4 * pow26 * pow26 * pow26 * pow26);
  assert (as_nat5 f <= pow26 - 5 + (pow2 26 - 1) * pow26 + (pow2 26 - 1) * pow26 * pow26 +
    (pow2 26 - 1) * pow26 * pow26 * pow26 + (pow2 26 - 1) * pow26 * pow26 * pow26 * pow26);
  assert_norm (pow2 26 * pow26 * pow26 * pow26 * pow26 = pow2 130);
  assert (as_nat5 f < pow2 130 - 5);
  assert (as_nat5 f == as_nat5 f');
  FStar.Math.Lemmas.modulo_lemma (as_nat5 f') prime

val lemma_subtract_p5_1: f:felem5{felem_fits5 f (1, 1, 1, 1, 1)} -> f':felem5 ->
  Lemma
  (requires
    (let (f0, f1, f2, f3, f4) = f in
     let (f0', f1', f2', f3', f4') = f' in
     (v f4 = 0x3ffffff && v f3 = 0x3ffffff && v f2 = 0x3ffffff && v f1 = 0x3ffffff && v f0 >= 0x3fffffb) /\
     (v f0' = v f0 - 0x3fffffb && v f1' = v f1 - 0x3ffffff && v f2' = v f2 - 0x3ffffff &&
      v f3' = v f3 - 0x3ffffff && v f4' = v f4 - 0x3ffffff)))
  (ensures as_nat5 f' == feval f)
let lemma_subtract_p5_1 f f' =
  let (f0, f1, f2, f3, f4) = f in
  let (f0', f1', f2', f3', f4') = f' in
  assert_norm (0x3ffffff = max26);
  assert_norm (0x3fffffb = max26 - 4);
  assert (as_nat5 f' % prime ==
    (v f0' + v f1' * pow26 + v f2' * pow26 * pow26 +
     v f3' * pow26 * pow26 * pow26 + v f4' * pow26 * pow26 * pow26 * pow26) % prime);
  assert (as_nat5 f' % prime ==
    (v f0 - (pow2 26 - 5) + (v f1 - (pow2 26 - 1)) * pow26 + (v f2 - (pow2 26 - 1)) * pow26 * pow26 +
    (v f3 - (pow2 26 - 1)) * pow26 * pow26 * pow26 + (v f4 - (pow2 26 - 1)) * pow26 * pow26 * pow26 * pow26) % prime);
  assert_norm (pow2 26 * pow26 * pow26 * pow26 * pow26 = pow2 130);
  assert (as_nat5 f' % prime ==
    (v f0 + v f1 * pow2 26 + v f2 * pow26 * pow26 +
    v f3 * pow26 * pow26 * pow26 +
    v f4 * pow26 * pow26 * pow26 * pow26 - prime) % prime);
  FStar.Math.Lemmas.lemma_mod_sub
    (v f0 + v f1 * pow2 26 + v f2 * pow26 * pow26 +
    v f3 * pow26 * pow26 * pow26 + v f4 * pow26 * pow26 * pow26 * pow26) 1 prime

val lemma_subtract_p5: f:felem5{felem_fits5 f (1, 1, 1, 1, 1)} -> f':felem5 ->
  Lemma
  (requires
    (let (f0, f1, f2, f3, f4) = f in
     let (f0', f1', f2', f3', f4') = f' in
     ((v f4 = 0x3ffffff && v f3 = 0x3ffffff && v f2 = 0x3ffffff && v f1 = 0x3ffffff && v f0 >= 0x3fffffb) /\
     (v f0' = v f0 - 0x3fffffb && v f1' = v f1 - 0x3ffffff && v f2' = v f2 - 0x3ffffff &&
      v f3' = v f3 - 0x3ffffff && v f4' = v f4 - 0x3ffffff)) \/
     ((v f4 <> 0x3ffffff || v f3 <> 0x3ffffff || v f2 <> 0x3ffffff || v f1 <> 0x3ffffff || v f0 < 0x3fffffb) /\
     (v f0' = v f0 && v f1' = v f1 && v f2' = v f2 && v f3' = v f3 && v f4' = v f4))))
  (ensures as_nat5 f' == feval f)
let lemma_subtract_p5 f f' =
  let (f0, f1, f2, f3, f4) = f in
  let (f0', f1', f2', f3', f4') = f' in
  if ((v f4 <> 0x3ffffff || v f3 <> 0x3ffffff || v f2 <> 0x3ffffff || v f1 <> 0x3ffffff || v f0 < 0x3fffffb) &&
     (v f0' = v f0 && v f1' = v f1 && v f2' = v f2 && v f3' = v f3 && v f4' = v f4))
  then lemma_subtract_p5_0 f f'
  else lemma_subtract_p5_1 f f'
