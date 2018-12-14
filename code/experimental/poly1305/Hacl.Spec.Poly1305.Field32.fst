module Hacl.Spec.Poly1305.Field32

open Lib.Sequence
open Lib.IntTypes
open NatPrime

#reset-options "--z3rlimit 50  --using_facts_from '* -FStar.Seq'"

let felem5 = (uint32 * uint32 * uint32 * uint32 * uint32)
let felem_wide5 = (uint64 * uint64 * uint64 * uint64 * uint64)

let scale32 = s:nat{s <= 64}
let scale64 = s:nat{s <= 4096}
let nat5 = (nat * nat * nat * nat * nat)

let scale32_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in
		       x1 <= 64 /\ x2 <= 64 /\ x3 <= 64 /\ x4 <= 64 /\ x5 <= 64}
let scale64_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in
		       x1 <= 4096 /\ x2 <= 4096 /\ x3 <= 4096 /\ x4 <= 4096 /\ x5 <= 4096}

let s32x5 (x:scale32) : scale32_5 = (x,x,x,x,x)
let s64x5 (x:scale64) : scale64_5 = (x,x,x,x,x)

open FStar.Mul

let ( <=* ) (x:nat5) (y:nat5) : Type =
  let (x1,x2,x3,x4,x5) = x in
  let (y1,y2,y3,y4,y5) = y in
  (x1 <= y1) /\
  (x2 <= y2) /\
  (x3 <= y3) /\
  (x4 <= y4) /\
  (x5 <= y5)

let ( +* ) (x:nat5) (y:nat5) : nat5 =
  let (x1,x2,x3,x4,x5) = x in
  let (y1,y2,y3,y4,y5) = y in
  (x1 + y1 ,
   x2 + y2 ,
   x3 + y3 ,
   x4 + y4 ,
   x5 + y5)

let ( ** ) (x:nat5) (y:nat5) : nat5 =
  let (x1,x2,x3,x4,x5) = x in
  let (y1,y2,y3,y4,y5) = y in
  (x1 * y1 ,
   x2 * y2 ,
   x3 * y3 ,
   x4 * y4 ,
   x5 * y5)

#set-options "--z3rlimit 100"

let ( *^ ) (x:scale32) (y:scale32_5) : scale64_5 =
  let (y1,y2,y3,y4,y5) = y in
  (x * y1 ,
   x * y2 ,
   x * y3 ,
   x * y4 ,
   x * y5)

assume val pow26: nat
inline_for_extraction
let max26 = pow26 - 1

assume val lemma_pow_32_26: _:unit{pow2 32 == 64 * pow26}
assume val lemma_pow_64_26: _:unit{pow2 64 == 4096 * pow26 * pow26}

//let _ : (x:unit{pow2 32 == 64 * pow2 26}) =
//      assert_norm (pow2 32 == 64 * pow2 26)
//let _ : (x:unit{pow2 64 == 4096 * pow2 26 * pow2 26}) =
//      assert_norm (pow2 64 == 4096 * pow2 26 * pow2 26)


let felem_fits1 (x:uint32) (m:scale32) =
  uint_v x <= m * max26

let felem_wide_fits1 (x:uint64) (m:scale64) =
  uint_v x <= m * max26 * max26

let felem_fits5 (f:felem5) (m:scale32_5) =
  let (x1,x2,x3,x4,x5) = f in
  let (m1,m2,m3,m4,m5) = m in
  felem_fits1 x1 m1 /\
  felem_fits1 x2 m2 /\
  felem_fits1 x3 m3 /\
  felem_fits1 x4 m4 /\
  felem_fits1 x5 m5

let felem_wide_fits5 (f:felem_wide5) (m:scale64_5) =
  let (x1,x2,x3,x4,x5) = f in
  let (m1,m2,m3,m4,m5) = m in
  felem_wide_fits1 x1 m1 /\
  felem_wide_fits1 x2 m2 /\
  felem_wide_fits1 x3 m3 /\
  felem_wide_fits1 x4 m4 /\
  felem_wide_fits1 x5 m5

noextract
val as_nat5: f:felem5 -> GTot nat
let as_nat5 f =
  let (s0,s1,s2,s3,s4) = f in
  uint_v s0 + (uint_v s1 * pow26) + (uint_v s2 * pow26 * pow26) +
    (uint_v s3 * pow26 * pow26 * pow26) + (uint_v s4 * pow26 * pow26 * pow26 * pow26)

noextract
val wide_as_nat5: f:felem_wide5 -> GTot nat
let wide_as_nat5 f =
  let (s0,s1,s2,s3,s4) = f in
  uint_v s0 + (uint_v s1 * pow26) + (uint_v s2 * pow26 * pow26) +
    (uint_v s3 * pow26 * pow26 * pow26) + (uint_v s4 * pow26 * pow26 * pow26 * pow26)

let feval (f:felem5) : GTot felem = (as_nat5 f) % prime
let feval_wide (f:felem_wide5) : GTot felem = (wide_as_nat5 f) % prime

#set-options "--max_fuel 0"

inline_for_extraction
val fadd5:
    f1:felem5{felem_fits5 f1 (1, 2, 1, 1, 1)}
  -> f2:felem5{felem_fits5 f2 (1, 1, 1, 1, 1)}
  -> out:felem5{felem_fits5 f2 (2, 3, 2, 2, 2) /\
      feval out == fadd (feval f1) (feval f2)}
let fadd5 (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24) =
  let o0 = f10 +! f20 in
  let o1 = f11 +! f21 in
  let o2 = f12 +! f22 in
  let o3 = f13 +! f23 in
  let o4 = f14 +! f24 in
  FStar.Math.Lemmas.lemma_mod_plus_distr_l
    (as_nat5 (f10, f11, f12, f13, f14)) (as_nat5 (f20, f21, f22, f23, f24)) prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
    ((as_nat5 (f10, f11, f12, f13, f14)) % prime) (as_nat5 (f20, f21, f22, f23, f24)) prime;
  (o0, o1, o2, o3, o4)

inline_for_extraction
val mul_wide32:
    #m1:scale32
  -> #m2:scale32
  -> x:uint32{felem_fits1 x m1}
  -> y:uint32{felem_fits1 y m2 /\ m1 * m2 <= 4096}
  -> z:uint64{uint_v z == uint_v x * uint_v y /\ felem_wide_fits1 z (m1 * m2)}
let mul_wide32 #m1 #m2 x y =
  assert (v x * v y <= m1 * max26 * m2 * max26);
  assert (v x * v y <= m1 * m2 * max26 * max26);
  to_u64 x *! to_u64 y

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

inline_for_extraction
val smul_felem5:
    #m1:scale32
  -> #m2:scale32_5
  -> u1:uint32{felem_fits1 u1 m1}
  -> f2:felem5{felem_fits5 f2 m2}
  -> out:felem_wide5{felem_wide_fits5 out (m1 *^ m2) /\
      wide_as_nat5 out == uint_v u1 * as_nat5 f2}
let smul_felem5 #m1 #m2 u1 (f20,f21,f22,f23,f24) =
  let (m20, m21, m22, m23, m24) = m2 in
  let o0 = mul_wide32 #m1 #m20 u1 f20 in
  let o1 = mul_wide32 #m1 #m21 u1 f21 in
  let o2 = mul_wide32 #m1 #m22 u1 f22 in
  let o3 = mul_wide32 #m1 #m23 u1 f23 in
  let o4 = mul_wide32 #m1 #m24 u1 f24 in
  lemma_smul_felem5 #m1 #m2 u1 (f20,f21,f22,f23,f24);
  (o0, o1, o2, o3, o4)

inline_for_extraction
val mul_add_wide64:
    #m1:scale32
  -> #m2:scale32
  -> #m3:scale64
  -> x:uint32{felem_fits1 x m1}
  -> y:uint32{felem_fits1 y m2}
  -> z:uint64{felem_wide_fits1 z m3 /\ m3 + m1 * m2 <= 4096}
  -> r:uint64{uint_v r == uint_v z + uint_v x * uint_v y /\ felem_wide_fits1 r (m3 + m1 * m2)}
let mul_add_wide64 #m1 #m2 #m3 x y z =
  z +! mul_wide32 #m1 #m2 x y

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
    v f23 * pow26 * pow26 * pow26 + v f24 * pow26 * pow26 * pow26 * pow26))

inline_for_extraction
val smul_add_felem5:
    #m1:scale32
  -> #m2:scale32_5
  -> #m3:scale64_5
  -> u1:uint32{felem_fits1 u1 m1}
  -> f2:felem5{felem_fits5 f2 m2}
  -> acc1:felem_wide5{felem_wide_fits5 acc1 m3 /\ m3 +* m1 *^ m2 <=* s64x5 4096}
  -> acc2:felem_wide5{
      wide_as_nat5 acc2 == wide_as_nat5 acc1 + uint_v u1 * as_nat5 f2 /\
      felem_wide_fits5 acc2 (m3 +* m1 *^ m2)}
let smul_add_felem5 #m1 #m2 #m3 u1 (f20, f21, f22, f23, f24) (o0, o1, o2, o3, o4) =
  let (m20, m21, m22, m23, m24) = m2 in
  let (m30, m31, m32, m33, m34) = m3 in
  [@inline_let]
  let o0' = mul_add_wide64 #m1 #m20 #m30 u1 f20 o0 in
  [@inline_let]
  let o1' = mul_add_wide64 #m1 #m21 #m31 u1 f21 o1 in
  [@inline_let]
  let o2' = mul_add_wide64 #m1 #m22 #m32 u1 f22 o2 in
  [@inline_let]
  let o3' = mul_add_wide64 #m1 #m23 #m33 u1 f23 o3 in
  [@inline_let]
  let o4' = mul_add_wide64 #m1 #m24 #m34 u1 f24 o4 in
  [@inline_let]
  let out = (o0', o1', o2', o3', o4') in
  lemma_smul_add_felem5 #m1 #m2 #m3 u1 (f20, f21, f22, f23, f24) (o0, o1, o2, o3, o4);
  out

inline_for_extraction
val precomp_r5:
    r:felem5{felem_fits5 r (1, 1, 1, 1, 1)}
  -> r5:felem5{felem_fits5 r5 (5, 5, 5, 5 ,5)}
let precomp_r5 (r0, r1, r2, r3, r4) =
  let r50 = r0 *! u32 5 in
  let r51 = r1 *! u32 5 in
  let r52 = r2 *! u32 5 in
  let r53 = r3 *! u32 5 in
  let r54 = r4 *! u32 5 in
  (r50, r51, r52, r53, r54)

#reset-options "--z3rlimit 200"

inline_for_extraction
val mul_felem5:
    f1:felem5{felem_fits5 f1 (2, 3, 2, 2, 2)}
  -> r:felem5{felem_fits5 r (1, 1, 1, 1, 1)}
  -> r5:felem5{felem_fits5 r5 (5, 5, 5, 5, 5) /\ r5 == precomp_r5 r}
  -> out:felem_wide5{felem_wide_fits5 out (47, 35, 27, 19, 11) /\
      feval_wide out == fmul (feval f1) (feval r)}
let mul_felem5 (f10,f11,f12,f13,f14) (r0,r1,r2,r3,r4) (r50,r51,r52,r53,r54) =
  let (a0,a1,a2,a3,a4) = smul_felem5 #2 #(1,1,1,1,1) f10 (r0,r1,r2,r3,r4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #3 #(5,1,1,1,1) #(2,2,2,2,2) f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #2 #(5,5,1,1,1) #(17,5,5,5,5) f12 (r53,r54,r0,r1,r2) (a0,a1,a2,a3,a4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #2 #(5,5,5,1,1) #(27,15,7,7,7) f13 (r52,r53,r54,r0,r1) (a0,a1,a2,a3,a4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #2 #(5,5,5,5,1) #(37,25,17,9,9) f14 (r51,r52,r53,r54,r0) (a0,a1,a2,a3,a4) in
  admit();
  (a0,a1,a2,a3,a4)

inline_for_extraction
let mask26: x:uint32{v x == pow2 26 - 1} =
  assert_norm (pow2 26 - 1 == 0x3ffffff);
  u32 0x3ffffff

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

inline_for_extraction
val carry26:
    l:uint32
  -> cin:uint32
  -> Pure (uint32 & uint32)
    (requires felem_fits1 l 2 /\ felem_fits1 cin 62)
    (ensures fun (l0, l1) ->
      felem_fits1 l0 1 /\ uint_v l1 <= 64 /\
      v l + v cin == v l1 * pow2 26 + v l0)
let carry26 l cin =
  let l1 = l +! cin in
  lemma_carry26 l cin;
  (l1 &. mask26, l1 >>. 26ul)

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

inline_for_extraction
val carry26_wide:
    #m:scale64{m < 64}
  -> l:uint64{felem_wide_fits1 l m}
  -> cin:uint32{felem_fits1 cin 64}
  -> Pure (uint32 & uint32)
    (requires True)
    (ensures fun (l0, l1) ->
      v l + v cin == v l1 * pow2 26 + v l0 /\
      felem_fits1 l0 1 /\ felem_fits1 l1 (m + 1))
let carry26_wide #m l cin =
  let l1 = l +! to_u64 cin in
  lemma_carry26_wide #m l cin;
  (to_u32 l1 &. mask26, to_u32 (l1 >>. 26ul))

val lemma_prime: unit ->
  Lemma (pow2 130 % prime = 5)
let lemma_prime () =
  assert_norm (pow2 130 % prime = 5 % prime);
  assert_norm (5 < prime);
  FStar.Math.Lemmas.modulo_lemma 5 prime

val lemma_mul_assos_6:
  a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> f:nat ->
  Lemma (a * b * c * d * e * f == a * (b * c * d * e * f))
let lemma_mul_assos_6 a b c d e f = ()

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

inline_for_extraction
val carry_wide5:
    inp:felem_wide5{felem_wide_fits5 inp (47, 35, 27, 19, 11)}
  -> out:felem5{felem_fits5 out (1, 2, 1, 1, 1) /\
      feval out == feval_wide inp}
let carry_wide5 (i0, i1, i2, i3, i4) =
  assert_norm (47 < 64);
  assert_norm (64 < max26);
  let tmp0, c0 = carry26_wide #47 i0 (u32 0) in
  let tmp1, c1 = carry26_wide #35 i1 c0 in
  let tmp2, c2 = carry26_wide #27 i2 c1 in
  let tmp3, c3 = carry26_wide #19 i3 c2 in
  let tmp4, c4 = carry26_wide #11 i4 c3 in
  lemma_carry_wide5_simplify (i0, i1, i2, i3, i4) c0 c1 c2 c3 c4 tmp0 tmp1 tmp2 tmp3 tmp4;
  let tmp0', c5 = carry26 tmp0 (c4 *! u32 5) in
  let tmp1' = tmp1 +! c5 in
  (tmp0', tmp1', tmp2, tmp3, tmp4)

inline_for_extraction
val fmul_r5:
    f1:felem5
  -> p:(felem5 & felem5)
  -> Pure felem5
    (requires
     (let r, r5 = p in
      felem_fits5 f1 (2, 3, 2, 2, 2) /\
      felem_fits5 r (1, 1, 1, 1, 1) /\
      felem_fits5 r5 (5, 5, 5, 5, 5) /\
      r5 == precomp_r5 r))
    (ensures fun out ->
     (let r, r5 = p in
      felem_fits5 out (1, 2, 1, 1, 1) /\
      feval out == fmul (feval f1) (feval r)))
let fmul_r5 f1 p =
  let r, r5 = p in
  let tmp = mul_felem5 f1 r r5 in
  carry_wide5 tmp

inline_for_extraction
val fadd_mul_r5:
    acc:felem5
  -> f1:felem5
  -> p:(felem5 & felem5)
  -> Pure felem5
    (requires
     (let r, r5 = p in
      felem_fits5 acc (1, 2, 1, 1, 1) /\
      felem_fits5 f1 (1, 1, 1, 1, 1) /\
      felem_fits5 r (1, 1, 1, 1, 1) /\
      felem_fits5 r5 (5, 5, 5, 5, 5) /\
      r5 == precomp_r5 r))
    (ensures fun out ->
     (let r, r5 = p in
      felem_fits5 out (1, 2, 1, 1, 1) /\
      feval out == fmul (fadd (feval acc) (feval f1)) (feval r)))
let fadd_mul_r5 acc f1 p =
  let r, r5 = p in
  let acc = fadd5 acc f1 in
  let tmp = mul_felem5 acc r r5 in
  carry_wide5 tmp

(* reduce_felem *)

inline_for_extraction
val carry_felem5:
    inp:felem5{felem_fits5 inp (1, 2, 1, 1, 1)}
  -> out:felem5{felem_fits5 out (1, 1, 1, 1, 2)}
let carry_felem5 (f0, f1, f2, f3, f4) =
  let tmp0, c = carry26 f0 (u32 0) in
  let tmp1, c = carry26 f1 c in
  let tmp2, c = carry26 f2 c in
  let tmp3, c = carry26 f3 c in
  let tmp4 = f4 +. c in
  (tmp0, tmp1, tmp2, tmp3, tmp4)

inline_for_extraction
val carry_top_felem5:
    f:felem5{felem_fits5 f (1, 1, 1, 1, 2)}
  -> out:felem5//{felem_fits5 f (1, 2, 1, 1, 1)}
let carry_top_felem5 (f0, f1, f2, f3, f4) =
  let tmp4, carry = carry26 f4 (u32 0) in
  let tmp0, carry = carry26 f0 (carry *. u32 5) in
  let tmp1 = f1 +. carry in
  (tmp0, tmp1, f2, f3, tmp4)

inline_for_extraction
val subtract_p5:
    f:felem5
  -> out:felem5
let subtract_p5 (f0, f1, f2, f3, f4) =
  let mask = eq_mask f4 (u32 0x3ffffff) in
  let mask = mask &. eq_mask f3 (u32 0x3ffffff) in
  let mask = mask &. eq_mask f2 (u32 0x3ffffff) in
  let mask = mask &. eq_mask f1 (u32 0x3ffffff) in
  let mask = mask &. gte_mask f0 (u32 0x3fffffb) in
  let p0 = mask &. u32 0x3fffffb in
  let p1 = mask &. u32 0x3ffffff in
  let p2 = mask &. u32 0x3ffffff in
  let p3 = mask &. u32 0x3ffffff in
  let p4 = mask &. u32 0x3ffffff in
  let f0 = f0 -. p0 in
  let f1 = f1 -. p1 in
  let f2 = f2 -. p2 in
  let f3 = f3 -. p3 in
  let f4 = f4 -. p4 in
  (f0, f1, f2, f3, f4)

inline_for_extraction
val reduce_felem:
    f:felem5{felem_fits5 f (1, 2, 1, 1, 1)}
  -> out:felem5
let reduce_felem f =
  let f = carry_felem5 f in
  let f = carry_top_felem5 f in
  subtract_p5 f
