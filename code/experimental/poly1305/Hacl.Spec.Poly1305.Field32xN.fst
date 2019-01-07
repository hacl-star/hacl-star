module Hacl.Spec.Poly1305.Field32xN

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence

(* high-level spec *)
let prime:pos =
  assert_norm (pow2 130 - 5 > 0);
  pow2 130 - 5

let pfelem = x:nat{x < prime}
let pfadd (f1:pfelem) (f2:pfelem) : pfelem = (f1 + f2) % prime
let pfmul (f1:pfelem) (f2:pfelem) : pfelem = (f1 `op_Multiply` f2) % prime

(* low-level spec *)

let lanes = w:width{w == 1 \/ w == 2 \/ w == 4}

inline_for_extraction
let uint64xN (w:lanes) = vec_t U64 w

inline_for_extraction
let zero (w:lanes) = vec_zero U64 w

inline_for_extraction
let mask26 (w:lanes) = vec_load (u64 0x3ffffff) w
inline_for_extraction
let mask14 (w:lanes) = vec_load (u64 0x3fff) w

inline_for_extraction
let felem5 (w:lanes) = (uint64xN w * uint64xN w * uint64xN w * uint64xN w * uint64xN w)
inline_for_extraction
let felem_wide5 (w:lanes) = felem5 w

let scale32 = s:nat{s <= 64}
let scale64 = s:nat{s <= 4096}
let nat5 = (nat * nat * nat * nat * nat)

let scale32_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in
		       x1 <= 64 /\ x2 <= 64 /\ x3 <= 64 /\ x4 <= 64 /\ x5 <= 64}
let scale64_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in
		       x1 <= 4096 /\ x2 <= 4096 /\ x3 <= 4096 /\ x4 <= 4096 /\ x5 <= 4096}

let s64x5 (x:scale64) : scale64_5 = (x,x,x,x,x)

open FStar.Mul

#reset-options "--z3rlimit 100 --using_facts_from '* -FStar.Seq'"

noextract
let ( *^ ) (x:scale32) (y:scale32_5) : scale64_5 =
  assert_norm (64 * 64 = 4096);
  let (y1,y2,y3,y4,y5) = y in
  (x * y1 ,
   x * y2 ,
   x * y3 ,
   x * y4 ,
   x * y5)

noextract
let ( +* ) (x:nat5) (y:nat5) : nat5 =
  let (x1,x2,x3,x4,x5) = x in
  let (y1,y2,y3,y4,y5) = y in
  (x1 + y1 ,
   x2 + y2 ,
   x3 + y3 ,
   x4 + y4 ,
   x5 + y5)

noextract
let ( <=* ) (x:nat5) (y:nat5) : Type =
  let (x1,x2,x3,x4,x5) = x in
  let (y1,y2,y3,y4,y5) = y in
  (x1 <= y1) /\
  (x2 <= y2) /\
  (x3 <= y3) /\
  (x4 <= y4) /\
  (x5 <= y5)

assume val pow26: nat
inline_for_extraction
let max26 = pow26 - 1

assume val lemma_pow_32_26: _:unit{pow2 32 == 64 * pow26}
assume val lemma_pow_64_26: _:unit{pow2 64 == 4096 * pow26 * pow26}

let felem_fits1 (#w:lanes) (x:uint64xN w) (m:scale32) =
  forall (i:nat). i < w ==> uint_v (vec_v x).[i] <= m * max26

let felem_wide_fits1 (#w:lanes) (x:uint64xN w) (m:scale64) =
  forall (i:nat). i < w ==> uint_v (vec_v x).[i] <= m * max26 * max26

let felem_fits5 (#w:lanes) (f:felem5 w) (m:scale32_5) =
  let (x1,x2,x3,x4,x5) = f in
  let (m1,m2,m3,m4,m5) = m in
  felem_fits1 x1 m1 /\
  felem_fits1 x2 m2 /\
  felem_fits1 x3 m3 /\
  felem_fits1 x4 m4 /\
  felem_fits1 x5 m5

let felem_wide_fits5 (#w:lanes) (f:felem_wide5 w) (m:scale64_5) =
  let (x1,x2,x3,x4,x5) = f in
  let (m1,m2,m3,m4,m5) = m in
  felem_wide_fits1 x1 m1 /\
  felem_wide_fits1 x2 m2 /\
  felem_wide_fits1 x3 m3 /\
  felem_wide_fits1 x4 m4 /\
  felem_wide_fits1 x5 m5


let tup64_5 = (uint64 & uint64 & uint64 & uint64 & uint64)
noextract
val as_nat5: f:tup64_5 -> nat
let as_nat5  f =
  let (s0,s1,s2,s3,s4) = f in
  uint_v s0 + (uint_v s1 * pow26) + (uint_v s2 * pow26 * pow26) +
    (uint_v s3 * pow26 * pow26 * pow26) + (uint_v s4 * pow26 * pow26 * pow26 * pow26)

noextract
let as_pfelem5 (f:tup64_5) : pfelem =
  (as_nat5 f) % prime

noextract
let uint64xN_v (#w:lanes) (e:uint64xN w) : lseq nat w =
  let e = vec_v e in
  createi #nat w (fun i -> uint_v e.[i])

noextract
let transpose (#w:lanes) (f:felem5 w) : lseq tup64_5 w =
  let (f0,f1,f2,f3,f4) = f in
  let v0 = vec_v f0 in
  let v1 = vec_v f1 in
  let v2 = vec_v f2 in
  let v3 = vec_v f3 in
  let v4 = vec_v f4 in
  createi #tup64_5 w (fun i -> (v0.[i],v1.[i],v2.[i],v3.[i],v4.[i]))

noextract
let feval5 (#w:lanes) (f:felem5 w) : lseq pfelem w =
  map as_pfelem5 (transpose f)

noextract
let fas_nat5 (#w:lanes) (f:felem5 w) : lseq nat w =
  map as_nat5 (transpose f)

inline_for_extraction noextract
val fadd5:
    #w:lanes
  -> f1:felem5 w
  -> f2:felem5 w
  -> out:felem5 w
let fadd5 #w (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24) =
  [@inline_let]
  let o0 = f10 +| f20 in
  [@inline_let]
  let o1 = f11 +| f21 in
  [@inline_let]
  let o2 = f12 +| f22 in
  [@inline_let]
  let o3 = f13 +| f23 in
  [@inline_let]
  let o4 = f14 +| f24 in
  (o0, o1, o2, o3, o4)

val fadd5_fits_lemma:
    #w:lanes
  -> f1:felem5 w
  -> f2:felem5 w
  -> Lemma
    (requires felem_fits5 f1 (1,2,1,1,1) /\ felem_fits5 f2 (1,1,1,1,1))
    (ensures  felem_fits5 (fadd5 f1 f2) (2,3,2,2,2))
    [SMTPat (fadd5 f1 f2)]
let fadd5_fits_lemma #w f1 f2 =
  let (f10, f11, f12, f13, f14) = f1 in
  let (f20, f21, f22, f23, f24) = f2 in
  let o = fadd5 f1 f2 in
  vec_add_mod_lemma f10 f20;
  vec_add_mod_lemma f11 f21;
  vec_add_mod_lemma f12 f22;
  vec_add_mod_lemma f13 f23;
  vec_add_mod_lemma f14 f24

val fadd5_eval_lemma_i:
    #w:lanes
  -> f1:felem5 w
  -> f2:felem5 w
  -> i:nat{i < w}
  -> Lemma
    (requires felem_fits5 f1 (1,2,1,1,1) /\ felem_fits5 f2 (1,1,1,1,1))
    (ensures  (feval5 (fadd5 f1 f2)).[i] == pfadd (feval5 f1).[i] (feval5 f2).[i])
let fadd5_eval_lemma_i #w f1 f2 i =
  let (f10, f11, f12, f13, f14) = f1 in
  let (f20, f21, f22, f23, f24) = f2 in
  let o = fadd5 f1 f2 in
  let (o0, o1, o2, o3, o4) = o in

  FStar.Math.Lemmas.modulo_lemma (v ((vec_v f10).[i]) + v ((vec_v f20).[i])) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v ((vec_v f11).[i]) + v ((vec_v f21).[i])) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v ((vec_v f12).[i]) + v ((vec_v f22).[i])) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v ((vec_v f13).[i]) + v ((vec_v f23).[i])) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v ((vec_v f14).[i]) + v ((vec_v f24).[i])) (pow2 64);
  assert (
    as_nat5 ((vec_v o0).[i],(vec_v o1).[i],(vec_v o2).[i],(vec_v o3).[i],(vec_v o4).[i]) ==
    as_nat5 ((vec_v f10).[i],(vec_v f11).[i],(vec_v f12).[i],(vec_v f13).[i],(vec_v f14).[i]) +
    as_nat5 ((vec_v f20).[i],(vec_v f21).[i],(vec_v f22).[i],(vec_v f23).[i],(vec_v f24).[i]));
  FStar.Math.Lemmas.lemma_mod_plus_distr_l
    (as_nat5 ((vec_v f10).[i],(vec_v f11).[i],(vec_v f12).[i],(vec_v f13).[i],(vec_v f14).[i]))
    (as_nat5 ((vec_v f20).[i],(vec_v f21).[i],(vec_v f22).[i],(vec_v f23).[i],(vec_v f24).[i])) prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
    ((as_nat5 ((vec_v f10).[i],(vec_v f11).[i],(vec_v f12).[i],(vec_v f13).[i],(vec_v f14).[i])) % prime)
    (as_nat5 ((vec_v f20).[i],(vec_v f21).[i],(vec_v f22).[i],(vec_v f23).[i],(vec_v f24).[i])) prime;
  assert ((feval5 o).[i] == pfadd (feval5 f1).[i] (feval5 f2).[i])

val fadd5_eval_lemma:
    #w:lanes
  -> f1:felem5 w
  -> f2:felem5 w
  -> Lemma
    (requires felem_fits5 f1 (1,2,1,1,1) /\ felem_fits5 f2 (1,1,1,1,1))
    (ensures  feval5 (fadd5 f1 f2) == map2 pfadd (feval5 f1) (feval5 f2))
    [SMTPat (fadd5 f1 f2)]
let fadd5_eval_lemma #w f1 f2 =
  let o = fadd5 f1 f2 in

  match w with
  | 1 ->
    fadd5_eval_lemma_i f1 f2 0;
    eq_intro (feval5 o) (map2 pfadd (feval5 f1) (feval5 f2))
  | 2 ->
    fadd5_eval_lemma_i f1 f2 0;
    fadd5_eval_lemma_i f1 f2 1;
    eq_intro (feval5 o) (map2 pfadd (feval5 f1) (feval5 f2))
  | 4 ->
    fadd5_eval_lemma_i f1 f2 0;
    fadd5_eval_lemma_i f1 f2 1;
    fadd5_eval_lemma_i f1 f2 2;
    fadd5_eval_lemma_i f1 f2 3;
    eq_intro (feval5 o) (map2 pfadd (feval5 f1) (feval5 f2))

inline_for_extraction noextract
val smul_felem5:
    #w:lanes
  -> u1:uint64xN w
  -> f2:felem5 w
  -> out:felem_wide5 w
let smul_felem5 #w u1 (f20, f21, f22, f23, f24) =
  [@inline_let]
  let o0 = vec_mul_mod f20 u1 in
  [@inline_let]
  let o1 = vec_mul_mod f21 u1 in
  [@inline_let]
  let o2 = vec_mul_mod f22 u1 in
  [@inline_let]
  let o3 = vec_mul_mod f23 u1 in
  [@inline_let]
  let o4 = vec_mul_mod f24 u1 in
  (o0, o1, o2, o3, o4)

val lemma_mult_le: a:nat -> b:nat -> c:nat -> d:nat -> Lemma
  (requires (a <= b /\ c <= d))
  (ensures  (a * c <= b * d))
let lemma_mult_le a b c d = ()

#set-options "--z3rlimit 100"

val smul_felem5_fits_lemma_i:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32
  -> u1:uint64xN w
  -> f2:uint64xN w
  -> i:nat{i < w}
  -> Lemma
    (requires felem_fits1 u1 m1 /\ felem_fits1 f2 m2)
    (ensures uint_v (vec_v (vec_mul_mod f2 u1)).[i] <= m1 * m2 * max26 * max26)
let smul_felem5_fits_lemma_i #w #m1 #m2 u1 f2 i =
  let o = vec_mul_mod f2 u1 in
  assert ((vec_v o).[i] == (vec_v f2).[i] *. (vec_v u1).[i]);
  assert (uint_v (vec_v o).[i] == (uint_v (vec_v f2).[i] * uint_v (vec_v u1).[i]) % pow2 64);
  lemma_mult_le (uint_v (vec_v f2).[i]) (m2 * max26) (uint_v (vec_v u1).[i]) (m1 * max26);
  //assert (uint_v (vec_v f2).[i] * uint_v (vec_v u1).[i] <= m2 * max26 * m1 * max26);
  assert (uint_v (vec_v f2).[i] * uint_v (vec_v u1).[i] <= m1 * m2 * max26 * max26);
  FStar.Math.Lemmas.modulo_lemma (uint_v (vec_v f2).[i] * uint_v (vec_v u1).[i]) (pow2 64);
  assert (uint_v (vec_v o).[i] == uint_v (vec_v f2).[i] * uint_v (vec_v u1).[i])

val smul_felem5_fits_lemma1:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32
  -> u1:uint64xN w
  -> f2:uint64xN w
  -> Lemma
    (requires felem_fits1 u1 m1 /\ felem_fits1 f2 m2)
    (ensures felem_wide_fits1 (vec_mul_mod f2 u1) (m1 * m2))
let smul_felem5_fits_lemma1 #w #m1 #m2 u1 f2 =
  match w with
  | 1 ->
    smul_felem5_fits_lemma_i #w #m1 #m2 u1 f2 0
  | 2 ->
    smul_felem5_fits_lemma_i #w #m1 #m2 u1 f2 0;
    smul_felem5_fits_lemma_i #w #m1 #m2 u1 f2 1
  | 4 ->
    smul_felem5_fits_lemma_i #w #m1 #m2 u1 f2 0;
    smul_felem5_fits_lemma_i #w #m1 #m2 u1 f2 1;
    smul_felem5_fits_lemma_i #w #m1 #m2 u1 f2 2;
    smul_felem5_fits_lemma_i #w #m1 #m2 u1 f2 3

val smul_felem5_fits_lemma:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> u1:uint64xN w
  -> f2:felem5 w
  -> Lemma
    (requires felem_fits1 u1 m1 /\ felem_fits5 f2 m2)
    (ensures  felem_wide_fits5 (smul_felem5 #w u1 f2) (m1 *^ m2))
let smul_felem5_fits_lemma #w #m1 #m2 u1 f2 =
  let (f20, f21, f22, f23, f24) = f2 in
  let (m20, m21, m22, m23, m24) = m2 in
  smul_felem5_fits_lemma1 #w #m1 #m20 u1 f20;
  smul_felem5_fits_lemma1 #w #m1 #m21 u1 f21;
  smul_felem5_fits_lemma1 #w #m1 #m22 u1 f22;
  smul_felem5_fits_lemma1 #w #m1 #m23 u1 f23;
  smul_felem5_fits_lemma1 #w #m1 #m24 u1 f24

val smul_mod_lemma:
    #m1:scale32
  -> #m2:scale32
  -> a:nat{a <= m1 * max26}
  -> b:nat{b <= m2 * max26}
  -> c:nat{c == a * b % pow2 64}
  -> Lemma (c == a * b)
let smul_mod_lemma #m1 #m2 a b c =
  lemma_mult_le a (m1 * max26) b (m2 * max26);
  assert (a * b <= m1 * m2 * max26 * max26);
  FStar.Math.Lemmas.modulo_lemma (a * b) (pow2 64)

#set-options "--z3rlimit 150 --max_fuel 1"

val smul_felem5_eval_lemma_i:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> u1:uint64xN w
  -> f2:felem5 w
  -> i:nat{i < w}
  -> Lemma
    (requires felem_fits1 u1 m1 /\ felem_fits5 f2 m2)
    (ensures (fas_nat5 (smul_felem5 #w u1 f2)).[i] == (uint64xN_v u1).[i] * (fas_nat5 f2).[i])
let smul_felem5_eval_lemma_i #w #m1 #m2 u1 f2 i =
  let (f20, f21, f22, f23, f24) = f2 in
  let (m20, m21, m22, m23, m24) = m2 in
  let vf20 = v (vec_v f20).[i] in
  let vf21 = v (vec_v f21).[i] in
  let vf22 = v (vec_v f22).[i] in
  let vf23 = v (vec_v f23).[i] in
  let vf24 = v (vec_v f24).[i] in
  let vu1 = (uint64xN_v u1).[i] in

  let o = smul_felem5 #w u1 f2 in
  let (o0, o1, o2, o3, o4) = o in
  let vo0 = v (vec_v o0).[i] in
  let vo1 = v (vec_v o1).[i] in
  let vo2 = v (vec_v o2).[i] in
  let vo3 = v (vec_v o3).[i] in
  let vo4 = v (vec_v o4).[i] in

  smul_mod_lemma #m1 #m20 vu1 vf20 vo0;
  smul_mod_lemma #m1 #m21 vu1 vf21 vo1;
  smul_mod_lemma #m1 #m22 vu1 vf22 vo2;
  smul_mod_lemma #m1 #m23 vu1 vf23 vo3;
  smul_mod_lemma #m1 #m24 vu1 vf24 vo4;

  assert ((fas_nat5 o).[i] == vf20 * vu1 + vf21 * vu1 * pow26 + vf22 * vu1 * pow26 * pow26 +
    vf23 * vu1 * pow26 * pow26 * pow26 + vf24 * vu1 * pow26 * pow26 * pow26 * pow26);

  assert (vu1 * (fas_nat5 f2).[i] == vu1 * (vf20 + vf21 * pow26 + vf22 * pow26 * pow26 +
   vf23 * pow26 * pow26 * pow26 + vf24 * pow26 * pow26 * pow26 * pow26));

  assert (
   vu1 * (vf20 + vf21 * pow26 + vf22 * pow26 * pow26 +
   vf23 * pow26 * pow26 * pow26 + vf24 * pow26 * pow26 * pow26 * pow26) ==
   vf20 * vu1 + vf21 * vu1 * pow26 + vf22 * vu1 * pow26 * pow26 +
   vf23 * vu1 * pow26 * pow26 * pow26 + vf24 * vu1 * pow26 * pow26 * pow26 * pow26)

val smul_felem5_eval_lemma:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> u1:uint64xN w
  -> f2:felem5 w
  -> Lemma
    (requires felem_fits1 u1 m1 /\ felem_fits5 f2 m2)
    (ensures
      fas_nat5 (smul_felem5 #w u1 f2) ==
      map2 #nat #nat #nat (fun a b -> a * b) (uint64xN_v u1) (fas_nat5 f2))
let smul_felem5_eval_lemma #w #m1 #m2 u1 f2 =
  match w with
  | 1 ->
    smul_felem5_eval_lemma_i #w #m1 #m2 u1 f2 0;
    eq_intro (fas_nat5 (smul_felem5 #w u1 f2))
      (map2 #nat #nat #nat (fun a b -> a * b) (uint64xN_v u1) (fas_nat5 f2))
  | 2 ->
    smul_felem5_eval_lemma_i #w #m1 #m2 u1 f2 0;
    smul_felem5_eval_lemma_i #w #m1 #m2 u1 f2 1;
    eq_intro (fas_nat5 (smul_felem5 #w u1 f2))
      (map2 #nat #nat #nat (fun a b -> a * b) (uint64xN_v u1) (fas_nat5 f2))
  | 4 ->
    smul_felem5_eval_lemma_i #w #m1 #m2 u1 f2 0;
    smul_felem5_eval_lemma_i #w #m1 #m2 u1 f2 1;
    smul_felem5_eval_lemma_i #w #m1 #m2 u1 f2 2;
    smul_felem5_eval_lemma_i #w #m1 #m2 u1 f2 3;
    eq_intro (fas_nat5 (smul_felem5 #w u1 f2))
      (map2 #nat #nat #nat (fun a b -> a * b) (uint64xN_v u1) (fas_nat5 f2))

inline_for_extraction noextract
val smul_add_felem5:
    #w:lanes
  -> u1:uint64xN w
  -> f2:felem5 w
  -> acc1:felem_wide5 w
  -> acc2:felem_wide5 w
let smul_add_felem5 #w u1 (f20, f21, f22, f23, f24) (o0, o1, o2, o3, o4) =
  [@inline_let]
  let o0 = vec_add_mod o0 (vec_mul_mod f20 u1) in
  [@inline_let]
  let o1 = vec_add_mod o1 (vec_mul_mod f21 u1) in
  [@inline_let]
  let o2 = vec_add_mod o2 (vec_mul_mod f22 u1) in
  [@inline_let]
  let o3 = vec_add_mod o3 (vec_mul_mod f23 u1) in
  [@inline_let]
  let o4 = vec_add_mod o4 (vec_mul_mod f24 u1) in
  (o0, o1, o2, o3, o4)

val smul_add_felem5_fits_lemma_i:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32
  -> #m3:scale64
  -> u1:uint64xN w
  -> f2:uint64xN w
  -> acc1:uint64xN w
  -> i:nat{i < w}
  -> Lemma
    (requires
      felem_fits1 u1 m1 /\ felem_fits1 f2 m2 /\
      felem_wide_fits1 acc1 m3 /\ m3 + m1 * m2 <= 4096)
    (ensures
      uint_v (vec_v (vec_add_mod acc1 (vec_mul_mod f2 u1))).[i] <= (m3 + m1 * m2) * max26 * max26)
let smul_add_felem5_fits_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 i =
  let o = vec_add_mod acc1 (vec_mul_mod f2 u1) in
  assert ((vec_v o).[i] == (vec_v acc1).[i] +. (vec_v f2).[i] *. (vec_v u1).[i]);
  assert (v (vec_v o).[i] == (v (vec_v acc1).[i] + (v (vec_v f2).[i] * v (vec_v u1).[i]) % pow2 64) % pow2 64);
  lemma_mult_le (uint_v (vec_v f2).[i]) (m2 * max26) (uint_v (vec_v u1).[i]) (m1 * max26);
  assert (uint_v (vec_v f2).[i] * uint_v (vec_v u1).[i] <= m1 * m2 * max26 * max26);
  FStar.Math.Lemmas.modulo_lemma (uint_v (vec_v f2).[i] * uint_v (vec_v u1).[i]) (pow2 64);
  assert (v (vec_v o).[i] == (v (vec_v acc1).[i] + v (vec_v f2).[i] * v (vec_v u1).[i]) % pow2 64);
  assert (v (vec_v acc1).[i] + v (vec_v f2).[i] * v (vec_v u1).[i] <= m3 * max26 * max26 + m1 * m2 * max26 * max26);
  assert (v (vec_v acc1).[i] + v (vec_v f2).[i] * v (vec_v u1).[i] <= (m3 + m1 * m2) * max26 * max26)

val smul_add_felem5_fits_lemma1:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32
  -> #m3:scale64
  -> u1:uint64xN w
  -> f2:uint64xN w
  -> acc1:uint64xN w
  -> Lemma
    (requires
      felem_fits1 u1 m1 /\ felem_fits1 f2 m2 /\
      felem_wide_fits1 acc1 m3 /\ m3 + m1 * m2 <= 4096)
    (ensures felem_wide_fits1 (vec_add_mod acc1 (vec_mul_mod f2 u1)) (m3 + m1 * m2))
let smul_add_felem5_fits_lemma1 #w #m1 #m2 #m3 u1 f2 acc1 =
  match w with
  | 1 ->
    smul_add_felem5_fits_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 0
  | 2 ->
    smul_add_felem5_fits_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 0;
    smul_add_felem5_fits_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 1
  | 4 ->
    smul_add_felem5_fits_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 0;
    smul_add_felem5_fits_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 1;
    smul_add_felem5_fits_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 2;
    smul_add_felem5_fits_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 3

val smul_add_felem5_fits_lemma:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> #m3:scale64_5
  -> u1:uint64xN w
  -> f2:felem5 w
  -> acc1:felem_wide5 w
  -> Lemma
    (requires
      felem_fits1 u1 m1 /\ felem_fits5 f2 m2 /\
      felem_wide_fits5 acc1 m3 /\ m3 +* m1 *^ m2 <=* s64x5 4096)
    (ensures
      felem_wide_fits5 (smul_add_felem5 #w u1 f2 acc1) (m3 +* m1 *^ m2))
let smul_add_felem5_fits_lemma #w #m1 #m2 #m3 u1 f2 acc1 =
  let (f20, f21, f22, f23, f24) = f2 in
  let (m20, m21, m22, m23, m24) = m2 in
  let (a0, a1, a2, a3, a4) = acc1 in
  let (m30, m31, m32, m33, m34) = m3 in
  smul_add_felem5_fits_lemma1 #w #m1 #m20 #m30 u1 f20 a0;
  smul_add_felem5_fits_lemma1 #w #m1 #m21 #m31 u1 f21 a1;
  smul_add_felem5_fits_lemma1 #w #m1 #m22 #m32 u1 f22 a2;
  smul_add_felem5_fits_lemma1 #w #m1 #m23 #m33 u1 f23 a3;
  smul_add_felem5_fits_lemma1 #w #m1 #m24 #m34 u1 f24 a4

val smul_add_mod_lemma:
    #m1:scale32
  -> #m2:scale32
  -> #m3:scale64
  -> a:nat{a <= m1 * max26}
  -> b:nat{b <= m2 * max26}
  -> c:nat{c <= m3 * max26 * max26 /\ m3 + m1 * m2 <= 4096}
  -> d:nat{d == (c + (a * b) % pow2 64) % pow2 64}
  -> Lemma (d == c + a * b)
let smul_add_mod_lemma #m1 #m2 #m3 a b c d =
  lemma_mult_le a (m1 * max26) b (m2 * max26);
  assert (a * b <= m1 * m2 * max26 * max26);
  FStar.Math.Lemmas.modulo_lemma (a * b) (pow2 64)

val smul_add_lemma:
  va0:nat -> va1:nat -> va2:nat -> va3:nat -> va4:nat -> vu1:nat ->
  vf20:nat -> vf21:nat -> vf22:nat -> vf23:nat -> vf24:nat ->
  Lemma (
    va0 + va1 * pow26 + va2 * pow26 * pow26 +
    va3 * pow26 * pow26 * pow26 + va4 * pow26 * pow26 * pow26 * pow26 +
    vu1 * vf20 + vu1 * vf21 * pow26 + vu1 * vf22 * pow26 * pow26 +
    vu1 * vf23 * pow26 * pow26 * pow26 + vu1 * vf24 * pow26 * pow26 * pow26 * pow26 ==
    va0 + va1 * pow26 + va2 * pow26 * pow26 +
    va3 * pow26 * pow26 * pow26 + va4 * pow26 * pow26 * pow26 * pow26 +
    vu1 * (vf20 + vf21 * pow26 + vf22 * pow26 * pow26 +
    vf23 * pow26 * pow26 * pow26 + vf24 * pow26 * pow26 * pow26 * pow26))
let smul_add_lemma va0 va1 va2 va3 va4 vu1 vf20 vf21 vf22 vf23 vf24 = ()

val smul_add_felem5_eval_lemma_i:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> #m3:scale64_5
  -> u1:uint64xN w
  -> f2:felem5 w
  -> acc1:felem_wide5 w
  -> i:nat{i < w}
  -> Lemma
    (requires
      felem_fits1 u1 m1 /\ felem_fits5 f2 m2 /\
      felem_wide_fits5 acc1 m3 /\ m3 +* m1 *^ m2 <=* s64x5 4096)
    (ensures
      (fas_nat5 (smul_add_felem5 #w u1 f2 acc1)).[i] ==
	(fas_nat5 acc1).[i] + (uint64xN_v u1).[i] * (fas_nat5 f2).[i])
let smul_add_felem5_eval_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 i =
  let vu1 = (uint64xN_v u1).[i] in

  let (f20, f21, f22, f23, f24) = f2 in
  let (m20, m21, m22, m23, m24) = m2 in
  let vf20 = v (vec_v f20).[i] in
  let vf21 = v (vec_v f21).[i] in
  let vf22 = v (vec_v f22).[i] in
  let vf23 = v (vec_v f23).[i] in
  let vf24 = v (vec_v f24).[i] in

  let (m30, m31, m32, m33, m34) = m3 in
  let (a0, a1, a2, a3, a4) = acc1 in
  let va0 = v (vec_v a0).[i] in
  let va1 = v (vec_v a1).[i] in
  let va2 = v (vec_v a2).[i] in
  let va3 = v (vec_v a3).[i] in
  let va4 = v (vec_v a4).[i] in

  let o = smul_add_felem5 #w u1 f2 acc1 in
  let (o0, o1, o2, o3, o4) = o in
  let vo0 = v (vec_v o0).[i] in
  let vo1 = v (vec_v o1).[i] in
  let vo2 = v (vec_v o2).[i] in
  let vo3 = v (vec_v o3).[i] in
  let vo4 = v (vec_v o4).[i] in

  smul_add_mod_lemma #m1 #m20 #m30 vu1 vf20 va0 vo0;
  smul_add_mod_lemma #m1 #m21 #m31 vu1 vf21 va1 vo1;
  smul_add_mod_lemma #m1 #m22 #m32 vu1 vf22 va2 vo2;
  smul_add_mod_lemma #m1 #m23 #m33 vu1 vf23 va3 vo3;
  smul_add_mod_lemma #m1 #m24 #m34 vu1 vf24 va4 vo4;

  assert ((fas_nat5 o).[i] ==
    va0 + vu1 * vf20 + (va1 + vu1 * vf21) * pow26 + (va2 + vu1 * vf22) * pow26 * pow26 +
    (va3 + vu1 * vf23) * pow26 * pow26 * pow26 + (va4 + vu1 * vf24) * pow26 * pow26 * pow26 * pow26);

  assert ((fas_nat5 o).[i] ==
    va0 + va1 * pow26 + va2 * pow26 * pow26 +
    va3 * pow26 * pow26 * pow26 + va4 * pow26 * pow26 * pow26 * pow26 +
    vu1 * vf20 + vu1 * vf21 * pow26 + vu1 * vf22 * pow26 * pow26 +
    vu1 * vf23 * pow26 * pow26 * pow26 + vu1 * vf24 * pow26 * pow26 * pow26 * pow26);

  assert ((fas_nat5 acc1).[i] + vu1 * (fas_nat5 f2).[i] ==
    va0 + va1 * pow26 + va2 * pow26 * pow26 +
    va3 * pow26 * pow26 * pow26 + va4 * pow26 * pow26 * pow26 * pow26 +
    vu1 * (vf20 + vf21 * pow26 + vf22 * pow26 * pow26 +
    vf23 * pow26 * pow26 * pow26 + vf24 * pow26 * pow26 * pow26 * pow26));
  smul_add_lemma va0 va1 va2 va3 va4 vu1 vf20 vf21 vf22 vf23 vf24

val smul_add_felem5_eval_lemma:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> #m3:scale64_5
  -> u1:uint64xN w
  -> f2:felem5 w
  -> acc1:felem_wide5 w
  -> Lemma
    (requires
      felem_fits1 u1 m1 /\
      felem_fits5 f2 m2 /\
      felem_wide_fits5 acc1 m3 /\
      m3 +* m1 *^ m2 <=* s64x5 4096)
    (ensures
      fas_nat5 (smul_add_felem5 #w u1 f2 acc1) ==
	map2 #nat #nat #nat (fun a b -> a + b) (fas_nat5 acc1)
	  (map2 #nat #nat #nat (fun a b -> a * b) (uint64xN_v u1) (fas_nat5 f2)))
let smul_add_felem5_eval_lemma #w #m1 #m2 #m3 u1 f2 acc1 =
  let tmp =
    map2 #nat #nat #nat (fun a b -> a + b) (fas_nat5 acc1)
      (map2 #nat #nat #nat (fun a b -> a * b) (uint64xN_v u1) (fas_nat5 f2)) in

  match w with
  | 1 ->
    smul_add_felem5_eval_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 0;
    eq_intro (fas_nat5 (smul_add_felem5 #w u1 f2 acc1)) tmp
  | 2 ->
    smul_add_felem5_eval_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 0;
    smul_add_felem5_eval_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 1;
    eq_intro (fas_nat5 (smul_add_felem5 #w u1 f2 acc1)) tmp
  | 4 ->
    smul_add_felem5_eval_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 0;
    smul_add_felem5_eval_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 1;
    smul_add_felem5_eval_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 2;
    smul_add_felem5_eval_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 3;
    eq_intro (fas_nat5 (smul_add_felem5 #w u1 f2 acc1)) tmp

inline_for_extraction noextract
val mul_felem5:
    #w:lanes
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> out:felem_wide5 w
let mul_felem5 #w (f10,f11,f12,f13,f14) (r0,r1,r2,r3,r4) (r50,r51,r52,r53,r54) =
  let (a0,a1,a2,a3,a4) = smul_felem5 #w f10 (r0,r1,r2,r3,r4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #w f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #w f12 (r53,r54,r0,r1,r2) (a0,a1,a2,a3,a4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #w f13 (r52,r53,r54,r0,r1) (a0,a1,a2,a3,a4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #w f14 (r51,r52,r53,r54,r0) (a0,a1,a2,a3,a4) in
  (a0,a1,a2,a3,a4)

val mul_felem5_fits_lemma:
    #w:lanes
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> Lemma
    (requires
      felem_fits5 f1 (2, 3, 2, 2, 2) /\
      felem_fits5 r (1, 1, 1, 1, 1) /\
      felem_fits5 r5 (5, 5, 5, 5, 5))
    (ensures
      felem_wide_fits5 (mul_felem5 #w f1 r r5) (47, 35, 27, 19, 11))
    [SMTPat (mul_felem5 #w f1 r r5)]
let mul_felem5_fits_lemma #w f1 r r5 =
  let (r0, r1, r2, r3, r4) = r in
  let (f10, f11, f12, f13, f14) = f1 in
  let (r50, r51, r52, r53, r54) = r5 in

  let (a0,a1,a2,a3,a4) = smul_felem5 #w f10 (r0,r1,r2,r3,r4) in
  smul_felem5_fits_lemma #w #2 #(1,1,1,1,1) f10 (r0,r1,r2,r3,r4);
  assert (felem_wide_fits5 (a0,a1,a2,a3,a4) (2,2,2,2,2));
  let (a10,a11,a12,a13,a14) = smul_add_felem5 #w f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4) in
  smul_add_felem5_fits_lemma #w #3 #(5,1,1,1,1) #(2,2,2,2,2) f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4);
  let (a20,a21,a22,a23,a24) = smul_add_felem5 #w f12 (r53,r54,r0,r1,r2) (a10,a11,a12,a13,a14) in
  smul_add_felem5_fits_lemma #w #2 #(5,5,1,1,1) #(17,5,5,5,5) f12 (r53,r54,r0,r1,r2) (a10,a11,a12,a13,a14);
  let (a30,a31,a32,a33,a34) = smul_add_felem5 #w f13 (r52,r53,r54,r0,r1) (a20,a21,a22,a23,a24) in
  smul_add_felem5_fits_lemma #w #2 #(5,5,5,1,1) #(27,15,7,7,7) f13 (r52,r53,r54,r0,r1) (a20,a21,a22,a23,a24);
  let (a40,a41,a42,a43,a44) = smul_add_felem5 #w f14 (r51,r52,r53,r54,r0) (a30,a31,a32,a33,a34) in
  smul_add_felem5_fits_lemma #w #2 #(5,5,5,5,1) #(37,25,17,9,9) f14 (r51,r52,r53,r54,r0) (a30,a31,a32,a33,a34)

noextract
val precomp_r5:
    #w:lanes
  -> r:felem5 w
  -> r5:felem5 w
let precomp_r5 #w (r0, r1, r2, r3, r4) =
  let r50 = vec_smul_mod r0 (u64 5) in
  let r51 = vec_smul_mod r1 (u64 5) in
  let r52 = vec_smul_mod r2 (u64 5) in
  let r53 = vec_smul_mod r3 (u64 5) in
  let r54 = vec_smul_mod r4 (u64 5) in
  (r50, r51, r52, r53, r54)

noextract
let as_tup64_i (#w:lanes) (f:felem5 w) (i:nat{i < w}): tup64_5 =
  let (f0,f1,f2,f3,f4) = f in
  let v0 = vec_v f0 in
  let v1 = vec_v f1 in
  let v2 = vec_v f2 in
  let v3 = vec_v f3 in
  let v4 = vec_v f4 in
  (v0.[i],v1.[i],v2.[i],v3.[i],v4.[i])

let tup64_fits1 (f:uint64) (m:scale32) =
  uint_v f <= m * max26

let tup64_fits5 (f:tup64_5) (m:scale32_5) =
  let (x0, x1, x2, x3, x4) = f in
  let (m0, m1, m2, m3, m4) = m in
  tup64_fits1 x0 m0 /\
  tup64_fits1 x1 m1 /\
  tup64_fits1 x2 m2 /\
  tup64_fits1 x3 m3 /\
  tup64_fits1 x4 m4

noextract
let acc_inv_t (#w:lanes) (acc:felem5 w) : Type0 =
  let (o0, o1, o2, o3, o4) = acc in
  forall (i:nat). i < w ==>
   (if uint_v (vec_v o1).[i] >= pow2 26 then
      tup64_fits5 (as_tup64_i acc i) (1, 2, 1, 1, 1) /\
      uint_v (vec_v o1).[i] % pow2 26 < 64
    else tup64_fits5 (as_tup64_i acc i) (1, 1, 1, 1, 1))

val mul_felem5_eval_lemma:
    #w:lanes
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> Lemma
    (requires
      felem_fits5 f1 (2, 3, 2, 2, 2) /\
      felem_fits5 r (1, 1, 1, 1, 1) /\
      felem_fits5 r5 (5, 5, 5, 5, 5) /\
      r5 == precomp_r5 r)
    (ensures
      feval5 (mul_felem5 #w f1 r r5) == map2 (pfmul) (feval5 f1) (feval5 r))
    [SMTPat (mul_felem5 #w f1 r r5)]
let mul_felem5_eval_lemma #w f1 r r5 = admit()

inline_for_extraction noextract
val carry26:
    #w:lanes
  -> l:uint64xN w
  -> cin:uint64xN w
  -> uint64xN w & uint64xN w
let carry26 #w l cin =
  let l = vec_add_mod l cin in
  (vec_and l (mask26 w), vec_shift_right l 26ul)

let uint64xN_fits (#w:lanes) (x:uint64xN w) (m:nat) =
  forall (i:nat). i < w ==> uint_v (vec_v x).[i] < m

val carry26_lemma1:
    #w:lanes
  -> l:uint64
  -> cin:uint64
  -> Lemma
    (requires v l <= 2 * max26 /\ v cin <= 62 * max26)
    (ensures
     (let l' = l +. cin in
      let l0 = l' &. (u64 0x3ffffff) in
      let l1 = l' >>. 26ul in
      v l + v cin == v l1 * pow2 26 + v l0 /\
      v l0 <= max26 /\ v l1 < 64))
let carry26_lemma1 #w l cin =
  let mask26 = u64 0x3ffffff in
  assert_norm (0x3ffffff = pow2 26 - 1);
  let l'' = l +. cin in
  assert (v l'' == (v l + v cin) % pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v l + v cin) (pow2 64);
  let l' = l +! cin in
  assert (v l' == v l'');
  let l0 = l' &. mask26 in
  let l1 = l' >>. 26ul in
  mod_mask_lemma l' 26ul;
  uintv_extensionality (mod_mask #U64 26ul) mask26;
  assert (v l0 == v l' % pow2 26);
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v l') 26 32;
  FStar.Math.Lemmas.pow2_minus 32 26

val carry26_lemma_i:
    #w:lanes
  -> l:uint64xN w
  -> cin:uint64xN w
  -> i:nat{i < w}
  -> Lemma
    (requires felem_fits1 l 2 /\ felem_fits1 cin 62)
    (ensures
     (let (l0, l1) = carry26 #w l cin in
      (uint64xN_v l0).[i] <= max26 /\ (uint64xN_v l1).[i] < 64 /\
      (uint64xN_v l).[i] + (uint64xN_v cin).[i] ==
	(uint64xN_v l1).[i] * pow2 26 + (uint64xN_v l0).[i]))
let carry26_lemma_i #w l cin i =
  let li = (vec_v l).[i] in
  let cini = (vec_v cin).[i] in
  carry26_lemma1 #w li cini

val carry26_fits_lemma:
    #w:lanes
  -> l:uint64xN w
  -> cin:uint64xN w
  -> Lemma
    (requires felem_fits1 l 2 /\ felem_fits1 cin 62)
    (ensures
     (let (l0, l1) = carry26 #w l cin in
      felem_fits1 l0 1 /\ uint64xN_fits l1 64))
let carry26_fits_lemma #w l cin =
  match w with
  | 1 ->
    carry26_lemma_i #w l cin 0
  | 2 ->
    carry26_lemma_i #w l cin 0;
    carry26_lemma_i #w l cin 1
  | 4 ->
    carry26_lemma_i #w l cin 0;
    carry26_lemma_i #w l cin 1;
    carry26_lemma_i #w l cin 2;
    carry26_lemma_i #w l cin 3

val carry26_eval_lemma:
    #w:lanes
  -> l:uint64xN w
  -> cin:uint64xN w
  -> Lemma
    (requires felem_fits1 l 2 /\ felem_fits1 cin 62)
    (ensures
     (let (l0, l1) = carry26 #w l cin in
      (forall (i:nat). i < w ==>
	(uint64xN_v l).[i] + (uint64xN_v cin).[i] ==
	(uint64xN_v l1).[i] * pow2 26 + (uint64xN_v l0).[i])))
let carry26_eval_lemma #w l cin =
  match w with
  | 1 ->
    carry26_lemma_i #w l cin 0
  | 2 ->
    carry26_lemma_i #w l cin 0;
    carry26_lemma_i #w l cin 1
  | 4 ->
    carry26_lemma_i #w l cin 0;
    carry26_lemma_i #w l cin 1;
    carry26_lemma_i #w l cin 2;
    carry26_lemma_i #w l cin 3

inline_for_extraction noextract
val carry26_wide:
    #w:lanes
  -> l:uint64xN w
  -> cin:uint64xN w
  -> uint64xN w & uint64xN w
let carry26_wide #w l cin = carry26 #w l cin

val carry26_wide_lemma1:
    #w:lanes
  -> #m:scale64{m < 64}
  -> l:uint64{v l <= m * max26 * max26}
  -> cin:uint64{v cin <= 64 * max26}
  -> Lemma (
      let l' = l +. cin in
      let l0 = l' &. (u64 0x3ffffff) in
      let l1 = l' >>. 26ul in
      v l + v cin == v l1 * pow2 26 + v l0 /\
      v l0 <= max26 /\ v l1 <= (m + 1) * max26)
let carry26_wide_lemma1 #w #m l cin =
  let mask26 = u64 0x3ffffff in
  assert_norm (0x3ffffff = pow2 26 - 1);
  let l'' = l +. cin in
  assert (v l'' == (v l + v cin) % pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v l + v cin) (pow2 64);
  let l' = l +! cin in
  assert (v l' == v l'');
  let l0 = l' &. mask26 in
  let l1 = l' >>. 26ul in
  mod_mask_lemma l' 26ul;
  uintv_extensionality (mod_mask #U64 26ul) mask26;
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v l') 26 32;
  FStar.Math.Lemmas.euclidean_division_definition (v l') (pow2 26)

val carry26_wide_lemma_i:
    #w:lanes
  -> #m:scale64{m < 64}
  -> l:uint64xN w
  -> cin:uint64xN w
  -> i:nat{i < w}
  -> Lemma
    (requires felem_wide_fits1 l m /\ felem_fits1 cin 64)
    (ensures
     (let (l0, l1) = carry26 #w l cin in
      (uint64xN_v l0).[i] <= max26 /\ (uint64xN_v l1).[i] <= (m + 1) * max26 /\
      (uint64xN_v l).[i] + (uint64xN_v cin).[i] ==
	(uint64xN_v l1).[i] * pow2 26 + (uint64xN_v l0).[i]))
let carry26_wide_lemma_i #w #m l cin i =
  let li = (vec_v l).[i] in
  let cini = (vec_v cin).[i] in
  carry26_wide_lemma1 #w #m li cini

val carry26_wide_fits_lemma:
    #w:lanes
  -> #m:scale64{m < 64}
  -> l:uint64xN w
  -> cin:uint64xN w
  -> Lemma
    (requires felem_wide_fits1 l m /\ felem_fits1 cin 64)
    (ensures
     (let (l0, l1) = carry26 #w l cin in
      felem_fits1 l0 1 /\ felem_fits1 l1 (m + 1)))
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
  -> #m:scale64{m < 64}
  -> l:uint64xN w
  -> cin:uint64xN w
  -> Lemma
    (requires felem_wide_fits1 l m /\ felem_fits1 cin 64)
    (ensures
     (let (l0, l1) = carry26 #w l cin in
      felem_fits1 l0 1 /\ felem_fits1 l1 (m + 1)))
let carry26_wide_eval_lemma #w #m l cin =
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

inline_for_extraction noextract
val carry_wide_felem5:
    #w:lanes
  -> inp:felem_wide5 w
  -> out:felem5 w
let carry_wide_felem5 #w (i0, i1, i2, i3, i4) =
  let tmp0,c0 = carry26_wide i0 (zero w) in
  let tmp1,c1 = carry26_wide i1 c0 in
  let tmp2,c2 = carry26_wide i2 c1 in
  let tmp3,c3 = carry26_wide i3 c2 in
  let tmp4,c4 = carry26_wide i4 c3 in
  let tmp0,c5 = carry26 tmp0 (vec_smul_mod c4 (u64 5)) in
  let tmp1 = vec_add_mod tmp1 c5 in
  (tmp0, tmp1, tmp2, tmp3, tmp4)

(*
val vec_smul_mod_fits_lemma_i:
    #w:lanes
  -> c4:uint64xN w
  -> i:nat{i < w}
  -> Lemma
    (requires felem_fits1 c4 12)
    (ensures uint_v (vec_v (vec_smul_mod c4 (u64 5))).[i] <= 62 * max26)
let vec_smul_mod_fits_lemma_i #w c4 i = ()
*)

val vec_smul_mod_fits_lemma:
    #w:lanes
  -> c4:uint64xN w
  -> Lemma
    (requires felem_fits1 c4 12)
    (ensures  felem_fits1 (vec_smul_mod c4 (u64 5)) 62)
let vec_smul_mod_fits_lemma #w c4 = ()

val acc_inv_lemma_i:
    #w:lanes
  -> acc:felem5 w
  -> cin:uint64xN w
  -> i:nat{i < w}
  -> Lemma
    (requires
      felem_fits5 acc (1, 1, 1, 1, 1) /\
      uint64xN_fits cin 64)
    (ensures
      (let (i0, i1, i2, i3, i4) = acc in
       let i1' = vec_add_mod i1 cin in
       let acc1 = (i0, i1', i2, i3, i4) in
      (if uint_v (vec_v i1').[i] >= pow2 26 then
	 tup64_fits5 (as_tup64_i acc1 i) (1, 2, 1, 1, 1) /\
	 uint_v (vec_v i1').[i] % pow2 26 < 64
       else tup64_fits5 (as_tup64_i acc1 i) (1, 1, 1, 1, 1))))
let acc_inv_lemma_i #w acc cin i =
  let (i0, i1, i2, i3, i4) = acc in
  let i1' = vec_add_mod i1 cin in
  assert ((vec_v i1').[i] == (vec_v i1).[i] +. (vec_v cin).[i]);
  assert (v (vec_v i1).[i] + v (vec_v cin).[i] <= max26 + 63);
  assert_norm (max26 = pow2 26 - 1);
  FStar.Math.Lemmas.euclidean_division_definition (v (vec_v i1).[i] + v (vec_v cin).[i]) (pow2 26)

val acc_inv_lemma:
    #w:lanes
  -> acc:felem5 w
  -> cin:uint64xN w
  -> Lemma
    (requires
      felem_fits5 acc (1, 1, 1, 1, 1) /\
      uint64xN_fits cin 64)
    (ensures
      (let (i0, i1, i2, i3, i4) = acc in
       let i1' = vec_add_mod i1 cin in
       acc_inv_t (i0, i1', i2, i3, i4)))
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

val carry_wide_felem5_fits_lemma:
    #w:lanes
  -> inp:felem_wide5 w
  -> Lemma
    (requires felem_wide_fits5 inp (47, 35, 27, 19, 11))
    (ensures acc_inv_t (carry_wide_felem5 #w inp))
let carry_wide_felem5_fits_lemma #w inp =
  let (i0, i1, i2, i3, i4) = inp in
  let tmp0,c0 = carry26_wide i0 (zero w) in
  carry26_wide_eval_lemma #w #47 i0 (zero w);
  let tmp1,c1 = carry26_wide i1 c0 in
  carry26_wide_eval_lemma #w #35 i1 c0;
  let tmp2,c2 = carry26_wide i2 c1 in
  carry26_wide_eval_lemma #w #27 i2 c1;
  let tmp3,c3 = carry26_wide i3 c2 in
  carry26_wide_eval_lemma #w #19 i3 c2;
  let tmp4,c4 = carry26_wide i4 c3 in
  carry26_wide_eval_lemma #w #11 i4 c3;
  let tmp0',c5 = carry26 tmp0 (vec_smul_mod c4 (u64 5)) in
  vec_smul_mod_fits_lemma #w c4;
  carry26_fits_lemma #w tmp0 (vec_smul_mod c4 (u64 5));
  let tmp1' = vec_add_mod tmp1 c5 in
  acc_inv_lemma #w (tmp0', tmp1, tmp2, tmp3, tmp4) c5

val carry_wide_felem5_eval_lemma:
    #w:lanes
  -> inp:felem_wide5 w
  -> Lemma
    (requires felem_wide_fits5 inp (47, 35, 27, 19, 11))
    (ensures feval5 (carry_wide_felem5 #w inp) == feval5 inp)
let carry_wide_felem5_eval_lemma #w inp = admit()

inline_for_extraction noextract
val fmul_r5:
    #w:lanes
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> out:felem5 w
let fmul_r5 #w (f10, f11, f12, f13, f14) (r0, r1, r2, r3, r4) (r50, r51, r52, r53, r54) =
  let (t0, t1, t2, t3, t4) =
    mul_felem5 (f10, f11, f12, f13, f14) (r0, r1, r2, r3, r4) (r50, r51, r52, r53, r54) in
  carry_wide_felem5 (t0, t1, t2, t3, t4)

val fmul_r5_fits_lemma:
    #w:lanes
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> Lemma
    (requires
      felem_fits5 f1 (2, 3, 2, 2, 2) /\
      felem_fits5 r (1, 1, 1, 1, 1) /\
      felem_fits5 r5 (5, 5, 5, 5, 5))
    (ensures
      acc_inv_t (fmul_r5 #w f1 r r5))
    [SMTPat (fmul_r5 #w f1 r r5)]
let fmul_r5_fits_lemma #w f1 r r5 =
  let tmp = mul_felem5 f1 r r5 in
  mul_felem5_fits_lemma #w f1 r r5;
  let res = carry_wide_felem5 tmp in
  carry_wide_felem5_fits_lemma #w tmp

val fmul_r5_eval_lemma:
    #w:lanes
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> Lemma
    (requires
      felem_fits5 f1 (2, 3, 2, 2, 2) /\
      felem_fits5 r (1, 1, 1, 1, 1) /\
      felem_fits5 r5 (5, 5, 5, 5, 5) /\
      r5 == precomp_r5 r)
    (ensures
      feval5 (fmul_r5 #w f1 r r5) == map2 (pfmul) (feval5 f1) (feval5 r))
    [SMTPat (fmul_r5 #w f1 r r5)]
let fmul_r5_eval_lemma #w f1 r r5 =
  let tmp = mul_felem5 f1 r r5 in
  mul_felem5_eval_lemma #w f1 r r5;
  let res = carry_wide_felem5 tmp in
  carry_wide_felem5_eval_lemma #w tmp

inline_for_extraction noextract
val fadd_mul_r5:
    #w:lanes
  -> acc:felem5 w
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> out:felem5 w
let fadd_mul_r5 #w (a0, a1, a2, a3, a4) (f10, f11, f12, f13, f14) (r0, r1, r2, r3, r4) (r50, r51, r52, r53, r54) =
  let (a0, a1, a2, a3, a4) = fadd5 (a0, a1, a2, a3, a4) (f10, f11, f12, f13, f14) in
  let (t0, t1, t2, t3, t4) = mul_felem5 (a0, a1, a2, a3, a4) (r0, r1, r2, r3, r4) (r50, r51, r52, r53, r54) in
  carry_wide_felem5 (t0, t1, t2, t3, t4)

val fadd_mul_r5_fits_lemma:
    #w:lanes
  -> acc:felem5 w
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> Lemma
    (requires
      felem_fits5 acc (1, 2, 1, 1, 1) /\
      felem_fits5 f1 (1, 1, 1, 1, 1) /\
      felem_fits5 r (1, 1, 1, 1, 1) /\
      felem_fits5 r5 (5, 5, 5, 5, 5))
    (ensures
      acc_inv_t (fadd_mul_r5 acc f1 r r5))
    [SMTPat (fadd_mul_r5 acc f1 r r5)]
let fadd_mul_r5_fits_lemma #w acc f1 r r5 =
  let acc1 = fadd5 acc f1 in
  fadd5_fits_lemma #w acc f1;
  let tmp = mul_felem5 acc1 r r5 in
  mul_felem5_fits_lemma #w acc1 r r5;
  let res = carry_wide_felem5 tmp in
  carry_wide_felem5_fits_lemma #w tmp

val fadd_mul_r5_eval_lemma:
    #w:lanes
  -> acc:felem5 w
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> Lemma
    (requires
      felem_fits5 acc (1, 2, 1, 1, 1) /\
      felem_fits5 f1 (1, 1, 1, 1, 1) /\
      felem_fits5 r (1, 1, 1, 1, 1) /\
      felem_fits5 r5 (5, 5, 5, 5, 5) /\
      r5 == precomp_r5 r)
    (ensures
      feval5 (fadd_mul_r5 acc f1 r r5) ==
	map2 (pfmul) (map2 (pfadd) (feval5 acc) (feval5 f1)) (feval5 r))
    [SMTPat (fadd_mul_r5 acc f1 r r5)]
let fadd_mul_r5_eval_lemma #w acc f1 r r5 =
  let acc1 = fadd5 acc f1 in
  fadd5_eval_lemma #w acc f1;
  let tmp = mul_felem5 acc1 r r5 in
  mul_felem5_eval_lemma #w acc1 r r5;
  let res = carry_wide_felem5 tmp in
  carry_wide_felem5_eval_lemma #w tmp

inline_for_extraction noextract
val fmul_rn5:
    #w:lanes
  -> f1:felem5 w
  -> rn:felem5 w
  -> rn5:felem5 w
  -> out:felem5 w
let fmul_rn5 #w (f10, f11, f12, f13, f14) (rn0, rn1, rn2, rn3, rn4) (rn50, rn51, rn52, rn53, rn54) =
  let (t0, t1, t2, t3, t4) = mul_felem5 (f10, f11, f12, f13, f14)
    (rn0, rn1, rn2, rn3, rn4) (rn50, rn51, rn52, rn53, rn54) in
  carry_wide_felem5 (t0, t1, t2, t3, t4)
