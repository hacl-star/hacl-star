module Hacl.Impl.Poly1305.Field32xN

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.IntVector

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

(* high-level spec *)
let prime:pos =
  assert_norm (pow2 130 - 5 > 0);
  pow2 130 - 5

let pfelem = x:nat{x < prime}
noextract
let pfadd (f1:pfelem) (f2:pfelem) : pfelem = (f1 + f2) % prime
noextract
let pfmul (f1:pfelem) (f2:pfelem) : pfelem = (f1 `op_Multiply` f2) % prime

(* low-level spec *)

let lanes = w:width{w == 1 \/ w == 2 \/ w == 4}
inline_for_extraction
let uint64xN (w:lanes) = vec_t U64 w

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

unfold
let op_String_Access #a #len = LSeq.index #a #len

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

(* the impl *)

let felem (w:lanes) = lbuffer (uint64xN w) 5ul
let felem_wide (w:lanes) = felem w
let precomp_r (w:lanes) = lbuffer (uint64xN w) 20ul

noextract
val as_tup5: #w:lanes -> h:mem -> f:felem w -> GTot (felem5 w)
let as_tup5 #w h f =
  let s = as_seq h f in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  (s0,s1,s2,s3,s4)

noextract
val felem_fits: #w:lanes -> h:mem -> f:felem w -> m:scale32_5 -> Type0
let felem_fits #w h f m =
  felem_fits5 (as_tup5 h f) m

noextract
val felem_wide_fits: #w:lanes -> h:mem -> f:felem w -> m:scale32_5 -> Type0
let felem_wide_fits #w h f m =
  felem_wide_fits5 (as_tup5 h f) m

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
let transpose (#w:lanes) (f:felem5 w) : LSeq.lseq tup64_5 w =
  let (f0,f1,f2,f3,f4) = f in
  let v0 = vec_v f0 in
  let v1 = vec_v f1 in
  let v2 = vec_v f2 in
  let v3 = vec_v f3 in
  let v4 = vec_v f4 in
  LSeq.createi #tup64_5 w (fun i -> (v0.[i],v1.[i],v2.[i],v3.[i],v4.[i]))

noextract
let feval5 (#w:lanes) (f:felem5 w) : LSeq.lseq pfelem w =
  LSeq.map as_pfelem5 (transpose f)

noextract
let feval (#w:lanes) (h:mem) (f:felem w) : GTot (LSeq.lseq pfelem w) =
  feval5 (as_tup5 h f)

noextract
let fas_nat5 (#w:lanes) (f:felem5 w) : LSeq.lseq nat w =
  LSeq.map as_nat5 (transpose f)

noextract
let fas_nat (#w:lanes) (h:mem) (f:felem w) : GTot (LSeq.lseq nat w) =
  fas_nat5 (as_tup5 h f)

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

#reset-options "--z3rlimit 100 --using_facts_from '* -FStar.Seq'"

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
  assert (as_nat5 ((vec_v o0).[i],(vec_v o1).[i],(vec_v o2).[i],(vec_v o3).[i],(vec_v o4).[i]) ==
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
    (ensures  feval5 (fadd5 f1 f2) == LSeq.map2 pfadd (feval5 f1) (feval5 f2))
    [SMTPat (fadd5 f1 f2)]
let fadd5_eval_lemma #w f1 f2 =
  let open Lib.Sequence in
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

//[@CInline]
inline_for_extraction
val fadd_:
    #w:lanes
  -> out:felem w
  -> f1:felem w
  -> f2:felem w
  -> Stack unit
    (requires fun h ->
      live h f1 /\ live h f2 /\ live h out /\
      felem_fits h f1 (1,2,1,1,1) /\
      felem_fits h f2 (1,1,1,1,1))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      as_tup5 h1 out == fadd5 (as_tup5 h0 f1) (as_tup5 h0 f2) /\
      felem_fits h1 out (2, 3, 2, 2, 2) /\
      feval h1 out == LSeq.map2 pfadd (feval h0 f1) (feval h0 f2))
let fadd_ #w out f1 f2 =
  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in
  let f14 = f1.(4ul) in
  let f20 = f2.(0ul) in
  let f21 = f2.(1ul) in
  let f22 = f2.(2ul) in
  let f23 = f2.(3ul) in
  let f24 = f2.(4ul) in
  let (o0,o1,o2,o3,o4) =
    fadd5 (f10,f11,f12,f13,f14) (f20,f21,f22,f23,f24) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  out.(4ul) <- o4;
  ()

//[@CInline]
inline_for_extraction
val fadd:
    #w:lanes
  -> out:felem w
  -> f1:felem w
  -> f2:felem w
  -> Stack unit
    (requires fun h ->
      live h f1 /\ live h f2 /\ live h out /\
      felem_fits h f1 (1,2,1,1,1) /\
      felem_fits h f2 (1,1,1,1,1))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      felem_fits h1 out (2, 3, 2, 2, 2) /\
      feval h1 out == LSeq.map2 pfadd (feval h0 f1) (feval h0 f2))
let fadd #w out f1 f2 = fadd_ #w out f1 f2


inline_for_extraction
let zero (w:lanes) = vec_zero U64 w

inline_for_extraction
let mask26 (w:lanes) = vec_load (u64 0x3ffffff) w
inline_for_extraction
let mask14 (w:lanes) = vec_load (u64 0x3fff) w

inline_for_extraction
val create_felem:
    w:lanes
  -> StackInline (felem w)
    (requires fun h -> True)
    (ensures  fun h0 b h1 ->
      stack_allocated b h0 h1 (LSeq.create 5 (zero w)))
let create_felem w = create 5ul (zero w)

inline_for_extraction
val create_wide:
    w:lanes
  -> StackInline (felem_wide w)
    (requires fun h -> True)
    (ensures  fun h0 b h1 ->
      stack_allocated b h0 h1 (LSeq.create 5 (zero w)))
let create_wide w = create 5ul (zero w)

inline_for_extraction
val set_bit:
    #w:lanes
  -> f:felem w
  -> i:size_t{size_v i < 130}
  -> Stack unit
    (requires fun h -> live h f)
    (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1)
let set_bit #w f i =
  let b = u64 1 <<. (i %. 26ul) in
  let mask = vec_load b w in
  let fi = f.(i /. 26ul) in
  f.(i /. 26ul) <- vec_or fi mask

inline_for_extraction
val set_bit128:
    #w:lanes
  -> f:felem w
  -> Stack unit
    (requires fun h -> live h f)
    (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1)
let set_bit128 #w f =
  let b = u64 0x1000000 in
  let mask = vec_load b w in
  let f4 = f.(4ul) in
  f.(4ul) <- vec_or f4 mask

inline_for_extraction
val set_zero:
    #w:lanes
  -> f:felem w
  -> Stack unit
    (requires fun h -> live h f)
    (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1)
let set_zero #w f =
  f.(0ul) <- zero w;
  f.(1ul) <- zero w;
  f.(2ul) <- zero w;
  f.(3ul) <- zero w;
  f.(4ul) <- zero w

inline_for_extraction
val copy_felem:
    #w:lanes
  -> f1:felem w
  -> f2:felem w
  -> Stack unit
    (requires fun h -> live h f1 /\ live h f2)
    (ensures  fun h0 _ h1 -> modifies (loc f1) h0 h1)
let copy_felem #w f1 f2 =
  f1.(0ul) <- f2.(0ul);
  f1.(1ul) <- f2.(1ul);
  f1.(2ul) <- f2.(2ul);
  f1.(3ul) <- f2.(3ul);
  f1.(4ul) <- f2.(4ul)

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

val smul_felem5_fits_lemma:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> u1:uint64xN w
  -> f2:felem5 w
  -> Lemma
    (requires felem_fits1 u1 m1 /\ felem_fits5 f2 m2)
    (ensures  felem_wide_fits5 (smul_felem5 #w u1 f2) (m1 *^ m2))
let smul_felem5_fits_lemma #w #m1 #m2 u1 f2 = admit()

noextract
let uint64xN_v (#w:lanes) (e:uint64xN w) : LSeq.lseq nat w =
  let e = vec_v e in
  LSeq.createi #nat w (fun i -> uint_v e.[i])

val smul_felem5_eval_lemma:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> u1:uint64xN w
  -> f2:felem5 w
  -> Lemma
    (requires felem_fits1 u1 m1 /\ felem_fits5 f2 m2)
    (ensures  fas_nat5 (smul_felem5 #w u1 f2) == LSeq.map2 #nat #nat #nat (fun a b -> a * b) (uint64xN_v u1) (fas_nat5 f2))
let smul_felem5_eval_lemma #w #m1 #m2 u1 f2 = admit()

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
      felem_fits1 u1 m1 /\
      felem_fits5 f2 m2 /\
      felem_wide_fits5 acc1 m3 /\
      m3 +* m1 *^ m2 <=* s64x5 4096)
    (ensures
      felem_wide_fits5 (smul_add_felem5 #w u1 f2 acc1) (m3 +* m1 *^ m2))
let smul_add_felem5_fits_lemma #w #m1 #m2 #m3 u1 f2 acc1 = admit()

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
	LSeq.map2 #nat #nat #nat (fun a b -> a + b) (fas_nat5 acc1)
	  (LSeq.map2 #nat #nat #nat (fun a b -> a * b) (uint64xN_v u1) (fas_nat5 f2)))
let smul_add_felem5_eval_lemma #w #m1 #m2 #m3 u1 f2 acc1 = admit()

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
let mul_felem5_fits_lemma #w f1 r r5 = admit()

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
      feval5 (mul_felem5 #w f1 r r5) == LSeq.map2 (pfmul) (feval5 f1) (feval5 r))
    [SMTPat (mul_felem5 #w f1 r r5)]
let mul_felem5_eval_lemma #w f1 r r5 = admit()

inline_for_extraction
val mul_felem_:
    #w:lanes
  -> out:felem_wide w
  -> f1:felem w
  -> r:felem w
  -> r5:felem w
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\ live h r /\ live h r5 /\
      felem_fits h f1 (2, 3, 2, 2, 2) /\
      felem_fits h r (1, 1, 1, 1, 1) /\
      felem_fits h r5 (5, 5, 5, 5, 5) /\
      as_tup5 h r5 == precomp_r5 (as_tup5 h r))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      as_tup5 h1 out == mul_felem5 (as_tup5 h0 f1) (as_tup5 h0 r) (as_tup5 h0 r5) /\
      felem_wide_fits h1 out (47, 35, 27, 19, 11) /\
      feval h1 out == LSeq.map2 (pfmul) (feval h0 f1) (feval h0 r))
let mul_felem_ #w out f1 r r5 =
  let r0 = r.(0ul) in
  let r1 = r.(1ul) in
  let r2 = r.(2ul) in
  let r3 = r.(3ul) in
  let r4 = r.(4ul) in

  let r50 = r5.(0ul) in
  let r51 = r5.(1ul) in
  let r52 = r5.(2ul) in
  let r53 = r5.(3ul) in
  let r54 = r5.(4ul) in

  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in
  let f14 = f1.(4ul) in
  let (o0, o1, o2, o3, o4) =
    mul_felem5 #w (f10, f11, f12, f13, f14)
      (r0, r1, r2, r3, r4) (r50, r51, r52, r53, r54) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  out.(4ul) <- o4


inline_for_extraction
val mul_felem:
    #w:lanes
  -> out:felem_wide w
  -> f1:felem w
  -> r:felem w
  -> r5:felem w
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\ live h r /\ live h r5 /\
      felem_fits h f1 (2, 3, 2, 2, 2) /\
      felem_fits h r (1, 1, 1, 1, 1) /\
      felem_fits h r5 (5, 5, 5, 5, 5) /\
      as_tup5 h r5 == precomp_r5 (as_tup5 h r))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      felem_wide_fits h1 out (47, 35, 27, 19, 11) /\
      feval h1 out == LSeq.map2 (pfmul) (feval h0 f1) (feval h0 r))
[@ CInline]
let mul_felem #w out f1 r r5 = mul_felem_ #w out f1 r r5

inline_for_extraction noextract
val carry26:
    #w:lanes
  -> l:uint64xN w
  -> cin:uint64xN w
  -> uint64xN w & uint64xN w
let carry26 #w l cin =
  let l = vec_add_mod l cin in
  (vec_and l (mask26 w), vec_shift_right l 26ul)

inline_for_extraction noextract
val carry26_wide:
    #w:lanes
  -> l:uint64xN w
  -> cin:uint64xN w
  -> uint64xN w & uint64xN w
let carry26_wide #w l cin = carry26 #w l cin

inline_for_extraction noextract
val carry_wide_felem5:
    #w:lanes
  -> inp:felem5 w
  -> out:felem_wide5 w
let carry_wide_felem5 #w (i0, i1, i2, i3, i4) =
  let tmp0,c0 = carry26_wide i0 (zero w) in
  let tmp1,c1 = carry26_wide i1 c0 in
  let tmp2,c2 = carry26_wide i2 c1 in
  let tmp3,c3 = carry26_wide i3 c2 in
  let tmp4,c4 = carry26_wide i4 c3 in
  let tmp0,c5 = carry26 tmp0 (vec_smul_mod c4 (u64 5)) in
  let tmp1 = vec_add_mod tmp1 c5 in
  (tmp0, tmp1, tmp2, tmp3, tmp4)

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

noextract
let acc_inv_t (#w:lanes) (acc:felem5 w) : Type0 =
  let (o0, o1, o2, o3, o4) = acc in
  forall (i:nat). i < w ==>
   (if uint_v (vec_v o1).[i] >= pow2 26 then
      felem_fits5 acc (1, 2, 1, 1, 1) /\
      uint_v (vec_v o1).[i] % pow2 26 < 64
    else felem_fits5 acc (1, 1, 1, 1, 1))

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
let fmul_r5_fits_lemma #w f1 r r5 = admit()

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
      feval5 (fmul_r5 #w f1 r r5) == LSeq.map2 (pfmul) (feval5 f1) (feval5 r))
    [SMTPat (fmul_r5 #w f1 r r5)]
let fmul_r5_eval_lemma #w f1 r r5 = admit()

inline_for_extraction
val fmul_r_:
    #w:lanes
  -> out:felem w
  -> f1:felem w
  -> p:precomp_r w
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\ live h p /\
     (let r = gsub p 0ul 5ul in
      let r5 = gsub p 5ul 5ul in
      felem_fits h f1 (2, 3, 2, 2, 2) /\
      felem_fits h r (1, 1, 1, 1, 1) /\
      felem_fits h r5 (5, 5, 5, 5, 5) /\
      as_tup5 h r5 == precomp_r5 (as_tup5 h r)))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
     (let r = gsub p 0ul 5ul in
      let r5 = gsub p 5ul 5ul in
      //as_tup5 h1 out == fmul_r5 (as_tup5 h0 f1) (as_tup5 h0 r) (as_tup5 h0 r5)))
      acc_inv_t (as_tup5 h1 out) /\
      feval h1 out == LSeq.map2 (pfmul) (feval h0 f1) (feval h0 r)))
let fmul_r_ #w out f1 p =
  let r = sub p 0ul 5ul in
  let r5 = sub p 5ul 5ul in
  let r0 = r.(0ul) in
  let r1 = r.(1ul) in
  let r2 = r.(2ul) in
  let r3 = r.(3ul) in
  let r4 = r.(4ul) in

  let r50 = r5.(0ul) in
  let r51 = r5.(1ul) in
  let r52 = r5.(2ul) in
  let r53 = r5.(3ul) in
  let r54 = r5.(4ul) in

  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in
  let f14 = f1.(4ul) in

  let (o0, o1, o2, o3, o4) =
    fmul_r5 (f10, f11, f12, f13, f14)
      (r0, r1, r2, r3, r4) (r50, r51, r52, r53, r54) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  out.(4ul) <- o4


inline_for_extraction
val fmul_r:
    #w:lanes
  -> out:felem w
  -> f1:felem w
  -> p:precomp_r w
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\ live h p /\
     (let r = gsub p 0ul 5ul in
      let r5 = gsub p 5ul 5ul in
      felem_fits h f1 (2, 3, 2, 2, 2) /\
      felem_fits h r (1, 1, 1, 1, 1) /\
      felem_fits h r5 (5, 5, 5, 5, 5) /\
      as_tup5 h r5 == precomp_r5 (as_tup5 h r)))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
     (let r = gsub p 0ul 5ul in
      let r5 = gsub p 5ul 5ul in
      acc_inv_t (as_tup5 h1 out) /\
      feval h1 out == LSeq.map2 (pfmul) (feval h0 f1) (feval h0 r)))
let fmul_r #w out f1 p = fmul_r_ out f1 p

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
let fadd_mul_r5_fits_lemma #w acc f1 r r5 = admit()

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
	LSeq.map2 (pfmul) (LSeq.map2 (pfadd) (feval5 acc) (feval5 f1)) (feval5 r))
    [SMTPat (fadd_mul_r5 acc f1 r r5)]
let fadd_mul_r5_eval_lemma #w acc f1 r r5 = admit()

inline_for_extraction
val fadd_mul_r_:
    #w:lanes
  -> acc:felem w
  -> f1:felem w
  -> p:precomp_r w
  -> Stack unit
    (requires fun h ->
      live h acc /\ live h f1 /\ live h p /\
     (let r = gsub p 0ul 5ul in
      let r5 = gsub p 5ul 5ul in
      felem_fits h acc (1, 2, 1, 1, 1) /\
      felem_fits h f1 (1, 1, 1, 1, 1) /\
      felem_fits h r (1, 1, 1, 1, 1) /\
      felem_fits h r5 (5, 5, 5, 5, 5) /\
      as_tup5 h r5 == precomp_r5 (as_tup5 h r)))
    (ensures  fun h0 _ h1 ->
      modifies (loc acc) h0 h1 /\
     (let r = gsub p 0ul 5ul in
      let r5 = gsub p 5ul 5ul in
      //as_tup5 h1 acc == fadd_mul_r5 (as_tup5 h0 acc) (as_tup5 h0 f1) (as_tup5 h0 r) (as_tup5 h0 r5) /\
      acc_inv_t (as_tup5 h1 acc) /\
      feval h1 acc == LSeq.map2 (pfmul) (LSeq.map2 (pfadd) (feval h0 acc) (feval h0 f1)) (feval h0 r)))
let fadd_mul_r_ #w out f1 p =
  let r = sub p 0ul 5ul in
  let r5 = sub p 5ul 5ul in
  let r0 = r.(0ul) in
  let r1 = r.(1ul) in
  let r2 = r.(2ul) in
  let r3 = r.(3ul) in
  let r4 = r.(4ul) in

  let r50 = r5.(0ul) in
  let r51 = r5.(1ul) in
  let r52 = r5.(2ul) in
  let r53 = r5.(3ul) in
  let r54 = r5.(4ul) in

  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in
  let f14 = f1.(4ul) in

  let a0 = out.(0ul) in
  let a1 = out.(1ul) in
  let a2 = out.(2ul) in
  let a3 = out.(3ul) in
  let a4 = out.(4ul) in

  let (o0, o1, o2, o3, o4) =
    fadd_mul_r5 (a0, a1, a2, a3, a4) (f10, f11, f12, f13, f14)
      (r0, r1, r2, r3, r4) (r50, r51, r52, r53, r54) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  out.(4ul) <- o4

inline_for_extraction
val fadd_mul_r:
    #w:lanes
  -> acc:felem w
  -> f1:felem w
  -> p:precomp_r w
  -> Stack unit
    (requires fun h ->
      live h acc /\ live h f1 /\ live h p /\
     (let r = gsub p 0ul 5ul in
      let r5 = gsub p 5ul 5ul in
      felem_fits h acc (1, 2, 1, 1, 1) /\
      felem_fits h f1 (1, 1, 1, 1, 1) /\
      felem_fits h r (1, 1, 1, 1, 1) /\
      felem_fits h r5 (5, 5, 5, 5, 5) /\
      as_tup5 h r5 == precomp_r5 (as_tup5 h r)))
    (ensures  fun h0 _ h1 ->
      modifies (loc acc) h0 h1 /\
     (let r = gsub p 0ul 5ul in
      let r5 = gsub p 5ul 5ul in
      acc_inv_t (as_tup5 h1 acc) /\
      feval h1 acc == LSeq.map2 (pfmul) (LSeq.map2 (pfadd) (feval h0 acc) (feval h0 f1)) (feval h0 r)))
let fadd_mul_r #w out f1 p = fadd_mul_r_ #w out f1 p

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

inline_for_extraction
val fmul_rn:
    #w:lanes
  -> out:felem w
  -> f1:felem w
  -> p:precomp_r w
  -> Stack unit
    (requires fun h -> live h out /\ live h f1 /\ live h p)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1)
let fmul_rn #w out f1 p =
  let rn = sub p 10ul 5ul in
  let rn5 = sub p 15ul 5ul in

  let rn0 = rn.(0ul) in
  let rn1 = rn.(1ul) in
  let rn2 = rn.(2ul) in
  let rn3 = rn.(3ul) in
  let rn4 = rn.(4ul) in

  let rn50 = rn5.(0ul) in
  let rn51 = rn5.(1ul) in
  let rn52 = rn5.(2ul) in
  let rn53 = rn5.(3ul) in
  let rn54 = rn5.(4ul) in

  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in
  let f14 = f1.(4ul) in

  let (o0, o1, o2, o3, o4) =
    fmul_rn5 (f10, f11, f12, f13, f14)
      (rn0, rn1, rn2, rn3, rn4) (rn50, rn51, rn52, rn53, rn54) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  out.(4ul) <- o4



//[@ CInline]
inline_for_extraction
val carry_wide_felem: #w:lanes -> out:felem w -> inp:felem_wide w -> Stack unit
                   (requires (fun h -> live h out /\ live h inp))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let carry_wide_felem #w out inp =
  let i0 = inp.(size 0) in
  let i1 = inp.(size 1) in
  let i2 = inp.(size 2) in
  let i3 = inp.(size 3) in
  let i4 = inp.(size 4) in
  let tmp0,carry = carry26_wide i0 (zero w) in
  let tmp1,carry = carry26_wide i1 carry in
  let tmp2,carry = carry26_wide i2 carry in
  let tmp3,carry = carry26_wide i3 carry in
  let tmp4,carry = carry26_wide i4 carry in
  let tmp0,carry = carry26 tmp0 (vec_smul_mod carry (u64 5)) in
  let tmp1 = vec_add_mod tmp1 carry in
  out.(size 0) <- tmp0;
  out.(size 1) <- tmp1;
  out.(size 2) <- tmp2;
  out.(size 3) <- tmp3;
  out.(size 4) <- tmp4

//[@ CInline]
inline_for_extraction
val carry_felem: #w:lanes -> f:felem w -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
[@ CInline]
let carry_felem #w f =
  let f0 = f.(size 0) in
  let f1 = f.(size 1) in
  let f2 = f.(size 2) in
  let f3 = f.(size 3) in
  let f4 = f.(size 4) in
  let tmp0,carry = carry26 f0 (zero w) in
  let tmp1,carry = carry26 f1 carry in
  let tmp2,carry = carry26 f2 carry in
  let tmp3,carry = carry26 f3 carry in
  let tmp4 = vec_add_mod f4 carry in
  f.(size 0) <- tmp0;
  f.(size 1) <- tmp1;
  f.(size 2) <- tmp2;
  f.(size 3) <- tmp3;
  f.(size 4) <- tmp4

//[@ CInline]
inline_for_extraction
val carry_top_felem: #w:lanes -> f:felem w -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
[@ CInline]
let carry_top_felem #w f =
  let f0 = f.(size 0) in
  let f1 = f.(size 1) in
  let f2 = f.(size 2) in
  let f3 = f.(size 3) in
  let f4 = f.(size 4) in
  let tmp4,carry = carry26 f4 (zero w) in
  let tmp0,carry = carry26 f0 (vec_smul_mod carry (u64 5)) in
  let tmp1 = vec_add_mod f1 carry in
  f.(size 0) <- tmp0;
  f.(size 1) <- tmp1;
  f.(size 4) <- tmp4

inline_for_extraction
val precompute_shift_reduce: #w:lanes -> f1:felem w -> f2:felem w -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc f1) h0 h1))
let precompute_shift_reduce #w f1 f2 =
    let f20 = f2.(size 0) in
    let f21 = f2.(size 1) in
    let f22 = f2.(size 2) in
    let f23 = f2.(size 3) in
    let f24 = f2.(size 4) in
    f1.(size 0) <- vec_smul_mod f20 (u64 5);
    f1.(size 1) <- vec_smul_mod f21 (u64 5);
    f1.(size 2) <- vec_smul_mod f22 (u64 5);
    f1.(size 3) <- vec_smul_mod f23 (u64 5);
    f1.(size 4) <- vec_smul_mod f24 (u64 5)

inline_for_extraction
val fmul_r1_normalize: out:felem 1 -> p:precomp_r 1 -> Stack unit
                   (requires (fun h -> live h out /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc out |+| loc p) h0 h1))
[@ CInline]
let fmul_r1_normalize out p =
    push_frame();
    admit();
    let tmp = create_felem 1 in
    let r = sub p (size 0) (size 5) in
    let r_5 = sub p (size 5) (size 5) in
    mul_felem tmp out r r_5;
    carry_wide_felem out tmp;
    pop_frame()

inline_for_extraction
val fmul_r2_normalize: out:felem 2 -> p:precomp_r 2 -> Stack unit
                   (requires (fun h -> live h out /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc out |+| loc p) h0 h1))
[@ CInline]
let fmul_r2_normalize out p =
    push_frame();
    admit();
    let tmp = create_felem 2 in
    let r = sub p (size 0) (size 5) in
    let r2 = sub p (size 10) (size 5) in
    let r2_5 = sub p (size 15) (size 5) in
    r2.(size 0) <- vec_interleave_low r2.(size 0) r.(size 0);
    r2.(size 1) <- vec_interleave_low r2.(size 1) r.(size 1);
    r2.(size 2) <- vec_interleave_low r2.(size 2) r.(size 2);
    r2.(size 3) <- vec_interleave_low r2.(size 3) r.(size 3);
    r2.(size 4) <- vec_interleave_low r2.(size 4) r.(size 4);
    precompute_shift_reduce r2_5 r2;
    mul_felem tmp out r2 r2_5;
    carry_wide_felem out tmp;
    let o0 = out.(0ul) in
    let o1 = out.(1ul) in
    let o2 = out.(2ul) in
    let o3 = out.(3ul) in
    let o4 = out.(4ul) in
    out.(size 0) <- vec_add_mod o0 (vec_interleave_high o0 o0);
    out.(size 1) <- vec_add_mod o1 (vec_interleave_high o1 o1);
    out.(size 2) <- vec_add_mod o2 (vec_interleave_high o2 o2);
    out.(size 3) <- vec_add_mod o3 (vec_interleave_high o3 o3);
    out.(size 4) <- vec_add_mod o4 (vec_interleave_high o4 o4);
    carry_felem out;
    carry_top_felem out;
    pop_frame()

inline_for_extraction
val fmul_r4_normalize: out:felem 4 -> p:precomp_r 4 -> Stack unit
                   (requires (fun h -> live h out /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc out |+| loc p) h0 h1))
[@ CInline]
let fmul_r4_normalize out p =
    push_frame();
    admit();
    let r = sub p (size 0) (size 5) in
    let r_5 = sub p (size 5) (size 5) in
    let r4 = sub p (size 10) (size 5) in
    let r4_5 = sub p (size 15) (size 5) in
    let r2 = create_felem 4 in
    let r3 = create_felem 4 in
    let tmp = create_felem 4 in
    mul_felem tmp r r r_5;
    carry_wide_felem r2 tmp;
    mul_felem tmp r2 r r_5;
    carry_wide_felem r3 tmp;
    let h0 = ST.get() in
    loop_nospec #h0 (size 5) r2
      (fun i ->
         let v1212 = vec_interleave_low r2.(i) r.(i) in
         let v3434 = vec_interleave_low r4.(i) r3.(i) in
	 let v1234 = vec_interleave_low (cast U128 2 v3434) (cast U128 2 v1212) in
	 r2.(i) <- cast U64 4 v1234);

    let r1234 = r2 in
    let r1234_5 = r3 in
    precompute_shift_reduce r1234_5 r1234;
    mul_felem tmp out r1234 r1234_5;
    carry_wide_felem out tmp;

    loop_nospec #h0 (size 5) out
      (fun i ->
	 let oi = out.(i) in
	 let v0 = cast U64 4 (vec_interleave_high (cast U128 2 oi) (cast U128 2 oi)) in
         let v1 = vec_add_mod oi v0 in
	 let v2 =
	   vec_add_mod v1 (vec_permute4 v1 1ul 1ul 1ul 1ul) in
	 out.(i) <- v2);
    carry_felem out;
    carry_top_felem out;
    pop_frame()

inline_for_extraction
val fmul_rn_normalize: #w:lanes -> out:felem w -> p:precomp_r w -> Stack unit
                   (requires (fun h -> live h out /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc out |+| loc p) h0 h1))
[@ CInline]
let fmul_rn_normalize #w out p =
  match w with
  | 1 -> fmul_r1_normalize out p
  | 2 -> fmul_r2_normalize out p
  | 4 -> fmul_r4_normalize out p



inline_for_extraction
val load_felem: #w:lanes -> f:felem w -> lo:uint64xN w -> hi:uint64xN w -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felem #w f lo hi =
    f.(size 0) <- vec_and lo (mask26 w);
    f.(size 1) <- vec_and (vec_shift_right lo (size 26)) (mask26 w);
    f.(size 2) <- vec_or (vec_shift_right lo (size 52)) (vec_shift_left (vec_and hi (mask14 w)) (size 12));
    f.(size 3) <- vec_and (vec_shift_right hi (size 14)) (mask26 w);
    f.(size 4) <- vec_shift_right hi (size 40)


inline_for_extraction
val load_precompute_r1: p:precomp_r 1 -> r0:uint64 -> r1:uint64 -> Stack unit
                   (requires (fun h -> live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc p) h0 h1))
let load_precompute_r1 p r0 r1 =
    push_frame();
    admit();
    let r = sub p (size 0) (size 5) in
    let r5 = sub p (size 5) (size 5) in
    let rn = sub p (size 10) (size 5) in
    let rn_5 = sub p (size 15) (size 5) in
    let r_vec0 = vec_load r0 1 in
    let r_vec1 = vec_load r1 1 in
    load_felem r r_vec0 r_vec1;
    precompute_shift_reduce r5 r;
    copy_felem rn r;
    copy_felem rn_5 r5;
    pop_frame()

inline_for_extraction
val load_precompute_r2: p:precomp_r 2 -> r0:uint64 -> r1:uint64 -> Stack unit
                   (requires (fun h -> live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc p) h0 h1))
let load_precompute_r2 p r0 r1 =
    push_frame();
    admit();
    let r = sub p (size 0) (size 5) in
    let r5 = sub p (size 5) (size 5) in
    let rn = sub p (size 10) (size 5) in
    let rn_5 = sub p (size 15) (size 5) in
    let r_vec0 = vec_load r0 2 in
    let r_vec1 = vec_load r1 2 in
    load_felem r r_vec0 r_vec1;
    precompute_shift_reduce r5 r;
    let tmp = create_felem 2 in
    mul_felem tmp r r r5;
    carry_wide_felem rn tmp;
    precompute_shift_reduce rn_5 rn;
    pop_frame()

inline_for_extraction
val load_precompute_r4: p:precomp_r 4 -> r0:uint64 -> r1:uint64 -> Stack unit
                   (requires (fun h -> live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc p) h0 h1))
let load_precompute_r4 p r0 r1 =
    push_frame();
    admit();
    let r = sub p (size 0) (size 5) in
    let r5 = sub p (size 5) (size 5) in
    let rn = sub p (size 10) (size 5) in
    let rn_5 = sub p (size 15) (size 5) in
    let r_vec0 = vec_load r0 4 in
    let r_vec1 = vec_load r1 4 in
    load_felem r r_vec0 r_vec1;
    precompute_shift_reduce r5 r;
    let tmp = create_felem 4 in
    mul_felem tmp r r r5;
    carry_wide_felem rn tmp;
    precompute_shift_reduce rn_5 rn;
    mul_felem tmp rn rn rn_5;
    carry_wide_felem rn tmp;
    precompute_shift_reduce rn_5 rn;
    pop_frame()

inline_for_extraction
val load_precompute_r: #w:lanes -> p:precomp_r w -> r0:uint64 -> r1:uint64 -> Stack unit
                   (requires (fun h -> live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc p) h0 h1))
let load_precompute_r #w p r0 r1 =
  match w with
  | 1 -> load_precompute_r1 p r0 r1
  | 2 -> load_precompute_r2 p r0 r1
  | 4 -> load_precompute_r4 p r0 r1

inline_for_extraction
val subtract_p: #w:lanes -> f:felem w -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let subtract_p #w f =
  let f0 = f.(size 0) in
  let f1 = f.(size 1) in
  let f2 = f.(size 2) in
  let f3 = f.(size 3) in
  let f4 = f.(size 4) in
  let mh = vec_load (u64 0x3ffffff) w in
  let ml = vec_load (u64 0x3fffffb) w in
  let mask = vec_eq_mask f4 mh in
  let mask = vec_and mask (vec_eq_mask f3 mh) in
  let mask = vec_and mask (vec_eq_mask f2 mh) in
  let mask = vec_and mask (vec_eq_mask f1 mh) in
  let mask = vec_and mask (vec_gte_mask f0 ml) in
  let ph = vec_and mask mh in
  let pl = vec_and mask ml in
  f.(size 0) <- vec_sub_mod f0 pl;
  f.(size 1) <- vec_sub_mod f1 ph;
  f.(size 2) <- vec_sub_mod f2 ph;
  f.(size 3) <- vec_sub_mod f3 ph;
  f.(size 4) <- vec_sub_mod f4 ph

inline_for_extraction
val reduce_felem: #w:lanes -> f:felem w -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let reduce_felem #w f =
    carry_felem f;
    carry_top_felem f;
    subtract_p f

inline_for_extraction
val load_felem1_le: f:felem 1 -> b:lbuffer uint8 16ul -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felem1_le f b =
    let lo = vec_load_le U64 1 (sub b (size 0) (size 8)) in
    let hi = vec_load_le U64 1 (sub b (size 8) (size 8)) in
    load_felem f lo hi

inline_for_extraction
val load_felem2_le: f:felem 2 -> b:lbuffer uint8 32ul -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felem2_le f b =
    let b1 = vec_load_le U64 2 (sub b (size 0) (size 16)) in
    let b2 = vec_load_le U64 2 (sub b (size 16) (size 16)) in
    let lo = vec_interleave_low b1 b2 in
    let hi = vec_interleave_high b1 b2 in
    load_felem f lo hi

inline_for_extraction
val load_felem4_le: f:felem 4 -> b:lbuffer uint8 64ul -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felem4_le f b =
    let lo0 = vec_load_le U128 2 (sub b (size 0) (size 32)) in
    let hi0 = vec_load_le U128 2 (sub b (size 32) (size 32)) in
    let lo1 = vec_interleave_low lo0 hi0 in
    let hi1 = vec_interleave_high lo0 hi0 in
    let lo2 = cast U64 4 lo1 in
    let hi2 = cast U64 4 hi1 in
    let lo = vec_interleave_low lo2 hi2 in
    let hi = vec_interleave_high lo2 hi2 in
    load_felem f lo hi

inline_for_extraction
val load_felems_le: #w:lanes -> f:felem w -> b:lbuffer uint8 (size w *! 16ul) -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felems_le #w f b =
  match w with
  | 1 -> load_felem1_le f b
  | 2 -> load_felem2_le f b
  | 4 -> load_felem4_le f b


inline_for_extraction
val load_felem_le: #w:lanes -> f:felem w -> b:lbuffer uint8 16ul -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felem_le #w f b =
  let lo = uint_from_bytes_le #U64 (sub b 0ul 8ul) in
  let hi = uint_from_bytes_le #U64 (sub b 8ul 8ul) in
  let f0 = vec_load lo w in
  let f1 = vec_load hi w in
  load_felem f f0 f1

inline_for_extraction
val store_felem: #w:lanes -> f:felem w -> Stack (uint64xN w & uint64xN w)
                 (requires (fun h -> live h f))
		 (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let store_felem #w f =
    carry_felem f;
    let f0 = f.(0ul) in
    let f1 = f.(1ul) in
    let f2 = f.(2ul) in
    let f3 = f.(3ul) in
    let f4 = f.(4ul) in
    let f0 = vec_or (vec_or f0 (vec_shift_left f1 (size 26))) (vec_shift_left f2 (size 52)) in
    let f1 = vec_or (vec_or (vec_shift_right f2 (size 12)) (vec_shift_left f3 (size 14))) (vec_shift_left f4 (size 40)) in
    (f0,f1)

inline_for_extraction
val store_felem1_le: b:lbuffer uint8 16ul -> f:felem 1 -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f |+| loc b) h0 h1))
let store_felem1_le b f =
    let (r0,r1) = store_felem #1 f in
    vec_store_le (sub b (size 0) (size 8)) r0;
    vec_store_le (sub b (size 8) (size 8)) r1

inline_for_extraction
val store_felem2_le: b:lbuffer uint8 16ul -> f:felem 2 -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f |+| loc b) h0 h1))
let store_felem2_le b f =
    let (f0,f1) = store_felem #2 f in
    let r0 = vec_interleave_low f0 f1 in
    vec_store_le (sub b (size 0) (size 16)) r0

inline_for_extraction
val store_felem4_le: b:lbuffer uint8 16ul -> f:felem 4 -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f |+| loc b) h0 h1))
let store_felem4_le b f =
    push_frame ();
    let (f0,f1) = store_felem #4 f in
    let lo = vec_interleave_low f0 f1 in
    let hi = vec_interleave_high f0 f1 in
    let lo1 = cast U128 2 lo in
    let hi1 = cast U128 2 hi in
    let r0 = vec_interleave_low lo1 hi1 in
    let tmp = create (size 32) (u8 0) in
    vec_store_le (sub tmp (size 0) (size 32)) r0;
    copy b (sub tmp 0ul 16ul);
    pop_frame()

inline_for_extraction
val store_felem_le: #w:lanes -> b:lbuffer uint8 16ul -> f:felem w -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f |+| loc b) h0 h1))
let store_felem_le #w b f =
  match w with
  | 1 -> store_felem1_le b f
  | 2 -> store_felem2_le b f
  | 4 -> store_felem4_le b f
