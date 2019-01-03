module Poly1305.Field32

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

#reset-options "--z3rlimit 50  --using_facts_from '* -FStar.Seq'"

(* high-level spec *)
let prime:pos =
  assert_norm (pow2 130 - 5 > 0);
  pow2 130 - 5

let pfelem = x:nat{x < prime}

val pfadd: pfelem -> pfelem -> pfelem
let pfadd f1 f2 = (f1 + f2) % prime

(* low-level spec *)

let felem5 = (uint32 * uint32 * uint32 * uint32 * uint32)
let felem_wide5 = (uint64 * uint64 * uint64 * uint64 * uint64)

let scale32 = s:nat{s <= 64}
let scale64 = s:nat{s <= 4096}
let nat5 = (nat * nat * nat * nat * nat)

let scale32_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in
		       x1 <= 64 /\ x2 <= 64 /\ x3 <= 64 /\ x4 <= 64 /\ x5 <= 64}
let scale64_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in
		       x1 <= 4096 /\ x2 <= 4096 /\ x3 <= 4096 /\ x4 <= 4096 /\ x5 <= 4096}

open FStar.Mul

// let ( <=* ) (x:nat5) (y:nat5) : Type =
//   let (x1,x2,x3,x4,x5) = x in
//   let (y1,y2,y3,y4,y5) = y in
//   (x1 <= y1) /\
//   (x2 <= y2) /\
//   (x3 <= y3) /\
//   (x4 <= y4) /\
//   (x5 <= y5)

// let ( +* ) (x:nat5) (y:nat5) : nat5 =
//   let (x1,x2,x3,x4,x5) = x in
//   let (y1,y2,y3,y4,y5) = y in
//   (x1 + y1 ,
//    x2 + y2 ,
//    x3 + y3 ,
//    x4 + y4 ,
//    x5 + y5)

// let ( ** ) (x:nat5) (y:nat5) : nat5 =
//   let (x1,x2,x3,x4,x5) = x in
//   let (y1,y2,y3,y4,y5) = y in
//   (x1 * y1 ,
//    x2 * y2 ,
//    x3 * y3 ,
//    x4 * y4 ,
//    x5 * y5)

// #set-options "--z3rlimit 100"

// let ( *^ ) (x:scale32) (y:scale32_5) : scale64_5 =
//   assert_norm (64 * 64 = 4096);
//   let (y1,y2,y3,y4,y5) = y in
//   (x * y1 ,
//    x * y2 ,
//    x * y3 ,
//    x * y4 ,
//    x * y5)

assume val pow26: nat
inline_for_extraction
let max26 = pow26 - 1

assume val lemma_pow_32_26: _:unit{pow2 32 == 64 * pow26}
assume val lemma_pow_64_26: _:unit{pow2 64 == 4096 * pow26 * pow26}

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

let feval (f:felem5) : GTot pfelem = (as_nat5 f) % prime
let feval_wide (f:felem_wide5) : GTot pfelem = (wide_as_nat5 f) % prime

(* the impl *)

let felem = lbuffer uint32 5ul
let felem_wide = lbuffer uint64 5ul
let precomp_r = lbuffer uint32 10ul

noextract
val felem_fits: h:mem -> f:felem -> m:scale32_5 -> Type0
let felem_fits h f m =
  let s = as_seq h f in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  felem_fits5 (s0, s1, s2, s3, s4) m

noextract
val felem_wide_fits: h:mem -> f:felem_wide -> m:scale64_5 -> Type0
let felem_wide_fits h f m =
  let s = as_seq h f in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  felem_wide_fits5 (s0, s1, s2, s3, s4) m

noextract
val as_nat: h:mem -> e:felem -> GTot nat
let as_nat h e =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  as_nat5 (s0, s1, s2, s3, s4)

noextract
val wide_as_nat: h:mem -> e:felem_wide -> GTot nat
let wide_as_nat h e =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  wide_as_nat5 (s0,s1,s2,s3,s4)

noextract
val fevalh: h:mem -> f:felem -> GTot pfelem
let fevalh h f = (as_nat h f) % prime

noextract
val feval_wideh: h:mem -> f:felem_wide -> GTot pfelem
let feval_wideh h f = (wide_as_nat h f) % prime

inline_for_extraction
val fadd5:
    f1:felem5{felem_fits5 f1 (1, 2, 1, 1, 1)}
  -> f2:felem5{felem_fits5 f2 (1, 1, 1, 1, 1)}
  -> out:felem5{felem_fits5 f2 (2, 3, 2, 2, 2) /\
      feval out == pfadd (feval f1) (feval f2)}
let fadd5 (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24) =
  [@inline_let]
  let o0 = f10 +! f20 in
  [@inline_let]
  let o1 = f11 +! f21 in
  [@inline_let]
  let o2 = f12 +! f22 in
  [@inline_let]
  let o3 = f13 +! f23 in
  [@inline_let]
  let o4 = f14 +! f24 in
  FStar.Math.Lemmas.lemma_mod_plus_distr_l
    (as_nat5 (f10, f11, f12, f13, f14)) (as_nat5 (f20, f21, f22, f23, f24)) prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
    ((as_nat5 (f10, f11, f12, f13, f14)) % prime) (as_nat5 (f20, f21, f22, f23, f24)) prime;
  (o0, o1, o2, o3, o4)

[@CInline]
val fadd:
    out:felem
  -> f1:felem
  -> f2:felem
  -> Stack unit
    (requires fun h ->
      live h f1 /\ live h f2 /\ live h out /\
      felem_fits h f1 (1, 2, 1, 1, 1) /\
      felem_fits h f2 (1, 1, 1, 1, 1))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      felem_fits h1 out (2, 3, 2, 2, 2) /\
      fevalh h1 out == pfadd (fevalh h0 f1) (fevalh h0 f2))
let fadd out f1 f2 =
  let h0 = ST.get () in
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
  out.(0ul) <- f10 +! f20;
  out.(1ul) <- f11 +! f21;
  out.(2ul) <- f12 +! f22;
  out.(3ul) <- f13 +! f23;
  out.(4ul) <- f14 +! f24;
  let h1 = ST.get () in
  assert (as_nat h1 out == as_nat h0 f1 + as_nat h0 f2);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l
    (as_nat h0 f1) (as_nat h0 f2) prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
    (as_nat h0 f1 % prime) (as_nat h0 f2) prime
