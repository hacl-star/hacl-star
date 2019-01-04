module Poly1305.Field64xN

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.IntVector
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

let lanes = w:width{w == 1 \/ w == 2 \/ w == 4}
let uint64xN (w:lanes) = vec_t U64 w

let felem5 (w:lanes) = (uint64xN w * uint64xN w * uint64xN w * uint64xN w * uint64xN w)
let felem_wide5 (w:lanes) = felem5 w

let scale32 = s:nat{s <= 64}
let scale64 = s:nat{s <= 4096}
let nat5 = (nat * nat * nat * nat * nat)

let scale32_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in
		       x1 <= 64 /\ x2 <= 64 /\ x3 <= 64 /\ x4 <= 64 /\ x5 <= 64}
let scale64_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in
		       x1 <= 4096 /\ x2 <= 4096 /\ x3 <= 4096 /\ x4 <= 4096 /\ x5 <= 4096}

open FStar.Mul

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

(*
noextract
val as_nat5: #w:lanes -> f:felem5 w -> GTot (lseq nat w)
let as_nat5 #w f =
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
*)

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

(*
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
*)


inline_for_extraction
val fadd5_:
    #w:lanes 
  -> f1:felem5 w{felem_fits5 f1 (1, 2, 1, 1, 1)}
  -> f2:felem5 w{felem_fits5 f2 (1, 1, 1, 1, 1)}
  -> out:felem5 w{felem_fits5 out (2, 3, 2, 2, 2)} 
  (* /\ 
      feval out == pfadd (feval f1) (feval f2)} *)
let fadd5_ #w (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24) =
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


let tup64_5 = (uint64 & uint64 & uint64 & uint64 & uint64)
noextract
val as_nat5: f:tup64_5 -> nat
let as_nat5  f =
  let (s0,s1,s2,s3,s4) = f in
  uint_v s0 + (uint_v s1 * pow26) + (uint_v s2 * pow26 * pow26) +
    (uint_v s3 * pow26 * pow26 * pow26) + (uint_v s4 * pow26 * pow26 * pow26 * pow26)

let as_pfelem5 (f:tup64_5) : pfelem = 
  (as_nat5 f) % prime
  
let transpose (#w:lanes) (f:felem5 w) : lseq tup64_5 w =
  let (f0,f1,f2,f3,f4) = f in
  let v0 = vec_v f0 in
  let v1 = vec_v f1 in
  let v2 = vec_v f2 in
  let v3 = vec_v f3 in
  let v4 = vec_v f4 in
  createi #tup64_5 w (fun i -> (v0.[i],v1.[i],v2.[i],v3.[i],v4.[i]))
  
let feval5 (#w:lanes) (f:felem5 w) : lseq pfelem w =
  map as_pfelem5 (transpose f)

let feval (#w:lanes) (h:mem) (f:felem w) : GTot (lseq pfelem w) = 
  feval5 (as_tup5 h f)
  
inline_for_extraction
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

val fadd5_fits_lemma :
    #w:lanes 
  -> f1:felem5 w
  -> f2:felem5 w
  -> Lemma (requires (felem_fits5 f1 (1,2,1,1,1) /\ felem_fits5 f2 (1,1,1,1,1)))
	  (ensures (felem_fits5 (fadd5 f1 f2) (2,3,2,2,2)))
	  [SMTPat (fadd5 f1 f2)]
let fadd5_fits_lemma #w f1 f2 = ()

val fadd5_eval_lemma :
    #w:lanes 
  -> f1:felem5 w
  -> f2:felem5 w
  -> Lemma (requires (felem_fits5 f1 (1,2,1,1,1) /\ felem_fits5 f2 (1,1,1,1,1)))
	  (ensures (feval5 (fadd5 f1 f2) == map2 pfadd (feval5 f1) (feval5 f2)))
	  [SMTPat (fadd5 f1 f2)]
let fadd5_eval_lemma #w f1 f2 = 
    assert(Seq.equal (feval5 (fadd5 f1 f2)) (map2 pfadd (feval5 f1) (feval5 f2)))

[@CInline]
val fadd:
    #w:lanes
  -> out:felem w
  -> f1:felem w
  -> f2:felem w
  -> Stack unit
    (requires fun h ->
      live h f1 /\ live h f2 /\ live h out)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      as_tup5 h1 out == fadd5 (as_tup5 h0 f1) (as_tup5 h0 f2))
let fadd #w out f1 f2 =
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
  let (o0,o1,o2,o3,o4) = fadd5 (f10,f11,f12,f13,f14) (f20,f21,f22,f23,f24) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  out.(4ul) <- o4;
  ()
