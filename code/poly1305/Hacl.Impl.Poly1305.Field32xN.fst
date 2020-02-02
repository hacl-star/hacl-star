module Hacl.Impl.Poly1305.Field32xN

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.IntVector

include Hacl.Spec.Poly1305.Field32xN
open Hacl.Spec.Poly1305.Field32xN.Lemmas
open Hacl.Impl.Poly1305.Lemmas

module Vec = Hacl.Spec.Poly1305.Vec
module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50 --using_facts_from '* -FStar.Seq'"

inline_for_extraction noextract
let felem (w:lanes) = lbuffer (uint64xN w) 5ul
inline_for_extraction noextract
let felem_wide (w:lanes) = felem w
inline_for_extraction noextract
let precomp_r (w:lanes) = lbuffer (uint64xN w) 20ul

unfold noextract
let op_String_Access #a #len = LSeq.index #a #len

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

noextract
let feval (#w:lanes) (h:mem) (f:felem w) : GTot (LSeq.lseq Vec.pfelem w) =
  feval5 (as_tup5 h f)

noextract
let fas_nat (#w:lanes) (h:mem) (f:felem w) : GTot (LSeq.lseq nat w) =
  fas_nat5 (as_tup5 h f)

noextract
let felem_less (#w:lanes) (h:mem) (f:felem w) (max:nat) : Type0 =
  felem_less5 (as_tup5 h f) max

val lemma_feval_is_fas_nat:
    #w:lanes
  -> h:mem
  -> f:felem w
  -> Lemma
    (requires felem_less h f (pow2 128))
    (ensures  (forall (i:nat). i < w ==> (feval h f).[i] == (fas_nat h f).[i]))
let lemma_feval_is_fas_nat #w h f =
  lemma_feval_is_fas_nat (as_tup5 h f)

val fmul_precomp_r_pre:
    #w:lanes
  -> h:mem
  -> precomp:precomp_r w
  -> Type0
let fmul_precomp_r_pre #w h precomp =
  let r = gsub precomp 0ul 5ul in
  let r_5 = gsub precomp 5ul 5ul in
  felem_fits h r (1, 1, 1, 1, 1) /\
  felem_fits h r_5 (5, 5, 5, 5, 5) /\
  as_tup5 h r_5 == precomp_r5 (as_tup5 h r)

noextract
val load_precompute_r_post:
    #w:lanes
  -> h:mem
  -> p:precomp_r w
  -> Type0
let load_precompute_r_post #w h p =
  assert_norm (pow2 128 < Vec.prime);
  let r = gsub p 0ul 5ul in
  let rn = gsub p 10ul 5ul in
  let rn_5 = gsub p 15ul 5ul in
  fmul_precomp_r_pre h p /\
  felem_fits h rn (2, 2, 2, 2, 2) /\
  felem_fits h rn_5 (10, 10, 10, 10, 10) /\
  as_tup5 h rn_5 == precomp_r5 (as_tup5 h rn) /\
  feval h rn == Vec.compute_rw (feval h r).[0]

inline_for_extraction noextract
val create_felem:
    w:lanes
  -> StackInline (felem w)
    (requires fun h -> True)
    (ensures  fun h0 b h1 ->
      stack_allocated b h0 h1 (LSeq.create 5 (zero w)) /\
      feval h1 b == LSeq.create w 0)
let create_felem w =
  let r = create 5ul (zero w) in
  let h1 = ST.get () in
  LSeq.eq_intro (feval h1 r) (LSeq.create w 0);
  r

#push-options "--z3rlimit 100"
inline_for_extraction noextract
val set_bit:
    #w:lanes
  -> f:felem w
  -> i:size_t{size_v i <= 128}
  -> Stack unit
    (requires fun h ->
      live h f /\
      felem_fits h f (1, 1, 1, 1, 1) /\
      felem_less #w h f (pow2 (v i)))
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      felem_fits h1 f (1, 1, 1, 1, 1) /\
     (Math.Lemmas.pow2_le_compat 128 (v i);
      feval h1 f == LSeq.map (Vec.pfadd (pow2 (v i))) (feval h0 f)))
let set_bit #w f i =
  let b = u64 1 <<. (i %. 26ul) in
  let mask = vec_load b w in
  let fi = f.(i /. 26ul) in
  let h0 = ST.get () in
  f.(i /. 26ul) <- vec_or fi mask;
  set_bit5_lemma (as_seq h0 f) (v i)
#pop-options

inline_for_extraction noextract
val set_bit128:
    #w:lanes
  -> f:felem w
  -> Stack unit
    (requires fun h ->
      live h f /\
      felem_fits h f (1, 1, 1, 1, 1) /\
      felem_less #w h f (pow2 128))
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      felem_fits h1 f (1, 1, 1, 1, 1) /\
      feval h1 f == LSeq.map (Vec.pfadd (pow2 128)) (feval h0 f))
let set_bit128 #w f =
  let b = u64 0x1000000 in
  assert_norm (0x1000000 = pow2 24);
  assert (v b == v (u64 1 <<. 24ul));
  let mask = vec_load b w in
  let f4 = f.(4ul) in
  let h0 = ST.get () in
  f.(4ul) <- vec_or f4 mask;
  set_bit5_lemma (as_seq h0 f) 128

inline_for_extraction noextract
val set_zero:
    #w:lanes
  -> f:felem w
  -> Stack unit
    (requires fun h -> live h f)
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      felem_fits h1 f (0, 0, 0, 0, 0) /\
      feval h1 f == LSeq.create w 0)
let set_zero #w f =
  f.(0ul) <- zero w;
  f.(1ul) <- zero w;
  f.(2ul) <- zero w;
  f.(3ul) <- zero w;
  f.(4ul) <- zero w;
  let h1 = ST.get () in
  LSeq.eq_intro (feval h1 f) (LSeq.create w 0)

inline_for_extraction noextract
val copy_felem:
    #w:lanes
  -> #m:scale32_5
  -> f1:felem w
  -> f2:felem w
  -> Stack unit
    (requires fun h ->
      live h f1 /\ live h f2 /\ disjoint f1 f2 /\
      felem_fits h f2 m)
    (ensures  fun h0 _ h1 ->
      modifies (loc f1) h0 h1 /\
      felem_fits h1 f1 m /\
      as_tup5 h1 f1 == as_tup5 h0 f2)
let copy_felem #w #m f1 f2 =
  f1.(0ul) <- f2.(0ul);
  f1.(1ul) <- f2.(1ul);
  f1.(2ul) <- f2.(2ul);
  f1.(3ul) <- f2.(3ul);
  f1.(4ul) <- f2.(4ul)

inline_for_extraction noextract
val fadd:
    #w:lanes
  -> out:felem w
  -> f1:felem w
  -> f2:felem w
  -> Stack unit
    (requires fun h ->
      live h f1 /\ live h f2 /\ live h out /\
      felem_fits h f1 (2,2,2,2,2) /\
      felem_fits h f2 (1,1,1,1,1))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      //as_tup5 h1 out == fadd5 (as_tup5 h0 f1) (as_tup5 h0 f2) /\
      felem_fits h1 out (3,3,3,3,3) /\
      feval h1 out == LSeq.map2 Vec.pfadd (feval h0 f1) (feval h0 f2))
let fadd #w out f1 f2 =
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
    fadd5 #w (f10,f11,f12,f13,f14) (f20,f21,f22,f23,f24) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  out.(4ul) <- o4

#push-options "--max_fuel 1"

inline_for_extraction noextract
val fmul_r:
    #w:lanes
  -> out:felem w
  -> f1:felem w
  -> r:felem w
  -> r5:felem w
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\
      live h r /\ live h r5 /\
      felem_fits h f1 (3,3,3,3,3) /\
      felem_fits h r (2,2,2,2,2) /\
      felem_fits h r5 (10,10,10,10,10) /\
      as_tup5 h r5 == precomp_r5 (as_tup5 h r))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      felem_fits h1 out (1,2,1,1,2) /\
      feval h1 out == LSeq.map2 (Vec.pfmul) (feval h0 f1) (feval h0 r))
let fmul_r #w out f1 r r5 =
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
    fmul_r5 #w (f10, f11, f12, f13, f14)
      (r0, r1, r2, r3, r4) (r50, r51, r52, r53, r54) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  out.(4ul) <- o4

#pop-options

inline_for_extraction noextract
val fadd_mul_r:
    #w:lanes
  -> acc:felem w
  -> f1:felem w
  -> p:precomp_r w
  -> Stack unit
    (requires fun h ->
      live h acc /\ live h f1 /\ live h p /\
      felem_fits h acc (2,2,2,2,2) /\
      felem_fits h f1 (1,1,1,1,1) /\
      fmul_precomp_r_pre h p)
    (ensures  fun h0 _ h1 ->
      modifies (loc acc) h0 h1 /\
      felem_fits h1 acc (1,2,1,1,2) /\
      feval h1 acc == LSeq.map2 (Vec.pfmul)
        (LSeq.map2 (Vec.pfadd) (feval h0 acc) (feval h0 f1)) (feval h0 (gsub p 0ul 5ul)))
let fadd_mul_r #w out f1 p =
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
    fadd_mul_r5 #w (a0, a1, a2, a3, a4) (f10, f11, f12, f13, f14)
      (r0, r1, r2, r3, r4) (r50, r51, r52, r53, r54) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  out.(4ul) <- o4

inline_for_extraction noextract
val fmul_rn:
    #w:lanes
  -> out:felem w
  -> f1:felem w
  -> p:precomp_r w
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\ live h p /\
     (let rn = gsub p 10ul 5ul in
      let rn_5 = gsub p 15ul 5ul in
      felem_fits h f1 (3,3,3,3,3) /\
      felem_fits h rn (2,2,2,2,2) /\
      felem_fits h rn_5 (10,10,10,10,10) /\
      as_tup5 h rn_5 == precomp_r5 (as_tup5 h rn)))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      felem_fits h1 out (1,2,1,1,2) /\
      feval h1 out == LSeq.map2 Vec.pfmul (feval h0 f1) (feval h0 (gsub p 10ul 5ul)))
let fmul_rn #w out f1 p =
  let rn = sub p 10ul 5ul in
  let rn5 = sub p 15ul 5ul in
  fmul_r #w out f1 rn rn5

inline_for_extraction noextract
val reduce_felem:
    #w:lanes
  -> f:felem w
  -> Stack unit
    (requires fun h ->
      live h f /\ felem_fits h f (2,2,2,2,2))
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      felem_fits h1 f (1, 1, 1, 1, 1) /\
      (fas_nat h1 f).[0] == (feval h0 f).[0])
let reduce_felem #w f =
  let f0 = f.(0ul) in
  let f1 = f.(1ul) in
  let f2 = f.(2ul) in
  let f3 = f.(3ul) in
  let f4 = f.(4ul) in
  let (f0, f1, f2, f3, f4) =
    reduce_felem5 (f0, f1, f2, f3, f4) in
  f.(0ul) <- f0;
  f.(1ul) <- f1;
  f.(2ul) <- f2;
  f.(3ul) <- f3;
  f.(4ul) <- f4

inline_for_extraction noextract
val precompute_shift_reduce:
    #w:lanes
  -> f1:felem w
  -> f2:felem w
  -> Stack unit
    (requires fun h -> live h f1 /\ live h f2)
    (ensures  fun h0 _ h1 ->
      modifies (loc f1) h0 h1 /\
      as_tup5 h1 f1 == precomp_r5 (as_tup5 h0 f2))
let precompute_shift_reduce #w f1 f2 =
  let f20 = f2.(0ul) in
  let f21 = f2.(1ul) in
  let f22 = f2.(2ul) in
  let f23 = f2.(3ul) in
  let f24 = f2.(4ul) in
  f1.(0ul) <- vec_smul_mod f20 (u64 5);
  f1.(1ul) <- vec_smul_mod f21 (u64 5);
  f1.(2ul) <- vec_smul_mod f22 (u64 5);
  f1.(3ul) <- vec_smul_mod f23 (u64 5);
  f1.(4ul) <- vec_smul_mod f24 (u64 5)

inline_for_extraction noextract
val load_felem:
    #w:lanes
  -> f:felem w
  -> lo:uint64xN w
  -> hi:uint64xN w
  -> Stack unit
    (requires fun h -> live h f)
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      felem_fits h1 f (1, 1, 1, 1, 1) /\
      felem_less h1 f (pow2 128) /\
      feval h1 f == LSeq.createi #Vec.pfelem w
	(fun i -> (uint64xN_v hi).[i] * pow2 64 + (uint64xN_v lo).[i]))
let load_felem #w f lo hi =
  let (f0, f1, f2, f3, f4) = load_felem5 #w lo hi in
  load_felem5_lemma #w lo hi;
  f.(0ul) <- f0;
  f.(1ul) <- f1;
  f.(2ul) <- f2;
  f.(3ul) <- f3;
  f.(4ul) <- f4

#push-options "--max_fuel 2"

inline_for_extraction noextract
val load_precompute_r1:
    p:precomp_r 1
  -> r0:uint64
  -> r1:uint64
  -> Stack unit
    (requires fun h -> live h p)
    (ensures  fun h0 _ h1 ->
      modifies (loc p) h0 h1 /\
      load_precompute_r_post h1 p /\
     (assert_norm (pow2 64 * pow2 64 = pow2 128);
      feval h1 (gsub p 0ul 5ul) ==
        LSeq.create 1 (uint_v r1 * pow2 64 + uint_v r0)))
let load_precompute_r1 p r0 r1 =
  let r = sub p 0ul 5ul in
  let r5 = sub p 5ul 5ul in
  let rn = sub p 10ul 5ul in
  let rn_5 = sub p 15ul 5ul in

  let r_vec0 = vec_load r0 1 in
  let r_vec1 = vec_load r1 1 in

  let h0 = ST.get () in
  load_felem r r_vec0 r_vec1;
  let h1 = ST.get () in
  LSeq.eq_intro
    (LSeq.createi #Vec.pfelem 1 (fun i -> (uint64xN_v r_vec1).[i] * pow2 64 + (uint64xN_v r_vec0).[i]))
    (LSeq.create 1 (uint_v r1 * pow2 64 + uint_v r0));
  assert (feval h1 r == LSeq.create 1 (uint_v r1 * pow2 64 + uint_v r0));
  precompute_shift_reduce r5 r;

  copy_felem #_ #(1,1,1,1,1) rn r;
  copy_felem #_ #(5,5,5,5,5) rn_5 r5

inline_for_extraction noextract
val load_precompute_r2:
    p:precomp_r 2
  -> r0:uint64
  -> r1:uint64
  -> Stack unit
    (requires fun h -> live h p)
    (ensures  fun h0 _ h1 ->
      modifies (loc p) h0 h1 /\
      load_precompute_r_post h1 p /\
     (assert_norm (pow2 64 * pow2 64 = pow2 128);
      feval h1 (gsub p 0ul 5ul) ==
        LSeq.create 2 (uint_v r1 * pow2 64 + uint_v r0)))
let load_precompute_r2 p r0 r1 =
  let r = sub p 0ul 5ul in
  let r5 = sub p 5ul 5ul in
  let rn = sub p 10ul 5ul in
  let rn_5 = sub p 15ul 5ul in

  let r_vec0 = vec_load r0 2 in
  let r_vec1 = vec_load r1 2 in

  let h0 = ST.get () in
  load_felem r r_vec0 r_vec1;
  let h1 = ST.get () in
  LSeq.eq_intro
    (LSeq.createi #Vec.pfelem 2 (fun i -> (uint64xN_v r_vec1).[i] * pow2 64 + (uint64xN_v r_vec0).[i]))
    (LSeq.create 2 (uint_v r1 * pow2 64 + uint_v r0));
  assert (feval h1 r == LSeq.create 2 (uint_v r1 * pow2 64 + uint_v r0));

  precompute_shift_reduce r5 r;
  let h2 = ST.get () in
  fmul_r rn r r r5;
  let h3 = ST.get () in
  LSeq.eq_intro (feval h3 rn) (Vec.compute_rw (feval h2 r).[0]);
  precompute_shift_reduce rn_5 rn

inline_for_extraction noextract
val load_precompute_r4:
    p:precomp_r 4
  -> r0:uint64
  -> r1:uint64
  -> Stack unit
    (requires fun h -> live h p)
    (ensures  fun h0 _ h1 ->
      modifies (loc p) h0 h1 /\
      load_precompute_r_post h1 p /\
     (assert_norm (pow2 64 * pow2 64 = pow2 128);
      feval h1 (gsub p 0ul 5ul) ==
        LSeq.create 4 (uint_v r1 * pow2 64 + uint_v r0)))
let load_precompute_r4 p r0 r1 =
  let r = sub p 0ul 5ul in
  let r5 = sub p 5ul 5ul in
  let rn = sub p 10ul 5ul in
  let rn_5 = sub p 15ul 5ul in

  let r_vec0 = vec_load r0 4 in
  let r_vec1 = vec_load r1 4 in

  let h0 = ST.get () in
  load_felem r r_vec0 r_vec1;
  let h1 = ST.get () in
  LSeq.eq_intro
    (LSeq.createi #Vec.pfelem 4 (fun i -> (uint64xN_v r_vec1).[i] * pow2 64 + (uint64xN_v r_vec0).[i]))
    (LSeq.create 4 (uint_v r1 * pow2 64 + uint_v r0));
  assert (feval h1 r == LSeq.create 4 (uint_v r1 * pow2 64 + uint_v r0));

  precompute_shift_reduce r5 r;
  fmul_r rn r r r5;
  precompute_shift_reduce rn_5 rn;
  fmul_r rn rn rn rn_5;
  let h3 = ST.get () in
  LSeq.eq_intro (feval h3 rn) (Vec.compute_rw (feval h1 r).[0]);
  precompute_shift_reduce rn_5 rn

inline_for_extraction noextract
val load_precompute_r:
    #w:lanes
  -> p:precomp_r w
  -> r0:uint64
  -> r1:uint64
  -> Stack unit
    (requires fun h -> live h p)
    (ensures  fun h0 _ h1 ->
      modifies (loc p) h0 h1 /\
      load_precompute_r_post #w h1 p /\
      (assert_norm (pow2 64 * pow2 64 = pow2 128);
      feval h1 (gsub p 0ul 5ul) ==
        LSeq.create w (uint_v r1 * pow2 64 + uint_v r0)))
let load_precompute_r #w p r0 r1 =
  match w with
  | 1 -> load_precompute_r1 p r0 r1
  | 2 -> load_precompute_r2 p r0 r1
  | 4 -> load_precompute_r4 p r0 r1

#pop-options

inline_for_extraction noextract
val load_felem1_le:
    f:felem 1
  -> b:lbuffer uint8 16ul
  -> Stack unit
    (requires fun h -> live h f /\ live h b)
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      felem_fits h1 f (1, 1, 1, 1, 1) /\
      felem_less h1 f (pow2 128) /\
      feval h1 f == Vec.load_elem1 (as_seq h0 b))
let load_felem1_le f b =
  let h0 = ST.get () in
  let lo = vec_load_le U64 1 (sub b 0ul 8ul) in
  let hi = vec_load_le U64 1 (sub b 8ul 8ul) in

  load_felem f lo hi;
  let h1 = ST.get () in
  uints_from_bytes_le_lemma64_1 (as_seq h0 b);
  LSeq.eq_intro (feval h1 f) (Vec.load_elem1 (as_seq h0 b))

inline_for_extraction noextract
val load_felem2_le:
    f:felem 2
  -> b:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h -> live h f /\ live h b)
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      felem_fits h1 f (1, 1, 1, 1, 1) /\
      felem_less h1 f (pow2 128) /\
      feval h1 f == Vec.load_elem2 (as_seq h0 b))
let load_felem2_le f b =
  let h0 = ST.get () in
  let b1 = vec_load_le U64 2 (sub b 0ul 16ul) in
  let b2 = vec_load_le U64 2 (sub b 16ul 16ul) in
  let lo = vec_interleave_low b1 b2 in
  let hi = vec_interleave_high b1 b2 in
  load_felem f lo hi;
  let h1 = ST.get () in
  vec_interleave_low_lemma2 b1 b2;
  vec_interleave_high_lemma2 b1 b2;
  uints_from_bytes_le_lemma64_2 (as_seq h0 b);
  LSeq.eq_intro (feval h1 f) (Vec.load_elem2 (as_seq h0 b))

inline_for_extraction noextract
val load_felem4_le:
    f:felem 4
  -> b:lbuffer uint8 64ul
  -> Stack unit
    (requires fun h -> live h f /\ live h b)
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      felem_fits h1 f (1, 1, 1, 1, 1) /\
      felem_less h1 f (pow2 128) /\
      feval h1 f == Vec.load_elem4 (as_seq h0 b))
let load_felem4_le f b =
  let h0 = ST.get () in
  let lo = vec_load_le U64 4 (sub b 0ul 32ul) in
  let hi = vec_load_le U64 4 (sub b 32ul 32ul) in
  let (o0, o1, o2, o3, o4) = load_felem5_4 lo hi in
  load_felem5_le (as_seq h0 b);
  f.(0ul) <- o0;
  f.(1ul) <- o1;
  f.(2ul) <- o2;
  f.(3ul) <- o3;
  f.(4ul) <- o4


inline_for_extraction noextract
val load_felems_le:
    #w:lanes
  -> f:felem w
  -> b:lbuffer uint8 (size w *! 16ul)
  -> Stack unit
    (requires fun h -> live h f /\ live h b)
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      felem_fits h1 f (1, 1, 1, 1, 1) /\
      felem_less h1 f (pow2 128) /\
      feval h1 f == Vec.load_elem (as_seq h0 b))
let load_felems_le #w f b =
  match w with
  | 1 -> load_felem1_le f b
  | 2 -> load_felem2_le f b
  | 4 -> load_felem4_le f b

inline_for_extraction noextract
val load_blocks:
    #w:lanes
  -> f:felem w
  -> b:lbuffer uint8 (size w *! 16ul)
  -> Stack unit
    (requires fun h ->
      live h b /\ live h f /\ disjoint b f)
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      felem_fits h1 f (1, 1, 1, 1, 1) /\
      feval h1 f == Vec.load_blocks #w (as_seq h0 b))
let load_blocks #s f b =
  load_felems_le f b;
  set_bit128 f

inline_for_extraction noextract
val load_felem_le:
    #w:lanes
  -> f:felem w
  -> b:lbuffer uint8 16ul
  -> Stack unit
    (requires fun h -> live h f /\ live h b)
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      felem_fits h1 f (1, 1, 1, 1, 1) /\
      felem_less h1 f (pow2 128) /\
      feval h1 f == LSeq.create w (BSeq.nat_from_bytes_le (as_seq h0 b)))
let load_felem_le #w f b =
  let lo = uint_from_bytes_le #U64 (sub b 0ul 8ul) in
  let hi = uint_from_bytes_le #U64 (sub b 8ul 8ul) in
  let f0 = vec_load lo w in
  let f1 = vec_load hi w in
  let h0 = ST.get () in
  load_felem f f0 f1;
  let h1 = ST.get () in
  uint_from_bytes_le_lemma (as_seq h0 b);
  LSeq.eq_intro (feval h1 f) (LSeq.create w (BSeq.nat_from_bytes_le (as_seq h0 b)))

inline_for_extraction noextract
val uints64_from_bytes_le:
    b:lbuffer uint8 16ul
  -> Stack (uint64 & uint64)
    (requires fun h -> live h b)
    (ensures  fun h0 (lo, hi) h1 -> h0 == h1 /\
      v hi * pow2 64 + v lo == BSeq.nat_from_bytes_le (as_seq h0 b))
let uints64_from_bytes_le b =
  let h0 = ST.get () in
  let lo = uint_from_bytes_le #U64 (sub b 0ul 8ul) in
  let hi = uint_from_bytes_le #U64 (sub b 8ul 8ul) in
  uint_from_bytes_le_lemma (as_seq h0 b);
  lo, hi

inline_for_extraction noextract
val uints64_from_felem_le:
    #w:lanes
  -> f:felem w
  -> Stack (uint64 & uint64)
    (requires fun h ->
      live h f /\ felem_fits h f (1, 1, 1, 1, 1))
    (ensures  fun h0 (lo, hi) h1 -> h0 == h1 /\
      v hi * pow2 64 + v lo == (fas_nat h0 f).[0] % pow2 128)
let uints64_from_felem_le #w f =
  let (f0, f1, f2, f3, f4) = (f.(0ul), f.(1ul), f.(2ul), f.(3ul), f.(4ul)) in
  store_felem5 #w (f0, f1, f2, f3, f4)

inline_for_extraction noextract
val uints64_to_bytes_le:
    b:lbuffer uint8 16ul
  -> lo:uint64
  -> hi:uint64
  -> Stack unit
    (requires fun h -> live h b)
    (ensures  fun h0 _ h1 ->
      modifies (loc b) h0 h1 /\
      as_seq h1 b == BSeq.nat_to_bytes_le 16 (v hi * pow2 64 + v lo))
let uints64_to_bytes_le b r0 r1 =
  let h0 = ST.get () in
  update_sub_f h0 b 0ul 8ul
    (fun h -> BSeq.uint_to_bytes_le #U64 r0)
    (fun _ -> uint_to_bytes_le (sub b 0ul 8ul) r0);
  let h1 = ST.get () in
  update_sub_f h1 b 8ul 8ul
    (fun h -> BSeq.uint_to_bytes_le #U64 r1)
    (fun _ -> uint_to_bytes_le (sub b 8ul 8ul) r1);
  //uint_to_bytes_le (sub b 0ul 8ul) r0;
  //uint_to_bytes_le (sub b 8ul 8ul) r1;
  let h2 = ST.get () in
  uints64_to_bytes_le_lemma r0 r1;
  LSeq.eq_intro (LSeq.sub (as_seq h2 b) 0 8) (BSeq.uint_to_bytes_le #U64 r0);
  LSeq.lemma_concat2 8 (BSeq.uint_to_bytes_le #U64 r0) 8 (BSeq.uint_to_bytes_le #U64 r1) (as_seq h2 b)

inline_for_extraction noextract
val mod_add128:
    a:(uint64 & uint64)
  -> b:(uint64 & uint64)
  -> Pure (uint64 & uint64)
    (requires True)
    (ensures (fun (r0, r1) ->
      let (a0, a1) = a in let (b0, b1) = b in
      v r1 * pow2 64 + v r0 == ((v a1 + v b1) * pow2 64 + v a0 + v b0) % pow2 128))
let mod_add128 (a0, a1) (b0, b1) =
  mod_add128_lemma (a0, a1) (b0, b1);
  mod_add128 (a0, a1) (b0, b1)
