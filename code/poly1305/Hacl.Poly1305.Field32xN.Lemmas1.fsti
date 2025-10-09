module Hacl.Poly1305.Field32xN.Lemmas1

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence
open FStar.Mul

open Hacl.Spec.Poly1305.Vec
include Hacl.Spec.Poly1305.Field32xN

noextract
let carry26_wide_zero (#w:lanes) (l : uint64xN w) : uint64xN w & uint64xN w =
  (vec_and l (mask26 w), vec_shift_right l 26ul)

val carry26_wide_zero_eq: #w:lanes -> f:uint64xN w -> Lemma
  (carry26_wide_zero f == carry26_wide f (zero w))

val vec_smul_mod_five_i: #w:lanes -> f:uint64xN w{uint64xN_fits f (4096 * max26)} -> i:nat{i < w} -> Lemma
  (u64 5 *. (vec_v f).[i] == (vec_v f).[i] +. ((vec_v f).[i] <<. 2ul))

val vec_smul_mod_five: #w:lanes -> f:uint64xN w{uint64xN_fits f (4096 * max26)} -> Lemma
  (vec_smul_mod f (u64 5) == vec_add_mod f (vec_shift_left f 2ul))

noextract
let carry_wide_felem5_compact (#w:lanes) (inp:felem_wide5 w) : felem5 w =
  let (x0, x1, x2, x3, x4) = inp in
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

val carry26_wide_fits_lemma:
    #w:lanes
  -> #m:scale64
  -> l:uint64xN w{felem_wide_fits1 l m}
  -> cin:uint64xN w{uint64xN_fits cin (4096 * max26)} ->
  Lemma
  (let (l0, l1) = carry26 #w l cin in
  felem_fits1 l0 1 /\ uint64xN_fits l1 ((m + 1) * max26))

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


val carry26_fits_lemma:
    #w:lanes
  -> m:scale64
  -> ml:scale32
  -> l:uint64xN w{felem_fits1 l ml}
  -> cin:uint64xN w{uint64xN_fits cin (m * max26)} ->
  Lemma
  (let (l0, l1) = carry26 #w l cin in
   felem_fits1 l0 1 /\ uint64xN_fits l1 (m + ml))

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

val carry_wide_felem5_fits_lemma:
    #w:lanes
  -> inp:felem_wide5 w ->
  Lemma
  (requires felem_wide_fits5 inp (126, 102, 78, 54, 30))
  (ensures  felem_fits5 (carry_wide_felem5 inp) (1, 2, 1, 1, 2))

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

val carry_wide_felem5_eval_lemma_i:
    #w:lanes
  -> inp:felem_wide5 w{felem_wide_fits5 inp (126, 102, 78, 54, 30)}
  -> i:nat{i < w} ->
  Lemma ((feval5 (carry_wide_felem5 #w inp)).[i] == (feval5 inp).[i])

val carry_wide_felem5_eval_lemma:
    #w:lanes
  -> inp:felem_wide5 w
  -> Lemma
    (requires felem_wide_fits5 inp (126, 102, 78, 54, 30))
    (ensures feval5 (carry_wide_felem5 #w inp) == feval5 inp)

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

#push-options "--z3rlimit 50"
#restart-solver
noextract
let subtract_p5_s
    (#w:lanes)
    (f:felem5 w{felem_fits5 f (1, 1, 1, 1, 1)})
    (i:nat{i < w})
: Pure tup64_5
  (requires True)
  (ensures  fun out ->
    tup64_fits5 out (1, 1, 1, 1, 1) /\
    as_nat5 out == as_nat5 (as_tup64_i f i) % prime)
=
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
  let out = (f0', f1', f2', f3', f4') in
  assert (as_nat5 out == as_nat5 (as_tup64_i f i) % prime);
  assert (tup64_fits5 out (1, 1, 1, 1, 1));
  // ^ This seems needed to trigger the SMT, why?
  out
#pop-options

val subtract_p5_felem5_lemma_i:
    #w:lanes
  -> f:felem5 w{felem_fits5 f (1, 1, 1, 1, 1)}
  -> i:nat{i < w} ->
  Lemma
  (tup64_fits5 (as_tup64_i (subtract_p5 #w f) i) (1, 1, 1, 1, 1) /\
   as_nat5 (as_tup64_i (subtract_p5 #w f) i) == as_nat5 (as_tup64_i f i) % prime)

val subtract_p5_felem5_lemma:
    #w:lanes
  -> f:felem5 w{felem_fits5 f (1, 1, 1, 1, 1)} ->
  Lemma
  (felem_fits5 (subtract_p5 f) (1, 1, 1, 1, 1) /\
  (fas_nat5 (subtract_p5 f)).[0] == (feval5 f).[0])

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

val acc_inv_lemma:
    #w:lanes
  -> acc:felem5 w{felem_fits5 acc (1, 1, 1, 1, 1)}
  -> cin:uint64xN w{uint64xN_fits cin 45} ->
  Lemma
  (let (i0, i1, i2, i3, i4) = acc in
   let i0' = vec_add_mod i0 cin in
   acc_inv_t (i0', i1, i2, i3, i4))

val carry_full_felem5_fits_lemma0: #w:lanes -> f:felem5 w{felem_fits5 f (8, 8, 8, 8, 8)} ->
  Lemma (let (f0, f1, f2, f3, f4) = f in
    let tmp0,c0 = carry26 f0 (zero w) in
    let tmp1,c1 = carry26 f1 c0 in
    let tmp2,c2 = carry26 f2 c1 in
    let tmp3,c3 = carry26 f3 c2 in
    let tmp4,c4 = carry26 f4 c3 in
    felem_fits5 (tmp0, tmp1, tmp2, tmp3, tmp4) (1, 1, 1, 1, 1) /\ uint64xN_fits c4 9)

val carry_full_felem5_fits_lemma: #w:lanes -> f:felem5 w{felem_fits5 f (8, 8, 8, 8, 8)} ->
  Lemma (acc_inv_t (carry_full_felem5 f))

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

val carry_full_felem5_eval_lemma_i:
    #w:lanes
  -> inp:felem_wide5 w{felem_fits5 inp (8, 8, 8, 8, 8)}
  -> i:nat{i < w} ->
  Lemma ((feval5 (carry_full_felem5 #w inp)).[i] == (feval5 inp).[i])

val carry_full_felem5_eval_lemma:
    #w:lanes
  -> inp:felem_wide5 w
  -> Lemma
    (requires felem_fits5 inp (8, 8, 8, 8, 8))
    (ensures  feval5 (carry_full_felem5 #w inp) == feval5 inp)

val carry_full_felem5_lemma:
    #w:lanes
  -> f:felem5 w{felem_fits5 f (8, 8, 8, 8, 8)} ->
  Lemma
  (felem_fits5 (carry_full_felem5 f) (2, 1, 1, 1, 1) /\
   feval5 (carry_full_felem5 f) == feval5 f)

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
   (if (uint64xN_v f0).[i] < pow2 26 then (uint64xN_v c4).[i] = 0 else (uint64xN_v c4).[i] <= 63))

val carry_reduce_felem5_fits_lemma_i1:
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
   (uint64xN_v c4).[i] <= 63 /\
   tup64_fits5 (as_tup64_i res i) (1, 1, 1, 1, 1))

val carry_reduce_felem5_fits_lemma_i:
    #w:lanes
  -> f:felem5 w{acc_inv_t f}
  -> i:nat{i < w} ->
  Lemma (tup64_fits5 (as_tup64_i (carry_full_felem5 f) i) (1, 1, 1, 1, 1))

val carry_reduce_felem5_fits_lemma:
    #w:lanes
  -> f:felem5 w{acc_inv_t f} ->
  Lemma (felem_fits5 (carry_full_felem5 f) (1, 1, 1, 1, 1))

val carry_reduce_felem5_lemma:
    #w:lanes
  -> f:felem5 w{acc_inv_t f} ->
  Lemma
  (felem_fits5 (carry_full_felem5 f) (1, 1, 1, 1, 1) /\
   feval5 (carry_full_felem5 f) == feval5 f)
