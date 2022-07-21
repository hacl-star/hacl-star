module Hacl.Impl.Curve25519.Finv

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Curve25519.Fields

module ST = FStar.HyperStack.ST
module C = Hacl.Impl.Curve25519.Fields.Core
module S = Hacl.Spec.Curve25519.Finv
module P = Spec.Curve25519

let _: squash (inversion field_spec) = allow_inversion field_spec

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0 --record_options"

noextract
val fsquare_times_inv: #s:field_spec -> h:mem -> f:felem s -> Type0
let fsquare_times_inv #s h f =
  match s with
  | M51 -> C.f51_felem_fits h f (1, 2, 1, 1, 1)
  | M64 -> True


val fsqr_s:
    #s:field_spec
  -> out:felem s
  -> f1:felem s
  -> tmp:felem_wide s
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\ live h tmp /\
      (disjoint out f1 \/ out == f1) /\
      (disjoint out tmp) /\
      disjoint tmp f1 /\
      fsquare_times_inv h f1)
    (ensures  fun h0 _ h1 ->
      modifies (loc out |+| loc tmp) h0 h1 /\
      fsquare_times_inv h1 out /\
      feval h1 out == P.fmul (feval h0 f1) (feval h0 f1))
[@ Meta.Attribute.inline_ ]
let fsqr_s #s out f1 tmp =
  C.fsqr #s out f1 tmp


noextract
val fmuls_pre: #s:field_spec -> h:mem -> f1:felem s -> f2:felem s -> Type0
let fmuls_pre #s h f1 f2 =
  match s with
  | M51 -> f51_felem_fits h f1 (1, 2, 1, 1, 1) /\ f51_felem_fits h f2 (1, 2, 1, 1, 1)
  | M64 -> True


val fmul_s:
    #s:field_spec
  -> out:felem s
  -> f1:felem s
  -> f2:felem s
  -> tmp:felem_wide2 s
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\ live h f2 /\ live h tmp /\
      (disjoint out f1 \/ out == f1) /\
      (disjoint out f2 \/ out == f2) /\
      (disjoint out tmp) /\
      (disjoint f1 f2 \/ f1 == f2) /\
      disjoint f1 tmp /\
      disjoint f2 tmp /\
      fmuls_pre h f1 f2)
    (ensures  fun h0 _ h1 ->
      modifies (loc out |+| loc tmp) h0 h1 /\ fsquare_times_inv h1 out /\
      feval h1 out == P.fmul (feval h0 f1) (feval h0 f2))
[@ Meta.Attribute.inline_ ]
let fmul_s #s out f1 f2 tmp =
  C.fmul #s out f1 f2 tmp


val fsquare_times:
    #s:field_spec
  -> o:felem s
  -> i:felem s
  -> tmp:felem_wide s
  -> n:size_t{v n > 0}
  -> Stack unit
    (requires fun h0 ->
      live h0 o /\ live h0 i /\ live h0 tmp /\
      (disjoint o i \/ o == i) /\
      disjoint o tmp /\
      disjoint tmp i /\
      fsquare_times_inv h0 i)
    (ensures  fun h0 _ h1 ->
      modifies (loc o |+| loc tmp) h0 h1 /\
      fsquare_times_inv h1 o /\
      feval h1 o == S.pow (feval #s h0 i) (pow2 (v n)))
[@ Meta.Attribute.specialize ]
let fsquare_times #s o inp tmp n =
  let h0 = ST.get() in
  fsqr_s #s o inp tmp;
  S.lemma_pow_one (feval h0 inp);
  S.lemma_pow_add (feval h0 inp) 1 1;
  assert_norm (pow2 1 = 2);

  let inv (h:mem) (i:nat{i < v n}) =
    modifies (loc o |+| loc tmp) h0 h /\
    fsquare_times_inv #s h o /\
    feval h o == S.pow (feval #s h0 inp) (pow2 (i + 1)) in

  let h1 = ST.get () in
  assert (inv h1 0);

  Lib.Loops.for 0ul (n -! 1ul) inv
  (fun i ->
    let h2 = ST.get () in
    fsqr_s #s o o tmp;
    S.lemma_pow_add (feval #s h0 inp) (pow2 (v i + 1)) (pow2 (v i + 1));
    Math.Lemmas.pow2_double_sum (v i + 1))


val finv1:
    #s:field_spec
  -> i:felem s
  -> t1:lbuffer (limb s) (4ul *! nlimb s)
  -> tmp:felem_wide2 s ->
  Stack unit
  (requires fun h0 ->
    live h0 i /\ live h0 t1 /\ live h0 tmp /\
    disjoint i t1 /\ disjoint i tmp /\ disjoint t1 tmp /\
    fsquare_times_inv h0 i)
  (ensures  fun h0 _ h1 ->
    modifies (loc t1 |+| loc tmp) h0 h1 /\
   (let as0 : felem s = gsub t1 0ul (nlimb s) in
    let bs : felem s = gsub t1 (nlimb s) (nlimb s) in
    let a = S.fsquare_times (feval h0 i) 1 in
    let t0 = S.fsquare_times a 2 in
    let b = P.fmul t0 (feval h0 i) in
    let a = P.fmul b a in
    let t0 = S.fsquare_times a 1 in
    let b = P.fmul t0 b in
    let t0 = S.fsquare_times b 5 in
    let b = P.fmul t0 b in
    feval h1 as0 == a /\ fsquare_times_inv h1 as0 /\
    feval h1 bs == b /\ fsquare_times_inv h1 bs))

[@ Meta.Attribute.inline_ ]
let finv1 #s i t1 tmp =
  let h0 = ST.get () in
  let a : felem s = sub t1 0ul (nlimb s) in
  let b : felem s = sub t1 (nlimb s) (nlimb s) in
  let c : felem s = sub t1 (2ul *! nlimb s) (nlimb s) in
  let t0 : felem s = sub t1 (3ul *! nlimb s) (nlimb s) in
  let tmp1 : felem_wide s = sub tmp 0ul (nwide s) in
  (* 2 *) fsquare_times #s a i tmp1 1ul;
  (* 8 *) fsquare_times #s t0 a tmp1 2ul;
  (* 9 *) fmul_s #s b t0 i tmp;
  (* 11 *) fmul_s #s a b a tmp;
  (* 22 *) fsquare_times #s t0 a tmp1 1ul;
  (* 2^5 - 2^0 = 31 *) fmul_s #s b t0 b tmp;
  (* 2^10 - 2^5 *) fsquare_times #s t0 b tmp1 5ul;
  (* 2^10 - 2^0 *) fmul_s #s b t0 b tmp


val finv2:
    #s:field_spec
  -> t1:lbuffer (limb s) (4ul *! nlimb s)
  -> tmp:felem_wide2 s ->
  Stack unit
  (requires fun h0 ->
    live h0 t1 /\ live h0 tmp /\ disjoint t1 tmp /\
   (let as0 : felem s = gsub t1 0ul (nlimb s) in
    let bs : felem s = gsub t1 (nlimb s) (nlimb s) in
    fsquare_times_inv h0 as0 /\ fsquare_times_inv h0 bs))
  (ensures  fun h0 _ h1 ->
    modifies (loc t1 |+| loc tmp) h0 h1 /\
   (let as0 : felem s = gsub t1 0ul (nlimb s) in
    let bs : felem s = gsub t1 (nlimb s) (nlimb s) in
    let cs : felem s = gsub t1 (2ul *! nlimb s) (nlimb s) in
    let t0 = S.fsquare_times (feval h0 bs) 10 in
    let c = P.fmul t0 (feval h0 bs) in
    let t0 = S.fsquare_times c 20 in
    let t0 = P.fmul t0 c in
    let t0 = S.fsquare_times t0 10 in
    let b = P.fmul t0 (feval h0 bs) in
    let t0 = S.fsquare_times b 50 in
    let c = P.fmul t0 b in
    feval h1 as0 == feval h0 as0 /\ fsquare_times_inv h1 as0 /\
    feval h1 bs == b /\ fsquare_times_inv h1 bs /\
    feval h1 cs == c /\ fsquare_times_inv h1 cs))

[@ Meta.Attribute.inline_ ]
let finv2 #s t1 tmp =
  let h0 = ST.get () in
  let a : felem s = sub t1 0ul (nlimb s) in
  let b : felem s = sub t1 (nlimb s) (nlimb s) in
  let c : felem s = sub t1 (2ul *! nlimb s) (nlimb s) in
  let t0 : felem s = sub t1 (3ul *! nlimb s) (nlimb s) in
  let tmp1 : felem_wide s = sub tmp 0ul (nwide s) in
  (* 2^20 - 2^10 *) fsquare_times #s t0 b tmp1 10ul;
  (* 2^20 - 2^0 *) fmul_s #s c t0 b tmp;
  (* 2^40 - 2^20 *) fsquare_times #s t0 c tmp1 20ul;
  (* 2^40 - 2^0 *) fmul_s #s t0 t0 c tmp;
  (* 2^50 - 2^10 *) fsquare_times #s t0 t0 tmp1 10ul;
  (* 2^50 - 2^0 *) fmul_s #s b t0 b tmp;
  (* 2^100 - 2^50 *) fsquare_times #s t0 b tmp1 50ul;
  (* 2^100 - 2^0 *) fmul_s #s c t0 b tmp


val finv3:
    #s:field_spec
  -> t1:lbuffer (limb s) (4ul *! nlimb s)
  -> tmp:felem_wide2 s ->
  Stack unit
  (requires fun h0 ->
    live h0 t1 /\ live h0 tmp /\ disjoint t1 tmp /\
   (let as0 : felem s = gsub t1 0ul (nlimb s) in
    let bs : felem s = gsub t1 (nlimb s) (nlimb s) in
    let cs : felem s = gsub t1 (2ul *! nlimb s) (nlimb s) in
    fsquare_times_inv h0 as0 /\ fsquare_times_inv h0 bs /\
    fsquare_times_inv h0 cs))
  (ensures  fun h0 _ h1 ->
    modifies (loc t1 |+| loc tmp) h0 h1 /\
   (let as0 : felem s = gsub t1 0ul (nlimb s) in
    let bs : felem s = gsub t1 (nlimb s) (nlimb s) in
    let cs : felem s = gsub t1 (2ul *! nlimb s) (nlimb s) in
    let ts0 : felem s = gsub t1 (3ul *! nlimb s) (nlimb s) in
    let t0 = S.fsquare_times (feval h0 cs) 100 in
    let t0 = P.fmul t0 (feval h0 cs) in
    let t0 = S.fsquare_times t0 50 in
    let t0 = P.fmul t0 (feval h0 bs) in
    let t0 = S.fsquare_times t0 5 in
    feval h1 as0 == feval h0 as0 /\ fsquare_times_inv h1 as0 /\
    feval h1 ts0 == t0 /\ fsquare_times_inv h1 ts0))

[@ Meta.Attribute.inline_ ]
let finv3 #s t1 tmp =
  let h0 = ST.get () in
  let a : felem s = sub t1 0ul (nlimb s) in
  let b : felem s = sub t1 (nlimb s) (nlimb s) in
  let c : felem s = sub t1 (2ul *! nlimb s) (nlimb s) in
  let t0 : felem s = sub t1 (3ul *! nlimb s) (nlimb s) in
  let tmp1 : felem_wide s = sub tmp 0ul (nwide s) in
  (* 2^200 - 2^100 *) fsquare_times #s t0 c tmp1 100ul;
  (* 2^200 - 2^0 *) fmul_s #s t0 t0 c tmp;
  (* 2^250 - 2^50 *) fsquare_times #s t0 t0 tmp1 50ul;
  (* 2^250 - 2^0 *) fmul_s #s t0 t0 b tmp;
  (* 2^255 - 2^5 *) fsquare_times #s t0 t0 tmp1 5ul


val finv0:
    #s:field_spec
  -> i:felem s
  -> t1:lbuffer (limb s) (4ul *! nlimb s)
  -> tmp:felem_wide2 s
  -> Stack unit
    (requires fun h0 ->
      live h0 i /\ live h0 t1 /\ live h0 tmp /\
      disjoint i t1 /\ disjoint i tmp /\ disjoint t1 tmp /\
      fsquare_times_inv h0 i)
    (ensures  fun h0 _ h1 ->
      modifies (loc t1 |+| loc tmp) h0 h1 /\
      (let a_s, t0_s = S.finv0 (feval h0 i) in
      let a = gsub t1 0ul (nlimb s) in
      let t0 = gsub t1 (3ul *! nlimb s) (nlimb s) in
      fsquare_times_inv h1 a /\
      fsquare_times_inv h1 t0 /\
      (feval h1 a, feval h1 t0) == (a_s, t0_s)))

[@ Meta.Attribute.inline_ ]
let finv0 #s i t1 tmp =
  let h0 = ST.get () in
  let a : felem s = sub t1 0ul (nlimb s) in
  let b : felem s = sub t1 (nlimb s) (nlimb s) in
  let c : felem s = sub t1 (2ul *! nlimb s) (nlimb s) in
  let t0 : felem s = sub t1 (3ul *! nlimb s) (nlimb s) in
  finv1 #s i t1 tmp;
  finv2 #s t1 tmp;
  finv3 #s t1 tmp;
  let h1 = ST.get () in
  assert (fsquare_times_inv h1 t0);
  assert (fsquare_times_inv h1 a);
  assert (modifies (loc t1 |+| loc tmp) h0 h1);
  assert ( (feval h1 a, feval h1 t0) == S.finv0 (feval h0 i))


val finv:
    #s:field_spec
  -> o:felem s
  -> i:felem s
  -> tmp:felem_wide2 s
  -> Stack unit
    (requires fun h0 ->
      live h0 o /\ live h0 i /\ live h0 tmp /\
      disjoint o i /\ disjoint i tmp /\
      (disjoint o tmp) /\
      fsquare_times_inv h0 i)
    (ensures  fun h0 _ h1 ->
      modifies (loc o |+| loc tmp) h0 h1 /\
      fsquare_times_inv h1 o /\
      feval h1 o == P.fpow (feval #s h0 i) (pow2 255 - 21))
[@ Meta.Attribute.specialize ]
let finv #s o i tmp =
  push_frame();
  let t1 = create (4ul *! nlimb s) (limb_zero s) in
  let h0 = ST.get () in
  finv0 #s i t1 tmp;
  let a : felem s = sub t1 0ul (nlimb s) in
  let t0 : felem s = sub t1 (3ul *! nlimb s) (nlimb s) in
  (* 2^255 - 21 *) fmul_s #s o t0 a tmp;
  let h1 = ST.get () in
  assert (feval h1 o == S.finv (feval h0 i));
  pop_frame()
