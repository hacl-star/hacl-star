module Hacl.Impl.Curve25519.Finv

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Curve25519.Fields

module ST = FStar.HyperStack.ST

module F51 = Hacl.Impl.Curve25519.Field51
module F64 = Hacl.Impl.Curve25519.Field64

module S = Hacl.Spec.Curve25519.Finv
module P = Spec.Curve25519

#reset-options "--using_facts_from '* -FStar.Seq'"

noextract
val fsquare_times_inv: #s:field_spec -> h:mem -> f:felem s -> Type0
let fsquare_times_inv #s h f =
  match s with
  | M51 -> F51.felem_fits h f (1, 2, 1, 1, 1)
  | M64 -> X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)

inline_for_extraction noextract
val fsqr_s:
    #s:field_spec
  -> out:felem s
  -> f1:felem s
  -> tmp:felem_wide s
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\ live h tmp /\
      (disjoint out f1 \/ out == f1) /\
      (disjoint out tmp \/ out == tmp) /\
      disjoint tmp f1 /\
      fsquare_times_inv h f1)
    (ensures  fun h0 _ h1 ->
      modifies (loc out |+| loc tmp) h0 h1 /\
      fsquare_times_inv h1 out /\
      feval h1 out == P.fmul (feval h0 f1) (feval h0 f1))
let fsqr_s #s out f1 tmp =
  match s with
  | M51 -> F51.fsqr out f1
  | M64 -> F64.fsqr out f1 tmp

noextract
val fmuls_pre: #s:field_spec -> h:mem -> f1:felem s -> f2:felem s -> Type0
let fmuls_pre #s h f1 f2 =
  match s with
  | M51 -> F51.felem_fits h f1 (1, 2, 1, 1, 1) /\ F51.felem_fits h f2 (1, 2, 1, 1, 1)
  | M64 -> X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)

inline_for_extraction noextract
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
      (disjoint out tmp \/ out == tmp) /\
      (disjoint f1 f2 \/ f1 == f2) /\
      disjoint f1 tmp /\
      disjoint f2 tmp /\
      fmuls_pre h f1 f2)
    (ensures  fun h0 _ h1 ->
      modifies (loc out |+| loc tmp) h0 h1 /\ fsquare_times_inv h1 out /\
      feval h1 out == P.fmul (feval h0 f1) (feval h0 f2))
let fmul_s #s out f1 f2 tmp =
  match s with
  | M51 -> F51.fmul out f1 f2
  | M64 -> F64.fmul out f1 f2 tmp

inline_for_extraction noextract
val fsquare_times_:
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
let fsquare_times_ #s o inp tmp n =
  let h0 = ST.get() in
  fsqr_s #s o inp tmp;
  let h1 = ST.get() in
  S.lemma_pow_one (feval h0 inp);
  S.lemma_pow_add (feval h0 inp) 1 1;
  assert_norm (pow2 1 = 2);
  let inv (h:mem) (i:nat{i < v n}) =
    modifies (loc o |+| loc tmp) h0 h /\ fsquare_times_inv #s h o /\
    feval h o == S.pow (feval #s h0 inp) (pow2 (i + 1)) in
  Lib.Loops.for 0ul (n -! 1ul) inv
  (fun i ->
    let h2 = ST.get () in
    fsqr_s #s o o tmp;
    let h3 = ST.get () in
    S.lemma_pow_one (feval h2 o);
    S.lemma_pow_add (feval h2 o) 1 1;
    S.lemma_pow_mul (feval #s h0 inp) (pow2 (v i + 1)) (pow2 1);
    assert_norm (pow2 (v i + 1) * pow2 1 = pow2 (v i + 2)))

(* WRAPPER to Prevent Inlining *)
[@CInline]
let fsquare_times_51 (o:F51.felem) (i:F51.felem) (tmp:felem_wide M51) (n:size_t{v n > 0}) = fsquare_times_ #M51 o i tmp n
[@CInline]
let fsquare_times_64 (o:F64.felem) (i:F64.felem) (tmp:felem_wide M64) (n:size_t{v n > 0}) = fsquare_times_ #M64 o i tmp n

inline_for_extraction noextract
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
      modifies (loc o |+| loc tmp) h0 h1 /\ live h1 o /\ live h1 i /\
      fsquare_times_inv h1 o /\
      feval h1 o == S.pow (feval #s h0 i) (pow2 (v n)))
let fsquare_times #s o i tmp n =
  match s with
  | M51 -> fsquare_times_51 o i tmp n
  | M64 -> fsquare_times_64 o i tmp n
(* WRAPPER to Prevent Inlining *)

#set-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 3"

inline_for_extraction noextract
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
let finv0 #s i t1 tmp =
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
  (* 2^10 - 2^0 *) fmul_s #s b t0 b tmp;
  (* 2^20 - 2^10 *) fsquare_times #s t0 b tmp1 10ul;
  (* 2^20 - 2^0 *) fmul_s #s c t0 b tmp;
  (* 2^40 - 2^20 *) fsquare_times #s t0 c tmp1 20ul;
  (* 2^40 - 2^0 *) fmul_s #s t0 t0 c tmp;
  (* 2^50 - 2^10 *) fsquare_times #s t0 t0 tmp1 10ul;
  (* 2^50 - 2^0 *) fmul_s #s b t0 b tmp;
  (* 2^100 - 2^50 *) fsquare_times #s t0 b tmp1 50ul;
  (* 2^100 - 2^0 *) fmul_s #s c t0 b tmp;
  (* 2^200 - 2^100 *) fsquare_times #s t0 c tmp1 100ul;
  (* 2^200 - 2^0 *) fmul_s #s t0 t0 c tmp;
  (* 2^250 - 2^50 *) fsquare_times #s t0 t0 tmp1 50ul;
  let h0' = ST.get () in
  (* 2^250 - 2^0 *) fmul_s #s t0 t0 b tmp;
  let h1' = ST.get () in
  assert (modifies (loc t1 |+| loc tmp) h0' h1');
  assert (modifies (loc t1 |+| loc tmp) h0 h1');
  (* 2^255 - 2^5 *) fsquare_times #s t0 t0 tmp1 5ul;
  let h1 = ST.get () in
  assert (fsquare_times_inv h1 t0);
  assert (fsquare_times_inv h1 a);
  assert (modifies (loc t1 |+| loc tmp) h0 h1);
  assert ( (feval h1 a, feval h1 t0) == S.finv0 (feval h0 i))

inline_for_extraction noextract
val finv_:
    #s:field_spec
  -> o:felem s
  -> i:felem s
  -> tmp:felem_wide2 s
  -> Stack unit
    (requires fun h0 ->
      live h0 o /\ live h0 i /\ live h0 tmp /\
      disjoint o i /\ disjoint i tmp /\
      (disjoint o tmp \/ o == tmp) /\
      fsquare_times_inv h0 i)
    (ensures  fun h0 _ h1 ->
      modifies (loc o |+| loc tmp) h0 h1 /\
      fsquare_times_inv h1 o /\
      feval h1 o == P.fpow (feval #s h0 i) (pow2 255 - 21))
let finv_ #s o i tmp =
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

(* WRAPPER to Prevent Inlining *)
[@CInline]
let finv_51 (o:F51.felem) (i:F51.felem) (tmp:felem_wide2 M51) = finv_ #M51 o i tmp
[@CInline]
let finv_64 (o:F64.felem) (i:F64.felem) (tmp:felem_wide2 M64) = finv_ #M64 o i tmp

inline_for_extraction noextract
val finv:
    #s:field_spec
  -> o:felem s
  -> i:felem s
  -> tmp:felem_wide2 s
  -> Stack unit
    (requires fun h0 ->
      live h0 o /\ live h0 i /\ live h0 tmp /\
      disjoint i tmp /\ disjoint i o /\
      (disjoint o tmp \/ o == tmp) /\
      fsquare_times_inv h0 i)
    (ensures  fun h0 _ h1 ->
      modifies (loc o |+| loc tmp) h0 h1 /\
      fsquare_times_inv h1 o /\
      feval h1 o == P.fpow (feval #s h0 i) (pow2 255 - 21))
let finv #s o i tmp =
  match s with
  | M51 -> finv_51 o i tmp
  | M64 -> finv_64 o i tmp
 (* WRAPPER to Prevent Inlining *)
