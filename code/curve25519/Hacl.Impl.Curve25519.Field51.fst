module Hacl.Impl.Curve25519.Field51

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer

include Hacl.Spec.Curve25519.Field51
include Hacl.Spec.Curve25519.Field51.Definition

module P = Spec.Curve25519
module S = Hacl.Spec.Curve25519.Field51.Definition
module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence
module Lemmas = Hacl.Spec.Curve25519.Field51.Lemmas

#reset-options "--z3rlimit 20"

let felem = lbuffer uint64 5ul
let felem2 = lbuffer uint64 10ul
let felem_wide = lbuffer uint128 5ul

noextract
val as_nat: h:mem -> e:felem -> GTot nat
let as_nat h e =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  S.as_nat5 (s0, s1, s2, s3, s4)

noextract
val wide_as_nat: h:mem -> e:felem_wide -> GTot nat
let wide_as_nat h e =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  S.wide_as_nat5 (s0, s1, s2, s3, s4)

noextract
val fevalh: h:mem -> f:felem -> GTot P.elem
let fevalh h f = (as_nat h f) % P.prime

noextract
val feval_wideh: h:mem -> f:felem_wide -> GTot P.elem
let feval_wideh h f = (wide_as_nat h f) % P.prime

noextract
val felem_fits: h:mem -> f:felem -> m:S.scale64_5 -> Type0
let felem_fits h f m =
  let s = as_seq h f in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  S.felem_fits5 (s0, s1, s2, s3, s4) m

noextract
val felem_wide_fits: h:mem -> f:felem_wide -> m:S.scale128_5 -> Type0
let felem_wide_fits h f m =
  let s = as_seq h f in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  S.felem_wide_fits5 (s0, s1, s2, s3, s4) m

noextract
let as_felem (h:mem) (f:felem) : GTot felem5 =
  let s = as_seq h f in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  (s0, s1, s2, s3, s4)

noextract
let mul_inv_t (h:mem) (f:felem) : GTot Type0 =
  let f = as_felem h f in
  mul_inv_t f

inline_for_extraction noextract
val create_felem: unit
  -> StackInline felem
    (requires fun _ -> True)
    (ensures  fun h0 f h1 ->
      stack_allocated f h0 h1 (LSeq.create 5 (u64 0)) /\
      as_nat h1 f == 0)
let create_felem () = create 5ul (u64 0)

inline_for_extraction noextract
val set_zero:
  f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 ->
    modifies (loc f) h0 h1 /\
    as_nat h1 f == 0)
let set_zero f =
  f.(0ul) <- u64 0;
  f.(1ul) <- u64 0;
  f.(2ul) <- u64 0;
  f.(3ul) <- u64 0;
  f.(4ul) <- u64 0

inline_for_extraction noextract
val set_one:
  f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 ->
    modifies (loc f) h0 h1 /\
    as_nat h1 f == 1)
let set_one f =
  f.(0ul) <- u64 1;
  f.(1ul) <- u64 0;
  f.(2ul) <- u64 0;
  f.(3ul) <- u64 0;
  f.(4ul) <- u64 0

inline_for_extraction noextract
val copy_felem:
    f1:felem
  -> f2:felem
  -> Stack unit
    (requires fun h ->
      live h f1 /\ live h f2 /\ disjoint f1 f2)
    (ensures  fun h0 _ h1 ->
      modifies (loc f1) h0 h1 /\
      as_seq h1 f1 == as_seq h0 f2)
let copy_felem f1 f2 =
  f1.(0ul) <- f2.(0ul);
  f1.(1ul) <- f2.(1ul);
  f1.(2ul) <- f2.(2ul);
  f1.(3ul) <- f2.(3ul);
  f1.(4ul) <- f2.(4ul);
  let h1 = ST.get () in
  LSeq.eq_intro (as_seq h1 f1) (as_seq h1 f2)

#set-options "--max_fuel 0 --max_ifuel 0"

val fadd:
    out:felem
  -> f1:felem
  -> f2:felem
  -> Stack unit
    (requires fun h ->
      live h f1 /\ live h f2 /\ live h out /\
      felem_fits h f1 (1, 2, 1, 1, 1) /\
      felem_fits h f2 (1, 2, 1, 1, 1))
    (ensures fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      felem_fits h1 out (2, 4, 2, 2, 2) /\
      fevalh h1 out == P.fadd (fevalh h0 f1) (fevalh h0 f2))
[@ CInline]
let fadd out f1 f2 =
  let h0 = ST.get () in
  let f10 = f1.(0ul) in
  let f20 = f2.(0ul) in
  let f11 = f1.(1ul) in
  let f21 = f2.(1ul) in
  let f12 = f1.(2ul) in
  let f22 = f2.(2ul) in
  let f13 = f1.(3ul) in
  let f23 = f2.(3ul) in
  let f14 = f1.(4ul) in
  let f24 = f2.(4ul) in
  out.(0ul) <- f10 +! f20;
  out.(1ul) <- f11 +! f21;
  out.(2ul) <- f12 +! f22;
  out.(3ul) <- f13 +! f23;
  out.(4ul) <- f14 +! f24;
  let h1 = ST.get () in
  assert (as_nat h1 out == as_nat h0 f1 + as_nat h0 f2);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l
    (as_nat h0 f1) (as_nat h0 f2) P.prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
    (as_nat h0 f1 % P.prime) (as_nat h0 f2) P.prime

val fsub:
    out:felem
  -> f1:felem
  -> f2:felem
  -> Stack unit
    (requires fun h ->
      live h f1 /\ live h f2 /\ live h out /\
      felem_fits h f1 (1, 2, 1, 1, 1) /\
      felem_fits h f2 (1, 2, 1, 1, 1))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      felem_fits h1 out (9, 10, 9, 9, 9) /\
      fevalh h1 out == P.fsub (fevalh h0 f1) (fevalh h0 f2))
[@ CInline]
let fsub out f1 f2 =
  let f10 = f1.(0ul) in
  let f20 = f2.(0ul) in
  let f11 = f1.(1ul) in
  let f21 = f2.(1ul) in
  let f12 = f1.(2ul) in
  let f22 = f2.(2ul) in
  let f13 = f1.(3ul) in
  let f23 = f2.(3ul) in
  let f14 = f1.(4ul) in
  let f24 = f2.(4ul) in
  out.(0ul) <- f10 +! u64 0x3fffffffffff68 -! f20;
  out.(1ul) <- f11 +! u64 0x3ffffffffffff8 -! f21;
  out.(2ul) <- f12 +! u64 0x3ffffffffffff8 -! f22;
  out.(3ul) <- f13 +! u64 0x3ffffffffffff8 -! f23;
  out.(4ul) <- f14 +! u64 0x3ffffffffffff8 -! f24;
  lemma_fsub (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24)

val fmul:
    out:felem
  -> f1:felem
  -> f2:felem
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\ live h f2 /\
      felem_fits h f1 (9, 10, 9, 9, 9) /\
      felem_fits h f2 (9, 10, 9, 9, 9))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      mul_inv_t h1 out /\
      fevalh h1 out == P.fmul (fevalh h0 f1) (fevalh h0 f2))
[@ CInline]
let fmul out f1 f2 =
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
    fmul5 (f10,f11,f12,f13,f14) (f20,f21,f22,f23,f24) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  out.(4ul) <- o4

val fmul2:
    out:felem2
  -> f1:felem2
  -> f2:felem2
  -> Stack unit
    (requires fun h ->
      let f10 = gsub f1 0ul 5ul in
      let f11 = gsub f1 5ul 5ul in
      let f20 = gsub f2 0ul 5ul in
      let f21 = gsub f2 5ul 5ul in
      felem_fits h f10 (9, 10, 9, 9, 9) /\
      felem_fits h f11 (9, 10, 9, 9, 9) /\
      felem_fits h f20 (9, 10, 9, 9, 9) /\
      felem_fits h f21 (9, 10, 9, 9, 9) /\
      live h out /\ live h f1 /\ live h f2)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
     (let out0 = gsub out 0ul 5ul in
      let out1 = gsub out 5ul 5ul in
      let f10 = gsub f1 0ul 5ul in
      let f11 = gsub f1 5ul 5ul in
      let f20 = gsub f2 0ul 5ul in
      let f21 = gsub f2 5ul 5ul in
      mul_inv_t h1 out0 /\
      mul_inv_t h1 out1 /\
      fevalh h1 out0 == P.fmul (fevalh h0 f10) (fevalh h0 f20) /\
      fevalh h1 out1 == P.fmul (fevalh h0 f11) (fevalh h0 f21)))
[@ CInline]
let fmul2 out f1 f2 =
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

  let f30 = f1.(5ul) in
  let f31 = f1.(6ul) in
  let f32 = f1.(7ul) in
  let f33 = f1.(8ul) in
  let f34 = f1.(9ul) in

  let f40 = f2.(5ul) in
  let f41 = f2.(6ul) in
  let f42 = f2.(7ul) in
  let f43 = f2.(8ul) in
  let f44 = f2.(9ul) in

  let ((o10,o11,o12,o13,o14), (o20,o21,o22,o23,o24)) =
    fmul25 (f10,f11,f12,f13,f14) (f20,f21,f22,f23,f24)
     (f30,f31,f32,f33,f34) (f40,f41,f42,f43,f44) in

  out.(0ul) <- o10;
  out.(1ul) <- o11;
  out.(2ul) <- o12;
  out.(3ul) <- o13;
  out.(4ul) <- o14;

  out.(5ul) <- o20;
  out.(6ul) <- o21;
  out.(7ul) <- o22;
  out.(8ul) <- o23;
  out.(9ul) <- o24

val fmul1:
    out:felem
  -> f1:felem
  -> f2:uint64
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\
      felem_fits h f1 (9, 10, 9, 9, 9) /\
      S.felem_fits1 f2 1)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      mul_inv_t h1 out /\
      fevalh h1 out == (fevalh h0 f1 * v f2) % P.prime)
[@ CInline]
let fmul1 out f1 f2 =
  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in
  let f14 = f1.(4ul) in
  let (o0,o1,o2,o3,o4) = fmul15 (f10,f11,f12,f13,f14) f2 in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  out.(4ul) <- o4

val fsqr:
     out:felem
  -> f:felem
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f /\
      felem_fits h f (9, 10, 9, 9, 9))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      mul_inv_t h1 out /\
      fevalh h1 out == P.fmul (fevalh h0 f) (fevalh h0 f))
[@ CInline]
let fsqr out f =
  let f0 = f.(0ul) in
  let f1 = f.(1ul) in
  let f2 = f.(2ul) in
  let f3 = f.(3ul) in
  let f4 = f.(4ul) in
  let (o0,o1,o2,o3,o4) = fsqr5 (f0,f1,f2,f3,f4) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  out.(4ul) <- o4

val fsqr2:
    out:felem2
  -> f:felem2
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f /\
     (let f1 = gsub f 0ul 5ul in
      let f2 = gsub f 5ul 5ul in
      felem_fits h f1 (9, 10, 9, 9, 9) /\
      felem_fits h f2 (9, 10, 9, 9, 9)))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
     (let out1 = gsub out 0ul 5ul in
      let out2 = gsub out 5ul 5ul in
      let f1 = gsub f 0ul 5ul in
      let f2 = gsub f 5ul 5ul in
      mul_inv_t h1 out1 /\
      mul_inv_t h1 out2 /\
      fevalh h1 out1 == P.fmul (fevalh h0 f1) (fevalh h0 f1) /\
      fevalh h1 out2 == P.fmul (fevalh h0 f2) (fevalh h0 f2)))
[@ CInline]
let fsqr2 out f =
  let f10 = f.(0ul) in
  let f11 = f.(1ul) in
  let f12 = f.(2ul) in
  let f13 = f.(3ul) in
  let f14 = f.(4ul) in

  let f20 = f.(5ul) in
  let f21 = f.(6ul) in
  let f22 = f.(7ul) in
  let f23 = f.(8ul) in
  let f24 = f.(9ul) in

  let ((o10,o11,o12,o13,o14),(o20,o21,o22,o23,o24)) =
    fsqr25 (f10,f11,f12,f13,f14) (f20,f21,f22,f23,f24) in
  out.(0ul) <- o10;
  out.(1ul) <- o11;
  out.(2ul) <- o12;
  out.(3ul) <- o13;
  out.(4ul) <- o14;

  out.(5ul) <- o20;
  out.(6ul) <- o21;
  out.(7ul) <- o22;
  out.(8ul) <- o23;
  out.(9ul) <- o24

inline_for_extraction noextract
val load_felem:
    f:felem
  -> u64s:lbuffer uint64 4ul
  -> Stack unit
    (requires fun h ->
      live h u64s /\ live h f /\ disjoint u64s f /\
      v (as_seq h u64s).[3] < pow2 63)
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      //felem_fits h1 f (1, 1, 1, 1, 1) /\
      mul_inv_t h1 f /\
      as_nat h1 f == BSeq.nat_from_intseq_le (as_seq h0 u64s))
let load_felem f u64s =
  let h0 = ST.get () in
  let f0l = u64s.(0ul) &. S.mask51 in
  let f0h = u64s.(0ul) >>. 51ul in
  let f1l = (u64s.(1ul) &. u64 0x3fffffffff) <<. 13ul in
  let f1h = u64s.(1ul) >>. 38ul in
  let f2l = (u64s.(2ul) &. u64 0x1ffffff) <<. 26ul in
  let f2h = u64s.(2ul) >>. 25ul in
  let f3l = (u64s.(3ul) &. u64 0xfff) <<. 39ul in
  let f3h = u64s.(3ul) >>. 12ul in
  f.(0ul) <- f0l;
  f.(1ul) <- f0h |. f1l;
  f.(2ul) <- f1h |. f2l;
  f.(3ul) <- f2h |. f3l;
  f.(4ul) <- f3h;
  Lemmas.lemma_load_felem (as_seq h0 u64s)

val store_felem:
    u64s:lbuffer uint64 4ul
  -> f:felem
  -> Stack unit
    (requires fun h ->
      live h f /\ live h u64s /\ mul_inv_t h f)
    (ensures  fun h0 _ h1 ->
      modifies (loc u64s) h0 h1 /\
      BSeq.nat_from_intseq_le (as_seq h1 u64s) == (as_nat h0 f) % P.prime)
let store_felem u64s f =
  let f0 = f.(0ul) in
  let f1 = f.(1ul) in
  let f2 = f.(2ul) in
  let f3 = f.(3ul) in
  let f4 = f.(4ul) in
  let (o0, o1, o2, o3) = store_felem5 (f0, f1, f2, f3, f4) in
  u64s.(0ul) <- o0;
  u64s.(1ul) <- o1;
  u64s.(2ul) <- o2;
  u64s.(3ul) <- o3;
  let h1 = ST.get () in
  Hacl.Impl.Curve25519.Lemmas.lemma_nat_from_uints64_le_4 (as_seq h1 u64s)

val cswap2:
    bit:uint64{v bit <= 1}
  -> p1:felem2
  -> p2:felem2
  -> Stack unit
    (requires fun h ->
      live h p1 /\ live h p2 /\
      (disjoint p1 p2 \/ p1 == p2))
    (ensures  fun h0 _ h1 ->
      modifies (loc p1 |+| loc p2) h0 h1 /\
      (v bit == 1 ==> as_seq h1 p1 == as_seq h0 p2 /\ as_seq h1 p2 == as_seq h0 p1) /\
      (v bit == 0 ==> as_seq h1 p1 == as_seq h0 p1 /\ as_seq h1 p2 == as_seq h0 p2))
[@ CInline]
let cswap2 bit p1 p2 =
  let h0 = ST.get () in
  let mask = u64 0 -. bit in

  [@ inline_let]
  let inv h1 (i:nat{i <= 10}) =
    (forall (k:nat{k < i}).
      if v bit = 1
      then (as_seq h1 p1).[k] == (as_seq h0 p2).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p1).[k]
      else (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    (forall (k:nat{i <= k /\ k < 10}).
      (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    modifies (loc p1 |+| loc p2) h0 h1 in

  Lib.Loops.for 0ul 10ul inv
    (fun i ->
      let dummy = mask &. (p1.(i) ^. p2.(i)) in
      p1.(i) <- p1.(i) ^. dummy;
      p2.(i) <- p2.(i) ^. dummy;
      Lemmas.lemma_cswap2_step bit ((as_seq h0 p1).[v i]) ((as_seq h0 p2).[v i])
    );
  let h1 = ST.get () in
  Lib.Sequence.eq_intro (as_seq h1 p1) (if v bit = 1 then as_seq h0 p2 else as_seq h0 p1);
  Lib.Sequence.eq_intro (as_seq h1 p2) (if v bit = 1 then as_seq h0 p1 else as_seq h0 p2)
