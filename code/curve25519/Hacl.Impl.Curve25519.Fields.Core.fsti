module Hacl.Impl.Curve25519.Fields.Core

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module P = Spec.Curve25519
module S = Hacl.Spec.Curve25519.Field64.Definition
module SC = Hacl.Spec.Curve25519.Field64

/// This module defines the core functions for which we will want to swap out
/// implementations. They are marked as assume val's since we strictly have more
/// than one implementation per index value.

#set-options "--z3rlimit 50 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1 --record_options"

/// Shared definitions for agility of the field type
/// ------------------------------------------------

type field_spec =
  | M51
  | M64

unfold noextract
let limb (s:field_spec) =
  match s with
  | M51 -> uint64
  | M64 -> uint64

unfold noextract
let limb_zero (s:field_spec) : limb s=
  match s with
  | M51 -> u64 0
  | M64 -> u64 0

unfold noextract
let nlimb (s:field_spec) : size_t =
  match s with
  | M51 -> 5ul
  | M64 -> 4ul

unfold noextract
let wide (s:field_spec) =
  match s with
  | M51 -> uint128
  | M64 -> uint64

unfold noextract
let wide_zero (s:field_spec) : wide s=
  match s with
  | M51 -> u128 0
  | M64 -> u64 0

unfold noextract
let nwide (s:field_spec) : size_t =
  match s with
  | M51 -> 5ul
  | M64 -> 8ul

inline_for_extraction noextract
let felem (s:field_spec) = lbuffer (limb s) (nlimb s)
inline_for_extraction noextract
let felem2 (s:field_spec) = lbuffer (limb s) (nlimb s +. nlimb s)
inline_for_extraction noextract
let felem_wide (s:field_spec) = lbuffer (wide s) (nwide s)
inline_for_extraction noextract
let felem_wide2 (s:field_spec) = lbuffer (wide s) (nwide s +. nwide s)


/// Introduce representation for each field + helpers to be able to state pre & posts
/// ---------------------------------------------------------------------------------

noextract
let f51_as_felem (h:mem) (f:felem M51) : GTot Hacl.Spec.Curve25519.Field51.Definition.felem5 =
  let s = as_seq h f in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  (s0, s1, s2, s3, s4)

let f51_as_nat h e = Hacl.Spec.Curve25519.Field51.Definition.as_nat5 (f51_as_felem h e)

noextract
let f51_felem_fits (h:mem) (f:felem M51) (m:Hacl.Spec.Curve25519.Field51.Definition.scale64_5): Type0 =
  Hacl.Spec.Curve25519.Field51.Definition.felem_fits5 (f51_as_felem h f) m

noextract
let f51_felem_fits1 = Hacl.Spec.Curve25519.Field51.Definition.felem_fits1

noextract
let f51_mul_inv_t (h:mem) (f:felem M51) : GTot Type0 =
  let f = f51_as_felem h f in
  Hacl.Spec.Curve25519.Field51.mul_inv_t f

noextract
let f64_as_nat (h:mem) (e: felem M64) : GTot nat =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  Hacl.Spec.Curve25519.Field64.Definition.as_nat4 (s0, s1, s2, s3)

noextract
let as_nat (#s:field_spec) (h:mem) (e:felem s): GTot nat =
  match s with
  | M51 -> f51_as_nat h e
  | M64 -> f64_as_nat h e

noextract
let feval (#s:field_spec) (h:mem) (e:felem s): GTot P.elem =
  (as_nat h e) % P.prime


/// Start of core combinators
/// -------------------------

let fadd_fsub_pre (#s:field_spec) (h:mem) (f1:felem s) (f2:felem s): Type0 =
  match s with
  | M51 ->
      f51_felem_fits h f1 (1, 2, 1, 1, 1) /\
      f51_felem_fits h f2 (1, 2, 1, 1, 1)
  | M64 -> Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)

let fadd_post (#s:field_spec) (h:mem) (out:felem s): Type0 =
  match s with
  | M51 -> f51_felem_fits h out (2, 4, 2, 2, 2)
  | M64 -> True

inline_for_extraction
let fadd_t (s:field_spec) =
    out:felem s
  -> f1:felem s
  -> f2:felem s
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\ live h f2 /\
      (disjoint out f1 \/ out == f1) /\
      (disjoint out f2 \/ out == f2) /\
      (disjoint f1 f2 \/ f1 == f2) /\
      fadd_fsub_pre h f1 f2)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\ fadd_post h1 out /\
      feval h1 out == P.fadd (feval h0 f1) (feval h0 f2))
[@ Meta.Attribute.specialize]
val fadd: #s:field_spec -> fadd_t s

let fsub_post (#s:field_spec) (h:mem) (out:felem s): Type0 =
  match s with
  | M51 -> f51_felem_fits h out (9, 10, 9, 9, 9)
  | M64 -> True

inline_for_extraction
let fsub_t (s:field_spec) =
    out:felem s
  -> f1:felem s
  -> f2:felem s
  -> Stack unit
    (requires fun h ->
      (s = M64 ==> Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)) /\
      live h out /\ live h f1 /\ live h f2 /\
      (disjoint out f1 \/ out == f1) /\
      (disjoint out f2 \/ out == f2) /\
      (disjoint f1 f2 \/ f1 == f2) /\
      fadd_fsub_pre h f1 f2)
    (ensures fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\ fsub_post h1 out /\
      feval h1 out == P.fsub (feval h0 f1) (feval h0 f2))
[@ Meta.Attribute.specialize ]
val fsub: #s:field_spec -> fsub_t s

let fmul_pre (#s:field_spec) (h:mem) (f1:felem s) (f2:felem s): Type0 =
  match s with
  | M51 ->
      f51_felem_fits h f1 (9, 10, 9, 9, 9) /\
      f51_felem_fits h f2 (9, 10, 9, 9, 9)
  | M64 -> Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)

let fmul_disjoint (#s:field_spec) (out f1 f2:felem s) (tmp:felem_wide2 s): Type0 =
  match s with
  | M51 -> True
  | M64 ->
      (disjoint out f1 \/ out == f1) /\
      (disjoint out f2 \/ out == f2) /\
      (disjoint out tmp \/ out == tmp) /\
      (disjoint f1 f2 \/ f1 == f2) /\
      disjoint f1 tmp /\
      disjoint f2 tmp


let state_inv_t (#s:field_spec) (h:mem) (f:felem s): Type0 =
  match s with
  | M51 -> f51_mul_inv_t h f
  | M64 -> True

inline_for_extraction
let fmul_t (s:field_spec) =
    out:felem s
  -> f1:felem s
  -> f2:felem s
  -> tmp:felem_wide2 s
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\ live h f2 /\ live h tmp /\
      fmul_disjoint out f1 f2 tmp /\
      fmul_pre h f1 f2)
    (ensures fun h0 _ h1 ->
      modifies (loc out |+| loc tmp) h0 h1 /\ state_inv_t h1 out /\
      feval h1 out == P.fmul (feval h0 f1) (feval h0 f2))
[@ Meta.Attribute.specialize ]
val fmul: #s:field_spec -> fmul_t s

let fmul2_pre (#s:field_spec) (h:mem) (f1:felem2 s) (f2:felem2 s): Type0 =
  match s with
  | M51 ->
      let f10 = gsub f1 0ul 5ul in
      let f11 = gsub f1 5ul 5ul in
      let f20 = gsub f2 0ul 5ul in
      let f21 = gsub f2 5ul 5ul in
      f51_felem_fits h f10 (9, 10, 9, 9, 9) /\
      f51_felem_fits h f11 (9, 10, 9, 9, 9) /\
      f51_felem_fits h f20 (9, 10, 9, 9, 9) /\
      f51_felem_fits h f21 (9, 10, 9, 9, 9)
  | M64 -> Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)

let fmul2_fsqr2_post (#s:field_spec) (h:mem) (out:felem2 s): Type0 =
  match s with
  | M51 ->
      let out0 = gsub out 0ul 5ul in
      let out1 = gsub out 5ul 5ul in
      f51_mul_inv_t h out0 /\
      f51_mul_inv_t h out1
  | M64 -> True

inline_for_extraction
let fmul2_t (s:field_spec) =
    out:felem2 s
  -> f1:felem2 s
  -> f2:felem2 s
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
      fmul2_pre h f1 f2)
    (ensures  fun h0 _ h1 ->
      modifies (loc out |+| loc tmp) h0 h1 /\ fmul2_fsqr2_post h1 out /\
     (let out0 = gsub out 0ul (nlimb s) in
      let out1 = gsub out (nlimb s) (nlimb s) in
      let f10 = gsub f1 0ul (nlimb s) in
      let f11 = gsub f1 (nlimb s) (nlimb s) in
      let f20 = gsub f2 0ul (nlimb s) in
      let f21 = gsub f2 (nlimb s) (nlimb s) in
      feval h1 out0 == P.fmul (feval h0 f10) (feval h0 f20) /\
      feval h1 out1 == P.fmul (feval h0 f11) (feval h0 f21)))

[@ Meta.Attribute.specialize ]
val fmul2: #s:field_spec -> fmul2_t s

let fmul1_pre (#s:field_spec) (h:mem) (f1:felem s) (f2:uint64): Type0 =
  match s with
  | M51 -> f51_felem_fits h f1 (9, 10, 9, 9, 9) /\ f51_felem_fits1 f2 1
  | M64 -> v f2 < pow2 17 /\ Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)

inline_for_extraction
let fmul1_t (s:field_spec) =
    out:felem s
  -> f1:felem s
  -> f2:uint64
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\
      (disjoint out f1 \/ out == f1) /\
      fmul1_pre h f1 f2)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\ state_inv_t h1 out /\
      feval h1 out == P.fmul (feval h0 f1) (v f2))
//     feval h1 out == (feval h0 f1 * v f2) % P.prime)

[@ Meta.Attribute.specialize ]
val fmul1: #s:field_spec -> fmul1_t s

let fsqr_pre (#s:field_spec) (h:mem) (f:felem s): Type0 =
  match s with
  | M51 -> f51_felem_fits h f (9, 10, 9, 9, 9)
  | M64 -> Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)

let fsqr_disjoint (#s:field_spec) (out f1:felem s) (tmp:felem_wide s): Type0 =
  match s with
  | M51 -> True
  | M64 ->
      (disjoint out f1 \/ out == f1) /\
      (disjoint out tmp \/ out == tmp) /\
      disjoint tmp f1

inline_for_extraction
let fsqr_t (s:field_spec) =
    out:felem s
  -> f1:felem s
  -> tmp:felem_wide s
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\ live h tmp /\
      fsqr_disjoint out f1 tmp /\
      fsqr_pre h f1)
    (ensures  fun h0 _ h1 ->
      modifies (loc out |+| loc tmp) h0 h1 /\
      state_inv_t h1 out /\
      feval h1 out == P.fmul (feval h0 f1) (feval h0 f1))

[@ Meta.Attribute.specialize ]
val fsqr: #s:field_spec -> fsqr_t s

let fsqr2_pre (#s:field_spec) (h:mem) (f:felem2 s): Type0 =
  match s with
  | M51 ->
      let f1 = gsub f 0ul 5ul in
      let f2 = gsub f 5ul 5ul in
      f51_felem_fits h f1 (9, 10, 9, 9, 9) /\
      f51_felem_fits h f2 (9, 10, 9, 9, 9)
  | M64 -> Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)

inline_for_extraction
let fsqr2_t (s:field_spec) =
    out:felem2 s
  -> f:felem2 s
  -> tmp:felem_wide2 s
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f /\ live h tmp /\
      (disjoint out f \/ out == f) /\
      (disjoint out tmp \/ out == tmp) /\
      disjoint tmp f /\
      fsqr2_pre h f)
    (ensures  fun h0 _ h1 ->
      modifies (loc out |+| loc tmp) h0 h1 /\ fmul2_fsqr2_post h1 out /\
     (let out1 = gsub out 0ul (nlimb s) in
      let out2 = gsub out (nlimb s) (nlimb s) in
      let f1 = gsub f 0ul (nlimb s) in
      let f2 = gsub f (nlimb s) (nlimb s) in
      feval h1 out1 == P.fmul (feval h0 f1) (feval h0 f1) /\
      feval h1 out2 == P.fmul (feval h0 f2) (feval h0 f2)))

[@ Meta.Attribute.specialize ]
val fsqr2: #s:field_spec -> fsqr2_t s

inline_for_extraction
let cswap2_t (s:field_spec) =
    bit:uint64{v bit <= 1}
  -> p1:felem2 s
  -> p2:felem2 s
  -> Stack unit
    (requires fun h0 ->
      (s = M64 ==> Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)) /\
      live h0 p1 /\ live h0 p2 /\
      (disjoint p1 p2 \/ p1 == p2))
    (ensures  fun h0 _ h1 ->
      modifies (loc p1 |+| loc p2) h0 h1 /\
      (v bit == 1 ==> as_seq h1 p1 == as_seq h0 p2 /\ as_seq h1 p2 == as_seq h0 p1) /\
      (v bit == 0 ==> as_seq h1 p1 == as_seq h0 p1 /\ as_seq h1 p2 == as_seq h0 p2))

[@ Meta.Attribute.specialize ]
val cswap2: #s:field_spec -> cswap2_t s

/// Field64-specific core operations
/// --------------------------------

inline_for_extraction
let add1_t = out:felem M64 -> f1:felem M64 -> f2:uint64
  -> Stack uint64
    (requires fun h ->
      Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled) /\
      live h f1 /\ live h out /\
      (disjoint out f1 \/ out == f1))
    (ensures  fun h0 c h1 ->
      modifies (loc out) h0 h1 /\
      as_nat h1 out + v c * pow2 256 == as_nat h0 f1 + v f2)
[@ CInline Meta.Attribute.specialize ]
val add1: add1_t
