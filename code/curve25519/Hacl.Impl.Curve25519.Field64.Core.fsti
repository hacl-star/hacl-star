module Hacl.Impl.Curve25519.Field64.Core

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer

module B = Lib.Buffer
module S = Hacl.Spec.Curve25519.Field64.Definition
module P = Spec.Curve25519

let u256 = lbuffer uint64 4ul
let u512 = lbuffer uint64 8ul
let u1024 = lbuffer uint64 16ul

noextract
let as_nat (h:mem) (e:u256) : GTot nat =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  S.as_nat4 (s0, s1, s2, s3)

noextract
let wide_as_nat (h:mem) (e:u512) : GTot nat =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  let s5 = s.[5] in
  let s6 = s.[6] in
  let s7 = s.[7] in
  S.wide_as_nat4 (s0, s1, s2, s3, s4, s5, s6, s7)

noextract
let fevalh (h:mem) (f:u256) : GTot P.elem = (as_nat h f) % P.prime

noextract
let feval_wideh (h:mem) (f:u512) : GTot P.elem = (wide_as_nat h f) % P.prime


[@ CInline]
val add1: out:u256 -> f1:u256  -> f2:uint64
  -> Stack uint64
    (requires fun h ->
      X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled) /\
      live h f1 /\ live h out /\
      (disjoint out f1 \/ out == f1))
    (ensures  fun h0 c h1 ->
      modifies (loc out) h0 h1 /\
      as_nat h1 out + v c * pow2 256 == as_nat h0 f1 + v f2)

[@ CInline]
val fadd: out:u256 -> f1:u256  -> f2:u256
  -> Stack unit
    (requires fun h ->
      X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled) /\    
      live h f1 /\ live h f2 /\ live h out /\
      (disjoint out f1 \/ out == f1) /\
      (disjoint out f2 \/ out == f2) /\
      (disjoint f1 f2 \/ f1 == f2))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      fevalh h1 out == P.fadd (fevalh h0 f1) (fevalh h0 f2))

[@ CInline]
val fsub: out:u256 -> f1:u256 -> f2:u256
  -> Stack unit
    (requires fun h ->
      X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled) /\    
      live h f1 /\ live h f2 /\ live h out /\
      (disjoint out f1 \/ out == f1) /\
      (disjoint out f2 \/ out == f2) /\
      (disjoint f1 f2 \/ f1 == f2))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      fevalh h1 out == P.fsub (fevalh h0 f1) (fevalh h0 f2))

[@ CInline]
val fmul: out:u256 -> f1:u256 -> f2:u256 -> tmp:u1024
  -> Stack unit
    (requires fun h ->
      X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled) /\    
      live h out /\ live h f1 /\ live h f2 /\ live h tmp /\
      (disjoint out f1 \/ out == f1) /\
      (disjoint out f2 \/ out == f2) /\
      (disjoint out tmp \/ out == tmp) /\
      (disjoint f1 f2 \/ f1 == f2) /\
      disjoint f1 tmp /\
      disjoint f2 tmp)
    (ensures  fun h0 _ h1 ->
      modifies (loc out |+| loc tmp) h0 h1 /\
      fevalh h1 out == P.fmul (fevalh h0 f1) (fevalh h0 f2))

[@ CInline]
val fmul2: out:u512 -> f1:u512 -> f2:u512 -> tmp:u1024
  -> Stack unit
    (requires fun h ->
      X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled) /\    
      live h out /\ live h f1 /\ live h f2 /\ live h tmp /\
      (disjoint out f1 \/ out == f1) /\
      (disjoint out f2 \/ out == f2) /\
      (disjoint out tmp \/ out == tmp) /\
      (disjoint f1 f2 \/ f1 == f2) /\
      disjoint f1 tmp /\
      disjoint f2 tmp)
    (ensures  fun h0 _ h1 ->
      modifies (loc out |+| loc tmp) h0 h1 /\
     (let out0 = gsub out 0ul 4ul in
      let out1 = gsub out 4ul 4ul in
      let f10 = gsub f1 0ul 4ul in
      let f11 = gsub f1 4ul 4ul in
      let f20 = gsub f2 0ul 4ul in
      let f21 = gsub f2 4ul 4ul in
      fevalh h1 out0 == P.fmul (fevalh h0 f10) (fevalh h0 f20) /\
      fevalh h1 out1 == P.fmul (fevalh h0 f11) (fevalh h0 f21)))

[@ CInline]
val fmul1: out:u256 -> f1:u256 -> f2:uint64{v f2 < pow2 17}
  -> Stack unit
    (requires fun h ->
      X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled) /\    
      live h out /\ live h f1 /\
      (disjoint out f1 \/ out == f1))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      fevalh h1 out == (fevalh h0 f1 * v f2) % P.prime)

[@ CInline]
val fsqr: out:u256 -> f1:u256 -> tmp:u512
  -> Stack unit
    (requires fun h ->
      X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled) /\    
      live h out /\ live h f1 /\ live h tmp /\
      (disjoint out f1 \/ out == f1) /\
      (disjoint out tmp \/ out == tmp) /\
      disjoint tmp f1)
    (ensures  fun h0 _ h1 ->
      modifies (loc out |+| loc tmp) h0 h1 /\
      fevalh h1 out == P.fmul (fevalh h0 f1) (fevalh h0 f1))

[@ CInline]
val fsqr2: out:u512 -> f:u512 -> tmp:u1024
  -> Stack unit
    (requires fun h ->
      X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled) /\    
      live h out /\ live h f /\ live h tmp /\
      (disjoint out f \/ out == f) /\
      (disjoint out tmp \/ out == tmp) /\
      disjoint tmp f)
    (ensures  fun h0 _ h1 ->
      modifies (loc out |+| loc tmp) h0 h1 /\
     (let out1 = gsub out 0ul 4ul in
      let out2 = gsub out 4ul 4ul in
      let f1 = gsub f 0ul 4ul in
      let f2 = gsub f 4ul 4ul in
      fevalh h1 out1 == P.fmul (fevalh h0 f1) (fevalh h0 f1) /\
      fevalh h1 out2 == P.fmul (fevalh h0 f2) (fevalh h0 f2)))

[@ CInline]
val cswap2: bit:uint64{v bit <= 1} -> p1:u512 -> p2:u512
  -> Stack unit
    (requires fun h ->
      X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled) /\    
      live h p1 /\ live h p2 /\
      (disjoint p1 p2 \/ p1 == p2))
    (ensures  fun h0 _ h1 ->
      modifies (loc p1 |+| loc p2) h0 h1 /\
      (v bit == 1 ==> as_seq h1 p1 == as_seq h0 p2 /\ as_seq h1 p2 == as_seq h0 p1) /\
      (v bit == 0 ==> as_seq h1 p1 == as_seq h0 p1 /\ as_seq h1 p2 == as_seq h0 p2))
