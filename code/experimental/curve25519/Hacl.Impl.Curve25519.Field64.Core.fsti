module Hacl.Impl.Curve25519.Field64.Core

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer

module B = Lib.Buffer
module S = Hacl.Spec.Curve25519.Field64.Definition

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
let fevalh (h:mem) (f:u256) : GTot S.felem = (as_nat h f) % S.prime

noextract
let feval_wideh (h:mem) (f:u512) : GTot S.felem = (wide_as_nat h f) % S.prime


[@ CInline]
val add1: out:u256 -> f1:u256  -> f2:uint64
  -> Stack uint64
    (requires fun h -> live h f1 /\ live h out)
    (ensures  fun h0 c h1 ->
      modifies (loc out) h0 h1 /\
      as_nat h1 out + v c * pow2 256 == as_nat h0 f1 + v f2)

[@ CInline]
val fadd: out:u256 -> f1:u256  -> f2:u256
  -> Stack unit
    (requires fun h -> live h f1 /\ live h f2 /\ live h out)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      fevalh h1 out == S.fadd (fevalh h0 f1) (fevalh h0 f2))

[@ CInline]
val fsub: out:u256 -> f1:u256 -> f2:u256
  -> Stack unit
    (requires fun h -> live h f1 /\ live h f2 /\ live h out)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      fevalh h1 out == S.fsub (fevalh h0 f1) (fevalh h0 f2))

[@ CInline]
val fmul: out:u256 -> f1:u256 -> f2:u256
  -> Stack unit
    (requires fun h -> live h out /\ live h f1 /\ live h f2)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      fevalh h1 out == S.fmul (fevalh h0 f1) (fevalh h0 f2))

[@ CInline]
val fmul2: out:u512 -> f1:u512 -> f2:u512
  -> Stack unit
    (requires fun h -> live h out /\ live h f1 /\ live h f2)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
     (let out0 = gsub out 0ul 4ul in
      let out1 = gsub out 4ul 4ul in
      let f10 = gsub f1 0ul 4ul in
      let f11 = gsub f1 4ul 4ul in
      let f20 = gsub f2 0ul 4ul in
      let f21 = gsub f2 4ul 4ul in
      fevalh h1 out0 == S.fmul (fevalh h0 f10) (fevalh h0 f20) /\
      fevalh h1 out1 == S.fmul (fevalh h0 f11) (fevalh h0 f21)))

[@ CInline]
val fmul1: out:u256 -> f1:u256 -> f2:uint64{v f2 < pow2 17}
  -> Stack unit
    (requires fun h -> live h out /\ live h f1)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      fevalh h1 out == (fevalh h0 f1 * v f2) % S.prime)

[@ CInline]
val fsqr: out:u256 -> f1:u256
  -> Stack unit
    (requires fun h -> live h out /\ live h f1)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      fevalh h1 out == S.fsqr (fevalh h0 f1))

[@ CInline]
val fsqr2: out:u512 -> f:u512
  -> Stack unit
    (requires fun h -> live h out /\ live h f)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
     (let out1 = gsub out 0ul 4ul in
      let out2 = gsub out 4ul 4ul in
      let f1 = gsub f 0ul 4ul in
      let f2 = gsub f 4ul 4ul in
      fevalh h1 out1 == S.fsqr (fevalh h0 f1) /\
      fevalh h1 out2 == S.fsqr (fevalh h0 f2)))
