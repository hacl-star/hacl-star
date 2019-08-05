module Hacl.Impl.Ed25519.Field56

open FStar.HyperStack

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer

open FStar.Mul

module S = Hacl.Spec.Ed25519.Field56.Definition
module P = Spec.Curve25519

open FStar.Calc

let felem = lbuffer uint64 5ul
let felem10 = lbuffer uint64 10ul
let fwide9 = lbuffer uint128 9ul

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
val as_nat10: h:mem -> e:felem10 -> GTot nat
let as_nat10 h e =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  let s5 = s.[5] in
  let s6 = s.[6] in
  let s7 = s.[7] in
  let s8 = s.[8] in
  let s9 = s.[9] in
  S.as_nat10 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9

noextract
val fevalh: h:mem -> f:felem -> GTot (n:nat{n < Spec.Ed25519.q})
let fevalh h f = (as_nat h f) % Spec.Ed25519.q

noextract
let felem_fits (h:mem) (f:felem) m =
  let s = as_seq h f in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  S.felem_fits (s0, s1, s2, s3, s4) m

noextract
val feval_wide9: h:mem -> f:fwide9 -> GTot nat
let feval_wide9 h f =
  let s = as_seq h f in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  let s5 = s.[5] in
  let s6 = s.[6] in
  let s7 = s.[7] in
  let s8 = s.[8] in
  S.eval_wide9 s0 s1 s2 s3 s4 s5 s6 s7 s8
