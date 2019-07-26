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
