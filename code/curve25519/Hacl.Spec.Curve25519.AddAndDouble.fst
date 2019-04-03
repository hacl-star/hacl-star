module Hacl.Spec.Curve25519.AddAndDouble

open FStar.Mul
open Lib.IntTypes
open Spec.Curve25519

val lemma_add:
  q:proj_point -> nq:proj_point -> nqp1:proj_point ->
  Lemma (add q nq nqp1 == snd (add_and_double q nq nqp1))
let lemma_add q nq nqp1 = ()

val lemma_double:
  q:proj_point -> nq:proj_point -> nqp1:proj_point ->
  Lemma (double nq == fst (add_and_double q nq nqp1))
let lemma_double q nq nqp1 = ()

let montgomery_ladder1_0 (k:scalar) (q:proj_point) (nq:proj_point) (nqp1:proj_point) =
  // bit 255 is 0 and bit 254 is 1
  let nq,nqp1 = cswap2 (u64 1) nq nqp1 in
  let nq,nqp1 = add_and_double q nq nqp1 in
  let swap = u64 1 in
  let nq,nqp1,swap = Lib.LoopCombinators.repeati 251 (ladder_step k q) (nq, nqp1, swap) in
  let nq,nqp1 = cswap2 swap nq nqp1 in
  nq

let montgomery_ladder1_1 (nq:proj_point) =
  let nq = double nq in
  let nq = double nq in
  let nq = double nq in
  nq

let montgomery_ladder1_2 (init:elem) =
  let q = (init, one) in
  let nq = (one, zero) in
  let nqp1 = (init, one) in
  q, nq, nqp1

let montgomery_ladder1 (init:elem) (k:scalar) : Tot proj_point =
  let q, nq, nqp1 = montgomery_ladder1_2 init in
  let nq = montgomery_ladder1_0 k q nq nqp1 in
  montgomery_ladder1_1 nq

val lemma_montgomery_ladder: init:elem -> k:scalar ->
  Lemma (montgomery_ladder1 init k == montgomery_ladder init k)
let lemma_montgomery_ladder init k = ()
