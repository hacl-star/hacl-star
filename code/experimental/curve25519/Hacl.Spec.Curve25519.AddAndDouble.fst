module Hacl.Spec.Curve25519.AddAndDouble

open FStar.Mul
open Lib.IntTypes
open Spec.Curve25519

let add q nq nqp1 =
  let x_1, z_1 = q in
  let x_2, z_2 = nq in
  let x_3, z_3 = nqp1 in
  let a  = x_2 +% z_2 in
  let b  = x_2 -% z_2 in
  let c = x_3 +% z_3 in
  let d = x_3 -% z_3 in
  let da = d *% a in
  let cb = c *% b in
  let x_3 = da +% cb in
  let z_3 = da -% cb in
  let x_3 = x_3 *% x_3 in
  let z_3 = z_3 *% z_3 in
  let z_3 = z_3 *% x_1 in
  x_3, z_3

val lemma_add:
  q:proj_point -> nq:proj_point -> nqp1:proj_point ->
  Lemma (add q nq nqp1 == snd (add_and_double q nq nqp1))
let lemma_add q nq nqp1 = ()

val lemma_double:
  q:proj_point -> nq:proj_point -> nqp1:proj_point ->
  Lemma (double nq == fst (add_and_double q nq nqp1))
let lemma_double q nq nqp1 = ()

// let cswap2 (sw:uint8) (nq:proj_point) (nqp1:proj_point) =
//   let open Lib.RawIntTypes in
//   if uint_to_nat sw = 1 then (nqp1, nq) else (nq, nqp1)

let ladder_step1 (k:scalar) (q:proj_point) (i:nat{i < 251}) (nq, nqp1, swap) =
  let bit = ith_bit k (253-i) in
  let sw = swap ^. bit in
  let nq, nqp1 = cswap2 sw nq nqp1 in
  let nq, nqp1 = add_and_double q nq nqp1 in
  (nq, nqp1, bit)

let montgomery_ladder1_0 (k:scalar) (q:proj_point) (nq:proj_point) (nqp1:proj_point) =
  // bit 255 is 0 and bit 254 is 1
  let nq,nqp1 = cswap2 (u64 1) nq nqp1 in
  let nq,nqp1 = add_and_double q nq nqp1 in
  let swap = u64 1 in
  let nq,nqp1,swap = Lib.LoopCombinators.repeati 251 (ladder_step1 k q) (nq, nqp1, swap) in
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
let lemma_montgomery_ladder init k = admit()
