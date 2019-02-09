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
