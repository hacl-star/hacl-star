module Hacl.Spec.EC.AddAndDouble3

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Fsquare
open Hacl.Spec.Bignum.Fmul
open Hacl.Spec.EC.AddAndDouble
open Hacl.Spec.EC.AddAndDouble2


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val lemma_op_Star_Star_def_0: x:elem -> Lemma (Spec.Curve25519.(x ** 1 = x))
#set-options "--initial_fuel 1 --max_fuel 1"
let lemma_op_Star_Star_def_0 x = ()

#set-options "--initial_fuel 0 --max_fuel 0"

val lemma_op_Star_Star_def_1: x:elem -> n:int{n > 1 /\ n % 2 = 0} -> Lemma (Spec.Curve25519.(x ** n = op_Star_Star (x *@ x) (n / 2) ))
#set-options "--initial_fuel 1 --max_fuel 1"
let lemma_op_Star_Star_def_1 x n = ()

#set-options "--initial_fuel 0 --max_fuel 0"

val lemma_Star_Star: x:elem -> Lemma (Spec.Curve25519.(x ** 2 = x *@ x))
let lemma_Star_Star x =
  assert_norm(2 / 2 = 1); assert_norm(2 % 2 = 0);
  lemma_op_Star_Star_def_1 x 2;
  lemma_op_Star_Star_def_0 (x *@ x)

val lemma_add_and_multiply: x_1:elem -> x_2:elem -> z_2:elem -> x_3:elem -> z_3:elem -> Lemma
  ( let a  = x_2 +@ z_2 in
    let aa = a *@ a in
    let b  = x_2 -@ z_2 in
    let bb = b *@ b in
    let e = aa -@ bb in
    let c = x_3 +@ z_3 in
    let d = x_3 -@ z_3 in
    let da = d *@ a in
    let cb = c *@ b in
    let x3 = (da +@ cb) *@ (da +@ cb) in
    let z3 = x_1 *@ ((da -@ cb) *@ (da -@ cb)) in
    let x2 = aa *@ bb in
    let z2 = e *@ (aa +@ (121665 *@ e)) in
    (Spec.Curve25519.Proj x2 z2, Spec.Curve25519.Proj x3 z3) ==
      Spec.Curve25519.add_and_double x_1 (Spec.Curve25519.Proj x_2 z_2) (Spec.Curve25519.Proj x_3 z_3))
let lemma_add_and_multiply x_1 x_2 z_2 x_3 z_3 =
  let a  = x_2 +@ z_2 in
  lemma_Star_Star a;
  let aa = a *@ a in
  let b  = x_2 -@ z_2 in
  lemma_Star_Star b;
  let bb = b *@ b in
  let e = aa -@ bb in
  let c = x_3 +@ z_3 in
  let d = x_3 -@ z_3 in
  let da = d *@ a in
  let cb = c *@ b in
  lemma_Star_Star (da +@ cb);
  lemma_Star_Star (da -@ cb)


val lemma_fmonty_split:   px:s_513 -> pz:s_513 -> pqx:s_513 -> pqz:s_513 -> qx:s_513 ->
  Lemma (
    let x2, z2, x3, z3 = fmonty_tot px pz pqx pqz qx in
    let x2 = selem x2 in let z2 = selem z2 in let x3 = selem x3 in let z3 = selem z3 in
    let x_2 = selem px in let z_2 = selem pz in
    let x_3 = selem pqx in let z_3 = selem pqz in let x_1 = selem qx in
    (Spec.Curve25519.Proj x2 z2, Spec.Curve25519.Proj x3 z3) ==
      Spec.Curve25519.add_and_double x_1 (Spec.Curve25519.Proj x_2 z_2) (Spec.Curve25519.Proj x_3 z_3))
let lemma_fmonty_split px pz pqx pqz qx =
  lemma_add_and_multiply (selem qx) (selem px) (selem pz) (selem pqx) (selem pqz)
