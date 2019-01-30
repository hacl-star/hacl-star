module NatPrime

open FStar.Mul
open Lib.IntTypes

let prime:pos =
  assert_norm (pow2 130 - 5 > 0);
  pow2 130 - 5

let felem = x:nat{x < prime}

val fadd: felem -> felem -> felem
let fadd f1 f2 = (f1 + f2) % prime

val fmul: felem -> felem -> felem
let fmul f1 f2 = (f1 * f2) % prime
