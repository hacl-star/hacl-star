module NatPrime

open FStar.Mul
open Lib.IntTypes

let prime:pos =
  assert_norm (pow2 255 - 19 > 0);
  pow2 255 - 19

let felem = x:nat{x < prime}

val fadd: felem -> felem -> felem
let fadd f1 f2 = (f1 + f2) % prime

val fsub: felem -> felem -> felem
let fsub f1 f2 = (f1 - f2) % prime

val fmul: felem -> felem -> felem
let fmul f1 f2 = (f1 * f2) % prime

val fsqr: felem -> felem
let fsqr f1 = (f1 * f1) % prime
