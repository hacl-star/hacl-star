module Hacl.Bignum25519

#set-options "--lax"

abstract let red_513 s = Hacl.Spec.EC.AddAndDouble.red_513 s
abstract let red_53 s = Hacl.Spec.EC.AddAndDouble.red_53 s
abstract let red_5413 s = Hacl.Spec.EC.AddAndDouble.red_5413 s

let felem = Hacl.Bignum.Parameters.felem

val fsum:
  a:felem ->
  b:felem ->
  St unit
let fsum a b = Hacl.Bignum.fsum a b

val fdifference:
  a:felem ->
  b:felem ->
  St unit
let fdifference a b = Hacl.Bignum.fdifference a b

val reduce_513:
  a:felem -> 
  St unit
let reduce_513 a =
  Hacl.Bignum.Fproduct.carry_limb_ a 0ul;
  Hacl.Bignum.Modulo.carry_top a;
  Hacl.Bignum.Fproduct.carry_0_to_1 a

val fdifference_reduced:
  a:felem -> 
  b:felem -> 
  St unit
let fdifference_reduced a b =
  Hacl.Bignum.fdifference a b;
  reduce_513 a

val fmul:
  out:felem ->
  a:felem ->
  b:felem ->
  St unit
let fmul out a b = Hacl.Bignum.fmul out a b

val times_2:
  out:felem ->
  a:felem ->
  St unit
let times_2 out a =
  Hacl.Bignum.fscalar out a (Hacl.Cast.uint64_to_sint64 2uL)

val times_d:
  out:felem ->
  a:felem ->
  St unit
let times_d out a =
  push_frame();
  let d = Buffer.createL [0x00034dca135978a3uL; 0x0001a8283b156ebduL; 0x0005e7a26001c029uL; 
                          0x000739c663a03cbbuL; 0x00052036cee2b6ffuL] in
  fmul out a d;
  pop_frame()

val times_2d:
  out:felem ->
  a:felem ->
  St unit
let times_2d out a =
  push_frame();
  let d2 = Buffer.createL [0x00069b9426b2f159uL; 0x00035050762add7auL; 0x0003cf44c0038052uL;
                           0x0006738cc7407977uL; 0x0002406d9dc56dffuL] in
  fmul out a d2;
  pop_frame()

val fsquare:
  out:felem ->
  a:felem ->
  St unit
let fsquare out a =
  Hacl.Bignum.Fsquare.fsquare_times out a 1ul

val fsquare_times:
  out:felem ->
  a:felem ->
  n:UInt32.t ->
  St unit
let fsquare_times out a n =
  Hacl.Bignum.Fsquare.fsquare_times out a n

val inverse:
  out:felem ->
  a:felem ->
  St unit
let inverse out a =
  Hacl.Bignum.Crecip.crecip out a
