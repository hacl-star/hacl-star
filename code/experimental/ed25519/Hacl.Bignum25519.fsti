module Hacl.Bignum25519

#set-options "--lax"

val red_51: Hacl.Bignum.Parameters.seqelem -> GTot Type0
val red_513: Hacl.Bignum.Parameters.seqelem -> GTot Type0
val red_53: Hacl.Bignum.Parameters.seqelem -> GTot Type0
val red_5413: Hacl.Bignum.Parameters.seqelem -> GTot Type0

(* abstract let red_513 s = Hacl.Spec.EC.AddAndDouble.red_513 s *)
(* abstract let red_53 s = Hacl.Spec.EC.AddAndDouble.red_53 s *)
(* abstract let red_5413 s = Hacl.Spec.EC.AddAndDouble.red_5413 s *)

let felem = Hacl.Bignum.Parameters.felem

val fsum:
  a:felem ->
  b:felem ->
  St unit

val fdifference:
  a:felem ->
  b:felem ->
  St unit

val reduce_513:
  a:felem -> 
  St unit

val fdifference_reduced:
  a:felem -> 
  b:felem -> 
  St unit

val fmul:
  out:felem ->
  a:felem ->
  b:felem ->
  St unit

val times_2:
  out:felem ->
  a:felem ->
  St unit

val times_d:
  out:felem ->
  a:felem ->
  St unit

val times_2d:
  out:felem ->
  a:felem ->
  St unit

val fsquare:
  out:felem ->
  a:felem ->
  St unit

val fsquare_times:
  out:felem ->
  a:felem ->
  n:UInt32.t ->
  St unit

val fsquare_times_inplace:
  out:felem ->
  n:UInt32.t ->
  St unit

val inverse:
  out:felem ->
  a:felem ->
  St unit

val reduce:
  out:felem ->
  St unit
