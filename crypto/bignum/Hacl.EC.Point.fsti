module Hacl.EC.Point

open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum

module U32 = FStar.UInt32

val plen: pos
val cplen: x:U32.t{plen = U32.v x}

let point : Type0 = b:buffer limb{length b = plen}

(** Coordinate getters *)
val getx: point -> Tot felem
val gety: point -> Tot felem
val getz: point -> Tot felem


(** Liveness of the point, depends on the Jacobian/Projective setup **)
val live_coords: mem -> felem -> felem -> felem -> GTot Type0
val live: mem -> point -> GTot Type0

val make: x:felem -> y:felem -> z:felem -> Tot (p:point)


(** Workable state of a point **)
val valid: mem -> point -> GTot bool

val swap_conditional:
  a:point ->
  b:point ->
  i:limb ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))

val copy:
  output:point ->
  input:point ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
