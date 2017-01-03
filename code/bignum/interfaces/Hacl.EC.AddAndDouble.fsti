module Hacl.EC.AddAndDouble

open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.EC.Point

val fmonty:
  pp:point ->
  ppq:point ->
  p:point ->
  pq:point ->
  q:point ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
