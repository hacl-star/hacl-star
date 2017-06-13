module Hacl.EC.Format

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.EC.Point


type uint8_p = buffer Hacl.UInt8.t

val point_inf: unit -> StackInline point
  (requires (fun h -> true))
  (ensures (fun h0 p h1 -> modifies_0 h0 h1 /\ live h1 p))


val alloc_point: unit -> StackInline point
  (requires (fun h -> true))
  (ensures (fun h0 p h1 -> modifies_0 h0 h1 /\ live h1 p))


val point_of_scalar: scalar:buffer Hacl.UInt8.t{length scalar = keylen} -> StackInline point
  (requires (fun h -> Buffer.live h scalar))
  (ensures (fun h0 p h1 -> modifies_0 h0 h1 /\ live h1 p))


val scalar_of_point: scalar:uint8_p{length scalar = keylen} -> p:point -> Stack unit
  (requires (fun h -> Buffer.live h scalar /\ live h p))
  (ensures (fun h0 _ h1 -> modifies_1 scalar h0 h1 /\ Buffer.live h1 scalar))

val format_secret: secret:uint8_p{length secret = keylen} -> StackInline (s:uint8_p{length s = keylen})
  (requires (fun h -> Buffer.live h secret))
  (ensures (fun h0 s h1 -> Buffer.live h1 secret /\ modifies_0 h0 h1 /\ Buffer.live h1 s))
