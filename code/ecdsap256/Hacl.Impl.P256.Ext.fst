module Hacl.Impl.P256.Ext

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

open Lib.IntTypes
open Lib.Buffer

open Spec.P256.Definitions
open Hacl.Spec.P256.Felem
open Spec.P256

open Hacl.Impl.P256.Core
open Hacl.Impl.P256.Signature.Common


open FStar.Mul
open Spec.P256.MontgomeryMultiplication


#set-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 0" 


val point_to_bin: p: point -> result: lbuffer uint8 (size 64) ->
  Stack uint64 
  (requires fun h -> live h p /\ live h result /\ disjoint p result /\
    point_x_as_nat h p < prime /\
    point_y_as_nat h p < prime /\
    point_z_as_nat h p < prime)
  (ensures fun h0 r h1 -> modifies (loc result |+| loc p) h0 h1 /\ (
    let x, y, z = point_prime_to_coordinates (as_seq h0 p) in 
    if Spec.P256.isPointAtInfinity (x, y, z) then uint_v r = maxint U64 else uint_v r = 0 /\ (
    let oX = gsub result (size 0) (size 32) in 
    let oY = gsub result (size 32) (size 32) in 

    as_seq h1 oX == Lib.ByteSequence.nat_to_bytes_be 32 x /\ 
    as_seq h1 oY == Lib.ByteSequence.nat_to_bytes_be 32 y)))


let point_to_bin p result = 
  let isPointAtInfinityResult = isPointAtInfinityPrivate p in 
  fromFormPoint p result; 
  isPointAtInfinityResult




