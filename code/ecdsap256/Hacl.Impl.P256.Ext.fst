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


#set-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 0" 

(** 
The function takes as input a point as a buffer of uint64.
It moves the point out of domain, normalises it and writes it down to a uint8 buffer.
I think. 
**)


val point_to_bin: p: point -> result: lbuffer uint8 (size 64) -> tempBuffer: lbuffer uint64 (size 88) ->
  Stack uint64 
  (requires fun h -> live h p /\ live h result /\ live h tempBuffer /\ disjoint tempBuffer p /\ disjoint p result /\
    point_x_as_nat h p < prime /\
    point_y_as_nat h p < prime /\
    point_z_as_nat h p < prime)
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1)


let point_to_bin p result tempBuffer = 
    let h0 = ST.get() in 
  norm p p tempBuffer;
    let h1 = ST.get() in 
  let isPointAtInfinityResult = isPointAtInfinityPrivate p in 
  fromFormPoint p result; 
  isPointAtInfinityResult
