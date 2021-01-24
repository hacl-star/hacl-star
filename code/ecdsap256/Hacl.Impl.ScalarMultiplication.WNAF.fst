module Hacl.Impl.ScalarMultiplication.WNAF

open FStar.HyperStack.All
open FStar.HyperStack

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes

open Lib.Buffer

open Lib.IntTypes.Intrinsics
open Hacl.Impl.P256.Q.PrimitivesMasking


open Spec.P256.Definitions
open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Hacl.Impl.P256.PointDouble
open Hacl.Impl.P256.PointAdd
open Hacl.Impl.P256.MixedPointAdd


inline_for_extraction noextract
val copy_point: p: point -> result: point -> Stack unit 
  (requires fun h -> live h p /\ live h result /\ disjoint p result) 
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_seq h1 result == as_seq h0 p)

let copy_point p result = copy result p


val precomputePoints: b: lbuffer uint64 (size 192) -> publicKey: point ->
  tempBuffer: lbuffer uint64 (size 88) -> Stack unit  
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let precomputePoints b publicKey tempBuffer = 
  let point0 = sub b (size 0) (size 12) in 
  let point1 = sub b (size 12) (size 12) in 
  let point2 = sub b (size 24) (size 12) in 
  let point3 = sub b (size 36) (size 12) in 
  let point4 = sub b (size 48) (size 12) in 
  let point5 = sub b (size 60) (size 12) in 
  let point6 = sub b (size 72) (size 12) in 
  let point7 = sub b (size 84) (size 12) in 
  let point8 = sub b (size 96) (size 12) in 
  let point9 = sub b (size 108) (size 12) in 
  let point10 = sub b (size 120) (size 12) in 
  let point11 = sub b (size 132) (size 12) in 
  let point12 = sub b (size 144) (size 12) in 
  let point13 = sub b (size 156) (size 12) in 
  let point14 = sub b (size 168) (size 12) in 
  let point15 = sub b (size 180) (size 12) in 

  copy_point publicKey point0;
  point_double point0 point15 tempBuffer;

  point_add point0 point15 point1 tempBuffer;
  point_add point1 point15 point2 tempBuffer;
  point_add point2 point15 point3 tempBuffer;
  point_add point3 point15 point4 tempBuffer;
  point_add point4 point15 point5 tempBuffer;
  point_add point5 point15 point6 tempBuffer;
  point_add point6 point15 point7 tempBuffer;
  point_add point7 point15 point8 tempBuffer;
  point_add point8 point15 point9 tempBuffer;
  point_add point9 point15 point10 tempBuffer;
  point_add point10 point15 point11 tempBuffer;
  point_add point11 point15 point12 tempBuffer;
  point_add point12 point15 point13 tempBuffer;
  point_add point13 point15 point14 tempBuffer;
  point_add point14 point15 point15 tempBuffer
  



val scalar_multiplication_cmb:  #buf_type: buftype -> result: point -> 
  publicKey: point ->
  scalar: lbuffer_t buf_type uint8 (size 32) -> 
  tempBuffer:  lbuffer uint64 (size 88)  -> 
  Stack unit
  (requires fun h -> True )
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1)


let scalar_multiplication_cmb #buf_type result pk scalar tempBuffer = 
  push_frame();
    let precomputedBuffer = create (size 192) (u64 0) in 
    precomputePoints precomputedBuffer pk tempBuffer ;
  


  pop_frame()
