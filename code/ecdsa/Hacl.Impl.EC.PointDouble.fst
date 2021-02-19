module Hacl.Impl.EC.PointDouble

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
(* open Hacl.Impl.P256.Arithmetics *)

open Lib.Buffer

open Hacl.Lemmas.P256
open Hacl.Spec.P256.Definition
(* open Hacl.Impl.SolinasReduction *)
open Hacl.Spec.P.MontgomeryMultiplication
open Hacl.Impl.EC.LowLevel
open Hacl.Impl.P256.MontgomeryMultiplication
open Spec.P256
open Hacl.Impl.P256.Math 

open Hacl.Impl.P.PointDouble


val point_double: #c: curve -> p: point c -> result: point c 
  -> tempBuffer: lbuffer uint64  (getCoordinateLenU64 c *! 17ul) 
  -> Stack unit
    (requires fun h -> live h p /\ live h tempBuffer /\ live h result /\
      disjoint p tempBuffer /\ disjoint result tempBuffer /\
      eq_or_disjoint p result /\ point_eval c h p)
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc result) h0 h1 /\  
    (
      point_eval c h1 result /\ (
      
      let x, y, z = point_x_as_nat c h0 p, point_y_as_nat c h0 p, point_z_as_nat c h0 p in 
      let x3, y3, z3 = point_x_as_nat c h1 result, point_y_as_nat c h1 result, point_z_as_nat c h1 result in       
      let xD, yD, zD = fromDomain_ #c x, fromDomain_ #c y, fromDomain_ #c z in 
      let x3D, y3D, z3D = fromDomain_ #c x3, fromDomain_ #c y3, fromDomain_ #c z3 in
      let xN, yN, zN = _point_double #c (xD, yD, zD) in 
      x3D == xN /\ y3D == yN /\ z3D == zN )))


let point_double #c p result tempBuffer = 
	match c with 
	|P256 -> Hacl.Impl.P.PointDouble.point_double p result tempBuffer
	|P384 -> Hacl.Impl.P.PointDouble.point_double p result tempBuffer