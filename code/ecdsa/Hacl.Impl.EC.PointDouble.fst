module Hacl.Impl.EC.PointDouble

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.EC.LowLevel
open Hacl.Spec.EC.Definition
open Spec.ECC
open Spec.ECC.Curves

open Hacl.Spec.MontgomeryMultiplication

open Hacl.Impl.EC.K.PointDouble
open Hacl.Impl.EC.General.PointDouble
open Hacl.Impl.EC.NIST.PointDouble

#set-options "--z3rlimit 300 --ifuel 0 --fuel 0" 



val point_double_p256: p: point P256 -> result: point P256
  -> tempBuffer: lbuffer uint64  (getCoordinateLenU64 P256 *! 17ul) 
  -> Stack unit
  (requires fun h -> live h p /\ live h tempBuffer /\ live h result /\
    disjoint p tempBuffer /\ disjoint result tempBuffer /\
    eq_or_disjoint p result /\ point_eval P256 h p)
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc result) h0 h1 /\ point_eval P256 h1 result /\ (      
    fromDomainPoint #P256 #DH (point_as_nat P256 h1 result) == _point_double #P256 (fromDomainPoint #P256 #DH (point_as_nat P256 h0 p))))

let point_double_p256 p result tempBuffer = Hacl.Impl.EC.NIST.PointDouble.point_double #P256 p result tempBuffer


val point_double_p384: p: point P384 -> result: point P384
  -> tempBuffer: lbuffer uint64  (getCoordinateLenU64 P384 *! 17ul) 
  -> Stack unit
  (requires fun h -> live h p /\ live h tempBuffer /\ live h result /\
    disjoint p tempBuffer /\ disjoint result tempBuffer /\
    eq_or_disjoint p result /\ point_eval P384 h p)
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc result) h0 h1 /\ point_eval P384 h1 result /\ (      
    fromDomainPoint #P384 #DH (point_as_nat P384 h1 result) == _point_double #P384 (fromDomainPoint #P384 #DH (point_as_nat P384 h0 p))))

let point_double_p384 p result tempBuffer = Hacl.Impl.EC.NIST.PointDouble.point_double #P384 p result tempBuffer


val point_double_generic: p: point Default -> result: point Default 
-> tempBuffer: lbuffer uint64  (getCoordinateLenU64 Default *! 17ul) 
  -> Stack unit
  (requires fun h -> live h p /\ live h tempBuffer /\ live h result /\
    disjoint p tempBuffer /\ disjoint result tempBuffer /\
    eq_or_disjoint p result /\ point_eval Default h p)
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc result) h0 h1 /\ point_eval Default h1 result /\ (      
    fromDomainPoint #Default #DH (point_as_nat Default h1 result) == _point_double #Default (fromDomainPoint #Default #DH (point_as_nat Default h0 p))))

let point_double_generic p result tempBuffer = Hacl.Impl.EC.General.PointDouble.point_double #Default p result tempBuffer

inline_for_extraction noextract
val point_double: #c: curve -> p: point c -> result: point c 
  -> tempBuffer: lbuffer uint64  (getCoordinateLenU64 c *! 17ul) 
  -> Stack unit
  (requires fun h -> live h p /\ live h tempBuffer /\ live h result /\
    disjoint p tempBuffer /\ disjoint result tempBuffer /\
    eq_or_disjoint p result /\ point_eval c h p)
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc result) h0 h1 /\ point_eval c h1 result /\ (      
    fromDomainPoint #c #DH (point_as_nat c h1 result) == _point_double #c (fromDomainPoint #c #DH (point_as_nat c h0 p))))


let point_double #c p result tempBuffer =
  match c with 
  |P256 -> point_double_p256 p result tempBuffer
  |P384 -> point_double_p384 p result tempBuffer
  |Default -> point_double_generic p result tempBuffer

