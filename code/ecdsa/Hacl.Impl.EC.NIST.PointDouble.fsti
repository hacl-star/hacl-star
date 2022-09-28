module Hacl.Impl.EC.NIST.PointDouble

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.ECC
open Spec.ECC.Curves

open Hacl.Impl.EC.LowLevel
open Hacl.Spec.EC.Definition


open Hacl.Spec.MontgomeryMultiplication

inline_for_extraction noextract
val point_double: #c: curve -> p: point c -> result: point c 
  -> tempBuffer: lbuffer uint64  (getCoordinateLenU64 c *! 17ul) 
  -> Stack unit
  (requires fun h -> live h p /\ live h tempBuffer /\ live h result /\
    disjoint p tempBuffer /\ disjoint result tempBuffer /\
    eq_or_disjoint p result /\ point_eval c h p)
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc result) h0 h1 /\ point_eval c h1 result /\ (      
    fromDomainPoint #c #DH (point_as_nat c h1 result) == _point_double #c (fromDomainPoint #c #DH (point_as_nat c h0 p))))
