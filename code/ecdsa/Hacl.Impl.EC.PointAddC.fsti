module Hacl.Impl.EC.PointAddC

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.EC.MontgomeryMultiplication
open Spec.ECC
open Hacl.Spec.EC.Definition

open Spec.ECC.Curves

open Hacl.Spec.MontgomeryMultiplication
open FStar.Mul


inline_for_extraction
val point_add_c: #c: curve -> p: point c -> q: point c -> result: point c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) -> 
   Stack unit (requires fun h -> live h p /\ live h q /\ live h result /\ live h tempBuffer /\ 
     disjoint q result /\ disjoint p q /\ disjoint p tempBuffer /\ 
     disjoint q tempBuffer /\ disjoint p result /\ disjoint result tempBuffer /\ 
     point_eval c h p /\ point_eval c h q /\ ~ (isPointAtInfinity (point_as_nat c h q)))
   (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc result) h0 h1 /\ point_eval c h1 result /\ (
     let pD = fromDomainPoint #c #DH (point_as_nat c h0 p) in 
     let qD = fromDomainPoint #c #DH (point_as_nat c h0 q) in 
     fromDomainPoint #c #DH (point_as_nat c h1 result) == pointAdd #c pD qD))


inline_for_extraction noextract
val point_add_c_ct: #c: curve -> p: point c -> q: point c -> result: point c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) -> 
   Stack unit (requires fun h -> live h p /\ live h q /\ live h result /\ live h tempBuffer /\ 
     eq_or_disjoint q result /\ disjoint p q /\ disjoint p tempBuffer /\ 
     disjoint q tempBuffer /\ disjoint p result /\ disjoint result tempBuffer /\ 
     point_eval c h p /\ point_eval c h q /\ ~ (isPointAtInfinity (point_as_nat c h p)) /\ 
     ~ (isPointAtInfinity (point_as_nat c h q)))
   (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc result) h0 h1 /\ point_eval c h1 result /\ (
     let pD = fromDomainPoint #c #DH (point_as_nat c h0 p) in 
     let qD = fromDomainPoint #c #DH (point_as_nat c h0 q) in 
     fromDomainPoint #c #DH (point_as_nat c h1 result) == pointAdd #c pD qD))



inline_for_extraction noextract
val point_add_c_out: #c: curve -> p: point c -> q: point c -> result: point c ->
  Stack unit (requires fun h -> live h p /\ live h q /\ live h result /\ 
  disjoint q result /\ disjoint p q /\ disjoint p result /\
     point_eval c h p /\ point_eval c h q /\ ~ (isPointAtInfinity (point_as_nat c h p)) /\ 
     ~ (isPointAtInfinity (point_as_nat c h q)))
   (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ point_eval c h1 result /\ (
     let pD = fromDomainPoint #c #DH (point_as_nat c h0 p) in 
     let qD = fromDomainPoint #c #DH (point_as_nat c h0 q) in 
     fromDomainPoint #c #DH (point_as_nat c h1 result) == pointAdd #c pD qD))


inline_for_extraction noextract
val point_add_c_ct_out: #c: curve -> p: point c -> q: point c -> result: point c ->
  Stack unit (requires fun h -> live h p /\ live h q /\ live h result /\ 
    eq_or_disjoint q result /\ disjoint p q /\ disjoint p result /\
     point_eval c h p /\ point_eval c h q /\ ~ (isPointAtInfinity (point_as_nat c h p)) /\ 
     ~ (isPointAtInfinity (point_as_nat c h q)))
   (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ point_eval c h1 result /\ (
     let pD = fromDomainPoint #c #DH (point_as_nat c h0 p) in 
     let qD = fromDomainPoint #c #DH (point_as_nat c h0 q) in 
     fromDomainPoint #c #DH (point_as_nat c h1 result) == pointAdd #c pD qD))
