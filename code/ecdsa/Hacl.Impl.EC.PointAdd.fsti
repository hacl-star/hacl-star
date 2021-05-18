module Hacl.Impl.EC.PointAdd

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Spec.ECC
open Spec.ECC.Curves
open Hacl.Spec.MontgomeryMultiplication

#set-options "--z3rlimit 100"

let fromDomain #c = fromDomain_ #c #DH

[@CInline]
val point_add: #c: curve -> p: point c -> q: point c -> result: point c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h -> 
    live h p /\ live h q /\ live h result /\ live h tempBuffer /\ 
    eq_or_disjoint q result /\ disjoint p q /\ disjoint p tempBuffer /\ 
    disjoint q tempBuffer /\ disjoint p result /\ disjoint result tempBuffer /\  
    point_eval c h p /\ point_eval c h q)
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc result) h0 h1 /\ point_eval c h1 result /\
    fromDomainPoint #c #DH (point_as_nat c h1 result) == _point_add #c (fromDomainPoint #c #DH (point_as_nat c h0 p)) (fromDomainPoint #c #DH (point_as_nat c h0 q)))
