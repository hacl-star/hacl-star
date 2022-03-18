module Hacl.Impl.EC.PointAddMixed

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

inline_for_extraction noextract
val point_add_mixed: #c: curve -> p: point c -> q: pointAffine c -> result: point c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h -> 
    live h p /\ live h q /\ live h result /\ live h tempBuffer /\ 
    eq_or_disjoint p result /\ disjoint p q /\ disjoint p tempBuffer /\ 
    disjoint q tempBuffer /\ disjoint q result /\ disjoint result tempBuffer /\  
    point_eval c h p /\ point_aff_eval c h q)
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc result) h0 h1 /\ point_eval c h1 result /\ (
    let qD = fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h0 q)) in 
    fromDomainPoint #c #DH (point_as_nat c h1 result) == 
    _point_add_mixed #c  (fromDomainPoint #c #DH (point_as_nat c h0 p)) qD))
