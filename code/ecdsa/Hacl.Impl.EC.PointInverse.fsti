module Hacl.Impl.EC.PointInverse

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.ECC
open Spec.ECC.Curves
open Hacl.Spec.EC.Definition
open Hacl.Spec.MontgomeryMultiplication

module Def = Hacl.Spec.EC.Definition

inline_for_extraction noextract
val point_inv: #c: curve -> p: Def.point c -> result: Def.point c -> Stack unit
  (requires fun h -> live h p /\ live h result /\ disjoint p result /\ point_eval c h p)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ point_eval c h1 result /\
    fromDomainPoint #c #DH (point_as_nat c h1 result) == _point_inverse #c (fromDomainPoint #c #DH (point_as_nat c h0 p)))

