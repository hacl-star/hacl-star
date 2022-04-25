module Hacl.Impl.K256.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Hacl.Impl.EC.Math 

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Spec.EC.Definition
open Hacl.EC.Lemmas
open Hacl.Impl.P256.LowLevel 
open Spec.ECC
open Spec.ECC.Curves
open Lib.Loops

open Hacl.Impl.P256.MM.Lemmas

open Hacl.Impl.EC.MontgomeryMultiplication
open Hacl.Spec.MontgomeryMultiplication


#set-options "--z3rlimit 100 --ifuel 0 --fuel 0"


[@ CInline]
assume val exponent_k256: a: felem P256 -> result: felem P256 -> tempBuffer: lbuffer uint64 (getCoordinateLenU P256 *. 8ul) -> Stack unit
  (requires fun h -> live h a /\ live h tempBuffer /\ live h result)
  (ensures fun h0 _ h1 -> modifies2 result tempBuffer h0 h1)
