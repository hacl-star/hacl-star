module Hacl.Impl.Q.Test

open Spec.P256
open Spec.P256.Definitions
open Spec.P256.Lemmas
open Spec.P256.MontgomeryMultiplication
open FStar.Mul

open FStar.Calc
open FStar.Tactics

#set-options "--z3rlimit 200 --fuel 0 --ifuel 0" 

val lemmaBPBlinding: x0: nat -> y0: nat -> z0: nat -> r: nat 
  -> x1: nat 
  -> y1: nat  -> z1: nat -> 
  Lemma 
   (
    let resultFromDomain = fromDomain_ x1, fromDomain_ y1, fromDomain_ z1 in 
    let rnX, rnY, rnZ = _norm resultFromDomain in 
    rnX == x0)


let lemmaBPBlinding x0 y0 z0 r x1 y1 z1 =
  assert((fromDomain_ z0 * r % prime256) >= 0);
  admit();
  calc(==)
  {
   5;
    (==) {}
     5;
  };
  admit()
