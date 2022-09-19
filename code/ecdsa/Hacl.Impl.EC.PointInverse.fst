module Hacl.Impl.EC.PointInverse

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.EC.LowLevel
open Spec.ECC

open Hacl.Spec.MontgomeryMultiplication
open FStar.Mul

#set-options "--fuel 0 --ifuel 0 --z3rlimit 300"


let point_inv #c p result = 
  let h0 = ST.get() in 
  push_frame();
  
  let len = getCoordinateLenU64 c in 
  let yP = sub p len len in 
  let yResult = sub result len len in 

  felem_sub_zero #c yP yResult; 
  copy (sub result (size 0) len) (sub p (size 0) len); 
  copy (sub result (size 2 *! getCoordinateLenU64 c) (getCoordinateLenU64 c)) (sub p (size 2 *! getCoordinateLenU64 c) (getCoordinateLenU64 c));
  
  pop_frame(); 

  let h1 = ST.get() in 
  lemmaFromDomain #c #DH 0
