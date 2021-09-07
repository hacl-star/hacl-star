module Hacl.Impl.P256.PointInverse

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.P256.Arithmetics

open Lib.Buffer
open Spec.P256

open Spec.P256.Lemmas
open Spec.P256.Definitions
open Hacl.Spec.P256.Felem
open Spec.P256.MontgomeryMultiplication

open FStar.Mul 

#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

val copyH: a: felem -> b: felem -> Stack unit 
  (requires fun h -> live h a /\ live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ as_nat h1 b == as_nat h0 a /\ 
    fromDomain_ (as_nat h1 b) == fromDomain_ (as_nat h0 a))

let copyH a b = 
  assert_norm (pow2 64 * pow2 64 == pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 == pow2 192);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 == pow2 256);

  let a0 = index a (size 0) in 
  let a1 = index a (size 1) in 
  let a2 = index a (size 2) in 
  let a3 = index a (size 3) in 
  
  upd b (size 0) a0;
  upd b (size 1) a1;
  upd b (size 2) a2;
  upd b (size 3) a3


let point_inv p result = 
  push_frame();
    let temp4 = create (size 4) (u64 0) in 
  let h0 = ST.get() in 
  let yP = sub p (size 4) (size 4) in 
  let yResult = sub result (size 4) (size 4) in 

  Hacl.Impl.P256.LowLevel.PrimeSpecific.p256_sub_zero yP yResult temp4;
  copyH (sub p (size 0) (size 4)) (sub result (size 0) (size 4)); 
  copyH (sub p (size 8) (size 4)) (sub result (size 8) (size 4));
  
  pop_frame();

  let h1 = ST.get() in 
  lemmaFromDomain 0;
  FStar.Math.Lemmas.small_mod 0 prime256
