module Hacl.Impl.ECDSA.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.ECC
open Spec.ECC.Curves

open Hacl.Spec.EC.Definition
  
(*
val felem_add: #c: curve -> a: felem c -> b: felem c -> out: felem c -> 
  Stack unit
  (requires (fun h0 -> live h0 a /\ live h0 b /\ live h0 out /\ eq_or_disjoint a out /\  eq_or_disjoint b out /\
    as_nat c h0 a < getPrime c /\ as_nat c h0 b < getPrime c))
  (ensures (fun h0 _ h1 -> 
    modifies (loc out) h0 h1 /\ 
    as_nat c h1 out == (as_nat c h0 a + as_nat c h0 b) % getPrime c /\
    as_nat c h1 out == toDomain_ #c((fromDomain_ #c (as_nat c h0 a) + fromDomain_ #c (as_nat c h0 b)) % getPrime c)))


val lemma_felem_add: a: nat -> b: nat -> Lemma ((fromDomain_ a + fromDomain_ b) % (getOrder #P256) = fromDomain_ (a + b))



let felem_add arg1 arg2 out = 
  let t = add4 arg1 arg2 out in 
  reduction_prime_2prime_with_carry2 t out out


let lemma_felem_add a b = 
  lemmaFromDomain a;
  lemmaFromDomain b;
  lemmaFromDomain (a + b);
  assert(fromDomain_ a + fromDomain_ b = (a * modp_inv2_prime (pow2 256) prime_p256_order) % (getOrder #P256) + (b * modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order);
  let aD = a * modp_inv2_prime (pow2 256) (getOrder #P256) in 
  let bD = b * modp_inv2_prime (pow2 256) (getOrder #P256) in 
  assert(fromDomain_ (a + b) = (aD + bD) % prime_p256_order);

  lemma_mod_plus_distr_l aD bD prime_p256_order;
  lemma_mod_plus_distr_l bD (aD % prime_p256_order) prime_p256_order;
  assert(fromDomain_ (a + b) = (aD % (getOrder #P256) + bD % prime_p256_order) % prime_p256_order);

  assert(fromDomain_ (a + b) = (fromDomain_ a + fromDomain_ b) % prime_p256_order)
*)
