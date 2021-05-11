module Hacl.Impl.EC.Reduction

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Lib.Buffer

open Spec.ECC
open Hacl.Impl.EC.LowLevel
open Hacl.Spec.MontgomeryMultiplication

open Hacl.Impl.SolinasReduction.P384
open Hacl.Impl.SolinasReduction.P256
open Hacl.Impl.EC.MontgomeryMultiplication
open Hacl.Impl.EC.P521.Reduction

open Hacl.Spec.EC.Definition
open FStar.Mul

#reset-options "--fuel 1 --ifuel 1 --z3rlimit 100"

inline_for_extraction noextract
val upload_r2: #c: curve -> a: felem c -> Stack unit 
  (requires (fun h -> live h a))
  (ensures fun h0 _ h1 -> as_nat c h1 a == toDomain_ #c #DH (toDomain_ #c #DH 1) /\ as_nat c h1 a < getPrime c /\ modifies0 h0 h1)

let upload_r2 #c a = 
  admit()


val ml_reduction: #c: curve -> a: felem c -> b: felem c -> result: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h b /\ live h result /\ eq_or_disjoint a b /\ as_nat c h a < getPrime c /\ as_nat c h b < pow2 (getPower c)) 
  (ensures fun h0 _ h1 -> as_nat c h1 result = (as_nat c h0 a * as_nat c h0 b) % getPrime c /\ modifies (loc result) h0 h1)

let ml_reduction #c a b result = 
  push_frame();
    let len: FStar.UInt32.t = getCoordinateLenU64 c in 
    let t = create (len) (u64 0) in 
      upload_r2 #c t;
    let h0 = ST.get() in 
    montgomery_multiplication_buffer_dh #c a b result;
      let h1 = ST.get() in 
    assert(as_nat c h1 result == toDomain_ #c #DH (fromDomain_ #c #DH (as_nat c h0 a) * fromDomain_ #c #DH (as_nat c h0 b) % getPrime c)); 
    montgomery_multiplication_buffer_dh #c t result result;
      let h2 = ST.get() in 
    lemmaToDomain #c #DH 1;
    lemmaToDomainFromDomain #c #DH (toDomain_ #c #DH 1);
    lemmaToDomainFromDomain #c #DH ((fromDomain_ #c #DH (as_nat c h0 a) * fromDomain_ #c #DH (as_nat c h0 b) % getPrime c));

    pop_frame();

    let a = as_nat c h0 a in 
    let b = as_nat c h0 b in 

    let prime = getPrime c in 
    let m = modp_inv2_prime (pow2 (getPower c)) prime in 

    assert(as_nat c h2 result == toDomain_ #c #DH ((toDomain_ #c #DH 1 * (fromDomain_ #c #DH a * fromDomain_ #c #DH b % getPrime c)) % getPrime c)); 

    lemmaFromDomain #c #DH a;
    lemmaFromDomain #c #DH b;

    lemma_mod_mul_distr_r (toDomain_ #c #DH 1) (fromDomain_ #c #DH a * fromDomain_ #c #DH b) (getPrime c);
    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 

    assert(as_nat c h2 result == toDomain_ #c #DH ((pow2 (getPower c) % prime * (a * m % prime * (b * m % prime))) % prime)); 

    lemma_mod_mul_distr_l (pow2 (getPower c)) (a * m % prime * (b * m % prime)) prime;

    assert_by_tactic ((pow2 (getPower c) * (fromDomain_ #c #DH a * (b * m % prime))) == (fromDomain_ #c #DH a * pow2 (getPower c) * (b * m % prime))) canon;

    lemma_mod_mul_distr_l (fromDomain_ #c #DH a * pow2 (getPower c)) (b * m % prime) prime;
    lemmaToDomain #c #DH (fromDomain_ #c #DH a);
    lemmaFromDomainToDomain #c #DH a;

    lemmaToDomain #c #DH (a * fromDomain_ #c #DH b % prime);
    lemma_mod_mul_distr_l (a * fromDomain_ #c #DH b) (pow2 (getPower c)) prime;
    assert_by_tactic (a * fromDomain_  #c #DH b * pow2 (getPower c) == a * (fromDomain_  #c #DH b * pow2 (getPower c))) canon;
 
    lemma_mod_mul_distr_r a (fromDomain_ #c #DH b * pow2 (getPower c)) prime;
    lemmaToDomain #c #DH (fromDomain_ #c #DH b); 

    lemmaToDomainFromDomainModuloPrime #c #DH b;
    lemma_mod_mul_distr_r a b prime;
    assert(as_nat c h2 result =  a * (b % prime) % prime)

inline_for_extraction noextract
val ml_reduction1: #c: curve -> r: widefelem c -> result: felem c -> Stack unit 
  (requires fun h -> live h result /\ live h r /\ wide_as_nat c h r < getPrime c * pow2 (getPower c) /\ eq_or_disjoint r result) 
  (ensures fun h0 _ h1 -> as_nat c h1 result = wide_as_nat c h0 r % getPrime c /\ modifies (loc result |+| loc r) h0 h1)


let ml_reduction1 #c r result = 
  push_frame();
    let len: FStar.UInt32.t = getCoordinateLenU64 c in 
    let t = create (len) (u64 0) in 
      upload_r2 #c t;
    let h0 = ST.get() in 
    let len = getCoordinateLenU64 c in 
    Hacl.Impl.EC.MontgomeryMultiplication.montgomery_multiplication_reduction_dh #c r result;
      let h1 = ST.get() in 
    assert(as_nat c h1 result == fromDomain_ #c #DH (wide_as_nat c h0 r));
    montgomery_multiplication_buffer_dh #c t result result;
      let h2 = ST.get() in 
      pop_frame();

    let prime = getPrime c in 
    let p = pow2 (getPower c) in 
    lemmaToDomain #c #DH 1;
      assert(as_nat c h2 result == toDomain_ #c #DH (toDomain_ #c #DH 1 * fromDomain_ #c #DH (fromDomain_ #c #DH (wide_as_nat c h0 r)) % prime));

    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 

    calc (==) {
       toDomain_ #c #DH (toDomain_ #c #DH 1 * fromDomain_ #c #DH (fromDomain_ #c #DH (wide_as_nat c h0 r)) % prime);
       (==) {lemmaFromDomain #c #DH (fromDomain_ #c #DH (wide_as_nat c h0 r))}
       toDomain_ #c #DH ((toDomain_ #c #DH 1 * (fromDomain_ #c #DH (wide_as_nat c h0 r) * modp_inv2_prime p prime % prime)) % prime); 
       (==) {lemma_mod_mul_distr_l (toDomain_ #c #DH 1) ((fromDomain_ #c #DH (wide_as_nat c h0 r) * modp_inv2_prime p prime % prime)) prime}
       toDomain_ #c #DH ((toDomain_ #c #DH 1 * (fromDomain_ #c #DH (wide_as_nat c h0 r) * modp_inv2_prime p prime % prime)) % prime); 
       (==) {lemma_mod_mul_distr_r (toDomain_ #c #DH 1) (fromDomain_ #c #DH (wide_as_nat c h0 r) * modp_inv2_prime p prime) prime}
       toDomain_ #c #DH ((toDomain_ #c #DH 1 * (fromDomain_ #c #DH (wide_as_nat c h0 r) * modp_inv2_prime p prime)) % prime); 
       (==) {assert_by_tactic ((toDomain_ #c #DH 1 * (fromDomain_ #c #DH (wide_as_nat c h0 r) * modp_inv2_prime p prime)) == 
	 ((toDomain_ #c #DH 1 * modp_inv2_prime p prime) * fromDomain_ #c #DH (wide_as_nat c h0 r))) canon}
       toDomain_ #c #DH (((toDomain_ #c #DH 1 * modp_inv2_prime p prime) * fromDomain_ #c #DH (wide_as_nat c h0 r)) % prime); 
       (==) {lemma_mod_mul_distr_l (toDomain_ #c #DH 1 * modp_inv2_prime p prime) (fromDomain_ #c #DH (wide_as_nat c h0 r)) prime}
       toDomain_ #c #DH (((toDomain_ #c #DH 1 * modp_inv2_prime p prime % prime) * fromDomain_ #c #DH (wide_as_nat c h0 r)) % prime); 
       (==) {lemmaFromDomain #c #DH (toDomain_ #c #DH 1)}
       toDomain_ #c #DH (fromDomain_ #c #DH (wide_as_nat c h0 r) % prime); 
       (==) {inDomain_mod_is_not_mod #c #DH (fromDomain_ #c #DH (wide_as_nat c h0 r))}
       toDomain_ #c #DH (fromDomain_ #c #DH (wide_as_nat c h0 r)); 
       (==) {lemmaToDomainFromDomainModuloPrime #c #DH (wide_as_nat c h0 r)}
       (wide_as_nat c h0 r) % prime;}


let reduction #c i o =
  match c with 
    |P256 -> solinas_reduction_impl_p256 i o 
    |P384 -> solinas_reduction_impl_p384 i o
    |Default -> admit(); reduction_p521 i o
    |_ -> ml_reduction1 i o
