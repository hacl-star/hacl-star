module Hacl.Impl.ECDSA.MM.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas
open Hacl.Impl.EC.Math 

open Hacl.Impl.EC.LowLevel 
open Hacl.EC.Lemmas
open FStar.Tactics
open FStar.Tactics.Canon 

open Hacl.Impl.EC.MontgomeryMultiplication
open FStar.Mul

open Lib.Loops
open Hacl.Spec.EC.Definition

open Hacl.Impl.ECDSA.Setup
open Hacl.Impl.EC.MM.Exponent


#set-options " --z3rlimit 200 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val montgomery_ladder_exponent_: #c: curve -> a: felem c -> r: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h r /\ as_nat c h a < getOrder #c)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc r) h0 h1 /\ (
    let b_ = fromDomain_ #c #DSA (as_nat c h0 a) in 
    let r0D = exponent_spec #c b_ in 
    fromDomain_ #c #DSA (as_nat c h1 r) == r0D /\
    as_nat c h1 r < getOrder #c))

let montgomery_ladder_exponent_ #c a r = 
  recall_contents (order_inverse_buffer #c) (prime_order_inverse_seq #c);
  montgomery_ladder_power_dsa #c a (order_inverse_buffer #c) r

[@CInline]
let montgomery_ladder_exponent_dsa_p256 = montgomery_ladder_exponent_ #P256
[@CInline]
let montgomery_ladder_exponent_dsa_p384 = montgomery_ladder_exponent_ #P384

(* [@CInline]
let montgomery_ladder_exponent_dsa_generic = montgomery_ladder_exponent_ #Default

 *)
let montgomery_ladder_exponent #c a r = 
  match c with 
  |P256 -> montgomery_ladder_exponent_dsa_p256 a r
  |P384 -> montgomery_ladder_exponent_dsa_p384 a r 
  (* |Default -> montgomery_ladder_exponent_dsa_generic a r *)



let fromDomainImpl #c a result = 
  let h0 = ST.get() in 
  push_frame();
    let len = getCoordinateLenU64 c in 
    let one = create len (u64 0) in 
    uploadOneImpl #c one;
    montgomery_multiplication_buffer_dsa one a result;
    lemmaFromDomain #c #DSA (as_nat c h0 a);
  pop_frame()


val lemma_multPower: #c: curve -> a: nat -> b: nat -> Lemma (
  let order = getOrder #c in 
  toDomain_ #c #DSA (exponent_spec #c (fromDomain_ #c #DSA (fromDomain_ #c #DSA a)) * fromDomain_ #c #DSA (fromDomain_ #c #DSA (fromDomain_ #c #DSA b)) % order) == 
  (pow a (order - 2) * b) % order)

let lemma_multPower #c a b = 
let order = getOrder #c in 
  let r = modp_inv2_prime (pow2 (getPower c)) order in  

  lemma_exp_not_zero order (pow2 (getPower c) % order) (order - 2);
  Hacl.Impl.EC.Math.lemma_a_not_zero_b_not_zero_mod_not_zero order (r % order) (r % order);
  lemma_mod_mul_distr_l r (r % order) order;
  lemma_mod_mul_distr_r r r order;

  calc (==) {
    pow (r * r) (order - 2) * r * r % order;
    (==) {assert_by_tactic (pow (r * r) (order - 2) * r * r == (r * r) * pow (r * r) (order - 2)) canon} 
    (r * r) * pow (r * r) (order - 2) % order; 
    (==) {lemma_mod_mul_distr_r (r * r) (pow (r * r) (order - 2)) order}
    (r * r) * (pow (r * r) (order - 2) % order) % order;  
    (==) {power_distributivity (r * r) (order - 2) order}
    (r * r) * (pow (r * r % order) (order - 2) % order) % order; 
    (==) {lemma_pow_mod_n_is_fpow order (r * r % order) (order - 2)}
    (r * r) * (Spec.ECC.Curves.modp_inv2_prime (r * r) order) % order; 
    (==) {Hacl.Spec.MontgomeryMultiplication.lemma_mod_inv2_mult_prime order (r * r)}
    1;};


  calc (==) {
    toDomain_ #c #DSA (exponent_spec #c (fromDomain_ #c #DSA (fromDomain_ #c #DSA a)) * fromDomain_ #c #DSA (fromDomain_ #c #DSA (fromDomain_ #c #DSA b)) % order);
    (==) {} 
    toDomain_ #c #DSA (pow (fromDomain_ #c #DSA (fromDomain_ #c #DSA a)) (order - 2) % order * fromDomain_ #c #DSA (fromDomain_ #c #DSA (fromDomain_ #c #DSA b)) % order); 
    (==) {lemmaFromDomain #c #DSA a}
    toDomain_ #c #DSA (pow (fromDomain_ #c #DSA (a * r % order)) (order - 2) % order * fromDomain_ #c #DSA (fromDomain_ #c #DSA (fromDomain_ #c #DSA b)) % order); 
    (==) {lemmaFromDomain #c #DSA (a * r % order)}
    toDomain_ #c #DSA (pow ((a * r % order * r % order)) (order - 2) % order * fromDomain_ #c #DSA (fromDomain_ #c #DSA (fromDomain_ #c #DSA b)) % order); 
    (==) {lemma_mod_mul_distr_l (a * r) r order}
    toDomain_ #c #DSA (pow (a * r * r % order) (order - 2) % order * fromDomain_ #c #DSA (fromDomain_ #c #DSA (fromDomain_ #c #DSA b)) % order); 
    (==) {power_distributivity (a * r * r) (order - 2) order}
    toDomain_ #c #DSA (pow (a * r * r) (order - 2) % order * fromDomain_ #c #DSA (fromDomain_ #c #DSA (fromDomain_ #c #DSA b)) % order); 
    (==) {assert_by_tactic (a * r * r == a * (r * r)) canon}
    toDomain_ #c #DSA (pow (a * (r * r)) (order - 2) % order * fromDomain_ #c #DSA (fromDomain_ #c #DSA (fromDomain_ #c #DSA b)) % order); 
    (==) {lemmaFromDomain #c #DSA b; lemmaFromDomain #c #DSA (b * r % order)}
    toDomain_ #c #DSA (pow (a * (r * r)) (order - 2) % order * fromDomain_ #c #DSA ((b * r % order) * r % order) % order); 
    (==) {power_distributivity_2 a (r * r) (order - 2)}
    toDomain_ #c #DSA ((pow a (order - 2) * pow (r * r) (order - 2)) % order * fromDomain_ #c #DSA ((b * r % order) * r % order) % order); 
    (==) {lemma_mod_mul_distr_l (pow a (order - 2) * pow (r * r) (order - 2)) (fromDomain_ #c #DSA ((b * r % order) * r % order)) order}
    toDomain_ #c #DSA (pow a (order - 2) * pow (r * r) (order - 2) * fromDomain_ #c #DSA ((b * r % order) * r % order) % order); 
    (==) {lemmaFromDomain #c #DSA ((b * r % order) * r % order)}
    toDomain_ #c #DSA (pow a (order - 2) * pow (r * r) (order - 2) * ((b * r % order) * r % order * r % order) % order); 
    (==) {lemma_mod_mul_distr_l (b * r) r order}
    toDomain_ #c #DSA (pow a (order - 2) * pow (r * r) (order - 2) * (b * r * r % order * r % order) % order); 
    (==) {lemma_mod_mul_distr_l (b * r * r) r order}
    toDomain_ #c #DSA (pow a (order - 2) * pow (r * r) (order - 2) * (b * r * r * r % order) % order); 
    (==) {lemma_mod_mul_distr_r (pow a (order - 2) * pow (r * r) (order - 2)) (b * r * r * r) order}
    toDomain_ #c #DSA (pow a (order - 2) * pow (r * r) (order - 2) * (b * r * r * r) % order); 
    (==) {assert_by_tactic (pow a (order - 2) * pow (r * r) (order - 2) * (b * r * r * r) == 
      (r * (pow a (order - 2) * b * (pow (r * r) (order - 2) * r * r)))) canon}
    toDomain_ #c #DSA (r * (pow a (order - 2) * b * (pow (r * r) (order - 2) * r * r)) % order); 
    (==) {lemmaFromDomain #c #DSA ((pow a (order - 2) * b * (pow (r * r) (order - 2) * r * r)))}
    toDomain_ #c #DSA (fromDomain_ #c #DSA (pow a (order - 2) * b * (pow (r * r) (order - 2) * r * r))); 
    (==) {lemmaToDomainFromDomainModuloPrime #c #DSA (pow a (order - 2) * b * (pow (r * r) (order - 2) * r * r))}
    (pow a (order - 2) * b * (pow (r * r) (order - 2) * r * r)) % order; 
    (==) {lemma_mod_mul_distr_r (pow a (order - 2) * b) (pow (r * r) (order - 2) * r * r) order}
    (pow a (order - 2) * b * (pow (r * r) (order - 2) * r * r % order)) % order;}



let multPower #c a b result = 
  push_frame();
  let len = getCoordinateLenU64 c in 
  let tempB1 = create len (u64 0) in 
  let buffFromDB = create len (u64 0) in 
    let h0 = ST.get() in 
  fromDomainImpl #c a tempB1;
  fromDomainImpl #c b buffFromDB;
    let h1 = ST.get() in 
  fromDomainImpl #c buffFromDB buffFromDB;
    let h2 = ST.get() in 
  montgomery_ladder_exponent #c tempB1 tempB1;
  montgomery_multiplication_buffer_dsa tempB1 buffFromDB result;
    let h3 = ST.get() in 
    pop_frame();

  lemma_multPower #c (as_nat c h0 a) (as_nat c h0 b)


let multPowerPartial #c s a b result = 
  let h0 = ST.get() in 
  push_frame();
    let len = getCoordinateLenU64 c in 
    let buffFromDB = create len (u64 0) in 
    fromDomainImpl #c b buffFromDB;
    fromDomainImpl #c buffFromDB buffFromDB;
    montgomery_multiplication_buffer_dsa a buffFromDB result;
  pop_frame();
  lemma_multPower #c (as_nat c h0 s) (as_nat c h0 b)
