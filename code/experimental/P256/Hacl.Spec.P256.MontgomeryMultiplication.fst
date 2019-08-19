module Hacl.Spec.P256.MontgomeryMultiplication

open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
module ST = FStar.HyperStack.ST

open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.Core

open Lib.IntTypes
open Lib.Buffer
open Lib.Sequence
open Lib.Loops

#reset-options "--z3rlimit 300"

let prime = prime256

let fromDomain_ a = (a * modp_inv2 (pow2 256)) % prime256

let fromDomainPoint a = 
  let x, y, z = a in 
  fromDomain_ x, fromDomain_ y, fromDomain_ z


val fromDomain: a: felem4{as_nat4 a < prime256} -> Tot (result: felem4 {as_nat4 result = fromDomain_ (as_nat4 a)})

let fromDomain a =  
  let one = ((u64 1), (u64 0), u64 0, u64 0) in
    assert_norm (as_nat4 one = 1);
  Core.montgomery_multiplication one a


let toDomain_ a = (a * pow2 256) % prime256

let lemmaFromDomain a = ()

let lemmaToDomain a = ()


#reset-options "--z3rlimit 300 --z3refresh"

let lemmaToDomainAndBackIsTheSame a = 
  let to = toDomain_ a in 
    lemmaToDomain a;
  let from = fromDomain_ to in 
    lemmaFromDomain to;
    lemma_mod_mul_distr_l (a * pow2 256) (modp_inv2 (pow2 256)) prime256;
    assert(from = (a * pow2 256 * modp_inv2 (pow2 256)) % prime256);
    assert_norm (pow2 256 * modp_inv2 (pow2 256) % prime256 = 1);
  modulo_distributivity_mult_last_two a 1 1 (pow2 256) (modp_inv2 (pow2 256)) prime256;
    assert((a * pow2 256 * modp_inv2 (pow2 256)) % prime256 == (a * (pow2 256 * modp_inv2 (pow2 256) % prime)) % prime256);
    modulo_lemma a prime;
    assert(from = a)


let lemmaFromDomainToDomain a = 
  let from = fromDomain_ a in 
    lemmaFromDomain a;
  let to = toDomain_ from in 
    lemmaToDomain from;
  lemma_mod_mul_distr_l (a * modp_inv2 (pow2 256)) (pow2 256)  prime256;
  assert_norm (modp_inv2 (pow2 256) * (pow2 256) % prime = 1);
  modulo_distributivity_mult_last_two a 1 1 (modp_inv2 (pow2 256)) (pow2 256) prime256;
  modulo_lemma a prime


val lemmaFromDomainToDomainModuloPrime: a: int -> Lemma (a % prime256 == fromDomain_(toDomain_ a))

let lemmaFromDomainToDomainModuloPrime a = 
  lemma_mod_mul_distr_l (a*pow2 256) (modp_inv2 (pow2 256)) prime256;
  assert_norm (pow2 256 * modp_inv2 (pow2 256) % prime256 = 1);
  modulo_distributivity_mult_last_two a 1 1 (pow2 256) (modp_inv2 (pow2 256)) prime256

(* it is the key lemma of Montgomery Multiplication, showing that it's correct (i.e. mm(a, b) = a * b * 2^-256 *)
(*
val lemmaMontgomeryMultiplicationCorrect: a: felem4{as_nat4 a < prime} -> b: felem4{as_nat4 b < prime} -> Lemma (
  let aDomain = toDomain_ a in 
  let bDomain = toDomain b in 
  let multInDomain = Core.montgomery_multiplication aDomain bDomain in 
  let multResultFromDomain = fromDomain multInDomain in 
  as_nat4 a * as_nat4 b % prime == as_nat4 multResultFromDomain)


let lemmaMontgomeryMultiplicationCorrect a b = 
  let aDomain = toDomain a in 
  let bDomain = toDomain b in 
  let multInDomain = montgomery_multiplication aDomain bDomain in 
  assert_norm (prime > 0);
  modulo_distributivity_mult2 (as_nat4 a * pow2 256) (as_nat4 b * pow2 256) (modp_inv2 (pow2 256)) prime;  
  lemma_brackets_l (as_nat4 a * pow2 256) ((as_nat4 b * pow2 256) * modp_inv2 (pow2 256)) (modp_inv2 (pow2 256));
  lemma_twice_brackets (as_nat4 a) (pow2 256) 1 (as_nat4 b) (pow2 256) 1 (modp_inv2 (pow2 256));
  modulo_distributivity_mult2 (as_nat4 a * pow2 256) (as_nat4 b * pow2 256) (modp_inv2 (pow2 256)) prime;
  modulo_distributivity_mult_last_two (as_nat4 a) (pow2 256) (as_nat4 b) (pow2 256) (modp_inv2 (pow2 256)) prime;
  assert_norm((pow2 256 * modp_inv2 (pow2 256)) % prime = 1);
  lemma_distr_mult3 (as_nat4 a) (pow2 256) (as_nat4 b);
  let multFromDomain = fromDomain multInDomain in 
  lemma_mod_mul_distr_l (as_nat4 a * as_nat4 b *pow2 256) (modp_inv2 (pow2 256)) prime;
  modulo_distributivity_mult_last_two (as_nat4 a) (as_nat4 b) 1 (pow2 256) (modp_inv2 (pow2 256)) prime
*)


let inDomain_mod_is_not_mod a = 
  lemma_mod_mul_distr_l a (pow2 256) prime256


(* the lemma shows that the result of multiplication moved out of domain is the multiplication of the numbers moved out of domain *)
val multiplicationInDomain: #k: nat -> #l: nat -> 
  a: felem4 {as_nat4 a == toDomain_ (k) /\ as_nat4 a < prime} -> 
  b: felem4 {as_nat4 b == toDomain_ (l) /\ as_nat4 b < prime256} -> Lemma 
    (ensures (let multResult = Core.montgomery_multiplication a b in as_nat4 multResult == toDomain_ (k * l)))
    
let multiplicationInDomain #k #l a b = 
  let multResult = Core.montgomery_multiplication a b in 
  lemma_mul_nat2 k l;
  let secondBracket = toDomain_ (k * l) in 
    assert(as_nat4 multResult = toDomain_ (k) * toDomain_ (l) * modp_inv2 (pow2 256) % prime);
  modulo_distributivity_mult2 (k * pow2 256) (l* pow2 256) (modp_inv2 (pow2 256)) prime;
  lemma_twice_brackets k (pow2 256) 1 l (pow2 256) 1 (modp_inv2 (pow2 256));
  assert_norm (pow2 256 * modp_inv2 (pow2 256) % prime == 1);
  modulo_distributivity_mult_last_two k (pow2 256) l (pow2 256) (modp_inv2 (pow2 256)) prime;
  lemma_distr_mult3 k (pow2 256) l


val additionInDomain: #k: nat -> #l: nat -> 
  a: felem4 {as_nat4 a == toDomain_ (k) /\ as_nat4 a < prime} -> 
  b: felem4 {as_nat4 b == toDomain_ (l) /\ as_nat4 b < prime} -> Lemma 
  (ensures (let result = felem_add a b in as_nat4 result == toDomain_(k + l)))

let additionInDomain #k #l a b = 
  let result = felem_add a b in 
  assert(as_nat4 result = (as_nat4 a + as_nat4 b) % prime);
  assert(as_nat4 result = (toDomain_(k) + toDomain_(l)) % prime);
  assert(as_nat4 result = ((k * pow2 256 % prime) + (l * pow2 256 % prime)) % prime);
  modulo_distributivity (k * pow2 256) (l *pow2 256) prime;
  assert(as_nat4 result = toDomain_ (k + l))


val additionInDomainNat: #k: nat -> #l: nat -> a: nat {a == toDomain_ k /\ a < prime} -> b: nat {b == toDomain_ l /\ b < prime} ->
  Lemma (let result = (a + b) % prime in result == toDomain_ (k + l))

let additionInDomainNat #k #l a b = 
  modulo_distributivity (k * pow2 256) (l * pow2 256) prime


(* the lemma shows that the result of addition in domain (moved out of domain) is the same if the variables were out of domain *)
val additionInDomain2: a: felem4{as_nat4 a < prime} -> b: felem4 {as_nat4 b < prime} -> Lemma (let result = felem_add a b in 
  as_nat4 result = toDomain_ (fromDomain_ (as_nat4 a) + fromDomain_ (as_nat4 b)))

let additionInDomain2 a b = 
  let k = fromDomain_ (as_nat4 a) in 
  let l = fromDomain_ (as_nat4 b) in 
  lemmaFromDomainToDomain (as_nat4 a);
  lemmaFromDomainToDomain (as_nat4 b);
  additionInDomain #k #l a b


let additionInDomain2Nat a b = 
  let k = fromDomain_ a in 
  let l = fromDomain_ b in 
  lemmaFromDomainToDomain a;
  lemmaFromDomainToDomain b;
  additionInDomainNat #k #l a b


(* the lemma shows the equivalence between fromDomain(a:nat) and fromDomain(a % prime) *)
val fromDomain_mod_is_not_mod: a: nat -> Lemma (fromDomain_ a == fromDomain_ (a % prime))

let fromDomain_mod_is_not_mod a = 
  lemma_mod_mul_distr_l a (modp_inv2(pow2 256)) prime


val additionInDomainLemma2: a: felem4{as_nat4 a < prime} -> b: felem4{as_nat4 b < prime} -> 
  Lemma (ensures (as_nat4 (fromDomain (felem_add a b)) = (as_nat4(fromDomain (a)) + as_nat4(fromDomain (b))) % prime))

let  additionInDomainLemma2 a b =  
  let k = (as_nat4 (fromDomain a) + as_nat4 (fromDomain b)) % prime in 
  modulo_distributivity (as_nat4 a * modp_inv2 (pow2 256)) (as_nat4 b * modp_inv2 (pow2 256)) prime;
  distributivity_add_left (as_nat4 a) (as_nat4 b) (modp_inv2 (pow2 256));
  fromDomain_mod_is_not_mod (as_nat4 a + as_nat4 b)

val subtractionInDomain: #k: nat -> #l: nat -> 
  a: felem4 {as_nat4 a == toDomain_ (k) /\ as_nat4 a < prime} -> 
  b: felem4 {as_nat4 b == toDomain_ (l) /\ as_nat4 b < prime} -> Lemma 
  (ensures (let result = felem_sub a b in as_nat4 result == toDomain_(k - l)))

let subtractionInDomain #k #l a b = 
  let result = felem_sub a b in 
  lemma_mod_sub_distr (as_nat4 a) (l * pow2 256) prime;
  lemma_mod_add_distr (-l * pow2 256) (k * pow2 256) prime

val substractionInDomainNat: #k: nat -> #l: nat -> a: nat {a == toDomain_ k /\ a < prime} -> b: nat {b == toDomain_ l /\ b < prime} -> 
  Lemma ((a - b) % prime  == toDomain_ (k - l))

let substractionInDomainNat #k #l a b = 
  lemma_mod_sub_distr a (l * pow2 256) prime;
  lemma_mod_add_distr (-l * pow2 256) (k * pow2 256) prime


val substractionInDomain2: a: felem4{as_nat4 a < prime} -> b: felem4{as_nat4 b < prime} -> Lemma (let result = felem_sub a b in 
  as_nat4 result = toDomain_ (fromDomain_ (as_nat4 a) - fromDomain_ (as_nat4 b)))

let substractionInDomain2 a b = 
  let k = fromDomain_ (as_nat4 a) in 
  let l = fromDomain_ (as_nat4 b) in 
  lemmaFromDomainToDomain (as_nat4 a);
  lemmaFromDomainToDomain (as_nat4 b);
  subtractionInDomain #k #l a b

let substractionInDomain2Nat a b = 
  let k = fromDomain_ a in 
  let l = fromDomain_ b in 
  lemmaFromDomainToDomain a;
  lemmaFromDomainToDomain b;
  substractionInDomainNat #k #l a b


let felem_add_seq a b = 
  let a0 = index a 0 in 
  let a1 = index a 1 in 
  let a2 = index a 2 in 
  let a3 = index a 3 in 

  let b0 = index b 0 in 
  let b1 = index b 1 in 
  let b2 = index b 2 in 
  let b3 = index b 3 in 

  let (r0, r1, r2, r3) = felem_add (a0, a1, a2, a3) (b0, b1, b2, b3) in 
  
  let r = create 4 (u64 0)  in 
  let r = upd r 0 r0 in
  let r = upd r 1 r1 in 
  let r = upd r 2 r2 in 
  let r = upd r 3 r3 in 

  additionInDomain2 (a0, a1, a2, a3) (b0, b1, b2, b3);
  inDomain_mod_is_not_mod (fromDomain_ (as_nat4 (a0, a1, a2, a3)) + fromDomain_ (as_nat4 (b0, b1, b2, b3)));
  r


let felem_sub_seq a b = 
  let a0 = index a 0 in 
  let a1 = index a 1 in 
  let a2 = index a 2 in 
  let a3 = index a 3 in 

  let b0 = index b 0 in 
  let b1 = index b 1 in 
  let b2 = index b 2 in 
  let b3 = index b 3 in 

  let a_tuple = a0, a1, a2, a3 in 
  let b_tuple = b0, b1, b2, b3 in 
  let (r0, r1, r2, r3) = felem_sub a_tuple b_tuple in 

  
  let r = create 4 (u64 0)  in 
  let r = upd r 0 r0 in
  let r = upd r 1 r1 in 
  let r = upd r 2 r2 in 
  let r = upd r 3 r3 in 

  substractionInDomain2 (a0, a1, a2, a3) (b0, b1, b2, b3);
  inDomain_mod_is_not_mod (fromDomain_ (as_nat4 (a0, a1, a2, a3)) - fromDomain_ (as_nat4 (b0, b1, b2, b3)));
  r


let montgomery_multiplication_seq a b  = 
  let a0 = index a 0 in 
  let a1 = index a 1 in 
  let a2 = index a 2 in 
  let a3 = index a 3 in 

  let b0 = index b 0 in 
  let b1 = index b 1 in 
  let b2 = index b 2 in 
  let b3 = index b 3 in 

    [@inline_let]
  let a_tuple = a0, a1, a2, a3 in 
    [@inline_let]
  let b_tuple = b0, b1, b2, b3 in 
  let (r0, r1, r2, r3) = montgomery_multiplication (a0, a1, a2, a3) (b0, b1, b2, b3) in 
  lemmaFromDomainToDomain (as_nat4 a_tuple);
  lemmaFromDomainToDomain (as_nat4 b_tuple);
  multiplicationInDomain #(fromDomain_ (as_nat4 a_tuple)) #(fromDomain_ (as_nat4 b_tuple)) a_tuple b_tuple;
  inDomain_mod_is_not_mod (fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat b));

  let r = create 4 (u64 0)  in 
  let r = upd r 0 r0 in
  let r = upd r 1 r1 in 
  let r = upd r 2 r2 in 
  let r = upd r 3 r3 in 
   r


let montgomery_multiplication_buffer a b r= 

  let a0 = Lib.Buffer.index a (size 0) in 
  let a1 = Lib.Buffer.index a (size 1) in 
  let a2 = Lib.Buffer.index a (size 2) in 
  let a3 = Lib.Buffer.index a (size 3) in 

  let b0 = Lib.Buffer.index b (size 0) in 
  let b1 = Lib.Buffer.index b (size 1) in 
  let b2 = Lib.Buffer.index b (size 2) in 
  let b3 = Lib.Buffer.index b (size 3) in 

    let h0 = ST.get() in 
  let (r0, r1, r2, r3) = montgomery_multiplication (a0, a1, a2, a3) (b0, b1, b2, b3) in 
  Lib.Buffer.upd r (size 0) r0;
  Lib.Buffer.upd r (size 1) r1;
  Lib.Buffer.upd r (size 2) r2;
  Lib.Buffer.upd r (size 3) r3;

    let h1 = ST.get() in 

  lemmaFromDomainToDomain (as_nat4 (a0, a1, a2, a3));
  lemmaFromDomainToDomain (as_nat4 (b0, b1, b2, b3));
  multiplicationInDomain #(fromDomain_ (as_nat4 (a0, a1, a2, a3) )) #(fromDomain_ (as_nat4 (b0, b1, b2, b3))) (a0, a1, a2, a3)  (b0, b1, b2, b3);
  assert(Lib.Sequence.equal  (montgomery_multiplication_seq (as_seq h0 a) (as_seq h0 b))  (as_seq h1 r))

#reset-options "--z3refresh --z3rlimit 100" 

val modulo_distributivity_mult_three: 
  a: int -> b: int ->  c: int -> d: pos -> Lemma ((a * b  * c) % d = ((a % d) * (b % d) * (c % d)) % d)


let modulo_distributivity_mult_three a b c d = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  assert_by_tactic (a * b * c = a * (b * c)) canon;
  lemma_mod_mul_distr_l a (b * c) d;
  assert_by_tactic (((a % d) * b * c) % d == (b * ((a % d) * c)) % d) canon;
  lemma_mod_mul_distr_l b ((a % d) * c) d;
  lemma_mod_mul_distr_r ((a % d) * (b % d)) c d


val modulo_distributivity_mult_four: 
  a: int -> b: int ->  c: int -> d: nat ->  e: pos -> Lemma ((a * b  * c * d) % e = ((a % e) * (b % e) * (c % e) * (d % e)) % e)


let modulo_distributivity_mult_four a b c d e = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  assert_by_tactic ((a * b * c * d) % e == ((a * b * c) * d) % e) canon;
    assert((a * b * c * d) % e == ((a * b * c) * d) % e);
  lemma_mod_mul_distr_l (a * b * c) d e;
    assert((((a * b * c) * d) % e) == ((a * b * c) % e * d) % e);
  modulo_distributivity_mult_three a b c e;
    assert((((a * b * c) * d) % e) == (((a % e) * (b % e) * (c % e)) % e * d) % e);
  lemma_mod_mul_distr_l ((a % e) * (b % e) * (c % e)) d e;  
    assert(((((a % e) * (b % e) * (c % e)) % e * d) % e) == (((a % e) * (b % e) * (c % e)) * d) % e);
  lemma_mod_mul_distr_r ((a % e) * (b % e) * (c % e)) d e;
  assert_by_tactic ((((a % e) * (b % e) * (c % e)) * (d % e)) % e == ((a % e) * (b % e) * (c % e) * (d % e)) % e) canon


val lemma_toDomain_reduce_prime3: a: int -> b: int -> c: int -> Lemma (toDomain_ ((a % prime) * (b % prime) * (c % prime)) = toDomain_ (a * b * c))

let lemma_toDomain_reduce_prime3 a b c = 
  inDomain_mod_is_not_mod ((a % prime) * (b % prime) * (c % prime));
  assert(toDomain_ (((a % prime) * (b % prime) * (c % prime)) % prime) == toDomain_ ((a % prime) * (b % prime) * (c % prime)));
    modulo_distributivity_mult_three a b c prime;
  assert(toDomain_ ((a % prime) * (b % prime) * (c % prime) % prime) = toDomain_ ((a * b * c) % prime));
  inDomain_mod_is_not_mod (a * b * c);
  assert(toDomain_ ((a * b * c) % prime) = toDomain_ (a * b * c))


#reset-options "--z3refresh --z3rlimit 300" 
val lemma_toDomain_reduce_prime4: a: int -> b: int -> c: int -> d: nat -> Lemma (toDomain_ ((a % prime) * (b % prime) * (c % prime) * (d % prime)) = toDomain_ (a * b * c * d))

let lemma_toDomain_reduce_prime4 a b c d = 
  inDomain_mod_is_not_mod ((a % prime) * (b % prime) * (c % prime) * (d % prime));
  modulo_distributivity_mult_four a b c d prime;
  inDomain_mod_is_not_mod (a * b * c * d)


let mm_cube_seq a= 
    let a0 = index a 0 in 
    let a1 = index a 1 in 
    let a2 = index a 2 in 
    let a3 = index a 3 in  
    let a_tuple = (a0, a1, a2, a3) in  
    
    let (r0, r1, r2, r3) = cube_tuple (a0, a1, a2, a3) in 

    let r = create 4 (u64 0)  in 
    let r = upd r 0 r0 in
    let r = upd r 1 r1 in 
    let r = upd r 2 r2 in 
    let r = upd r 3 r3 in 
    let r_tuple = (r0, r1, r2, r3) in 
    
    lemma_brackets5_twice (as_nat4 a_tuple) (as_nat4 a_tuple) (as_nat4 a_tuple) (modp_inv2 (pow2 256)) (modp_inv2 (pow2 256));
    lemma_mod_mul_distr_l ((as_nat4 a_tuple * modp_inv2 (pow2 256))  * (as_nat4 a_tuple * modp_inv2 (pow2 256))  * as_nat4 a_tuple) (modp_inv2 (pow2 256)) prime;
    lemma_brackets5 (as_nat4 a_tuple * modp_inv2 (pow2 256)) (as_nat4 a_tuple * modp_inv2 (pow2 256))  1 (as_nat4 a_tuple) (modp_inv2 (pow2 256));
    lemmaFromDomainToDomain (as_nat4 r_tuple);
    inDomain_mod_is_not_mod ((as_nat4 a_tuple * modp_inv2 (pow2 256))  * (as_nat4 a_tuple * modp_inv2 (pow2 256))  * (as_nat4 a_tuple * modp_inv2 (pow2 256)) ) ;
    lemma_toDomain_reduce_prime3 (as_nat4 a_tuple * modp_inv2 (pow2 256)) (as_nat4 a_tuple * modp_inv2 (pow2 256)) (as_nat4 a_tuple * modp_inv2 (pow2 256));
    inDomain_mod_is_not_mod (fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a));
    r


let mm_quatre_seq a= 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  let result = montgomery_multiplication_seq a a in 
  let resultFinal = montgomery_multiplication_seq result result in 
      modulo_distributivity_mult ((fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a))) ((fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a))) prime;
      assert_by_tactic (((fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a))) * ((fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a))) == (fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a))) canon;
  resultFinal


val lemma_multiplicationInDomainByNumber: a: felem4 -> b: int -> Lemma (fromDomain_ (as_nat4 a * b % prime) = b * fromDomain_ (as_nat4 a) % prime)

let lemma_multiplicationInDomainByNumber a b = 
  lemma_mod_mul_distr_l (as_nat4 a * b) (modp_inv2 (pow2 256)) prime;
  lemma_brackets_l (as_nat4 a) b (modp_inv2 (pow2 256));
  lemma_brackets (as_nat4 a) b (modp_inv2 (pow2 256));
  lemma_brackets1 (as_nat4 a) b (modp_inv2 (pow2 256));
  lemma_mod_mul_distr_r b (as_nat4 a * modp_inv2 (pow2 256)) prime
  

let mm_byTwo_seq a = 
    let a0 = index a 0 in 
    let a1 = index a 1 in 
    let a2 = index a 2 in 
    let a3 = index a 3 in 
    let a_tuple = (a0, a1, a2, a3) in  
    
    let (r0, r1, r2, r3) = shift_left_felem (a0, a1, a2, a3) in 

    let r = create 4 (u64 0)  in 
    let r = upd r 0 r0 in
    let r = upd r 1 r1 in 
    let r = upd r 2 r2 in 
    let r = upd r 3 r3 in 
    let r_tuple = (r0, r1, r2, r3) in 
    lemma_multiplicationInDomainByNumber a_tuple 2;
    lemmaFromDomainToDomain (as_nat4 r_tuple);
    inDomain_mod_is_not_mod (2 * fromDomain_ (as_nat4 a_tuple));
    r


let lemma_add_same_value_is_by_two a = 
    let r1 = felem_add_seq a a in 
    let r2 = mm_byTwo_seq a in 
    let a_ = felem_seq_as_nat a in 
    lemma_mod_mul_distr_r 2 (fromDomain_ a_) prime;
    inDomain_mod_is_not_mod (2 * (fromDomain_ a_ % prime));
    lemma_eq_funct r1 r2



let mm_byThree_seq a = 
    let a0 = index a 0 in 
    let a1 = index a 1 in 
    let a2 = index a 2 in 
    let a3 = index a 3 in 
    let a_tuple = (a0, a1, a2, a3) in  
    
    let (r0, r1, r2, r3) = multByThree_tuple (a0, a1, a2, a3) in 

    let r = create 4 (u64 0)  in 
    let r = upd r 0 r0 in
    let r = upd r 1 r1 in 
    let r = upd r 2 r2 in 
    let r = upd r 3 r3 in 
    let r_tuple = (r0, r1, r2, r3) in 
    lemma_multiplicationInDomainByNumber a_tuple 3;
    lemmaFromDomainToDomain (as_nat4 r_tuple);
    inDomain_mod_is_not_mod (3 * fromDomain_ (as_nat4 a_tuple));
    r


let mm_byFour_seq a = 
    let a0 = index a 0 in 
    let a1 = index a 1 in 
    let a2 = index a 2 in 
    let a3 = index a 3 in 
    let a_tuple = (a0, a1, a2, a3) in  
    
    let (r0, r1, r2, r3) = multByFour_tuple (a0, a1, a2, a3) in 

    let r = create 4 (u64 0)  in 
    let r = upd r 0 r0 in
    let r = upd r 1 r1 in 
    let r = upd r 2 r2 in 
    let r = upd r 3 r3 in 
    let r_tuple = (r0, r1, r2, r3) in 
    lemma_multiplicationInDomainByNumber a_tuple 4;
    lemmaFromDomainToDomain (as_nat4 r_tuple);
    inDomain_mod_is_not_mod (4 * fromDomain_ (as_nat4 a_tuple)); 
    r


let mm_byEight_seq a = 
    let a0 = index a 0 in 
    let a1 = index a 1 in 
    let a2 = index a 2 in 
    let a3 = index a 3 in 
    let a_tuple = (a0, a1, a2, a3) in  
    
    let (r0, r1, r2, r3) = multByEight_tuple (a0, a1, a2, a3) in 

    let r = create 4 (u64 0)  in 
    let r = upd r 0 r0 in
    let r = upd r 1 r1 in 
    let r = upd r 2 r2 in 
    let r = upd r 3 r3 in 
    let r_tuple = (r0, r1, r2, r3) in 
    lemma_multiplicationInDomainByNumber a_tuple 8;
    lemmaFromDomainToDomain (as_nat4 r_tuple);
    inDomain_mod_is_not_mod (8 * fromDomain_ (as_nat4 a_tuple));
    r

let lemma_add_same_value_is_by_three a = 
  let two = mm_byTwo_seq a in 
  let three = felem_add_seq a two in 
  let r = mm_byThree_seq a in 
  let a_ = felem_seq_as_nat a in
  
  lemma_mod_add_distr (fromDomain_ a_) (2 * fromDomain_ a_) prime;
  lemma_eq_funct r three


let lemma_add_same_value_is_by_four a = 
  let two = mm_byTwo_seq a in 
  let four = mm_byTwo_seq two in 
  let r = mm_byFour_seq a in 
  let a_ = felem_seq_as_nat a in 
  
  assert(felem_seq_as_nat four = toDomain_ (((2 * fromDomain_ a_) % prime + (2 * fromDomain_ a_) % prime) % prime));
  lemma_mod_add_distr ((2 * fromDomain_ a_) % prime) (2 * fromDomain_ a_) prime;
  lemma_mod_add_distr (2 * fromDomain_ a_) (2 * fromDomain_ a_) prime;
  lemma_eq_funct r four


let lemma_add_same_value_is_by_eight a = 
  let two = mm_byTwo_seq a in 
  let four = mm_byTwo_seq two in 
  let eight = mm_byTwo_seq four in 
  let r = mm_byEight_seq a in 
  let a_ = felem_seq_as_nat a in 
  
  lemma_mod_add_distr ((2 * fromDomain_ a_) % prime) (2 * fromDomain_ a_) prime;
  lemma_mod_add_distr (2 * fromDomain_ a_) (2 * fromDomain_ a_) prime;
  lemma_mod_mul_distr_r 2 (4 * fromDomain_ a_) prime;

  lemma_eq_funct r eight
  

let mm_byMinusThree_seq a = 
    let a0 = index a 0 in 
    let a1 = index a 1 in 
    let a2 = index a 2 in 
    let a3 = index a 3 in 
    let a_tuple = (a0, a1, a2, a3) in  
    
    let (r0, r1, r2, r3) = multByMinusThree_tuple(a0, a1, a2, a3) in 

    let r = create 4 (u64 0)  in 
    let r = upd r 0 r0 in
    let r = upd r 1 r1 in 
    let r = upd r 2 r2 in 
    let r = upd r 3 r3 in 
    let r_tuple = (r0, r1, r2, r3) in 
    lemma_multiplicationInDomainByNumber a_tuple (-3);
    lemmaFromDomainToDomain (as_nat4 r_tuple);
    inDomain_mod_is_not_mod (-3 * fromDomain_ (as_nat4 a_tuple));
    r


let lemma_add_same_value_is_by_minus_three a zero = 
  let three = mm_byThree_seq a in 
  let a_ = felem_seq_as_nat a in 
    assert(felem_seq_as_nat three = toDomain_ (3 * fromDomain_ a_ % prime));
  let minusThree = felem_sub_seq zero three in 
    assert_norm (fromDomain_ 0 == 0);
    assert(felem_seq_as_nat minusThree = toDomain_ (( - (3 * fromDomain_ a_ % prime)) % prime));
  let r = mm_byMinusThree_seq a in
    lemma_mod_sub_distr 0 (3 * fromDomain_ a_) prime;
    lemma_eq_funct minusThree r
  

val lemmaDistributivityInDomain: a: int -> b: int -> Lemma (toDomain_ (a * (b % prime) % prime) = toDomain_ (a * b % prime))
  [SMTPat (toDomain_ (a * (b % prime) % prime))]

let lemmaDistributivityInDomain a b = 
  lemma_mod_mul_distr_r a b prime



#reset-options "--z3refresh --z3rlimit 500" 

val fsquarePowN: n: size_t -> a: felem -> Stack unit 
  (requires (fun h -> live h a /\ as_nat h a < prime)) 
  (ensures (fun h0 _ h1 -> modifies1 a h0 h1 /\  as_nat h1 a < prime /\ (let k = fromDomain_(as_nat h0 a) in as_nat h1 a = toDomain_ (pow k (pow2 (v n))))))

let fsquarePowN n a = 
  let h0 = ST.get() in  
  lemmaFromDomainToDomain (as_nat h0 a);
  let inv (h0: HyperStack.mem) (h1: HyperStack.mem) (i: nat) : Type0 =
    let k_before_d = as_nat h0 a in let k = fromDomain_ k_before_d in 
    as_nat h1 a = toDomain_ (pow k (pow2 i)) /\ 
    as_nat h1 a < prime /\ live h1 a /\ modifies1 a h0 h1 in 
  for (size 0) n (inv h0) (fun x -> 
    let h0_ = ST.get() in 
     montgomery_multiplication_buffer a a a; 
     let k = fromDomain_ (as_nat h0 a) in  
     inDomain_mod_is_not_mod (fromDomain_ (as_nat h0_ a) * fromDomain_ (as_nat h0_ a));
     lemmaFromDomainToDomainModuloPrime (let k = fromDomain_ (as_nat h0 a) in pow k (pow2 (v x)));
     modulo_distributivity_mult (pow k (pow2 (v x))) (pow k (pow2 (v x))) prime;
     pow_plus k  (pow2 (v x)) (pow2 (v x )); 
     pow2_double_sum (v x);
     inDomain_mod_is_not_mod (pow k (pow2 (v x + 1)))
  )


val fsquarePowNminusOne: n: size_t -> a: felem -> tempBuffer: felem -> Stack unit 
  (requires (fun h -> live h a /\ live h tempBuffer /\ as_nat h a < prime /\ disjoint a tempBuffer)) 
  (ensures (fun h0 _ h1 -> as_nat h1 a < prime /\ as_nat h1 tempBuffer < prime /\ modifies2 a tempBuffer h0 h1 
/\ (let k = fromDomain_ (as_nat h0 a) in  as_nat h1 a = toDomain_ (pow k (pow2 (v n))) /\ as_nat h1 tempBuffer = toDomain_ (pow
        k (pow2 (v n) -1 )))))

let fsquarePowNminusOne n a b = 
  let h0 = ST.get() in
  Lib.Buffer.upd b (size 0) (u64 1);
  Lib.Buffer.upd b (size 1) (u64 18446744069414584320);
  Lib.Buffer.upd b (size 2) (u64 18446744073709551615);
  Lib.Buffer.upd b (size 3) (u64 4294967294);

  let one = (u64 1, u64 18446744069414584320, u64 18446744073709551615, u64 4294967294) in 
  assert_norm (as_nat4 one = toDomain_(1));
  lemmaFromDomainToDomain (as_nat h0 a);

  let inv (h0: HyperStack.mem) (h1: HyperStack.mem) (i: nat) : Type0 = 
    let k = fromDomain_(as_nat h0 a) in 
    as_nat h1 b = toDomain_ (pow k (pow2 i - 1)) /\ as_nat h1 a < prime /\ live h1 a /\
    as_nat h1 a = toDomain_ (pow k (pow2 i)) /\ as_nat h1 b < prime /\ live h1 b /\ modifies2 a b h0 h1 in 

  for (size 0) n (inv h0) (fun x -> 
    let h0_ = ST.get() in 
    montgomery_multiplication_buffer b a b;
    montgomery_multiplication_buffer a a a;
    let k = fromDomain_ (as_nat h0 a) in 
    inDomain_mod_is_not_mod (fromDomain_ (as_nat h0_ b) * fromDomain_ (as_nat h0_ a));
    inDomain_mod_is_not_mod (fromDomain_ (as_nat h0_ a) * fromDomain_ (as_nat h0_ a));

    lemmaFromDomainToDomainModuloPrime (pow k (pow2 (v x) -1 ));
    lemmaFromDomainToDomainModuloPrime (pow k (pow2 (v x)));
    modulo_distributivity_mult (pow k (pow2 (v x) - 1)) (pow k (pow2 (v x))) prime;
    modulo_distributivity_mult (pow k (pow2 (v x))) (pow k (pow2 (v x))) prime;
    
    pow_plus k (pow2 (v x) -1 ) (pow2 (v x));
    pow_plus k (pow2 (v x)) (pow2 (v x));
    pow2_double_sum (v x);

    inDomain_mod_is_not_mod (pow k (pow2 (v x + 1)));
    inDomain_mod_is_not_mod (pow k (pow2 (v x + 1) - 1))
)

inline_for_extraction noextract   
val norm_part_one: a: felem -> tempBuffer: lbuffer uint64 (size 8) -> 
  Stack unit (requires fun h -> live h a /\ live h tempBuffer /\ disjoint a tempBuffer /\  as_nat h a < prime)
  (ensures fun h0 _ h1 -> modifies1 tempBuffer h0 h1 /\ (let buffer_result = gsub tempBuffer (size 4) (size 4) in as_nat h1 buffer_result < prime /\ 
  (let k = fromDomain_ (as_nat h0 a) in as_nat h1 buffer_result = toDomain_(pow k ((pow2 32 - 1) * pow2 224) % prime))))
    
let norm_part_one a tempBuffer = 
    let h0 = ST.get() in 
  Lib.Buffer.update_sub tempBuffer (size 0) (size 4) a;

  let buffer_a = Lib.Buffer.sub tempBuffer (size 0) (size 4) in 
  let buffer_b = Lib.Buffer.sub tempBuffer (size 4) (size 4) in 

  fsquarePowNminusOne (size 32) buffer_a buffer_b;
  fsquarePowN (size 224) buffer_b;

  let k = fromDomain_ (as_nat h0 a) in 
  lemmaFromDomainToDomainModuloPrime (pow k (pow2 32 - 1));
  let k_powers = pow k (pow2 32 - 1) in 
  let k_prime = k_powers % prime in 
  inDomain_mod_is_not_mod (pow k_prime (pow2 224));
  power_distributivity k_powers (pow2 224) prime;
  power_mult k (pow2 32 - 1) (pow2 224)
 
inline_for_extraction noextract   
val norm_part_two: a: felem -> tempBuffer: lbuffer uint64 (size 4) -> 
  Stack unit (requires fun h -> live h a /\ live h tempBuffer /\ disjoint a tempBuffer /\  as_nat h a < prime)
  (ensures fun h0 _ h1 -> as_nat h1 tempBuffer < prime /\ modifies1 tempBuffer h0 h1 /\
    (let k = fromDomain_ (as_nat h0 a) in as_nat h1 tempBuffer = toDomain_(pow k (pow2 192) % prime)))
    
let norm_part_two a tempBuffer = 
  let h0 = ST.get() in 
  Lib.Buffer.copy tempBuffer a;
  fsquarePowN (size 192) tempBuffer;
  let k = fromDomain_ (as_nat h0 a) in 
  inDomain_mod_is_not_mod (pow k (pow2 192))

inline_for_extraction noextract   
val norm_part_three:a: felem -> tempBuffer: lbuffer uint64 (size 8) -> 
  Stack unit (requires fun h -> live h a /\ live h tempBuffer /\ disjoint a tempBuffer /\  
   as_nat h a < prime)   
  (ensures fun h0 _ h1 ->  modifies1 tempBuffer h0 h1 /\ (let buffer_result = gsub tempBuffer (size 4) (size 4) in as_nat h1 buffer_result < prime
    /\ (let k = fromDomain_ (as_nat h0 a) in as_nat h1 buffer_result = toDomain_(pow k ((pow2 94 - 1) * pow2 2) % prime))))

let norm_part_three a tempBuffer = 
  let h0 = ST.get() in 
  Lib.Buffer.update_sub tempBuffer (size 0) (size 4) a;

  let buffer_a = Lib.Buffer.sub tempBuffer (size 0) (size 4) in 
  let buffer_b = Lib.Buffer.sub tempBuffer (size 4) (size 4) in 

  fsquarePowNminusOne (size 94) buffer_a buffer_b;
  fsquarePowN (size 2) buffer_b;

  let k = fromDomain_ (as_nat h0 a) in 
  lemmaFromDomainToDomainModuloPrime (pow k (pow2 94 - 1));
  let k_powers = pow k (pow2 94 - 1) in 
  let k_prime = k_powers % prime in 
  inDomain_mod_is_not_mod (pow k_prime (pow2 2));
  power_distributivity k_powers (pow2 2) prime;
  power_mult k (pow2 94 - 1) (pow2 2)


val lemma_inDomainModulo: a: nat -> b: nat -> Lemma ((toDomain_ ((a % prime) * (b % prime) % prime) = toDomain_ (a * b % prime)))

let lemma_inDomainModulo a b = 
  lemma_mod_mul_distr_l a (b % prime) prime;
  lemma_mod_mul_distr_r a b prime


let lemmaEraseToDomainFromDomain z = 
  lemma_mod_mul_distr_l (z * z) z prime


val big_power: a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> Lemma (pow a b * pow a c * pow a d * pow a e = pow a (b + c + d + e))

let big_power a b c d e = 
  assert(pow a b * pow a c * pow a d * pow a e = (pow a b * pow a c) * (pow a d * pow a e));
  pow_plus a b c;
  pow_plus a d e;
  pow_plus a (b + c) (d + e)


#reset-options "--z3refresh --z3rlimit 500"
let exponent a result tempBuffer = 
  let h0 = ST.get () in 

  let buffer_norm_1 = Lib.Buffer.sub  tempBuffer (size 0) (size 8) in 
    let buffer_result1 = Lib.Buffer.sub tempBuffer (size 4) (size 4) in 
  let buffer_result2 = Lib.Buffer.sub tempBuffer (size 8) (size 4) in 
  let buffer_norm_3 = Lib.Buffer.sub tempBuffer (size 12) (size 8) in 
    let buffer_result3 = Lib.Buffer.sub tempBuffer (size 16) (size 4) in 
 
  norm_part_one a buffer_norm_1;
  norm_part_two a buffer_result2;
  norm_part_three a buffer_norm_3;
  
    let h1 = ST.get() in 
  montgomery_multiplication_buffer buffer_result1 buffer_result2 buffer_result1;
    let h2 = ST.get() in 
  montgomery_multiplication_buffer buffer_result1 buffer_result3 buffer_result1;
    let h3 = ST.get() in 
  montgomery_multiplication_buffer buffer_result1 a buffer_result1;
    let h4 = ST.get() in 
  copy result buffer_result1; 
    let h5 = ST.get() in 
  
  let k = fromDomain_ (as_nat h0 a) in 
  let power1 = pow k ((pow2 32 - 1) * pow2 224) in 
  let power2 = pow k (pow2 192) in 
  let power3 = pow k ((pow2 94 - 1) * pow2 2) in 
  let power4 = pow k 1 in 

  lemma_inDomainModulo power1 power2;
  lemma_inDomainModulo (power1 * power2) power3;
  inDomain_mod_is_not_mod (((power1 * power2 * power3) % prime * power4));
  lemma_mod_mul_distr_l (power1 * power2 * power3) power4 prime;
  big_power k ((pow2 32 - 1) * pow2 224) (pow2 192) ((pow2 94 -1 ) * pow2 2) 1;
  assert_norm(((pow2 32 - 1) * pow2 224 + pow2 192 + (pow2 94 -1 ) * pow2 2 + 1) = prime256 - 2);
  admit()
