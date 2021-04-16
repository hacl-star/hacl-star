module Hacl.Spec.MontgomeryMultiplication

open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul

open Spec.ECC
open Spec.ECDSA.Lemmas
open Hacl.Spec.EC.Definition
open Hacl.Lemmas.P256

open Lib.IntTypes

#set-options "--z3rlimit 40 --fuel 0 --ifuel 0"


let fromDomain_ #c #m a = a * modp_inv2_prime (pow2 (getPower c)) (getModePrime m c) % getModePrime m c

let fromDomainPoint #c #m a =
  let x, y, z = a in 
  fromDomain_ #c #m x, fromDomain_ #c #m y, fromDomain_ #c #m z


let toDomain_ #c #m a = a * pow2 (getPower c) % getModePrime m c

let lemmaFromDomain a = ()

let lemmaToDomain #c a = ()

val lemma_mod_inv2_mult_prime: prime: pos {prime > 3 /\ Math.Euclid.is_prime prime} -> a: nat {a % prime <> 0} -> 
  Lemma (a * modp_inv2_prime a prime % prime == 1)

let lemma_mod_inv2_mult_prime prime a = 
  calc (==) {
    a * modp_inv2_prime a prime % prime;
    (==) {lemma_pow_mod_n_is_fpow prime (a % prime) (prime - 2)}
    a * (pow (a % prime) (prime - 2) % prime) % prime;
    (==) {power_distributivity a (prime - 2) prime}
    a * (pow a (prime - 2) % prime) % prime;
    (==) {lemma_mod_mul_distr_r a (pow a (prime - 2)) prime}
    a * (pow a (prime - 2)) % prime;
    (==) {power_one_2 a}
    pow a 1 * (pow a (prime - 2)) % prime;
    (==) {pow_plus a 1 (prime - 2)}
    pow a (prime - 1) % prime;
    (==) {power_as_specification_same_as_fermat a (prime - 1)}
    FStar.Math.Fermat.pow a (prime - 1) % prime;
    (==) {FStar.Math.Fermat.fermat_alt prime a}
    1;
  }

#set-options "--z3rlimit 200 --fuel 0 --ifuel 0"

val lemma_norm: #c: curve -> p: point_nat_prime #c {~ (isPointAtInfinity p)} 
  -> q: point_nat_prime #c {~ (isPointAtInfinity q)} ->  Lemma (
  let pX, pY, pZ = p in
  let qX, qY, qZ = q in 
  let pNX, pNY, pNZ = _norm p in 
  let qNX, qNY, qNZ = _norm q in 
  (pX == qX <==> pNX * (pZ * pZ) % getPrime c == qNX * (qZ * qZ) % getPrime c) /\ 
  (pY == qY <==> pNY * (pZ * pZ * pZ) % getPrime c == qNY * (qZ * qZ * qZ) % getPrime c))


let lemma_norm #c p q = 
  let prime = getPrime c in 
  let pX, pY, pZ = p in
  let qX, qY, qZ = q in 
  let pNX, pNY, pNZ = _norm p in 
  let qNX, qNY, qNZ = _norm q in 

  small_mod pZ prime;
  small_mod qZ prime;

  Hacl.Impl.EC.Math.lemma_a_not_zero_b_not_zero_mod_not_zero prime pZ pZ; 
  Hacl.Impl.EC.Math.lemma_a_not_zero_b_not_zero_mod_not_zero prime (pZ * pZ) pZ; 
  Hacl.Impl.EC.Math.lemma_a_not_zero_b_not_zero_mod_not_zero prime qZ qZ;
  Hacl.Impl.EC.Math.lemma_a_not_zero_b_not_zero_mod_not_zero prime (qZ * qZ) qZ;

  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  calc (==)
  {
    (pX * modp_inv2 #c (pZ * pZ)) % prime * (pZ * pZ) % prime;
    (==) {lemma_mod_mul_distr_l (pX * modp_inv2 #c (pZ * pZ)) (pZ * pZ) prime}
    pX * modp_inv2 #c (pZ * pZ) * (pZ * pZ) % prime;
    (==) {assert_by_tactic (pX * modp_inv2 #c (pZ * pZ) * (pZ * pZ) == pX * (modp_inv2 #c (pZ * pZ) * (pZ * pZ))) canon}
    pX * (modp_inv2 #c (pZ * pZ) * (pZ * pZ)) % prime;
    (==) {lemma_mod_mul_distr_r pX (modp_inv2 #c (pZ * pZ) * (pZ * pZ)) prime}
    pX * (modp_inv2 #c (pZ * pZ) * (pZ * pZ) % prime) % prime;
    (==) {lemma_mod_inv2_mult_prime prime (pZ * pZ)}
    pX % prime;
    (==) {small_mod pX prime}
    pX;
  };

  calc (==)
  {
    (pY * modp_inv2 #c (pZ * pZ * pZ)) % prime * (pZ * pZ * pZ) % prime;
    (==) {lemma_mod_mul_distr_l (pY * modp_inv2 #c (pZ * pZ * pZ)) (pZ * pZ * pZ) prime}
    pY * modp_inv2 #c (pZ * pZ * pZ) * (pZ * pZ * pZ) % prime; 
    (==) {assert_by_tactic (pY * modp_inv2 #c (pZ * pZ * pZ) * (pZ * pZ * pZ) == pY * (modp_inv2 #c (pZ * pZ * pZ) * (pZ * pZ * pZ))) canon}
    pY * (modp_inv2 #c (pZ * pZ * pZ) * (pZ * pZ * pZ)) % prime; 
    (==) {lemma_mod_mul_distr_r pY (modp_inv2 #c (pZ * pZ * pZ) * (pZ * pZ * pZ)) prime}
    pY * (modp_inv2 #c (pZ * pZ * pZ) * (pZ * pZ * pZ) % prime) % prime; 
    (==) {lemma_mod_inv2_mult_prime prime (pZ * pZ * pZ)}
    pY % prime;
    (==) {small_mod pY prime}
    pY; 
  };

  calc (==)
  {
    (qX * modp_inv2 #c (qZ * qZ)) % prime * (qZ * qZ) % prime;
    (==) {lemma_mod_mul_distr_l (qX * modp_inv2 #c (qZ * qZ)) (qZ * qZ) prime}
    qX * modp_inv2 #c (qZ * qZ) * (qZ * qZ) % prime;
    (==) {assert_by_tactic (qX * modp_inv2 #c (qZ * qZ) * (qZ * qZ) == qX * (modp_inv2 #c (qZ * qZ) * (qZ * qZ))) canon}
    qX * (modp_inv2 #c (qZ * qZ) * (qZ * qZ)) % prime;
    (==) {lemma_mod_mul_distr_r qX (modp_inv2 #c (qZ * qZ) * (qZ * qZ)) prime}
    qX * (modp_inv2 #c (qZ * qZ) * (qZ * qZ) % prime) % prime;
    (==) {lemma_mod_inv2_mult_prime prime (qZ * qZ)}
    qX % prime;
    (==) {small_mod qX prime}
    qX;
  };

  calc (==)
  {
    (qY * modp_inv2 #c (qZ * qZ * qZ)) % prime * (qZ * qZ * qZ) % prime;
    (==) {lemma_mod_mul_distr_l (qY * modp_inv2 #c (qZ * qZ * qZ)) (qZ * qZ * qZ) prime}
    qY * modp_inv2 #c (qZ * qZ * qZ) * (qZ * qZ * qZ) % prime; 
    (==) {assert_by_tactic (qY * modp_inv2 #c (qZ * qZ * qZ) * (qZ * qZ * qZ) == qY * (modp_inv2 #c (qZ * qZ * qZ) * (qZ * qZ * qZ))) canon}
    qY * (modp_inv2 #c (qZ * qZ * qZ) * (qZ * qZ * qZ)) % prime; 
    (==) {lemma_mod_mul_distr_r qY (modp_inv2 #c (qZ * qZ * qZ) * (qZ * qZ * qZ)) prime}
    qY * (modp_inv2 #c (qZ * qZ * qZ) * (qZ * qZ * qZ) % prime) % prime; 
    (==) {lemma_mod_inv2_mult_prime prime (qZ * qZ * qZ)}
    qY % prime;
    (==) {small_mod qY prime}
    qY; 
  };


  assert(pX == qX <==> pNX * (pZ * pZ) % prime == qNX * (qZ * qZ) % prime);
  assert(pY == qY <==> pNY * (pZ * pZ * pZ) % prime == qNY * (qZ * qZ * qZ) % prime)


let lemmaToDomainFromDomain #c #m a =
  let power = pow2 (getPower c) in 
  let prime = getModePrime m c in 

  calc (==) {
    fromDomain_ #c #m (toDomain_ #c #m a);
    (==) {lemmaFromDomain #c #m (toDomain_ #c #m a)}
    (toDomain_ #c #m a) * modp_inv2_prime power prime % prime;
    (==) {lemmaToDomain #c #m a}
    (a * power % prime) * modp_inv2_prime power prime % prime;
    (==) {lemma_mod_mul_distr_l (a * power) (modp_inv2_prime power prime) prime}
    a * pow2 (getPower c) * modp_inv2_prime power prime % prime;
    (==) {let open FStar.Tactics in let open FStar.Tactics.Canon in 
      assert_by_tactic (a * pow2 (getPower c) * modp_inv2_prime power prime == a * (pow2 (getPower c) * modp_inv2_prime power prime)) canon}
    a * (pow2 (getPower c) * modp_inv2_prime power prime) % prime;
    (==) {lemma_mod_mul_distr_r a (pow2 (getPower c) * modp_inv2_prime power prime) prime}
    a * (power * modp_inv2_prime power prime % prime) % prime;
    (==) {lemma_mod_inv2_mult_prime prime power}
    a % prime;
    (==) {modulo_lemma a prime}
    a;}


let lemmaFromDomainToDomain #c #m a =
  let prime = getModePrime m c in 
  let power = pow2 (getPower c) in 
  
  calc (==) {
    toDomain_ #c #m (fromDomain_ #c #m a);
    (==) {lemmaToDomain #c #m (fromDomain_ #c #m a)}
    (fromDomain_ #c #m a) * power % prime;
    (==) {lemmaToDomain #c #m a}
    (a * modp_inv2_prime power prime % prime) * power % prime; 
    (==) {lemma_mod_mul_distr_l (a * modp_inv2_prime power prime) power prime}
    (a * modp_inv2_prime power prime) * power % prime; 
    (==) {
      let open FStar.Tactics in let open FStar.Tactics.Canon in 
      assert_by_tactic (a  * modp_inv2_prime power prime * power == a * (pow2 (getPower c) * modp_inv2_prime power prime)) canon}
    a * (pow2 (getPower c) * modp_inv2_prime power prime) % prime;
    (==) {lemma_mod_mul_distr_r a (pow2 (getPower c) * modp_inv2_prime power prime) prime}
    a * (power * modp_inv2_prime power prime % prime) % prime;
    (==) {lemma_mod_inv2_mult_prime prime power}
    a % prime;
    (==) {modulo_lemma a prime}
    a; }


let lemmaFromDomainToDomainModuloPrime #c #m a =
  let prime = getModePrime m c in 
  let power = pow2 (getPower c) in 

  calc (==) {
    fromDomain_ #c #m (toDomain_ #c #m a);
    (==) {lemmaFromDomain #c #m (toDomain_ #c #m a)}
    (toDomain_ #c #m a) * modp_inv2_prime power prime % prime;
    (==) {lemmaToDomain #c #m a}
    (a * power % prime) * modp_inv2_prime power prime % prime;
    (==) {lemma_mod_mul_distr_l (a * power) (modp_inv2_prime power prime) prime}
    a * pow2 (getPower c) * modp_inv2_prime power prime % prime;
    (==) {let open FStar.Tactics in let open FStar.Tactics.Canon in 
      assert_by_tactic (a * pow2 (getPower c) * modp_inv2_prime power prime == a * (pow2 (getPower c) * modp_inv2_prime power prime)) canon}
    a * (pow2 (getPower c) * modp_inv2_prime power prime) % prime;
    (==) {lemma_mod_mul_distr_r a (pow2 (getPower c) * modp_inv2_prime power prime) prime}
    a * (power * modp_inv2_prime power prime % prime) % prime;
    (==) {lemma_mod_inv2_mult_prime prime power}
    a % prime;}

let lemmaToDomainFromDomainModuloPrime #c #m a = 
  let prime = getModePrime m c in 
  let power = pow2 (getPower c) in 

  calc (==) {
    toDomain_ #c #m (fromDomain_ #c #m a);
    (==) {lemmaToDomain #c #m (fromDomain_ #c #m a)}
    fromDomain_ #c #m a * power % prime;
    (==) {lemmaFromDomain #c #m a}
    (a * modp_inv2_prime power prime % prime) * power % prime;
    (==) {lemma_mod_mul_distr_l (a * modp_inv2_prime power prime) power prime}
    (a * modp_inv2_prime power prime) * power % prime; 
    (==) {let open FStar.Tactics in let open FStar.Tactics.Canon in 
      assert_by_tactic ((a * modp_inv2_prime power prime) * power == a * (power * modp_inv2_prime power prime)) canon}
    a * (pow2 (getPower c) * modp_inv2_prime power prime) % prime;  
    (==) {lemma_mod_mul_distr_r a (pow2 (getPower c) * modp_inv2_prime power prime) prime}
    a * (power * modp_inv2_prime power prime % prime) % prime;
    (==) {lemma_mod_inv2_mult_prime prime power}
    a % prime;}



let inDomain_mod_is_not_mod #c #m a =
  let prime = getModePrime m c in 
  let power = pow2 (getPower c) in 
  lemma_mod_mul_distr_l a power prime


let multiplicationInDomainNat #c #k #l #m a b =
  let prime = getModePrime m c in 
  let power = pow2 (getPower c) in 
  
  
  calc (==) { 
    a * b * modp_inv2_prime power prime % prime;
    (==) {}
    (toDomain_ #c #m k) * (toDomain_ #c #m l) * modp_inv2_prime power prime % prime;
    (==) {lemmaToDomain #c #m k; lemmaToDomain #c #m l}
    (k * power % prime) * (l * power % prime) * modp_inv2_prime power prime % prime;
    (==) {modulo_distributivity_mult2 (k * power) (l * power) (modp_inv2_prime power prime) prime}
    (k * power) * (l * power) * modp_inv2_prime power prime % prime;
    (==) {let open FStar.Tactics in let open FStar.Tactics.Canon in 
      assert_by_tactic ((k * power) * (l * power) * modp_inv2_prime power prime == 
	((k * l) * power) * (power * modp_inv2_prime power prime)) canon}
    ((k * l) * power) * (power * modp_inv2_prime power prime) % prime;
    (==) {lemma_mod_mul_distr_l ((k * l) * power) (power * modp_inv2_prime power prime) prime; 
      lemmaToDomain #c #m (k * l)} 
    toDomain_ #c #m (k * l) * (power * modp_inv2_prime power prime) % prime;
    (==) {lemma_mod_mul_distr_r (toDomain_ #c #m (k * l)) (power * modp_inv2_prime power prime) prime;
      lemma_mod_inv2_mult_prime prime power}
    toDomain_ #c #m (k * l) % prime;
    (==) {modulo_lemma (toDomain_ #c #m (k * l)) prime}
    toDomain_ #c #m (k * l);}


let additionInDomain #c #m a b =
  let prime = getModePrime m c in 
  let power = pow2 (getPower c) in 
  
  let k = fromDomain_ #c #m a in
  let l = fromDomain_ #c #m b in
  
  calc (==) {
    (a + b) % prime;
    == { lemmaFromDomainToDomain #c #m a; lemmaFromDomainToDomain #c #m b }
    (toDomain_ #c #m k + toDomain_ #c #m l) % prime;
    == { }
    (k * power % prime + l * power % prime) % prime;
    == { modulo_distributivity (k * power) (l * power) prime }
    (k * power + l * power) % prime;
    == { distributivity_add_left k l power }
    ((k + l) * power) % prime;
    == { }
    toDomain_ #c #m (fromDomain_ #c #m a + fromDomain_ #c #m b);
  }


let substractionInDomain #c #m a b =
  let prime = getModePrime m c in 
  let power = pow2 (getPower c) in 
  
  let k = fromDomain_ #c #m a in
  let l = fromDomain_ #c #m b in
  
  calc (==) {
    (a - b) % prime;
    == { lemmaFromDomainToDomain #c #m a; lemmaFromDomainToDomain #c #m b }
    (toDomain_ #c #m k - toDomain_ #c #m l) % prime;
    == { }
    (k * power % prime - l * power % prime) % prime;
    == { lemma_mod_sub_distr (k * power % prime) (l * power) prime }
    (k * power % prime - l * power) % prime;
    == { lemma_mod_add_distr (-(l * power)) (k * power) prime }
    (k * power - l * power) % prime;
    == { distributivity_sub_left k l power }
    ((k - l) * power) % prime;
    == { }
    toDomain_ #c #m (fromDomain_ #c #m a - fromDomain_ #c #m b);
  }


open Lib.ByteSequence

val ith_bit_power: #c: curve -> k: scalar_bytes #c -> i:nat{i < v (getScalarLen c)}
  -> t:uint64 {(v t == 0 \/ v t == 1) /\ v t == nat_from_intseq_le k / pow2 i % 2}

let ith_bit_power #c k i =
  let q = i / 8 in
  let r = i % 8 in
  let tmp1 = k.[q] >>. (size r) in
  let tmp2 = tmp1 &. u8 1 in
  let res = to_u64 tmp2 in
  
  logand_le tmp1 (u8 1);
  logand_mask tmp1 (u8 1) 1;
  lemma_scalar_ith c k q;
  
  let k = nat_from_intseq_le k in
  pow2_modulo_division_lemma_1 (k / pow2 (8 * (i / 8))) (i % 8) 8;
  division_multiplication_lemma k (pow2 (8 * (i / 8))) (pow2 (i % 8));
  lemma_euclidian_for_ithbit k i;
  pow2_modulo_modulo_lemma_1 (k / pow2 i) 1 (8 - (i % 8));
  res


let _pow_step0 #c #m r0 r1 =
  let prime = getModePrime m c in 
  let r1 = (r0 * r1) % prime in 
  let r0 = (r0 * r0) % prime in 
  r0, r1


let _pow_step1 #c #m r0 r1 =
  let prime = getModePrime m c in 
  let r0 = (r0 * r1) % prime in 
  let r1 = (r1 * r1) % prime in 
  (r0, r1)


let conditional_swap_pow i p q =
  if v i = 0 then (p, q) else (q, p)

let lemma_swaped_steps p q = ()

open Lib.ByteSequence

let _pow_step #c #m k i (p, q) =
  let bit = v (getScalarLen c) - 1 - i in
  let bit = ith_bit_power #c k bit in
  let open Lib.RawIntTypes in
  if uint_to_nat bit = 0 then _pow_step0 #c #m p q else _pow_step1 #c #m p q


val lemma_even: #c: curve -> #m: mode 
  -> index:pos{index <= v (getScalarLen c)} 
  -> k:scalar_bytes {v (ith_bit_power #c k (v (getScalarLen c) - index)) == 0} ->
  Lemma (
    let k = nat_from_bytes_le k in
    let newIndex = v (getScalarLen c) - index in
    2 * arithmetic_shift_right k (newIndex + 1) ==
    arithmetic_shift_right k newIndex)

let lemma_even #c index k =
  let number = nat_from_bytes_le k in
  let n = v (getScalarLen c) - index in
  FStar.Math.Lemmas.pow2_double_mult n;
  lemma_div_def (number / pow2 n) 2;
  FStar.Math.Lemmas.division_multiplication_lemma number (pow2 n) 2


val lemma_odd: #c: curve 
  -> index:pos{index <= v (getScalarLen c) } 
  -> k:scalar_bytes {uint_v (ith_bit_power #c k (v (getScalarLen c) - index)) == 1} ->
  Lemma(
    let k = nat_from_intseq_le k in
    let n = v (getScalarLen c) - index  in
    2 * arithmetic_shift_right k (n + 1) + 1 ==
    arithmetic_shift_right k n)

let lemma_odd #c index k =
  let number = nat_from_bytes_le k in
  let n = (getCoordinateLen c) * 8 - index in
  let a0 = 2 * arithmetic_shift_right number (n + 1) + 1 in
  lemma_div_def (number / pow2 n) 2;
  division_multiplication_lemma number (pow2 n) 2;
  pow2_double_mult n;
  assert (arithmetic_shift_right number (n + 1) == number / pow2 (n + 1));
  assert (arithmetic_shift_right number n ==
          2 * arithmetic_shift_right number (n + 1) + 1)


#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"

val lemma_exponen_spec:
  #c: curve 
  -> #m: mode 
  -> k: scalar_bytes #c
  -> start:tuple2 nat nat {let st0, st1 = start in st0 == 1 /\ st1 < getModePrime m c}
  -> index:nat{index <= v (getScalarLen c)} ->
  Lemma (
    let start0, start1 = start in
    let number = nat_from_bytes_le #SEC k in
    let newIndex = v (getScalarLen c) - index in
    let f0, f1 = Lib.LoopCombinators.repeati index (_pow_step #c #m k) (start0, start1) in
    f0 == pow start1 (arithmetic_shift_right number newIndex) % getModePrime m c /\
    f1 == pow start1 (arithmetic_shift_right number newIndex + 1) % getModePrime m c
  )


val lemma_exponen_spec_0:
  #c: curve 
  -> #m: mode 
  -> k: scalar_bytes #c
  -> start:tuple2 nat nat {let st0, st1 = start in st0 == 1 /\ st1 < getModePrime m c} 
  -> Lemma (
    let prime = getModePrime m c in 
    let start0, start1 = start in
    let number = nat_from_bytes_le k in
    let newIndex = v (getScalarLen c) in
    let f0, f1 = Lib.LoopCombinators.repeati 0 (_pow_step #c #m k) (start0, start1) in
    f0 == pow start1 (arithmetic_shift_right number newIndex) % prime /\
    f1 == pow start1 (arithmetic_shift_right number newIndex + 1) % prime
  )

let lemma_exponen_spec_0 #c #m k start =
  let prime = getModePrime m c in 
  let power = pow2 (getPower c) in 

  let st0, st1 = start in
  let number = nat_from_bytes_le #SEC k in
    assert (arithmetic_shift_right number (v (getScalarLen c)) == number / power);
  FStar.Math.Lemmas.lemma_div_lt_nat number (v (getScalarLen c)) (v (getScalarLen c));
    assert (arithmetic_shift_right number (v (getScalarLen c)) == 0);
  Lib.LoopCombinators.eq_repeati0 (v (getScalarLen c)) (_pow_step #c #m k) (st0, st1);
  FStar.Math.Lemmas.small_modulo_lemma_1 st1 prime


#pop-options

let rec lemma_exponen_spec #c #m k start index =
  let prime = getModePrime m c in 
  let power = pow2 (getPower c) in 

  let f = _pow_step #c #m k in
  let st0, st1 = start in
  let number = nat_from_bytes_le k in
  let newIndex = (getCoordinateLen c) * 8 - index in
  let open Lib.LoopCombinators in
  match index with
  | 0 -> lemma_exponen_spec_0 #c #m k start
  | _ ->
    begin
    let p2 = getPower c in 
    unfold_repeati p2 f (st0, st1) (index - 1);
    lemma_exponen_spec #c #m k start (index - 1);
    let bitMask = uint_v (ith_bit_power #c k (p2 - index)) in
    match bitMask with
      | 0 ->
        let a0 = pow st1 (arithmetic_shift_right number (p2 - index + 1)) in
        let a1 = pow st1 (arithmetic_shift_right number (p2 - index + 1) + 1) in
        calc (==) {
          (a0 % prime) * (a0 % prime) % prime;
          == {modulo_distributivity_mult a0 a0 prime}
          (a0 * a0) % prime;
          == { }
          (pow st1 (arithmetic_shift_right number (p2 - index + 1)) * pow st1 (arithmetic_shift_right number (p2 - index + 1))) % prime;
          == {pow_plus st1 (arithmetic_shift_right number (p2 - index + 1)) (arithmetic_shift_right number (p2 - index + 1))}
          (pow st1 (arithmetic_shift_right number (p2 - index + 1) + arithmetic_shift_right number (p2 - index + 1))) % prime;
          == {}
          (pow st1 (2 * arithmetic_shift_right number (p2 - index + 1))) % prime;
          == {lemma_even #c #m index k}
          pow st1 (arithmetic_shift_right number newIndex) % prime;
        };
        calc (==) {
          (a0 % prime) * (a1 % prime) % prime;
          == {modulo_distributivity_mult a0 a1 prime}
          (a0 * a1) % prime;
          == { }
          (pow st1 (arithmetic_shift_right number (p2 - index + 1)) * pow st1 (arithmetic_shift_right number (p2 - index + 1) + 1)) % prime;
          == {pow_plus st1 (arithmetic_shift_right number (p2 - index + 1)) (arithmetic_shift_right number (p2 - index + 1) + 1)}
          (pow st1 (arithmetic_shift_right number (p2 - index + 1) + arithmetic_shift_right number (p2 - index + 1) + 1)) % prime;
          == {}
          (pow st1 (2 * arithmetic_shift_right number (p2 - index + 1) + 1)) % prime;
          == {lemma_even #c #m index k}
          (pow st1 (arithmetic_shift_right number (p2 - index) + 1)) % prime;
        }
      | 1 ->
        let a0 = pow st1 (arithmetic_shift_right number (p2 - index + 1)) in
        let a1 = pow st1 (arithmetic_shift_right number (p2 - index + 1) + 1) in
        calc (==) {
          (a1 % prime) * (a1 % prime) % prime;
          == {modulo_distributivity_mult a1 a1 prime}
          (a1 * a1) % prime;
          == { }
          (pow st1 (arithmetic_shift_right number (p2 - index + 1) + 1) * pow st1 (arithmetic_shift_right number (p2 - index + 1) + 1)) % prime;
          == {pow_plus st1 (arithmetic_shift_right number (p2 - index + 1) + 1) (arithmetic_shift_right number (p2 - index + 1) + 1)}
          (pow st1 (arithmetic_shift_right number (p2 - index + 1) + 1 + arithmetic_shift_right number (p2 - index + 1) + 1)) % prime;
          == {}
          (pow st1 (2 * arithmetic_shift_right number (p2 - index + 1) + 2)) % prime;
          == {lemma_odd #c index k}
          pow st1 (arithmetic_shift_right number newIndex + 1) % prime;
        };
        calc (==) {
          (a0 % prime) * (a1 % prime) % prime;
          == {modulo_distributivity_mult a0 a1 prime}
          (a0 * a1) % prime;
          == { }
          (pow st1 (arithmetic_shift_right number (p2 - index + 1)) * pow st1 (arithmetic_shift_right number (p2 - index + 1) + 1)) % prime;
          == {pow_plus st1 (arithmetic_shift_right number (p2 - index + 1)) (arithmetic_shift_right number (p2 - index + 1) + 1)}
          (pow st1 (arithmetic_shift_right number (p2 - index + 1) + arithmetic_shift_right number (p2 - index + 1) + 1)) % prime;
          == {}
          (pow st1 (2 * arithmetic_shift_right number (p2 - index + 1) + 1)) % prime;
          == {lemma_odd #c index k}
          (pow st1 (arithmetic_shift_right (nat_from_bytes_le k) (p2 - index)) % prime);
        }
    end


let pow_spec #c #m k p =
  let a, b = Lib.LoopCombinators.repeati (v (getScalarLen c)) (_pow_step #c #m k) (1, p) in 
  lemma_exponen_spec #c #m k (1, p) (v (getScalarLen c));
  a


let sq_root_spec #c #m a = 
  let prime = getModePrime m c in 
  pow a ((prime + 1) / 4) % prime
