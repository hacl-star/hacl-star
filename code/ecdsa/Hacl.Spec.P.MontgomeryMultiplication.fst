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


let fromDomain_ #c a = a * modp_inv2 #c (pow2 (getPower c)) % (getPrime c)

let fromDomainPoint #c a =
  let x, y, z = a in
  fromDomain_ #c x, fromDomain_ #c y, fromDomain_ #c z


let toDomain_ #c a = a * pow2 (getPower c) % (getPrime c)

let lemmaFromDomain a = ()

let lemmaToDomain #c a = ()


let lemmaToDomainAndBackIsTheSame #c a =
  let power = getPower2 c in 
  let prime = getPrime c in 
  
  let to = toDomain_ #c a in
  lemmaToDomain #c a;
  let from = fromDomain_ #c to in
  lemmaFromDomain #c to;
  lemma_mod_mul_distr_l (a * power) (modp_inv2 #c power) prime;
  
  assert_norm (pow2 256 * modp_inv2 #P256 (pow2 256) % prime256 = 1);
  assert_norm (pow2 384 * modp_inv2 #P384 (pow2 384) % prime384 = 1);
  
  modulo_distributivity_mult_last_two a 1 1 power (modp_inv2 #c power) prime;
  modulo_lemma a prime


let lemmaFromDomainToDomain #c a =
  let prime = getPrime c in 
  let power = getPower2 c in 
  
  let from = fromDomain_ #c a in
  lemmaFromDomain #c a;
  let to = toDomain_ #c from in
  lemmaToDomain #c from;
  lemma_mod_mul_distr_l (a * modp_inv2 #c power) power prime;
  
  assert_norm (modp_inv2 #P256 (pow2 256) * (pow2 256) % prime256 = 1);
  assert_norm (modp_inv2 #P384 (pow2 384) * (pow2 384) % prime384 = 1);
  
  modulo_distributivity_mult_last_two a 1 1 (modp_inv2 #c power) power prime;
  modulo_lemma a prime


let lemmaFromDomainToDomainModuloPrime #c a =
  let prime = getPrime c in 
  let power = getPower2 c in 
  
  lemma_mod_mul_distr_l (a * power) (modp_inv2 #c power) prime;
  
  assert_norm (pow2 256 * modp_inv2 #P256 (pow2 256) % prime256 = 1);
  assert_norm (pow2 384 * modp_inv2 #P384 (pow2 384) % prime384 = 1);
  
  modulo_distributivity_mult_last_two a 1 1 power (modp_inv2 #c power) prime


let inDomain_mod_is_not_mod #c a =
  let prime = getPrime c in 
  let power = getPower2 c in 

  lemma_mod_mul_distr_l a power prime


let multiplicationInDomainNat #c #k #l a b =
  let prime = getPrime c in 
  let power = getPower2 c in 

  let multResult = a * b * modp_inv2_prime power prime % prime in
  
  modulo_distributivity_mult2 (k * power) (l * power) (modp_inv2_prime power prime) prime;
  lemma_twice_brackets k power 1 l power 1 (modp_inv2 #c power);
  
  assert_norm (pow2 256 * modp_inv2 #P256 (pow2 256) % prime256 == 1);
  assert_norm (pow2 384 * modp_inv2 #P384 (pow2 384) % prime384 == 1);
    
  modulo_distributivity_mult_last_two k power l power (modp_inv2 #c power) prime;
  lemma_mul_associativity_3 k power l


let additionInDomain #c a b =
  let prime = getPrime c in 
  let power = getPower2 c in 
  
  let k = fromDomain_ #c a in
  let l = fromDomain_ #c b in
  
  calc (==) {
    (a + b) % prime;
    == { lemmaFromDomainToDomain #c a; lemmaFromDomainToDomain #c b }
    (toDomain_ #c k + toDomain_ #c l) % prime;
    == { }
    (k * power % prime + l * power % prime) % prime;
    == { modulo_distributivity (k * power) (l * power) prime }
    (k * power + l * power) % prime;
    == { distributivity_add_left k l power }
    ((k + l) * power) % prime;
    == { }
    toDomain_ #c (fromDomain_ #c a + fromDomain_ #c b);
  }


let substractionInDomain #c a b =
  let prime = getPrime c in 
  let power = getPower2 c in 
  
  let k = fromDomain_ #c a in
  let l = fromDomain_ #c b in
  
  calc (==) {
    (a - b) % prime;
    == { lemmaFromDomainToDomain #c a; lemmaFromDomainToDomain #c b }
    (toDomain_ #c k - toDomain_ #c l) % prime;
    == { }
    (k * power % prime - l * power % prime) % prime;
    == { lemma_mod_sub_distr (k * power % prime) (l * power) prime }
    (k * power % prime - l * power) % prime;
    == { lemma_mod_add_distr (-(l * power)) (k * power) prime }
    (k * power - l * power) % prime;
    == { distributivity_sub_left k l power }
    ((k - l) * power) % prime;
    == { }
    toDomain_ #c (fromDomain_ #c a - fromDomain_ #c b);
  }


open Lib.ByteSequence

val ith_bit_power: #c: curve -> k:lbytes (getCoordinateLen c) 
  -> i:nat{i < (getCoordinateLen c) * 8}
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


let _pow_step0 #c r0 r1 =
  let r1 = (r0 * r1) % (getPrime c) in 
  let r0 = (r0 * r0) % (getPrime c) in 
  r0, r1


let _pow_step1 #c r0 r1 =
  let r0 = (r0 * r1) % (getPrime c) in 
  let r1 = (r1 * r1) % (getPrime c) in 
  (r0, r1)


let conditional_swap_pow i p q =
  if v i = 0 then (p, q) else (q, p)

let lemma_swaped_steps p q = ()

open Lib.ByteSequence

let _pow_step #c k i (p, q) =
  let bit = (getCoordinateLen c) * 8 -1 - i in
  let bit = ith_bit_power #c k bit in
  let open Lib.RawIntTypes in
  if uint_to_nat bit = 0 then _pow_step0 p q else _pow_step1 p q


val lemma_even: #c: curve 
  -> index:pos{index <= (getCoordinateLen c) * 8} 
  -> k:lseq uint8 (getCoordinateLen c) 
    {v (ith_bit_power k ((getCoordinateLen c) * 8 - index)) == 0} ->
  Lemma (
    let number = nat_from_bytes_le k in
    let newIndex = (getCoordinateLen c) * 8 - index in
    2 * arithmetic_shift_right number (newIndex + 1) ==
    arithmetic_shift_right number newIndex)

let lemma_even #c index k =
  let number = nat_from_bytes_le k in
  let n = (getCoordinateLen c) * 8 - index in
  FStar.Math.Lemmas.pow2_double_mult n;
  lemma_div_def (number / pow2 n) 2;
  FStar.Math.Lemmas.division_multiplication_lemma number (pow2 n) 2


val lemma_odd: #c: curve 
  -> index:pos{index <= (getCoordinateLen c) * 8} 
  -> k:lseq uint8 (getCoordinateLen c) 
    {uint_v (ith_bit_power k ((getCoordinateLen c) * 8 - index)) == 1} ->
  Lemma(
    let number = nat_from_intseq_le k in
    let n = (getCoordinateLen c) * 8 - index  in
    2 * arithmetic_shift_right number (n + 1) + 1 ==
    arithmetic_shift_right number n)

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


val lemma_exponen_spec:
  #c: curve 
  -> k: scalar_bytes #c
  -> start:tuple2 (nat_prime #c) (nat_prime #c) {let st0, st1 = start in st0 == 1}
  -> index:nat{index <= getPower c} ->
  Lemma (
    let start0, start1 = start in
    let number = nat_from_bytes_le #SEC k in
    let newIndex = getPower c - index in
    let f0, f1 = Lib.LoopCombinators.repeati index (_pow_step k) start in
    f0 == pow start1 (arithmetic_shift_right number newIndex) % getPrime c /\
    f1 == pow start1 (arithmetic_shift_right number newIndex + 1) % getPrime c
  )

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"

val lemma_exponen_spec_0:
  #c: curve 
  -> k: scalar_bytes #c
  -> start:tuple2 nat_prime nat_prime {let st0, _ = start in st0 == 1} 
  -> Lemma (
    let prime = getPrime c in 
    let start0, start1 = start in
    let number = nat_from_bytes_le k in
    let newIndex = (getCoordinateLen c) * 8 in
    let f0, f1 = Lib.LoopCombinators.repeati 0 (_pow_step #c k) start in
    f0 == pow start1 (arithmetic_shift_right number newIndex) % prime /\
    f1 == pow start1 (arithmetic_shift_right number newIndex + 1) % prime
  )

let lemma_exponen_spec_0 #c k start =
  let prime = getPrime c in 
  let power = getPower2 c in 

  let st0, st1 = start in
  let number = nat_from_bytes_le #SEC k in
    assert (arithmetic_shift_right number (getPower c) == number / power);
  FStar.Math.Lemmas.lemma_div_lt_nat number (getPower c) (getPower c);
    assert (arithmetic_shift_right number (getPower c) == 0);
  Lib.LoopCombinators.eq_repeati0 (getPower c) (_pow_step k) start;
  FStar.Math.Lemmas.small_modulo_lemma_1 st1 prime


#pop-options

let rec lemma_exponen_spec #c k start index =
  let prime = getPrime c in 
  let power = getPower2 c in 

  let f = _pow_step k in
  let st0, st1 = start in
  let number = nat_from_bytes_le k in
  let newIndex = (getCoordinateLen c) * 8 - index in
  let open Lib.LoopCombinators in
  match index with
  | 0 -> lemma_exponen_spec_0 k start
  | _ ->
    begin
    let p2 = getPower c in 
    unfold_repeati p2 f start (index - 1);
    lemma_exponen_spec k start (index - 1);
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
          == {lemma_even #c index k}
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
          == {lemma_even #c index k}
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


let pow_spec #c k p =
  let a, b = Lib.LoopCombinators.repeati (getScalarLenNat c) (_pow_step k) (1, p) in 
  lemma_exponen_spec k (1, p) (getPower c);
  a


let sq_root_spec #c a = 
  let prime = getPrime c in 
  pow a ((prime + 1) / 4) % prime
