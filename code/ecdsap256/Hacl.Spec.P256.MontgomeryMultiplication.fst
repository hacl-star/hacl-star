module Hacl.Spec.P256.MontgomeryMultiplication

open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul

open Spec.P256
open Spec.ECDSA.Lemmas
open Hacl.Spec.P256.Definition
open Hacl.Lemmas.P256

open Lib.IntTypes

#set-options "--z3rlimit 40 --fuel 0 --ifuel 0"

let fromDomain_ #c a = (a * modp_inv2 #c (pow2 (getPower c))) % (getPrime c)


let fromDomainPoint #c a =
  let x, y, z = a in
  fromDomain_ #c x, fromDomain_ #c y, fromDomain_ #c z


let toDomain_ #c a = (a * pow2 (getPower c)) % (getPrime c)


let lemmaFromDomain a = ()


let lemmaToDomain a = ()


let lemmaToDomainAndBackIsTheSame #c a =
  admit();
  let to = toDomain_ #c a in
  lemmaToDomain #c a;
  let from = fromDomain_ #c to in
  lemmaFromDomain #c to;
  lemma_mod_mul_distr_l (a * pow2 256) (modp_inv2 #P256 (pow2 256)) prime256;
  assert_norm (pow2 256 * modp_inv2 #P256 (pow2 256) % prime256 = 1);
  modulo_distributivity_mult_last_two a 1 1 (pow2 256) (modp_inv2 #P256 (pow2 256)) prime256;
  modulo_lemma a (getPrime c)


let lemmaFromDomainToDomain #c a =
  let prime = getPrime c in 
  let from = fromDomain_ #c a in
  lemmaFromDomain #c a;
  let to = toDomain_ #c from in
  lemmaToDomain #c from;
  lemma_mod_mul_distr_l (a * modp_inv2 #P256 (pow2 256)) (pow2 256)  prime256;
  assert_norm (modp_inv2 #P256 (pow2 256) * (pow2 256) % prime = 1);
  modulo_distributivity_mult_last_two a 1 1 (modp_inv2 #P256 (pow2 256)) (pow2 256) prime256;
  modulo_lemma a prime


let lemmaFromDomainToDomainModuloPrime a =
  lemma_mod_mul_distr_l (a*pow2 256) (modp_inv2 #P256 (pow2 256)) prime256;
  assert_norm (pow2 256 * modp_inv2 #P256 (pow2 256) % prime256 = 1);
  modulo_distributivity_mult_last_two a 1 1 (pow2 256) (modp_inv2 #P256 (pow2 256)) prime256


let inDomain_mod_is_not_mod a =
  lemma_mod_mul_distr_l a (pow2 256) prime256


let multiplicationInDomainNat #c #k #l a b =
  let prime = getPrime c in 
  assert_norm (prime256 > 3);
  let multResult = a * b * modp_inv2_prime (pow2 256) prime256 % prime256 in
  modulo_distributivity_mult2 (k * pow2 256) (l * pow2 256) (modp_inv2_prime (pow2 256) prime256) prime;
  lemma_twice_brackets k (pow2 256) 1 l (pow2 256) 1 (modp_inv2 #P256 (pow2 256));
  assert_norm (pow2 256 * modp_inv2 #P256 (pow2 256) % prime == 1);
  modulo_distributivity_mult_last_two k (pow2 256) l (pow2 256) (modp_inv2 #P256 (pow2 256)) prime;
  lemma_mul_associativity_3 k (pow2 256) l

let additionInDomain #c a b =
  let prime = getPrime c in 
  let k = fromDomain_ #c a in
  let l = fromDomain_ #c b in
  calc (==) {
    (a + b) % prime256;
    == { lemmaFromDomainToDomain #c a; lemmaFromDomainToDomain #c b }
    (toDomain_ #c k + toDomain_ #c l) % prime256;
    == { }
    (k * pow2 256 % prime256 + l * pow2 256 % prime256) % prime256;
    == { modulo_distributivity (k * pow2 256) (l * pow2 256) prime }
    (k * pow2 256 + l * pow2 256) % prime256;
    == { distributivity_add_left k l (pow2 256) }
    ((k + l) * pow2 256) % prime256;
    == { }
    toDomain_ #c (fromDomain_ #c a + fromDomain_ #c b);
  }


let substractionInDomain #c a b =
  let prime = getPrime c in 
  let k = fromDomain_ #c a in
  let l = fromDomain_ #c b in
  calc (==) {
    (a - b) % prime256;
    == { lemmaFromDomainToDomain #c a; lemmaFromDomainToDomain #c b }
    (toDomain_ #c k - toDomain_ #c l) % prime256;
    == { }
    (k * pow2 256 % prime256 - l * pow2 256 % prime256) % prime256;
    == { lemma_mod_sub_distr (k * pow2 256 % prime256) (l * pow2 256) prime }
    (k * pow2 256 % prime256 - l * pow2 256) % prime256;
    == { lemma_mod_add_distr (-(l * pow2 256)) (k * pow2 256) prime }
    (k * pow2 256 - l * pow2 256) % prime256;
    == { distributivity_sub_left k l (pow2 256) }
    ((k - l) * pow2 256) % prime256;
    == { }
    toDomain_ #c (fromDomain_ #c a - fromDomain_ #c b);
  }

open Lib.ByteSequence

val ith_bit_power: k:lbytes 32 -> i:nat{i < 256}
  -> t:uint64 {(v t == 0 \/ v t == 1) /\ v t == nat_from_intseq_le k / pow2 i % 2}

let ith_bit_power k i =
  let q = i / 8 in
  let r = i % 8 in
  let tmp1 = k.[q] >>. (size r) in
  let tmp2 = tmp1 &. u8 1 in
  let res = to_u64 tmp2 in
  logand_le tmp1 (u8 1);
  logand_mask tmp1 (u8 1) 1;
  lemma_scalar_ith P256 k q;
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

let _pow_step k i (p, q) =
  let bit = 255 - i in
  let bit = ith_bit_power k bit in
  let open Lib.RawIntTypes in
  if uint_to_nat bit = 0 then _pow_step0 p q else _pow_step1 p q



val lemma_even: index:pos{index <= 256} -> k:lseq uint8 32 {v (ith_bit_power k (256 - index)) == 0} ->
  Lemma (
    let number = nat_from_bytes_le k in
    let newIndex = 256 - index in
    2 * arithmetic_shift_right number (newIndex + 1) ==
    arithmetic_shift_right number newIndex)

let lemma_even index k =
  let number = nat_from_bytes_le k in
  let n = 256 - index in
  FStar.Math.Lemmas.pow2_double_mult n;
  lemma_div_def (number / pow2 n) 2;
  FStar.Math.Lemmas.division_multiplication_lemma number (pow2 n) 2


val lemma_odd: index:pos{index <= 256} -> k:lseq uint8 32 {uint_v (ith_bit_power k (256 - index)) == 1} ->
  Lemma(
    let number = nat_from_intseq_le k in
    let n = 256 - index  in
    2 * arithmetic_shift_right number (n + 1) + 1 ==
    arithmetic_shift_right number n)

let lemma_odd index k =
  let number = nat_from_bytes_le k in
  let n = 256 - index in
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
    let start0, start1 = start in
    let number = nat_from_bytes_le k in
    let newIndex = 256 in
    let f0, f1 = Lib.LoopCombinators.repeati 0 (_pow_step #c k) start in
    f0 == pow start1 (arithmetic_shift_right number newIndex) % prime256 /\
    f1 == pow start1 (arithmetic_shift_right number newIndex + 1) % prime256
  )

let lemma_exponen_spec_0 k start =
  let st0, st1 = start in
  let number = nat_from_bytes_le #SEC k in
    assert (arithmetic_shift_right number 256 == number / pow2 256);
  FStar.Math.Lemmas.lemma_div_lt_nat number 256 256;
    assert (arithmetic_shift_right number 256 == 0);
  Lib.LoopCombinators.eq_repeati0 256 (_pow_step k) start;
  FStar.Math.Lemmas.small_modulo_lemma_1 st1 prime256


#pop-options

let rec lemma_exponen_spec k start index =
  let f = _pow_step k in
  let st0, st1 = start in
  let number = nat_from_bytes_le k in
  let newIndex = 256 - index in
  let open Lib.LoopCombinators in
  match index with
  | 0 -> lemma_exponen_spec_0 k start
  | _ ->
    begin
    unfold_repeati 256 f start (index - 1);
    lemma_exponen_spec k start (index - 1);
    let bitMask = uint_v (ith_bit_power k (256 - index)) in
    match bitMask with
      | 0 ->
        let a0 = pow st1 (arithmetic_shift_right number (256 - index + 1)) in
        let a1 = pow st1 (arithmetic_shift_right number (256 - index + 1) + 1) in
        calc (==) {
          (a0 % prime256) * (a0 % prime256) % prime256;
          == {modulo_distributivity_mult a0 a0 prime256}
          (a0 * a0) % prime256;
          == { }
          (pow st1 (arithmetic_shift_right number (256 - index + 1)) * pow st1 (arithmetic_shift_right number (256 - index + 1))) % prime256;
          == {pow_plus st1 (arithmetic_shift_right number (256 - index + 1)) (arithmetic_shift_right number (256 - index + 1))}
          (pow st1 (arithmetic_shift_right number (256 - index + 1) + arithmetic_shift_right number (256 - index + 1))) % prime256;
          == {}
          (pow st1 (2 * arithmetic_shift_right number (256 - index + 1))) % prime256;
          == {lemma_even index k}
          pow st1 (arithmetic_shift_right number newIndex) % prime256;
        };
        calc (==) {
          (a0 % prime256) * (a1 % prime256) % prime256;
          == {modulo_distributivity_mult a0 a1 prime256}
          (a0 * a1) % prime256;
          == { }
          (pow st1 (arithmetic_shift_right number (256 - index + 1)) * pow st1 (arithmetic_shift_right number (256 - index + 1) + 1)) % prime256;
          == {pow_plus st1 (arithmetic_shift_right number (256 - index + 1)) (arithmetic_shift_right number (256 - index + 1) + 1)}
          (pow st1 (arithmetic_shift_right number (256 - index + 1) + arithmetic_shift_right number (256 - index + 1) + 1)) % prime256;
          == {}
          (pow st1 (2* arithmetic_shift_right number (256 - index + 1) + 1)) % prime256;
          == {lemma_even index k}
          (pow st1 (arithmetic_shift_right number (256 - index) + 1)) % prime256;
        }
      | 1 ->
        let a0 = pow st1 (arithmetic_shift_right number (256 - index + 1)) in
        let a1 = pow st1 (arithmetic_shift_right number (256 - index + 1) + 1) in
        calc (==) {
          (a1 % prime256) * (a1 % prime256) % prime256;
          == {modulo_distributivity_mult a1 a1 prime256}
          (a1 * a1) % prime256;
          == { }
          (pow st1 (arithmetic_shift_right number (256 - index + 1) + 1) * pow st1 (arithmetic_shift_right number (256 - index + 1) + 1)) % prime256;
          == {pow_plus st1 (arithmetic_shift_right number (256 - index + 1) + 1) (arithmetic_shift_right number (256 - index + 1) + 1)}
          (pow st1 (arithmetic_shift_right number (256 - index + 1) + 1 + arithmetic_shift_right number (256 - index + 1) + 1)) % prime256;
          == {}
          (pow st1 (2 * arithmetic_shift_right number (256 - index + 1) + 2)) % prime256;
          == {lemma_odd index k}
          pow st1 (arithmetic_shift_right number newIndex + 1) % prime256;
        };
        calc (==) {
          (a0 % prime256) * (a1 % prime256) % prime256;
          == {modulo_distributivity_mult a0 a1 prime256}
          (a0 * a1) % prime256;
          == { }
          (pow st1 (arithmetic_shift_right number (256 - index + 1)) * pow st1 (arithmetic_shift_right number (256 - index + 1) + 1)) % prime256;
          == {pow_plus st1 (arithmetic_shift_right number (256 - index + 1)) (arithmetic_shift_right number (256 - index + 1) + 1)}
          (pow st1 (arithmetic_shift_right number (256 - index + 1) + arithmetic_shift_right number (256 - index + 1) + 1)) % prime256;
          == {}
          (pow st1 (2* arithmetic_shift_right number (256 - index + 1) + 1)) % prime256;
          == {lemma_odd index k}
          (pow st1 (arithmetic_shift_right (nat_from_bytes_le k) (256 - index)) % prime256);
        }
    end


let pow_spec k p =
  assert_norm (1 < prime256);
  let a, b = Lib.LoopCombinators.repeati 256 (_pow_step k) (1, p) in 
  lemma_exponen_spec k (1, p) 256;
  a


let sq_root_spec a = 
  pow a ((prime256 + 1) / 4) % prime256
