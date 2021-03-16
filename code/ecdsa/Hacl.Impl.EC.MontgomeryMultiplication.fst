module Hacl.Impl.EC.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes

open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Impl.EC.LowLevel
open Hacl.Impl.EC.MontgomeryMultiplication.Lemmas

open Lib.Loops
open Hacl.Impl.EC.Setup

#set-options "--z3rlimit 300"

open Lib.Sequence 

val lemma_test: #l: size_nat -> c: curve ->  a: lseq uint64 l -> i: nat {i <= l} 
  -> Lemma (ensures (
    let a0 = sub a 0 i in 
    let a1 = sub a i (l - i) in 
    lseq_as_nat a = lseq_as_nat a0 + pow2 (64 * i) * lseq_as_nat a1))
    (decreases (l - i))

let rec lemma_test #l c a i = 
  if i = 0 then begin 
    let a0 = sub a 0 0 in 
    let a1 = sub a 0 l in 
    lseq_as_nat_last a0
    end
  else begin if i = l then lseq_as_nat_last (sub a l 0) else
    begin 
      let a0 = sub a 0 i in 
      let a1 = sub a i (l - i) in 

      calc (==) 
      {
	lseq_as_nat a1;
	(==) {lemma_test #(l - i) c a1 1}
	lseq_as_nat (sub a1 0 1) + pow2 64 * lseq_as_nat (sub a1 1 (l - i - 1));
	(==) {lseq_as_nat_first (sub a1 0 1)}
	v (index a1 0) + pow2 64 * lseq_as_nat (sub a1 1 (l - i - 1));
	(==) {Seq.lemma_index_slice a 0 (i + 1) i}
	v (index a i) + pow2 64 * lseq_as_nat (sub a (i + 1) (l - (i + 1)));
      };
    
    assert(lseq_as_nat a1 - v (index a i) =  pow2 64 * lseq_as_nat (sub a (i + 1) (l - (i + 1))));

    lemma_lseq_as_seq_extension (sub a 0 (i + 1)) (sub a 0 i) i;

    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 

    
    calc (==) {
      lseq_as_nat a;
      (==) {lemma_test c a (i + 1)}
      lseq_as_nat (sub a 0 (i + 1)) + pow2 (64 * (i + 1)) * lseq_as_nat (sub a (i + 1) (l - (i + 1)));
      (==) { pow2_plus (64 * i) 64}
      lseq_as_nat (sub a 0 (i + 1)) + pow2 (64 * i) * pow2 64 * lseq_as_nat (sub a (i + 1) (l - (i + 1)));
      (==) {assert_by_tactic (pow2 (64 * i) * pow2 64 * lseq_as_nat (sub a  (i + 1) (l - (i + 1))) == 
	pow2 (64 * i) * (pow2 64 * lseq_as_nat (sub a (i + 1) (l - (i + 1))))) canon}
      lseq_as_nat (sub a 0 (i + 1)) + pow2 (64 * i) * (pow2 64 * lseq_as_nat (sub a (i + 1) (l - (i + 1))));
      (==) {assert(lseq_as_nat a1 - v (index a i) =  pow2 64 * lseq_as_nat (sub a (i + 1) (l - (i + 1))))}
      lseq_as_nat (sub a 0 (i + 1)) - pow2 (64 * i) * v (index a i) + pow2 (64 * i) * lseq_as_nat a1; 
      (==) {assert (lseq_as_nat (sub a 0 (i + 1)) == lseq_as_nat (sub a 0 i) + pow2 (64 * i) * v (index a i))}
      lseq_as_nat (sub a 0 i) + pow2 (64 * i) * lseq_as_nat a1;}
    end end



open Lib.Buffer


inline_for_extraction
val supportsReducedMultiplication: #c: curve -> 
  Tot  (r: bool {r ==> v (Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWord #c)) == 1})

let supportsReducedMultiplication #c = 
  let open Lib.RawIntTypes in 
  let r = FStar.UInt64.eq (Lib.RawIntTypes.u64_to_UInt64 (getLastWord #c)) 0xffffffffffffffffuL in 
  lemma_mod_sub_distr 0 (getPrime c) (pow2 64);
  assert_norm (exp #(pow2 64) 1 (pow2 64 - 1) == 1);
  r


val montgomery_multiplication_round_w_k0: #c: curve -> t: widefelem c -> t2: widefelem c -> 
  Stack unit
  (requires fun h -> live h t /\ live h t2 /\ wide_as_nat c h t2 = 0)
  (ensures fun h0 _ h1 -> modifies (loc t2) h0 h1 /\ 
      wide_as_nat c h1 t2 = getPrime c * (wide_as_nat c h0 t % pow2 64) /\
      wide_as_nat c h1 t2 < getPrime c * pow2 64
  )
  
let montgomery_multiplication_round_w_k0 #c t t2 =
    let h0 = ST.get() in 
  let t1 = mod64 t in 
  recall_contents (prime_buffer #c) (Lib.Sequence.of_list (prime_list c)); 
  short_mul_bn (prime_buffer #c) t1 t2;
  lemma_mult_lt_left (getPrime c) (wide_as_nat c h0 t % pow2 64) (pow2 64)


val montgomery_multiplication_round_k0: #c: curve -> k0: uint64 -> t: widefelem c -> 
  t2: widefelem c -> 
  Stack unit
  (requires fun h -> live h t /\ live h t2 /\ wide_as_nat c h t2 = 0)
  (ensures fun h0 _ h1 -> modifies (loc t2) h0 h1 /\ 
    wide_as_nat c h1 t2 < getPrime c * pow2 64 /\
    wide_as_nat c h1 t2 = getPrime c * (((wide_as_nat c h0 t % pow2 64) * uint_v k0) % pow2 64))

let montgomery_multiplication_round_k0 #c k0 t t2 = 
  push_frame();
    let h0 = ST.get() in 
    let t1 = mod64 #c t in
    
    let y = create (size 1) (u64 0) in 
    let temp = create (size 1) (u64 0) in 
    
    mul_atomic t1 k0 y temp;
    recall_contents (prime_buffer #c) (Lib.Sequence.of_list (prime_list c)); 

    let h = ST.get() in 
    let y_ = index y (size 0) in   
    modulo_addition_lemma (uint_v (Lib.Sequence.index (as_seq h y) 0)) (pow2 64) (uint_v (Lib.Sequence.index (as_seq h temp) 0));
    short_mul_bn #c (prime_buffer #c) y_ t2;
    lemma_mult_lt_left (getPrime c) (((wide_as_nat c h0 t % pow2 64) * uint_v k0) % pow2 64) (pow2 64);
  pop_frame()


val montgomery_multiplication_round_: #c: curve -> t: widefelem c -> t2: widefelem c -> 
  Stack unit
  (requires fun h -> live h t /\ live h t2 /\ wide_as_nat c h t2 = 0)
  (ensures fun h0 _ h1 -> modifies (loc t2) h0 h1 /\ 
    wide_as_nat c h1 t2 < getPrime c * pow2 64 /\ (
    let k0 = Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWord #c) in 
    wide_as_nat c h1 t2 = getPrime c * (((wide_as_nat c h0 t % pow2 64) * v k0) % pow2 64))
  )

let montgomery_multiplication_round_ #c t t2 = 
  match supportsReducedMultiplication #c with   
  |true -> montgomery_multiplication_round_w_k0 t t2
  |false -> 
    let h0 = ST.get() in 
    let k0 = getK0 c in 
    montgomery_multiplication_round_k0 k0 t t2


open FStar.Math.Euclid 
open FStar.Math.Fermat


#push-options "--z3rlimit 100 --ifuel 0 --fuel 0"

val lemma_division_is_multiplication:
  t3: nat{t3 % pow2 64 = 0} ->
  prime: pos {is_prime prime /\ prime > 3 /\ prime > pow2 64} -> 
  Lemma (t3 * modp_inv2_prime (pow2 64) prime % prime = (t3 / pow2 64) % prime)

let lemma_division_is_multiplication t3 prime =  

  Hacl.Lemmas.P256.lemma_pow_mod_n_is_fpow prime (pow2 64 % prime) (prime - 2);
  lemma_mod_twice (Spec.P256.pow (pow2 64 % prime) (prime - 2)) prime;

  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  calc (==) {t3 * modp_inv2_prime (pow2 64) prime % prime;
    (==) {FStar.Math.Lib.lemma_div_def t3 (pow2 64)}
     pow2 64 * (t3 / pow2 64) * (Spec.P256.pow (pow2 64 % prime) (prime - 2) % prime) % prime;
    (==) {assert_by_tactic (pow2 64 * (t3 / pow2 64) * (Spec.P256.pow (pow2 64 % prime) (prime - 2) % prime) % prime == 
    (t3 / pow2 64) * (pow2 64 * (Spec.P256.pow (pow2 64 % prime) (prime - 2) % prime)) % prime) canon}
    (t3 / pow2 64) * (pow2 64 * (Spec.P256.pow (pow2 64 % prime) (prime - 2) % prime)) % prime;
    (==) {lemma_mod_mul_distr_r (t3 / pow2 64) (pow2 64 * (Spec.P256.pow (pow2 64 % prime) (prime - 2) % prime)) prime}
    (t3 / pow2 64) * (pow2 64 * (Spec.P256.pow (pow2 64 % prime) (prime - 2) % prime) % prime) % prime;
    (==) {Hacl.Lemmas.P256.power_distributivity (pow2 64) (prime - 2) prime}
    (t3 / pow2 64) * (pow2 64 * (Spec.P256.pow (pow2 64) (prime - 2) % prime) % prime) % prime;
    (==) {lemma_mod_mul_distr_r (pow2 64) (Spec.P256.pow (pow2 64) (prime - 2)) prime}
    (t3 / pow2 64) * (pow2 64 * (Spec.P256.pow (pow2 64) (prime - 2)) % prime) % prime;
    (==) {Hacl.Lemmas.P256.power_one_2 (pow2 64)}
    (t3 / pow2 64) * (Spec.P256.pow (pow2 64) 1 * (Spec.P256.pow (pow2 64) (prime - 2)) % prime) % prime;
    (==) {pow_plus (pow2 64) 1 (prime - 2)}
    (t3 / pow2 64) * ((Spec.P256.pow (pow2 64) (prime - 1)) % prime) % prime;
    (==) {  FStar.Math.Fermat.fermat_alt prime (pow2 64);
      power_as_specification_same_as_fermat (pow2 64) (prime - 1)}
    (t3 / pow2 64) % prime;
  }


val lemma_k0_computation: #c: curve-> t: nat -> k0 : uint64 {k0 == Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWord #c)} ->
  Lemma (let prime = getPrime c in  (t + prime * (((t % pow2 64) * v k0) % pow2 64)) % pow2 64 == 0)

let lemma_k0_computation #c t k0 = 
  let prime = getPrime c in 
  let n0 = getLastWord #c in 

  Hacl.Spec.Bignum.ModInv64.mod_inv_u64_lemma (getLastWord #c);

  let k = t + prime * (((t % pow2 64) * v k0) % pow2 64) in  
  lemma_mod_mul_distr_l t (v k0) (pow2 64);
  lemma_mod_add_distr t (prime * (t * v k0 % pow2 64)) (pow2 64);
  lemma_mod_mul_distr_r prime (t * v k0) (pow2 64);
  
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 


  assert_by_tactic (prime * (t * v k0) == t * (prime * v k0)) canon;

  assert(k % pow2 64 == (t + t * (prime * v k0) % pow2 64) % pow2 64);

  lemma_mod_mul_distr_r t (prime * v k0) (pow2 64);
  lemma_mod_mul_distr_l prime (v k0) (pow2 64);

  assert(k % pow2 64 == (t + t * ((-1 + (1 + prime % pow2 64 * v k0)) % pow2 64) % pow2 64) % pow2 64);

  lemma_mod_add_distr (-1) (1 + (prime) % pow2 64 * v k0) (pow2 64); 
  lemma_mod_mul_distr_r t (-1) (pow2 64);
  lemma_mod_add_distr t (t * (-1)) (pow2 64);
  
  assert(k % pow2 64 == 0)



val montgomery_multiplication_one_round_proof: 
  #c: curve ->
  t: nat ->
  k0 : uint64 {k0 == Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWord #c)} ->
  round: nat {round = (t + getPrime c * (((t % pow2 64) * v k0) % pow2 64)) / pow2 64} -> 
  co: nat {co % getPrime c = t % getPrime c} -> 
  Lemma (round  % getPrime c == co * (modp_inv2_prime (pow2 64) (getPrime c)) % ( getPrime c ))

let montgomery_multiplication_one_round_proof #c t k0 round co =
  let prime = getPrime c in 
  let round = (t + prime * (((t % pow2 64) * v k0) % pow2 64)) / pow2 64 in 
  assert(round % prime = (t + prime * (((t % pow2 64) * v k0) % pow2 64)) / pow2 64 % prime);

  let k = t + prime * (((t % pow2 64) * v k0) % pow2 64) in 

  lemma_k0_computation #c t k0;
  assume (is_prime prime /\ prime > pow2 64);
  lemma_division_is_multiplication k prime;

  modulo_addition_lemma t prime (((t % pow2 64) * v k0) % pow2 64);

  lemma_mod_mul_distr_l k (modp_inv2_prime (pow2 64) prime) prime;
  lemma_mod_mul_distr_l co (modp_inv2_prime (pow2 64) prime) prime



val montgomery_multiplication_round: #c: curve -> t: widefelem c -> round: widefelem c -> 
  Stack unit 
  (requires fun h -> live h t /\ live h round /\ eq_or_disjoint t round)
  (ensures fun h0 _ h1 -> modifies (loc round) h0 h1 /\ (
    let k0 = Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWord #c) in 
    wide_as_nat c h1 round = (wide_as_nat c h0 t + getPrime c * (((wide_as_nat c h0 t % pow2 64) * v k0) % pow2 64)) / pow2 64)
  )

let montgomery_multiplication_round #c t round =
  push_frame(); 
    let len = getCoordinateLenU64 c in  
    let t2 = create (size 2 *! len) (u64 0) in 
    lemma_create_zero_buffer (2 * v len) c;
    montgomery_multiplication_round_ #c t t2;
    let carry = add_long_bn t t2 t2 in 
    shift1_with_carry t2 round carry; 
  pop_frame()  


val lemma_up_bound0: #c: curve -> t0: nat {t0 < getPrime c * pow2 (64 * v (getCoordinateLenU64 c))} 
  -> t: nat{let prime = getPrime c in t <= t0 / (pow2 (64 * v (getCoordinateLenU64 c))) + prime} -> 
  Lemma (t < 2 * (getPrime c))

let lemma_up_bound0 #c t0 t = 
  let prime = getPrime c in 
  let s = pow2 (64 * v (getCoordinateLenU64 c)) in 
  lemma_mult_lt_left prime prime s;
  assert(t0 < prime * s);
  assert(t0 / s < prime);

  assert(t < prime + prime)


val lemma_up_bound1: #c: curve -> i: nat {i < v (getCoordinateLenU64 c)} 
  -> t: nat {t < getPrime c * pow2 (64 * v (getCoordinateLenU64 c))}  
  -> t0: nat {let prime = getPrime c in t0 <= t / (pow2 (64 * i)) + prime} 
  -> k0: nat {k0 < pow2 64} 
  -> t1: nat {t1 = (t0 + getPrime c * (((t0 % pow2 64) * k0) % pow2 64)) / pow2 64} -> 
  Lemma (let prime = getPrime c in t1 <= t / (pow2 (64 * (i + 1))) + prime)

let lemma_up_bound1 #c i t t0 k0 t1= 
  let prime = getPrime c in 
  assert(t0 <= t / (pow2 (64 * i)) + prime); 
  assert(t1 = (t0 + prime * (((t0 % pow2 64) * k0) % pow2 64)) / pow2 64);
  assert(((t0 % pow2 64) * k0) % pow2 64 <= pow2 64 - 1);
  lemma_mult_le_left prime (((t0 % pow2 64) * k0) % pow2 64) (pow2 64 - 1);
  assert(t1 <= (t0 + prime * (pow2 64 - 1)) / pow2 64);
  assert(t1 <= (t0 + prime * pow2 64 - prime) / pow2 64); 
  assert(t1 <= (t / (pow2 (64 * i)) / pow2 64 + prime));
  division_multiplication_lemma t (pow2 (64 * i)) (pow2 64);
  assert(t1 <= (t / (pow2 (64 * i) * pow2 64) + prime));
  pow2_plus (64 * i) 64


#push-options "--z3rlimit 100 --ifuel 2 --fuel 2"

val lemma_mm_reduction: #c: curve -> a0: nat -> i: nat -> Lemma
  (let prime = getPrime c in 
    a0 * modp_inv2 #c (pow2 (i * 64)) * modp_inv2 #c (pow2 64) % prime == a0 * modp_inv2 #c (pow2 ((i + 1) * 64)) % prime)

let lemma_mm_reduction #c a0 i = 
  let open Spec.P256 in 
  let prime = getPrime c in 
  
  let a = pow2 (i * 64) in 

  let exp_prime: pos = prime - 2 in 

  assert(modp_inv2 #c a == exp #prime (a % prime) exp_prime % prime);
  Hacl.Lemmas.P256.lemma_pow_mod_n_is_fpow prime (a % prime) exp_prime;
  lemma_mod_twice (pow (a % prime) exp_prime) prime;

  assert(modp_inv2 #c (pow2 64) == exp #prime (pow2 64 % prime) exp_prime % prime);
  Hacl.Lemmas.P256.lemma_pow_mod_n_is_fpow prime (pow2 64 % prime) exp_prime;
  lemma_mod_twice (pow (pow2 64 % prime) exp_prime) prime;

  Hacl.Lemmas.P256.power_distributivity_2 (a % prime) (pow2 64 % prime) exp_prime;


  lemma_mod_mul_distr_r a0 (modp_inv2 #c a * modp_inv2 #c (pow2 64)) prime;

  calc (==) {
    modp_inv2 #c a * modp_inv2 #c (pow2 64) % prime;
    (==) {}
    (pow (a % prime) exp_prime % prime * (pow (pow2 64 % prime) exp_prime % prime)) % prime; 
    (==) {lemma_mod_mul_distr_l (pow (a % prime) exp_prime) (pow (pow2 64 % prime) exp_prime % prime) prime}
    (pow (a % prime) exp_prime * (pow (pow2 64 % prime) exp_prime % prime)) % prime; 
    (==) {lemma_mod_mul_distr_r (pow (a % prime) exp_prime) (pow (pow2 64 % prime) exp_prime) prime}
    (pow (a % prime) exp_prime * pow (pow2 64 % prime) exp_prime) % prime; 
    (==) {pow_plus (a % prime) (pow2 64 % prime) exp_prime}
    (pow (a % prime * (pow2 64 % prime)) exp_prime) % prime; 
    (==) {Hacl.Lemmas.P256.power_distributivity (a % prime * (pow2 64 % prime)) exp_prime prime}
    (pow (a % prime * (pow2 64 % prime) % prime) exp_prime) % prime; 
    (==) {lemma_mod_mul_distr_l a (pow2 64 % prime) prime}
    (pow ((a * (pow2 64 % prime)) % prime) exp_prime) % prime; 
    (==) {lemma_mod_mul_distr_r a (pow2 64) prime}
    (pow ((a * pow2 64) % prime) exp_prime) % prime; 
    (==) {lemma_mod_twice (pow ((a * pow2 64) % prime) exp_prime) prime}
    ((pow ((a * pow2 64) % prime) exp_prime) % prime) % prime; 
    (==) {Hacl.Lemmas.P256.lemma_pow_mod_n_is_fpow prime (a * pow2 64 % prime) exp_prime} 
    exp #prime ((a * pow2 64) % prime) exp_prime % prime; 
    (==) {}
    modp_inv2 #c (a * pow2 64);
    (==) {pow2_plus (i * 64) 64}
    modp_inv2 #c (pow2 ((i + 1) * 64));};

  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  assert_by_tactic (a0 * modp_inv2 #c (pow2 (i * 64)) * modp_inv2 #c (pow2 64) % prime == a0 * (modp_inv2 #c (pow2 (i * 64)) * modp_inv2 #c (pow2 64)) % prime) canon

#pop-options


val montgomery_multiplication_reduction: #c: curve
  -> t: widefelem c 
  -> result: felem c -> 
  Stack unit 
  (requires (fun h -> live h t /\ wide_as_nat c h t < getPrime c * pow2 (getPower c) /\ live h result /\ 
    eq_or_disjoint t result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result |+| loc t) h0 h1 /\ (let prime = getPrime c in 
    as_nat c h1 result = (wide_as_nat c h0 t * modp_inv2_prime (getPower2 c) prime) % prime /\
    as_nat c h1 result = fromDomain_ #c (wide_as_nat c h0 t)))
  )


let montgomery_multiplication_reduction #c t result = 
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
   
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = 
    let prime = getPrime c in 
    live h t /\ modifies (loc t) h0 h /\
    wide_as_nat c h0 t < getPrime c * pow2 (getPower c) /\ 
    wide_as_nat c h t <= wide_as_nat c h0 t / (pow2 (64 * i)) + prime /\ 
    wide_as_nat c h t % prime = wide_as_nat c h0 t * modp_inv2 #c (pow2 (i * 64)) % prime in 

  lemma_mult_lt_left (getPrime c) (getPrime c) (pow2 (64 * v (getCoordinateLenU64 c)));

  let h1 = ST.get() in

  lemma_mod_inv #c (wide_as_nat c h0 t);

  for 0ul len inv (fun i ->
    let h0_ = ST.get() in 
    montgomery_multiplication_round #c t t; 
    let h1_ = ST.get() in

    let a0 = wide_as_nat c h0 t in 
    let a_i = wide_as_nat c h0_ t in 
    let a_il = wide_as_nat c h1_ t in 

    let prime = getPrime c in 
    let k0 = Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWord #c) in 
    let co = a0 * modp_inv2 #c (pow2 (v i * 64)) in 

    lemma_up_bound1 #c (v i) a0 a_i (v k0) a_il;
    montgomery_multiplication_one_round_proof #c a_i k0 a_il co;
    lemma_mm_reduction #c a0 (v i));

  let h2 = ST.get() in 
  lemma_up_bound0 #c (wide_as_nat c h0 t) (wide_as_nat c h2 t); 
  reduction_prime_2prime_with_carry t result;

  lemmaFromDomain #c (wide_as_nat c h0 t)


#push-options "--z3rlimit 200"




(*
val lemma_wide_as_nat: #c: curve -> a: widefelem c -> h: mem -> i: nat{i > getCoordinateLenU64 c} -> Lemma (
  let len = getCoordinateLenU64 c in 
  wide_as_nat c h a == as_nat c h (gsub a (size 0) len) + as_nat c h (gsub a len len) * pow2 (getPower c))

let lemma_wide_as_nat #c a h = 
  assert(wide_as_nat c h a == lseq_as_nat (as_seq h a));
  
  let len = getCoordinateLenU64 c in 
  
  let a0 = gsub a (size 0) len in 
  let a1 = gsub a len len in 

  assert(as_nat c h a0 == lseq_as_nat (as_seq h a0));
  assert(as_nat c h a1 == lseq_as_nat (as_seq h a1));

  admit()


let montgomery_multiplication_buffer_by_one #c a result = 
  push_frame();
  
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let t_low = sub t (size 0) len in 
    let t_high = sub t len len in 

  let h0 = ST.get() in 
  assert(as_nat c h0 a < getPrime c);
  
  copy t_low a; 

  let h1 = ST.get() in 
  lemma_create_zero_buffer (2 * v len) c; 
  assert(wide_as_nat c h0 t == 0);
  assert(wide_as_nat c h1 t == 

  montgomery_multiplication_reduction t result;
  pop_frame();
  
  lemmaFromDomain #c (as_nat c h0 a)


(*
val montgomery_multiplication_buffer: #c: curve
  -> a: felem c -> b: felem c -> result: felem c ->  
  Stack unit
  (requires (fun h -> live h a /\ as_nat c h a < getPrime c /\ live h b /\ 
      live h result /\ as_nat c h b < getPrime c)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result < getPrime c /\ (
    let prime = getPrime c in 
    as_nat c h1 result = (as_nat c h0 a * as_nat c h0 b * modp_inv2_prime (pow2 (getPower c)) prime) % prime /\
    as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 b) % prime) /\
    as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 b))))
  )
*)

let montgomery_multiplication_buffer #c a b result = 
  push_frame();
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let h0 = ST.get() in
  mul a b t;  
  montgomery_multiplication_reduction #c t result;
  pop_frame()
  (*

    let h1 = ST.get() in 
  
    let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = let prime = getPrime c in 
      live h t /\ wide_as_nat c h t < prime * prime /\ modifies (loc t) h0 h /\ 
      wide_as_nat c h t % prime = wide_as_nat c h1 t * modp_inv2 #c (pow2 (i * 64)) % prime in

    lemma_mult_lt_sqr (as_nat c h0 a) (as_nat c h0 b) (getPrime c);
    lemma_mod_inv #c (wide_as_nat c h1 t);

  for 0ul len inv (fun i -> let h0_ = ST.get() in
    montgomery_multiplication_round #c t t; 
      let h1_ = ST.get() in
      admit();
      montgomery_multiplication_one_round_proof_w_ko #c (wide_as_nat c h0_ t) (wide_as_nat c h1_ t) (wide_as_nat c h0_ t)
    );
    
    (*lemma_inv2 #c (wide_as_nat c h1 t) (wide_as_nat c h0_ t) (wide_as_nat c h1_ t) (v i)); *)

    let h2 = ST.get() in 
  
    assume (wide_as_nat c h2 t < 2 * getPrime c);
  reduction_prime_2prime_with_carry t result;
  
  pop_frame();

    let prime = getPrime c in 
    let multResult = as_nat c h0 a * as_nat c h0 b * modp_inv2_prime (pow2 (getPower c)) prime % prime in 

    let a_ = as_nat c h0 a in 
    let b_ = as_nat c h0 b in 
    let mod = modp_inv2_prime (pow2 (getPower c)) prime in 
  
    calc (==)
    {
      a_ * b_ * mod % prime;
      (==) {lemmaFromDomainToDomain #c multResult}
      toDomain_ #c (fromDomain_ #c multResult);
      (==) {lemmaFromDomain #c multResult}
      toDomain_ #c ((a_ * b_ * mod  % prime) * mod % prime);
      (==) {lemma_mod_mul_distr_l (a_ * b_ * mod) mod prime}
      toDomain_ #c (a_ * b_ * mod * mod % prime);
      (==) {
	let open FStar.Tactics in 
	let open FStar.Tactics.Canon in 
	assert_by_tactic (a_ * b_ * mod * mod == (a_ * mod) * (b_ * mod)) canon}
      toDomain_ #c ((a_ * mod) * (b_ * mod) % prime);
      (==) {
	lemma_mod_mul_distr_l (a_ * mod) (b_ *  mod) prime; 
	lemma_mod_mul_distr_r (a_ * mod % prime) (b_ * mod) prime}
      
      toDomain_ #c ((a_ * mod % prime) * (b_ * mod % prime) % prime);
      (==) {lemmaFromDomain #c a_; lemmaFromDomain #c b_}
      toDomain_ #c (fromDomain_ #c a_ * fromDomain_ #c b_ % prime);

    };

    inDomain_mod_is_not_mod #c (fromDomain_ #c a_ * fromDomain_ #c b_)
*)

(*
val montgomery_multiplication_buffer_k0: #c: curve -> a: felem c -> b: felem c 
  -> result: felem c ->  
  Stack unit
  (requires (fun h -> live h a /\ as_nat c h a < getPrime c /\ live h b /\ 
    live h result /\ as_nat c h b < getPrime c)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\  
    as_nat c h1 result < getPrime c /\ (
    let prime = getPrime c in 
    as_nat c h1 result = (as_nat c h0 a * as_nat c h0 b * modp_inv2_prime (pow2 (getPower c)) (getPrime c)) % prime /\
    as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 b) % prime) /\
    as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 b))))
  )

let montgomery_multiplication_buffer_k0 #c a b result = 
  push_frame();
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let h0 = ST.get() in 
  mul a b t;  
    let h1 = ST.get() in 
    
    let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = let prime = getPrime c in 
      live h t /\ wide_as_nat c h t < prime * prime /\ modifies (loc t) h0 h /\ 
      wide_as_nat c h t % prime = wide_as_nat c h1 t * modp_inv2 #c (pow2 (i * 64)) % prime in

    lemma_mult_lt_sqr (as_nat c h0 a) (as_nat c h0 b) (getPrime c);
    lemma_mod_inv #c (wide_as_nat c h1 t);

    assume (inv h1 0);
  for 0ul len inv (fun i -> let h0_ = ST.get() in
    montgomery_multiplication_round_k0 #c t t (getK0 c); 
      let h1_ = ST.get() in
      admit();
      montgomery_multiplication_one_round_proof_w_ko #c (wide_as_nat c h0_ t) (wide_as_nat c h1_ t) (wide_as_nat c h0_ t)
      (*lemma_inv2 #c (wide_as_nat c h1 t) (wide_as_nat c h0_ t) (wide_as_nat c h1_ t) (v i) *));

    let h2 = ST.get() in   
    assume (wide_as_nat c h2 t < 2 * getPrime c);
  reduction_prime_2prime_with_carry t result;
  
  pop_frame();

    let prime = getPrime c in 
    let multResult = as_nat c h0 a * as_nat c h0 b * modp_inv2_prime (pow2 (getPower c)) prime % prime in 

    let a_ = as_nat c h0 a in 
    let b_ = as_nat c h0 b in 
    let mod = modp_inv2_prime (pow2 (getPower c)) prime in 

    admit();
    calc (==)
    {
      a_ * b_ * mod % prime;
      (==) {lemmaFromDomainToDomain #c multResult}
      toDomain_ #c (fromDomain_ #c multResult);
      (==) {lemmaFromDomain #c multResult}
      toDomain_ #c ((a_ * b_ * mod  % prime) * mod % prime);
      (==) {lemma_mod_mul_distr_l (a_ * b_ * mod) mod prime}
      toDomain_ #c (a_ * b_ * mod * mod % prime);
      (==) {
	let open FStar.Tactics in 
	let open FStar.Tactics.Canon in 
	assert_by_tactic (a_ * b_ * mod * mod == (a_ * mod) * (b_ * mod)) canon}
      toDomain_ #c ((a_ * mod) * (b_ * mod) % prime);
      (==) {
	lemma_mod_mul_distr_l (a_ * mod) (b_ *  mod) prime; 
	lemma_mod_mul_distr_r (a_ * mod % prime) (b_ * mod) prime}
      
      toDomain_ #c ((a_ * mod % prime) * (b_ * mod % prime) % prime);
      (==) {lemmaFromDomain #c a_; lemmaFromDomain #c b_}
      toDomain_ #c (fromDomain_ #c a_ * fromDomain_ #c b_ % prime);

    };

    inDomain_mod_is_not_mod #c (fromDomain_ #c a_ * fromDomain_ #c b_)
*)

(*
val montgomery_square_buffer: #c: curve  -> a: felem c
  -> result: felem c ->  
  Stack unit
  (requires (fun h -> live h a /\ as_nat c h a < (getPrime c) /\ live h result)) 
  (ensures (fun h0 _ h1 -> (let prime = getPrime c in modifies (loc result) h0 h1 /\  
    as_nat c h1 result < prime /\ 
    as_nat c h1 result = (as_nat c h0 a * as_nat c h0 a * modp_inv2_prime (getPower c) prime) % prime /\
    as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) % prime) /\
    as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a)))))
*)

let montgomery_square_buffer #c a result = 
  push_frame();
    
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let h0 = ST.get() in 
  square_bn a t;  
  montgomery_multiplication_reduction #c t result;

  pop_frame()  




let fsquarePowN #c n a = 
  let h0 = ST.get() in  
  (* lemmaFromDomainToDomain #P256 (as_nat P256 h0 a); *)
  assert_norm (pow2 0 == 1); 
  let inv (h0: HyperStack.mem) (h1: HyperStack.mem) (i: nat) : Type0 = True (*
    let k = fromDomain_ #P256 (as_nat P256 h0 a) in 
    as_nat P256 h1 a = toDomain_ #P256 (pow k (pow2 i)) /\
    as_nat P256 h1 a < prime256 /\ live h1 a /\ modifies1 a h0 h1  *) in 

 (* power_one_2 (fromDomain_ #P256 (as_nat P256 h0 a)); *)

  for (size 0) n (inv h0) (fun x -> 
    let h0_ = ST.get() in 
     montgomery_square_buffer #c a a
     (* ; 
     let k = fromDomain_ #P256 (as_nat P256 h0 a) in  
     inDomain_mod_is_not_mod #P256 (fromDomain_ #P256 (as_nat P256 h0_ a) * fromDomain_ #P256 (as_nat P256 h0_ a)); 
     lemmaFromDomainToDomainModuloPrime #P256 (let k = fromDomain_ #P256 (as_nat P256 h0 a) in pow k (pow2 (v x)));

     (*modulo_distributivity_mult (pow k (pow2 (v x))) (pow k (pow2 (v x))) prime256; 
     pow_plus k  (pow2 (v x)) (pow2 (v x )); 
     pow2_double_sum (v x); *)
     inDomain_mod_is_not_mod #P256 (pow k (pow2 (v x + 1)))
 *)
   )
