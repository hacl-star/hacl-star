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


let montgomery_multiplication_buffer_by_one #c a result = 
  push_frame();
  
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let t_low = sub t (size 0) len in 
    let t_high = sub t len len in 

  let h0 = ST.get() in 
  copy t_low a; 

  let h1 = ST.get() in 
  
  lemma_create_zero_buffer (2 * v len) c; 

  lemma_test (as_seq h0 t) (v len);
  lemma_test (as_seq h1 t) (v len);

  
  montgomery_multiplication_reduction t result;
  pop_frame();
  
  lemmaFromDomain #c (as_nat c h0 a)



let montgomery_multiplication_buffer #c a b result = 
  push_frame();
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let h0 = ST.get() in
  mul a b t;  
    lemma_mult_lt_center (as_nat c h0 a) (as_nat c h0 b) (getPrime c) (pow2 (getPower c));
  montgomery_multiplication_reduction #c t result;
  pop_frame();
    let h1 = ST.get() in 
    lemma_domain #c (as_nat c h0 a) (as_nat c h0 b) (as_nat c h1 result)


let montgomery_square_buffer #c a result = 
  push_frame();
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let h0 = ST.get() in 
  square_bn a t;   
    lemma_mult_lt_center (as_nat c h0 a) (as_nat c h0 a) (getPrime c) (pow2 (getPower c));
  montgomery_multiplication_reduction #c t result;
  pop_frame();
    let h1 = ST.get() in
    lemma_domain #c (as_nat c h0 a) (as_nat c h0 a) (as_nat c h1 result)
    

let fsquarePowN #c n a = 
  let h0 = ST.get() in  
    lemmaFromDomainToDomain #c (as_nat c h0 a);  
  assert_norm (pow2 0 == 1); 
  let inv (h0: HyperStack.mem) (h1: HyperStack.mem) (i: nat) : Type0 = 
    let k = fromDomain_ #c (as_nat c h0 a) in 
    as_nat c h1 a = toDomain_ #c (Spec.P256.pow k (pow2 i)) /\
    as_nat c h1 a < getPrime c /\ live h1 a /\ modifies (loc a) h0 h1 in 

  Hacl.Lemmas.P256.power_one_2 (fromDomain_ #c (as_nat c h0 a)); 
  
  for (size 0) n (inv h0) (fun x -> 
    let h0_ = ST.get() in 
     montgomery_square_buffer #c a a;

     let pow = Spec.P256.pow in 
     let k = fromDomain_ #c (as_nat c h0 a) in  
     inDomain_mod_is_not_mod #c (fromDomain_ #c (as_nat c h0_ a) * fromDomain_ #c (as_nat c h0_ a)); 
     lemmaFromDomainToDomainModuloPrime #c (let k = fromDomain_ #c (as_nat c h0 a) in pow k (pow2 (v x)));

     Spec.ECDSA.Lemmas.modulo_distributivity_mult (pow k (pow2 (v x))) (pow k (pow2 (v x))) (getPrime c); 
     pow_plus k  (pow2 (v x)) (pow2 (v x )); 
     pow2_double_sum (v x); 
     inDomain_mod_is_not_mod #c (pow k (pow2 (v x + 1))))
