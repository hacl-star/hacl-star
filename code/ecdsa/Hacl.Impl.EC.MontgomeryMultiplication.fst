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
  Tot  (r: bool {r ==> v (Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWordPrime #c)) == 1})

let supportsReducedMultiplication #c = 
  let open Lib.RawIntTypes in 
  let r = FStar.UInt64.eq (Lib.RawIntTypes.u64_to_UInt64 (getLastWordPrime #c)) 0xffffffffffffffffuL in 
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
  short_mul_prime t1 t2;
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
    short_mul_prime #c y_ t2;
    lemma_mult_lt_left (getPrime c) (((wide_as_nat c h0 t % pow2 64) * uint_v k0) % pow2 64) (pow2 64);
  pop_frame()

val montgomery_multiplication_round_dsa_: #c: curve -> k0: uint64 -> t: widefelem c -> 
  t2: widefelem c -> 
  Stack unit
  (requires fun h -> live h t /\ live h t2 /\ wide_as_nat c h t2 = 0)
  (ensures fun h0 _ h1 -> modifies (loc t2) h0 h1 /\ 
    wide_as_nat c h1 t2 < getOrder #c * pow2 64 /\
    wide_as_nat c h1 t2 = getOrder #c * (((wide_as_nat c h0 t % pow2 64) * uint_v k0) % pow2 64))

let montgomery_multiplication_round_dsa_ #c k0 t t2 = 
  push_frame();
    let h0 = ST.get() in 
    let t1 = mod64 #c t in
    
    let y = create (size 1) (u64 0) in 
    let temp = create (size 1) (u64 0) in 
    
    mul_atomic t1 k0 y temp;
    recall_contents (order_buffer #c) (Lib.Sequence.of_list (order_list c)); 

    let h = ST.get() in 
    let y_ = index y (size 0) in   
    modulo_addition_lemma (uint_v (Lib.Sequence.index (as_seq h y) 0)) (pow2 64) (uint_v (Lib.Sequence.index (as_seq h temp) 0));
    short_mul_order #c y_ t2;
    lemma_mult_lt_left (getOrder #c) (((wide_as_nat c h0 t % pow2 64) * uint_v k0) % pow2 64) (pow2 64);
  pop_frame()


inline_for_extraction noextract
val montgomery_multiplication_round_: #c: curve -> m: mode -> t: widefelem c -> t2: widefelem c -> 
  Stack unit
  (requires fun h -> live h t /\ live h t2 /\ wide_as_nat c h t2 = 0)
  (ensures fun h0 _ h1 -> modifies (loc t2) h0 h1 /\ (
    let k0 = match m with 
      |DH -> Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWordPrime #c)
      |DSA -> Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWordOrder #c) in 
    let prime = getModePrime m c in  
    wide_as_nat c h1 t2 < prime * pow2 64 /\
    wide_as_nat c h1 t2 = prime * (((wide_as_nat c h0 t % pow2 64) * v k0) % pow2 64)))

let montgomery_multiplication_round_ #c m t t2 = 
  match m with 
  |DSA ->
    let k0 = Hacl.Bignum.ModInv64.mod_inv_u64 (getLastWordOrder #c) in 
    montgomery_multiplication_round_dsa_ #c k0 t t2
  |DH -> 
    match supportsReducedMultiplication #c with   
    |true -> montgomery_multiplication_round_w_k0 t t2
    |false -> 
      let h0 = ST.get() in 
      let k0 = getK0 c in 
      montgomery_multiplication_round_k0 k0 t t2


inline_for_extraction noextract
val montgomery_multiplication_round: #c: curve -> m: mode -> t: widefelem c 
  -> round: widefelem c -> 
  Stack unit 
  (requires fun h -> live h t /\ live h round /\ eq_or_disjoint t round)
  (ensures fun h0 _ h1 -> modifies (loc round) h0 h1 /\ (
    let k0 = match m with 
      |DH -> Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWordPrime #c)
      |DSA -> Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWordOrder #c) in 
    let prime = getModePrime m c in  
    wide_as_nat c h1 round = (wide_as_nat c h0 t + prime * (((wide_as_nat c h0 t % pow2 64) * v k0) % pow2 64)) / pow2 64))

let montgomery_multiplication_round #c m t round =
  push_frame(); 
    let len = getCoordinateLenU64 c in  
    let t2 = create (size 2 *! len) (u64 0) in 
    lemma_create_zero_buffer (2 * v len) c;
    montgomery_multiplication_round_ #c m t t2;
    let carry = add_long_bn t t2 t2 in 
    shift1_with_carry t2 round carry; 
  pop_frame()  


inline_for_extraction noextract
val montgomery_multiplication_reduction: #c: curve
  -> m: mode
  -> t: widefelem c 
  -> result: felem c -> 
  Stack unit 
  (requires (fun h -> live h t /\ (let prime = getModePrime m c in  
    wide_as_nat c h t < prime * pow2 (getPower c) /\ live h result /\ eq_or_disjoint t result)))
  (ensures (fun h0 _ h1 -> modifies (loc result |+| loc t) h0 h1 /\ (let prime = getModePrime m c in   
    as_nat c h1 result = (wide_as_nat c h0 t * modp_inv2_prime (pow2 (getPower c)) prime) % prime /\
    as_nat c h1 result = fromDomain_ #c #m (wide_as_nat c h0 t))))


let montgomery_multiplication_reduction #c m t result = 
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = 
    let prime = getModePrime m c in  
    live h t /\ modifies (loc t) h0 h /\
    wide_as_nat c h0 t < prime * pow2 (getPower c) /\ 
    wide_as_nat c h t <= wide_as_nat c h0 t / (pow2 (64 * i)) + prime /\ 
    wide_as_nat c h t % prime = wide_as_nat c h0 t * modp_inv2 #c (pow2 (i * 64)) % prime in 

  lemma_mult_lt_left (getModePrime m c) (getModePrime m c) (pow2 (64 * v (getCoordinateLenU64 c)));

  let h1 = ST.get() in

  lemma_mod_inv #c (wide_as_nat c h0 t);

  for 0ul len inv (fun i ->
    let h0_ = ST.get() in 
    montgomery_multiplication_round #c m t t; 
    let h1_ = ST.get() in

    let a0 = wide_as_nat c h0 t in 
    let a_i = wide_as_nat c h0_ t in 
    let a_il = wide_as_nat c h1_ t in 

    let prime = getModePrime m c in  
    let k0 = match m with 
      |DH -> Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWordPrime #c)
      |DSA -> Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWordOrder #c) in 
    let co = a0 * modp_inv2 #c (pow2 (v i * 64)) in 

    lemma_up_bound1 #c (v i) a0 a_i (v k0) a_il;
    montgomery_multiplication_one_round_proof #c a_i k0 a_il co;
    lemma_mm_reduction #c a0 (v i));

  let h2 = ST.get() in 
  lemma_up_bound0 #c (wide_as_nat c h0 t) (wide_as_nat c h2 t); 
  reduction_prime_2prime_with_carry t result;

  lemmaFromDomain #c #m (wide_as_nat c h0 t)


let montgomery_multiplication_reduction_dh #c t result = montgomery_multiplication_reduction #c DH t result

let montgomery_multiplication_reduction_dsa #c t result = montgomery_multiplication_reduction #c DSA t result


val montgomery_multiplication_buffer_by_one: #c: curve -> m: mode -> a: felem c -> result: felem c -> 
  Stack unit
  (requires (fun h -> live h a /\ as_nat c h a < getModePrime m c /\ live h result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (
    let prime = getModePrime m c in  
    as_nat c h1 result = (as_nat c h0 a * modp_inv2_prime (pow2 (getPower c)) prime) % prime /\
    as_nat c h1 result = fromDomain_ #c #m (as_nat c h0 a))))


let montgomery_multiplication_buffer_by_one #c m a result = 
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

  
  montgomery_multiplication_reduction m t result;
  pop_frame();
  
  lemmaFromDomain #c #m (as_nat c h0 a)


let montgomery_multiplication_buffer_by_one_dh #c a result = montgomery_multiplication_buffer_by_one #c DH a result

let montgomery_multiplication_buffer_by_one_dsa #c a result = montgomery_multiplication_buffer_by_one #c DSA a result


let montgomery_multiplication_buffer #c m a b result = 
  push_frame();
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let h0 = ST.get() in
  mul a b t;
    lemma_mult_lt_center (as_nat c h0 a) (as_nat c h0 b) (getModePrime m c) (pow2 (getPower c)); 
  montgomery_multiplication_reduction #c m t result;
  pop_frame();
    let h1 = ST.get() in admit();
    lemma_domain #c #m (as_nat c h0 a) (as_nat c h0 b) (as_nat c h1 result)

let montgomery_multiplication_buffer_dh #c a b result = montgomery_multiplication_buffer #c DH a b result

let montgomery_multiplication_buffer_dsa #c a b result = montgomery_multiplication_buffer #c DSA a b result


let montgomery_square_buffer #c m a result = 
  push_frame();
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let h0 = ST.get() in 
  square_bn a t;   
    lemma_mult_lt_center (as_nat c h0 a) (as_nat c h0 a) (getModePrime m c) (pow2 (getPower c));
  montgomery_multiplication_reduction #c m t result;
  pop_frame();
    let h1 = ST.get() in
    lemma_domain #c #m (as_nat c h0 a) (as_nat c h0 a) (as_nat c h1 result)


let montgomery_square_buffer_dh #c a result = montgomery_square_buffer #c DH a result

let montgomery_square_buffer_dsa #c a result = montgomery_square_buffer #c DSA a result


val fsquarePowN: #c: curve -> m: mode -> n: size_t -> a: felem c -> Stack unit 
  (requires (fun h -> live h a /\ as_nat c h a < getModePrime m c)) 
  (ensures (fun h0 _ h1 -> modifies (loc a) h0 h1 /\ (
    let k = fromDomain_ #c #m (as_nat c h0 a) in 
    as_nat c h1 a < getModePrime m c /\ as_nat c h1 a = toDomain_ #c #m (pow k (pow2 (v n))))))

let fsquarePowN #c m n a = 
  let h0 = ST.get() in 
    lemmaFromDomainToDomain #c #m (as_nat c h0 a);  
  assert_norm (pow2 0 == 1); 
  let inv (h0: HyperStack.mem) (h1: HyperStack.mem) (i: nat) : Type0 = 
    let k = fromDomain_ #c #m (as_nat c h0 a) in 
    as_nat c h1 a = toDomain_ #c #m (pow k (pow2 i)) /\
    as_nat c h1 a < getModePrime m c /\ live h1 a /\ modifies (loc a) h0 h1 in 

  Hacl.Lemmas.P256.power_one_2 (fromDomain_ #c #m (as_nat c h0 a)); 
  
  for (size 0) n (inv h0) (fun x -> 
    let h0_ = ST.get() in 
     montgomery_square_buffer m a a;
     let k = fromDomain_ #c #m (as_nat c h0 a) in  
     inDomain_mod_is_not_mod #c #m (fromDomain_ #c #m (as_nat c h0_ a) * fromDomain_ #c #m (as_nat c h0_ a)); 
     lemmaFromDomainToDomainModuloPrime #c #m (let k = fromDomain_ #c #m (as_nat c h0 a) in pow k (pow2 (v x)));

     Spec.ECDSA.Lemmas.modulo_distributivity_mult (pow k (pow2 (v x))) (pow k (pow2 (v x))) (getModePrime m c); 
     pow_plus k (pow2 (v x)) (pow2 (v x )); 
     pow2_double_sum (v x); 
     inDomain_mod_is_not_mod #c #m (pow k (pow2 (v x + 1))))


let fsquarePowN_dh #c n a = fsquarePowN #c DH n a 

let fsquarePowN_dsa #c n a = fsquarePowN #c DSA n a 
