module Hacl.Impl.EC.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Hacl.Impl.P256.Math 

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Spec.P256.Definition
open Hacl.Lemmas.P256
open Spec.P256
open Spec.ECDSA.Lemmas

open Hacl.Impl.EC.LowLevel
open Hacl.Impl.EC.MontgomeryMultiplication.Lemmas

open Lib.Loops
open Hacl.Spec.P.MontgomeryMultiplication
open Hacl.Impl.EC.Setup


#set-options "--z3rlimit 200 --fuel 0 --ifuel 0"


val montgomery_multiplication_round_: #c: curve -> t: widefelem c -> t2: widefelem c -> 
  Stack unit
    (requires fun h -> live h t /\ live h t2 /\ wide_as_nat c h t2 = 0)
    (ensures fun h0 _ h1 -> modifies (loc t2) h0 h1 /\ 
      wide_as_nat c h1 t2 < getPower2 c * pow2 64 /\
      wide_as_nat c h1 t2 = getPrime c * (wide_as_nat c h0 t % pow2 64))
  
let montgomery_multiplication_round_ #c t t2 =
  let t1 = mod64 t in 
  recall_contents (prime_buffer #c) (Lib.Sequence.of_list (prime_list c)); 
  short_mul_bn (prime_buffer #c) t1 t2
  

val montgomery_multiplication_round: #c: curve -> t: widefelem c -> round: widefelem c -> 
  Stack unit 
  (requires fun h -> live h t /\ live h round /\ wide_as_nat c h t < getPrime c * getPrime c /\
    eq_or_disjoint t round)
  (ensures fun h0 _ h1 -> modifies (loc round)  h0 h1 /\
    wide_as_nat c h1 round = (wide_as_nat c h0 t + getPrime c * (wide_as_nat c h0 t % pow2 64)) / pow2 64)

let montgomery_multiplication_round #c t round =
  push_frame(); 
    let len = getCoordinateLenU64 c in  
    let t2 = create (size 2 *! len) (u64 0) in 
    montgomery_multiplication_round_ #c t t2;
    add_long_without_carry t t2 round;
    shift1 round round; 
  pop_frame()  



#push-options "--z3rlimit 400"

val montgomery_multiplication_round_k0_: #c: curve -> k0: uint64 -> t: widefelem c -> 
  t2: widefelem c -> 
  Stack unit
  (requires fun h -> live h t /\ live h t2 /\ wide_as_nat c h t2 = 0)
  (ensures fun h0 _ h1 -> modifies (loc t2) h0 h1 /\ 
    wide_as_nat c h1 t2 < getPower2 c * pow2 64 /\
    wide_as_nat c h1 t2 = getPrime c * (((wide_as_nat c h0 t % pow2 64) * uint_v k0) % pow2 64))

let montgomery_multiplication_round_k0_ #c k0 t t2 = 
  push_frame();
    let t1 = mod64 #c t in
    
    let y = create (size 1) (u64 0) in 
    let temp = create (size 1) (u64 0) in 
    
    mul_atomic t1 k0 y temp;
    recall_contents (prime_buffer #c) (Lib.Sequence.of_list (prime_list c)); 

    let h = ST.get() in 
    let y_ = index y (size 0) in   
    modulo_addition_lemma (uint_v (Lib.Sequence.index (as_seq h y) 0)) (pow2 64) (uint_v (Lib.Sequence.index (as_seq h temp) 0));
    short_mul_bn #c (prime_buffer #c) y_ t2;
  pop_frame()


val montgomery_multiplication_round_k0: #c: curve -> t: widefelem c -> 
  round: widefelem c -> k0: uint64 ->
  Stack unit 
  (requires fun h -> 
    let prime = getPrime c in 
    live h t /\ live h round  /\ wide_as_nat c h t < prime * prime)
  (ensures fun h0 _ h1 -> modifies (loc round) h0 h1 /\ 
    wide_as_nat c h1 round = (wide_as_nat c h0 t + getPrime c * ((uint_v k0 * (wide_as_nat c h0 t % pow2 64)) % pow2 64)) / pow2 64
  )

let montgomery_multiplication_round_k0 #c t round k0 = 
  push_frame(); 
    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 
    
    let len = getCoordinateLenU64 c in 
    let t2 = create (size 2 *! len) (u64 0) in 

    let h0 = ST.get() in 
    montgomery_multiplication_round_k0_ k0 t t2;
    
    assert_by_tactic (getPrime c * (((wide_as_nat c h0 t % pow2 64) * uint_v k0) % pow2 64) == 
      getPrime c * ((uint_v k0 * (wide_as_nat c h0 t % pow2 64)) % pow2 64)) canon;
    
    add_long_without_carry #c t t2 t2; 
    shift1 #c t2 round;
  pop_frame()


val montgomery_multiplication_buffer_by_one_w_ko: #c: curve {(getPrime c + 1) % pow2 64 == 0} 
  -> a: felem c
  -> result: felem c -> 
  Stack unit
  (requires (fun h -> live h a /\ as_nat c h a < getPrime c /\ live h result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (let prime = getPrime c in 
    as_nat c h1 result  = (as_nat c h0 a * modp_inv2_prime (getPower2 c) prime) % prime /\
    as_nat c h1 result = fromDomain_ #c (as_nat c h0 a)))
  )

let montgomery_multiplication_buffer_by_one_w_ko #c a result = 
  push_frame();
  
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let t_low = sub t (size 0) len in 
    let t_high = sub t len len in 

  let h0 = ST.get() in 

  copy t_low a; 

  let h1 = ST.get() in 
  
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = let prime = getPrime c in 
    live h t /\ wide_as_nat c h t < prime * prime /\ modifies (loc t) h0 h /\
    wide_as_nat c h t % prime = wide_as_nat c h1 t * modp_inv2 #c (pow2 (i * 64)) % prime in 

  assert(wide_as_nat c h1 t = as_nat c h0 a + as_nat c h0 t_high * getPower2 c);
  assert(as_nat c h0 t_high = 0);

  lemma_inv1 (wide_as_nat c h1 t) (getPrime c);
  lemma_mod_inv #c (wide_as_nat c h1 t);

  let h3 = ST.get() in 
  for 0ul len inv (fun i ->
    let h0_ = ST.get() in 
    montgomery_multiplication_round #c t t; 
    let h1_ = ST.get() in


    let a0 = wide_as_nat c h1 t in 
    let a_i = wide_as_nat c h0_ t in 
    let a_il = wide_as_nat c h1_ t in 
    montgomery_multiplication_one_round_proof_border #c (a_i % pow2 64) a_i a_il;
    lemma_multiplication_by_inverse_w_k0 #c a0 a_i a_il (v i)
  );

  let h2 = ST.get() in 
  
  assume (wide_as_nat c h2 t < 2 * getPrime c);

  reduction_prime_2prime_with_carry t result;
  pop_frame();
  
  lemmaFromDomain #c (as_nat c h0 a)



val montgomery_multiplication_buffer_by_one_ko: #c: curve  
  -> a: felem c
  -> result: felem c -> 
  Stack unit
  (requires (fun h -> live h a /\ as_nat c h a < getPrime c /\ live h result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (
    let prime = getPrime c in 
    as_nat c h1 result  = (as_nat c h0 a * modp_inv2_prime (getPower2 c) prime) % prime /\
    as_nat c h1 result = fromDomain_ #c (as_nat c h0 a)))
  )

let montgomery_multiplication_buffer_by_one_ko #c a result = 
  push_frame();
  
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let t_low = sub t (size 0) len in 
    let t_high = sub t len len in 

    let h0 = ST.get() in 
  copy t_low a; 
    let h1 = ST.get() in 
    let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = let prime = getPrime c in 
      live h t /\ wide_as_nat c h t < prime * prime  /\
      modifies (loc t) h0 h /\ 
      wide_as_nat c h t % prime = wide_as_nat c h1 t * modp_inv2 #c (pow2 (i * 64)) % prime
    in 

    assert(wide_as_nat c h1 t = as_nat c h0 a + as_nat c h0 t_high * getPower2 c);
    assert(as_nat c h0 t_high = 0);

    lemma_inv1 (wide_as_nat c h1 t) (getPrime c);
    lemma_mod_inv #c (wide_as_nat c h1 t);
  
    for 0ul len inv (fun i -> let h0_ = ST.get() in 
    montgomery_multiplication_round_k0 #c t t (getKo c); 
      let h1_ = ST.get() in
    
      let a0 = wide_as_nat c h1 t in 
      let a_i = wide_as_nat c h0_ t in 
      let a_il = wide_as_nat c h1_ t in 

      montgomery_multiplication_one_round_proof_border #c (v (getKo c) * (a_i % pow2 64) % pow2 64) a_i a_il;
      lemma_multiplication_by_inverse_k0 #c a0 a_i a_il (v i)
    );
      let h2 = ST.get() in 
  
      assume (wide_as_nat c h2 t < 2 * getPrime c);

  reduction_prime_2prime_with_carry t result;
  pop_frame();
  
    lemmaFromDomain #c (as_nat c h0 a)


val montgomery_multiplication_buffer_w_k0: #c: curve {(getPrime c + 1) % pow2 64 == 0}
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


let montgomery_multiplication_buffer_w_k0 #c a b result = 
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
    montgomery_multiplication_round_k0 #c t t (getKo c); 
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



val montgomery_square_buffer_w_k0: #c: curve {(getPrime c + 1) % pow2 64 == 0} -> a: felem c
  -> result: felem c ->  
  Stack unit
  (requires (fun h -> live h a /\ as_nat c h a < (getPrime c) /\ live h result)) 
  (ensures (fun h0 _ h1 -> (let prime = getPrime c in modifies (loc result) h0 h1 /\  
    as_nat c h1 result < prime /\ 
    as_nat c h1 result = (as_nat c h0 a * as_nat c h0 a * modp_inv2_prime (getPower c) prime) % prime /\
    as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) % prime) /\
    as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a)))))


let montgomery_square_buffer_w_k0 #c a result = 
  push_frame();
    
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let h0 = ST.get() in 
  square_bn a t;  
    let h1 = ST.get() in 
  let inv h (i: nat { i <= uint_v len}) =  let prime = getPrime c in 
    live h t /\ wide_as_nat c h t < prime * prime  /\
    modifies (loc t) h0 h /\
    wide_as_nat c h t % prime = wide_as_nat c h1 t * modp_inv2 #c (pow2 (i * 64)) % prime in 

    assume (wide_as_nat c h1 t < getPrime c * getPrime c);
    assume (wide_as_nat c h1 t % getPrime c = wide_as_nat c h1 t * modp_inv2 #c (pow2 (0 * 64)) % getPrime c);
  
  for 0ul len inv (fun i ->
      let h0_ = ST.get() in 
    montgomery_multiplication_round #c t t; 
      let h1_ = ST.get() in

      let a0 = wide_as_nat c h1 t in 
      let a_i = wide_as_nat c h0_ t in 
      let a_il = wide_as_nat c h1_ t in 
      montgomery_multiplication_one_round_proof_border #c (a_i % pow2 64) a_i a_il;
      lemma_multiplication_by_inverse_w_k0 #c a0 a_i a_il (v i));

    let h2 = ST.get() in 
    assume (wide_as_nat c h2 t < 2 * getPrime c);
  reduction_prime_2prime_with_carry t result; 
    admit();
    
  pop_frame()  



val montgomery_square_buffer_k0: #c: curve -> a: felem c -> result: felem c ->  
  Stack unit
  (requires (fun h -> live h a /\ as_nat c h a < getPrime c /\ live h result)) 
  (ensures (fun h0 _ h1 -> (modifies (loc result) h0 h1 /\ (let prime = getPrime c in 
    as_nat c h1 result < prime /\ 
    as_nat c h1 result = (as_nat c h0 a * as_nat c h0 a * modp_inv2_prime (getPower c) prime) % prime /\
    as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) % prime) /\
    as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a)))))
  )


let montgomery_square_buffer_k0 #c a result = 
  push_frame();
    
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let h0 = ST.get() in 
  square_bn a t;  
    let h1 = ST.get() in 
  let inv h (i: nat { i <= uint_v len}) = True in 
    for 0ul len inv (fun i -> montgomery_multiplication_round_k0 #c t t (getKo c));

  reduction_prime_2prime_with_carry t result; 
  admit();
   
  pop_frame()  


inline_for_extraction
val supportsReducedMultiplication: #c: curve -> 
  Stack bool
    (requires fun h -> True)
    (ensures fun h0 r h1 -> r <==> (getPrime c + 1) % pow2 64 == 0)

let supportsReducedMultiplication #c = 
  let primeBuffer = prime_buffer #c in 
  let primeBuffer0 = index primeBuffer (size 0) in 
    eq_lemma #U64 primeBuffer0 (u64 0xffffffffffffffff);
  eq #U64 primeBuffer0 (u64 0xffffffffffffffff)


let montgomery_multiplication_buffer_by_one #c a result = 
  match supportsReducedMultiplication #c with 
  |true -> 
    montgomery_multiplication_buffer_by_one_w_ko a result
  |false -> montgomery_multiplication_buffer_by_one_ko a result


let montgomery_multiplication_buffer #c a b result = 
  match supportsReducedMultiplication #c with 
  |true -> 
    montgomery_multiplication_buffer_w_k0 a b result
  |false -> montgomery_multiplication_buffer_k0 a b result



let montgomery_square_buffer #c a result = 
  match supportsReducedMultiplication #c with 
  |true -> 
     montgomery_square_buffer_w_k0 a result
  |false -> montgomery_square_buffer_k0 a result




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
