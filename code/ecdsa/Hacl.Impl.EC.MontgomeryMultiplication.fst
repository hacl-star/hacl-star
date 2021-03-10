module Hacl.Impl.EC.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer


open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Impl.EC.LowLevel
open Hacl.Impl.EC.MontgomeryMultiplication.Lemmas

open Lib.Loops
open Hacl.Impl.EC.Setup

#set-options "--z3rlimit 200"


inline_for_extraction
val supportsReducedMultiplication: #c: curve -> 
  Tot  (r: bool {r ==> min_one_prime (pow2 64) (- getPrime c) == 1})

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
      wide_as_nat c h1 t2 < getPower2 c * pow2 64 /\
      wide_as_nat c h1 t2 = getPrime c * (wide_as_nat c h0 t % pow2 64))
  
let montgomery_multiplication_round_w_k0 #c t t2 =
  let t1 = mod64 t in 
  recall_contents (prime_buffer #c) (Lib.Sequence.of_list (prime_list c)); 
  short_mul_bn (prime_buffer #c) t1 t2


val montgomery_multiplication_round_k0: #c: curve -> k0: uint64 -> t: widefelem c -> 
  t2: widefelem c -> 
  Stack unit
  (requires fun h -> live h t /\ live h t2 /\ wide_as_nat c h t2 = 0)
  (ensures fun h0 _ h1 -> modifies (loc t2) h0 h1 /\ 
    wide_as_nat c h1 t2 < getPower2 c * pow2 64 /\
    wide_as_nat c h1 t2 = getPrime c * (((wide_as_nat c h0 t % pow2 64) * uint_v k0) % pow2 64))

let montgomery_multiplication_round_k0 #c k0 t t2 = 
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


val montgomery_multiplication_round_: #c: curve -> t: widefelem c -> t2: widefelem c -> 
  Stack unit
  (requires fun h -> live h t /\ live h t2 /\ wide_as_nat c h t2 = 0)
  (ensures fun h0 _ h1 -> modifies (loc t2) h0 h1 /\ 
    wide_as_nat c h1 t2 < getPower2 c * pow2 64 /\ (
    let k0 = min_one_prime (pow2 64) (- getPrime c) in 
    wide_as_nat c h1 t2 = getPrime c * (((wide_as_nat c h0 t % pow2 64) * k0) % pow2 64))
  )

let montgomery_multiplication_round_ #c t t2 = 
  match supportsReducedMultiplication #c with   
  |true -> montgomery_multiplication_round_w_k0 t t2
  |false -> 
    let h0 = ST.get() in 
    let k0 = getK0 c in 
    montgomery_multiplication_round_k0 k0 t t2


val montgomery_multiplication_one_round_proof: 
  #c: curve ->
  t: nat ->
  k0: nat {let prime = getPrime c in k0 = min_one_prime (pow2 64) (- prime)}  ->  
  round: nat {round = (t + getPrime c * (((t % pow2 64) * k0) % pow2 64)) / pow2 64} -> 
  co: nat {co % getPrime c = t % getPrime c} -> 
  Lemma (round  % getPrime c == co * (modp_inv2_prime (pow2 64) (getPrime c)) % ( getPrime c ))

let montgomery_multiplication_one_round_proof #c t k0 round co = admit()


val montgomery_multiplication_round: #c: curve -> t: widefelem c -> round: widefelem c -> 
  Stack unit 
  (requires fun h -> live h t /\ live h round /\ wide_as_nat c h t < getPrime c * getPrime c /\ eq_or_disjoint t round)
  (ensures fun h0 _ h1 -> modifies (loc round) h0 h1 /\ (
    let k0 = min_one_prime (pow2 64) (- getPrime c) in
    wide_as_nat c h1 round = (wide_as_nat c h0 t + getPrime c * (((wide_as_nat c h0 t % pow2 64) * k0) % pow2 64)) / pow2 64)
  )

let montgomery_multiplication_round #c t round =
  push_frame(); 
    let len = getCoordinateLenU64 c in  
    let t2 = create (size 2 *! len) (u64 0) in 
    lemma_create_zero_buffer (2 * v len) c;
    montgomery_multiplication_round_ #c t t2;
    add_long_without_carry t t2 round;
    shift1 round round; 
  pop_frame()  


val lemma_up_bound0: #c: curve -> t0: nat {t0 < getPrime c * pow2 (64 * v (getCoordinateLenU64 c))} 
  -> t: nat{let prime = getPrime c in 
  t <= t0 / (pow2 (64 * v (getCoordinateLenU64 c))) + prime} -> 
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


val montgomery_multiplication_reduction: #c: curve
  -> t: widefelem c 
  -> result: felem c -> 
  Stack unit 
  (requires (fun h -> live h t /\ wide_as_nat c h t < getPrime c /\ live h result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (let prime = getPrime c in 
    as_nat c h1 result = (wide_as_nat c h0 t * modp_inv2_prime (getPower2 c) prime) % prime /\
    as_nat c h1 result = fromDomain_ #c (wide_as_nat c h0 t)))
  )


let montgomery_multiplication_reduction #c t result = 
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
   
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = 
    let prime = getPrime c in 
    live h t /\ wide_as_nat c h t < prime * prime /\ 
    wide_as_nat c h t < prime * prime /\
    wide_as_nat c h t <= prime * prime / (pow2 (64 * i)) + prime
    
    
    in 

  lemma_inv1 (wide_as_nat c h0 t) (getPrime c);
  lemma_mod_inv #c (wide_as_nat c h0 t);

  let h1 = ST.get() in

  assert(wide_as_nat c h0 t < getPrime c * getPrime c);
  assert(wide_as_nat c h0 t < getPrime c * getPrime c / (pow2 (64 * 0)) + getPrime c);
    
  for 0ul len inv (fun i ->
    let h0_ = ST.get() in 
    montgomery_multiplication_round #c t t; 
    let h1_ = ST.get() in

    let a0 = wide_as_nat c h0 t in 
    let a_i = wide_as_nat c h0_ t in 
    let a_il = wide_as_nat c h1_ t in 

    let prime = getPrime c in 
    let k0 = min_one_prime (pow2 64) (- getPrime c) in 
    let co = a0 * modp_inv2 #c (pow2 (v i * 64)) in 

    lemma_up_bound1 #c (v i) a_i k0 a_il;

    admit();
    montgomery_multiplication_one_round_proof #c a_i k0 a_il co;
    admit()

  );


  let h2 = ST.get() in 
  lemma_up_bound0 #c (wide_as_nat c h2 t); 
  assume (eq_or_disjoint t result);

  reduction_prime_2prime_with_carry t result;
  admit()

(*
val montgomery_multiplication_buffer_by_one: #c: curve {(getPrime c + 1) % pow2 64 == 0} 
  -> a: felem c
  -> result: felem c -> 
  Stack unit
  (requires (fun h -> live h a /\ as_nat c h a < getPrime c /\ live h result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (let prime = getPrime c in 
    as_nat c h1 result  = (as_nat c h0 a * modp_inv2_prime (getPower2 c) prime) % prime /\
    as_nat c h1 result = fromDomain_ #c (as_nat c h0 a)))
  )

*)

let montgomery_multiplication_buffer_by_one #c a result = 
  push_frame();
  
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let t_low = sub t (size 0) len in 
    let t_high = sub t len len in 

  let h0 = ST.get() in 

  copy t_low a; 
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
