module Hacl.Impl.P256.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Hacl.Impl.P256.Math 

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas
open FStar.Mul

open Spec.P256.Definitions
open Spec.P256.Lemmas
open Hacl.Impl.LowLevel
open Hacl.Impl.P256.LowLevel

open Lib.Loops
open Spec.P256.MontgomeryMultiplication

#set-options "--z3rlimit 100"

inline_for_extraction noextract
val add8_without_carry1:  t: widefelem -> t1: widefelem -> result: widefelem  -> Stack unit
  (requires fun h -> 
    live h t /\ live h t1 /\ live h result /\ eq_or_disjoint t1 result /\ 
    eq_or_disjoint t result /\ wide_as_nat h t1 < pow2 320 /\ wide_as_nat h t < prime256 * prime256
  )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ wide_as_nat h1 result = wide_as_nat h0 t + wide_as_nat h0 t1)

let add8_without_carry1 t t1 result  = 
  let _  = add8 t t1 result in 
    assert_norm (pow2 320 + prime256 * prime256 < pow2 512)

inline_for_extraction
val montgomery_multiplication_round: t: widefelem -> round: widefelem -> Stack unit 
  (requires fun h -> live h t /\ live h round /\ wide_as_nat h t < prime256 * prime256)
  (ensures fun h0 _ h1 -> modifies (loc round)  h0 h1 /\
    wide_as_nat h1 round = (wide_as_nat h0 t + prime256 * (wide_as_nat h0 t % pow2 64)) / pow2 64
  )

let montgomery_multiplication_round t round =
  push_frame(); 
    let h0 = ST.get() in 
    let t2 = create (size 8) (u64 0) in 
    let t3 = create (size 8) (u64 0) in 
    let t1 = mod64 t in 
      recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list); 
    shortened_mul prime256_buffer t1 t2;
    add8_without_carry1 t t2 t3;
    shift8 t3 round;
  pop_frame()  


val montgomery_multiplication_one_round_proof: 
  t: nat {t < prime256 * prime256} -> 
  result: nat {result = (t + (t % pow2 64) * prime256) / pow2 64} ->
  co: nat {co % prime256 == t % prime256} -> Lemma (
    result % prime256 == co * modp_inv2 (pow2 64) % prime256 /\
    result < prime256 * prime256)

let montgomery_multiplication_one_round_proof t result co = 
  mult_one_round t co;
  mul_lemma_1 (t % pow2 64) (pow2 64) prime256;
  assert_norm (prime256 * prime256 + pow2 64 * prime256 < pow2 575);
  lemma_div_lt (t + (t % pow2 64) * prime256) 575 64; 
  assert_norm (prime256 * prime256 > pow2 (575 - 64))

inline_for_extraction
val montgomery_multiplication_round_twice: t: widefelem -> result: widefelem -> Stack unit 
  (requires fun h -> live h t /\ live h result  /\ wide_as_nat h t < prime256 * prime256)
  (ensures fun h0 _ h1 -> 
    modifies (loc result) h0 h1 /\
    (
      let round = (wide_as_nat h0 t + prime256 * (wide_as_nat h0 t % pow2 64)) / pow2 64 in 
      wide_as_nat h1 result < prime256 * prime256 /\
      wide_as_nat h1 result % prime256 == (wide_as_nat h0 t * modp_inv2_prime (pow2 128) prime256) % prime256 /\
      wide_as_nat h1 result == (round + prime256 * (round % pow2 64)) / pow2 64
    )
 )

let montgomery_multiplication_round_twice t result = 
  assert_norm(prime256 > 3);
  push_frame();
    let tempRound = create (size 8) (u64 0) in 
      let h0 = ST.get() in 
    montgomery_multiplication_round t tempRound; 
      let h1 = ST.get() in 
      montgomery_multiplication_one_round_proof (wide_as_nat h0 t)  (wide_as_nat h1 tempRound) (wide_as_nat h0 t);
    montgomery_multiplication_round tempRound result;
      let h2 = ST.get() in 
      montgomery_multiplication_one_round_proof (wide_as_nat h1 tempRound) (wide_as_nat h2 result) (wide_as_nat h0 t * modp_inv2_prime (pow2 64) prime256);
      lemma_montgomery_mod_inverse_addition (wide_as_nat h0 t);
  pop_frame()


val montgomery_multiplication_buffer_by_one: a: felem -> result: felem ->  Stack unit
  (requires (fun h -> live h a /\ as_nat h a < prime256 /\ live h result)) 
  (ensures (fun h0 _ h1 -> 
    modifies (loc result) h0 h1 /\ 
    as_nat h1 result  = (as_nat h0 a * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 result = fromDomain_ (as_nat h0 a))
  )


let montgomery_multiplication_buffer_by_one a result = 
  assert_norm (prime256 > 3);
  push_frame();
    let t = create (size 8) (u64 0) in 
      let t_low = sub t (size 0) (size 4) in 
      let t_high = sub t (size 4) (size 4) in 
    let round2 = create (size 8) (u64 0) in 
    let round4 = create (size 8) (u64 0) in  
      let h0 = ST.get() in 
    copy t_low a; 
      let h1 = ST.get() in 
      assert(wide_as_nat h0 t = as_nat h0 t_low + as_nat h0 t_high * pow2 256);
      assert_norm (prime256 < prime256 * prime256);
    montgomery_multiplication_round_twice t round2;
      let h2 = ST.get() in 
    montgomery_multiplication_round_twice round2 round4; 
      lemma_montgomery_mod_inverse_addition2 (wide_as_nat h1 t);
      lemma_mod_mul_distr_l (wide_as_nat h2 round2) (modp_inv2_prime (pow2 128) prime256) prime256;
      lemma_mod_mul_distr_l (wide_as_nat h1 t * modp_inv2_prime (pow2 128) prime256) (modp_inv2_prime (pow2 128) prime256) prime256;
	mul_lemma_2 (wide_as_nat h1 t % pow2 64) (pow2 64 - 1) prime256;
	mul_lemma_2 (let round = (wide_as_nat h1 t + prime256 * (wide_as_nat h1 t % pow2 64)) / pow2 64 in round % pow2 64) (pow2 64 - 1) prime256;
	mul_lemma_2 (
	  let round = (wide_as_nat h1 t + prime256 * (wide_as_nat h1 t % pow2 64)) / pow2 64 in  
	  let round2 = (round + prime256 * (round % pow2 64)) / pow2 64 in 
	  round2 % pow2 64) (pow2 64 - 1) prime256;
	mul_lemma_2 (	
	  let round = (wide_as_nat h1 t + prime256 * (wide_as_nat h1 t % pow2 64)) / pow2 64 in  
	  let round2 = (round + prime256 * (round % pow2 64)) / pow2 64 in 
	  let round3 = (round2 + prime256 * (round2 % pow2 64)) / pow2 64 in   
	  round3 % pow2 64) (pow2 64 - 1) prime256;
    reduction_prime256_2prime256_8_with_carry_impl round4 result;
    lemmaFromDomain (as_nat h0 a);
  pop_frame()  


val montgomery_multiplication_buffer: a: felem -> b: felem -> result: felem ->  Stack unit
  (requires (fun h -> live h a /\ as_nat h a < prime256 /\ live h b /\ live h result /\ as_nat h b < prime256)) 
  (ensures (fun h0 _ h1 -> 
    modifies (loc result) h0 h1 /\  
    as_nat h1 result = (as_nat h0 a * as_nat h0 b * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % prime256) /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b)))
  )


let montgomery_multiplication_buffer a b result = 
  assert_norm(prime256 > 3);
  push_frame();
    let t = create (size 8) (u64 0) in 
    let round2 = create (size 8) (u64 0) in 
    let round4 = create (size 8) (u64 0) in  
      let h0 = ST.get() in 
    mul a b t;  
      let h1 = ST.get() in 
      mul_lemma_ (as_nat h0 a) (as_nat h0 b) prime256;
  montgomery_multiplication_round_twice t round2;
      let h2 = ST.get() in 
  montgomery_multiplication_round_twice round2 round4; 
      let h3 = ST.get() in 
	lemma_montgomery_mod_inverse_addition2 (wide_as_nat h1 t);
	lemma_mod_mul_distr_l (wide_as_nat h2 round2) (modp_inv2_prime (pow2 128) prime256) prime256;
	lemma_mod_mul_distr_l (wide_as_nat h1 t * modp_inv2_prime (pow2 128) prime256) (modp_inv2_prime (pow2 128) prime256) prime256;
      mul_lemma_2 (wide_as_nat h1 t % pow2 64) (pow2 64 - 1) prime256;
      mul_lemma_ (as_nat h0 a) (as_nat h0 b) prime256;
      mul_lemma_1 ( 
         let round = (wide_as_nat h1 t + prime256 * (wide_as_nat h1 t % pow2 64)) / pow2 64 in  
	 round % pow2 64) (pow2 64) prime256; 
      mul_lemma_1 ( 
	let round = (wide_as_nat h1 t + prime256 * (wide_as_nat h1 t % pow2 64)) / pow2 64 in 
	let round2 = (round + prime256 * (round % pow2 64)) / pow2 64 in 
	round2 % pow2 64) (pow2 64) prime256; 
      mul_lemma_1 ( 
	let round = (wide_as_nat h1 t + prime256 * (wide_as_nat h1 t % pow2 64)) / pow2 64 in 
	let round2 = (round + prime256 * (round % pow2 64)) / pow2 64 in 
	let round3 = (round2 + prime256 * (round2 % pow2 64)) / pow2 64 in 
	round3 % pow2 64) (pow2 64) prime256;  
      assert_norm((prime256 * pow2 64 + (prime256 * pow2 64 + (prime256 * pow2 64 + ((pow2 64 - 1) * prime256 + prime256 * prime256) / pow2 64) / pow2 64)/ pow2 64) / pow2 64 < 2 * prime256);
  reduction_prime256_2prime256_8_with_carry_impl round4 result; 
  lemmaFromDomainToDomain (as_nat h0 a);
  lemmaFromDomainToDomain (as_nat h0 b);
  multiplicationInDomainNat #(fromDomain_ (as_nat h0 a)) #(fromDomain_ (as_nat h0 b))  (as_nat h0 a) (as_nat h0 b);
  inDomain_mod_is_not_mod (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b));
  pop_frame()  


val montgomery_square_buffer: a: felem -> result: felem ->  Stack unit
  (requires (fun h -> live h a /\ as_nat h a < prime256 /\ live h result)) 
  (ensures (fun h0 _ h1 -> 
    modifies (loc result) h0 h1 /\  
    as_nat h1 result = (as_nat h0 a * as_nat h0 a * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) % prime256) /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a)))
  )


let montgomery_square_buffer a result = 
  assert_norm(prime256 > 3);
  push_frame();
    let t = create (size 8) (u64 0) in 
    let round2 = create (size 8) (u64 0) in 
    let round4 = create (size 8) (u64 0) in  
      let h0 = ST.get() in 
    sq a t;  
      let h1 = ST.get() in 
      mul_lemma_ (as_nat h0 a) (as_nat h0 a) prime256;
  montgomery_multiplication_round_twice t round2;
      let h2 = ST.get() in 
  montgomery_multiplication_round_twice round2 round4; 
      let h3 = ST.get() in 
  lemma_montgomery_mod_inverse_addition2 (wide_as_nat h1 t);
  lemma_mod_mul_distr_l (wide_as_nat h2 round2) (modp_inv2_prime (pow2 128) prime256) prime256;
  lemma_mod_mul_distr_l (wide_as_nat h1 t * modp_inv2_prime (pow2 128) prime256) (modp_inv2_prime (pow2 128) prime256) prime256;
      mul_lemma_2 (wide_as_nat h1 t % pow2 64) (pow2 64 - 1) prime256;
      mul_lemma_ (as_nat h0 a) (as_nat h0 a) prime256;
      mul_lemma_1 ( 
         let round = (wide_as_nat h1 t + prime256 * (wide_as_nat h1 t % pow2 64)) / pow2 64 in  
   round % pow2 64) (pow2 64) prime256; 
      mul_lemma_1 ( 
  let round = (wide_as_nat h1 t + prime256 * (wide_as_nat h1 t % pow2 64)) / pow2 64 in 
  let round2 = (round + prime256 * (round % pow2 64)) / pow2 64 in 
  round2 % pow2 64) (pow2 64) prime256; 
      mul_lemma_1 ( 
  let round = (wide_as_nat h1 t + prime256 * (wide_as_nat h1 t % pow2 64)) / pow2 64 in 
  let round2 = (round + prime256 * (round % pow2 64)) / pow2 64 in 
  let round3 = (round2 + prime256 * (round2 % pow2 64)) / pow2 64 in 
  round3 % pow2 64) (pow2 64) prime256;  
      assert_norm((prime256 * pow2 64 + (prime256 * pow2 64 + (prime256 * pow2 64 + ((pow2 64 - 1) * prime256 + prime256 * prime256) / pow2 64) / pow2 64)/ pow2 64) / pow2 64 < 2 * prime256);
  reduction_prime256_2prime256_8_with_carry_impl round4 result; 
  lemmaFromDomainToDomain (as_nat h0 a);
  multiplicationInDomainNat #(fromDomain_ (as_nat h0 a)) #(fromDomain_ (as_nat h0 a))  (as_nat h0 a) (as_nat h0 a);
  inDomain_mod_is_not_mod (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a));
  pop_frame()  


#reset-options "--z3rlimit 500" 

val fsquarePowN: n: size_t -> a: felem -> Stack unit 
  (requires (fun h -> live h a /\ as_nat h a < prime256)) 
  (ensures (fun h0 _ h1 -> 
    modifies (loc a) h0 h1 /\  as_nat h1 a < prime256 /\ 
    (let k = fromDomain_(as_nat h0 a) in as_nat h1 a = toDomain_ (pow k (pow2 (v n)))))
  )

let fsquarePowN n a = 
  let h0 = ST.get() in  
  lemmaFromDomainToDomain (as_nat h0 a); 
  assert_norm (pow2 0 == 1); 
  let inv (h0: HyperStack.mem) (h1: HyperStack.mem) (i: nat) : Type0 =
    let k = fromDomain_ (as_nat h0 a) in 
    as_nat h1 a = toDomain_ (pow k (pow2 i)) /\
    as_nat h1 a < prime256 /\ live h1 a /\ modifies1 a h0 h1  in 
  power_one (fromDomain_ (as_nat h0 a)); 
  for (size 0) n (inv h0) (fun x -> 
    let h0_ = ST.get() in 
     montgomery_multiplication_buffer a a a; 
     let k = fromDomain_ (as_nat h0 a) in  
     inDomain_mod_is_not_mod (fromDomain_ (as_nat h0_ a) * fromDomain_ (as_nat h0_ a)); 
     lemmaFromDomainToDomainModuloPrime (let k = fromDomain_ (as_nat h0 a) in pow k (pow2 (v x)));
     modulo_distributivity_mult (pow k (pow2 (v x))) (pow k (pow2 (v x))) prime256; 
     pow_plus k  (pow2 (v x)) (pow2 (v x )); 
     pow2_double_sum (v x);
     inDomain_mod_is_not_mod (pow k (pow2 (v x + 1)))
  )


val fsquarePowNminusOne: n: size_t -> a: felem -> tempBuffer: felem -> Stack unit 
  (requires (fun h -> live h a /\ live h tempBuffer /\ as_nat h a < prime256 /\ disjoint a tempBuffer)) 
  (ensures (fun h0 _ h1 -> 
    as_nat h1 a < prime256 /\ as_nat h1 tempBuffer < prime256 /\ 
    modifies (loc a |+| loc tempBuffer) h0 h1 /\ 
    (
      let k = fromDomain_ (as_nat h0 a) in  
      as_nat h1 a = toDomain_ (pow k (pow2 (v n))) /\ as_nat h1 tempBuffer = toDomain_ (pow k (pow2 (v n) -1 )))
    )
   )

let fsquarePowNminusOne n a b = 
  let h0 = ST.get() in
  assert_norm(prime256 > 3);
  Lib.Buffer.upd b (size 0) (u64 1);
  Lib.Buffer.upd b (size 1) (u64 18446744069414584320);
  Lib.Buffer.upd b (size 2) (u64 18446744073709551615);
  Lib.Buffer.upd b (size 3) (u64 4294967294);

  let one = (u64 1, u64 18446744069414584320, u64 18446744073709551615, u64 4294967294) in 
      lemmaFromDomainToDomain (as_nat h0 a);
      lemmaToDomain 1;
      assert_norm (1 + pow2 64 * 18446744069414584320 + pow2 64 * pow2 64 * 18446744073709551615 + pow2 64 * pow2 64 * pow2 64 * 4294967294 = 26959946660873538059280334323183841250350249843923952699046031785985);
      assert_norm (pow2 256 % prime256 == 26959946660873538059280334323183841250350249843923952699046031785985);
      assert_norm (as_nat4 one = toDomain_(1));

  let inv (h0: HyperStack.mem) (h1: HyperStack.mem) (i: nat) : Type0 = 
    let k = fromDomain_(as_nat h0 a) in 
    as_nat h1 b = toDomain_ (pow k (pow2 i - 1)) /\ as_nat h1 a < prime256 /\ live h1 a /\
    as_nat h1 a = toDomain_ (pow k (pow2 i)) /\ as_nat h1 b < prime256 /\ live h1 b /\ modifies (loc a |+| loc b) h0 h1 in 
  for (size 0) n (inv h0) (fun x -> 
    let h0_ = ST.get() in 
    montgomery_multiplication_buffer b a b;
    montgomery_multiplication_buffer a a a;
    let k = fromDomain_ (as_nat h0 a) in 
    inDomain_mod_is_not_mod (fromDomain_ (as_nat h0_ b) * fromDomain_ (as_nat h0_ a));
    inDomain_mod_is_not_mod (fromDomain_ (as_nat h0_ a) * fromDomain_ (as_nat h0_ a));

    lemmaFromDomainToDomainModuloPrime (pow k (pow2 (v x) -1 ));
    lemmaFromDomainToDomainModuloPrime (pow k (pow2 (v x)));
    modulo_distributivity_mult (pow k (pow2 (v x) - 1)) (pow k (pow2 (v x))) prime256;
    modulo_distributivity_mult (pow k (pow2 (v x))) (pow k (pow2 (v x))) prime256;
    
    pow_plus k (pow2 (v x) -1 ) (pow2 (v x));
    pow_plus k (pow2 (v x)) (pow2 (v x));
    pow2_double_sum (v x);

    inDomain_mod_is_not_mod (pow k (pow2 (v x + 1)));
    inDomain_mod_is_not_mod (pow k (pow2 (v x + 1) - 1))
)


inline_for_extraction noextract   
val norm_part_one: a: felem -> tempBuffer: lbuffer uint64 (size 8) -> 
  Stack unit (requires fun h -> live h a /\ live h tempBuffer /\ disjoint a tempBuffer /\  as_nat h a < prime256)
  (ensures fun h0 _ h1 -> modifies1 tempBuffer h0 h1 /\ (let buffer_result = gsub tempBuffer (size 4) (size 4) in as_nat h1 buffer_result < prime256 /\ 
  (let k = fromDomain_ (as_nat h0 a) in as_nat h1 buffer_result = toDomain_(pow k ((pow2 32 - 1) * pow2 224) % prime256))))
    
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
  let k_prime = k_powers % prime256 in 
  inDomain_mod_is_not_mod (pow k_prime (pow2 224));
  power_distributivity k_powers (pow2 224) prime256;
  power_mult k (pow2 32 - 1) (pow2 224)
 
 
inline_for_extraction noextract   
val norm_part_two: a: felem -> tempBuffer: lbuffer uint64 (size 4) -> 
  Stack unit (requires fun h -> live h a /\ live h tempBuffer /\ disjoint a tempBuffer /\  as_nat h a < prime256)
  (ensures fun h0 _ h1 -> as_nat h1 tempBuffer < prime256 /\ modifies1 tempBuffer h0 h1 /\
    (let k = fromDomain_ (as_nat h0 a) in as_nat h1 tempBuffer = toDomain_(pow k (pow2 192) % prime256)))
    
let norm_part_two a tempBuffer = 
  let h0 = ST.get() in 
  Lib.Buffer.copy tempBuffer a;
  fsquarePowN (size 192) tempBuffer;
  let k = fromDomain_ (as_nat h0 a) in 
  inDomain_mod_is_not_mod (pow k (pow2 192))

inline_for_extraction noextract   
val norm_part_three:a: felem -> tempBuffer: lbuffer uint64 (size 8) -> 
  Stack unit (requires fun h -> live h a /\ live h tempBuffer /\ disjoint a tempBuffer /\  
   as_nat h a < prime256)   
  (ensures fun h0 _ h1 ->  modifies1 tempBuffer h0 h1 /\ (let buffer_result = gsub tempBuffer (size 4) (size 4) in as_nat h1 buffer_result < prime256
    /\ (let k = fromDomain_ (as_nat h0 a) in as_nat h1 buffer_result = toDomain_(pow k ((pow2 94 - 1) * pow2 2) % prime256))))

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
  let k_prime = k_powers % prime256 in 
  inDomain_mod_is_not_mod (pow k_prime (pow2 2));
  power_distributivity k_powers (pow2 2) prime256;
  power_mult k (pow2 94 - 1) (pow2 2)


val lemma_inDomainModulo: a: nat -> b: nat -> Lemma ((toDomain_ ((a % prime256) * (b % prime256) % prime256) = toDomain_ (a * b % prime256)))

let lemma_inDomainModulo a b = 
  lemma_mod_mul_distr_l a (b % prime256) prime256;
  lemma_mod_mul_distr_r a b prime256


let lemmaEraseToDomainFromDomain z = 
  lemma_mod_mul_distr_l (z * z) z prime256


val big_power: a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> Lemma (pow a b * pow a c * pow a d * pow a e = pow a (b + c + d + e))

let big_power a b c d e = 
  assert(pow a b * pow a c * pow a d * pow a e = (pow a b * pow a c) * (pow a d * pow a e));
  pow_plus a b c;
  pow_plus a d e;
  pow_plus a (b + c) (d + e)

val lemma_mul_nat: a: nat -> b: nat -> Lemma (a * b >= 0)

let lemma_mul_nat a b = ()


val exponent: a: felem ->result: felem -> tempBuffer: lbuffer uint64 (size 20) ->  Stack unit
  (requires fun h -> live h a /\ live h tempBuffer /\ live h result /\ disjoint tempBuffer result /\ 
  disjoint a tempBuffer /\ as_nat h a < prime256)
  (ensures fun h0 _ h1 -> modifies2 result tempBuffer h0 h1 /\ (let k = fromDomain_ (as_nat h0 a) in 
    as_nat h1 result =  toDomain_ ((pow k (prime256-2)) % prime256)))


#reset-options " --z3rlimit 200"
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
  assert_norm ((pow2 32 - 1) * pow2 224 >= 0);
  assert_norm (pow2 192 >= 0);
  assert_norm ((pow2 94 - 1) * pow2 2 >= 0);

  
  let k = fromDomain_ (as_nat h0 a) in 
  let power1 = pow k ((pow2 32 - 1) * pow2 224) in 
  let power2 = pow k (pow2 192) in 
  let power3 = pow k ((pow2 94 - 1) * pow2 2) in 
  let power4 = pow k 1 in 

  lemma_mul_nat power1 power2;

  lemma_inDomainModulo power1 power2;
  lemma_inDomainModulo (power1 * power2) power3;
  inDomain_mod_is_not_mod (((power1 * power2 * power3) % prime256 * power4));
  lemma_mod_mul_distr_l (power1 * power2 * power3) power4 prime256;
  big_power k ((pow2 32 - 1) * pow2 224) (pow2 192) ((pow2 94 -1 ) * pow2 2) 1;
  assert_norm(((pow2 32 - 1) * pow2 224 + pow2 192 + (pow2 94 -1 ) * pow2 2 + 1) = prime256 - 2)
