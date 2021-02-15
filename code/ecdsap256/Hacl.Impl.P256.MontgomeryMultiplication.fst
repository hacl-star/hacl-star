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
open Hacl.Impl.P256.LowLevel 
open Hacl.Impl.P256.LowLevel.PrimeSpecific

open Lib.Loops
open Spec.P256.MontgomeryMultiplication

open Hacl.Impl.P256.MM.Lemmas

#set-options "--z3rlimit 100 --ifuel 0 --fuel 0"


inline_for_extraction noextract
val add8_without_carry1: t: widefelem -> t1: widefelem -> result: widefelem -> Stack unit
  (requires fun h -> 
    live h t /\ live h t1 /\ live h result /\ eq_or_disjoint t1 result /\ 
    eq_or_disjoint t result /\ wide_as_nat h t1 < pow2 320 /\ wide_as_nat h t < prime256 * prime256)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ wide_as_nat h1 result = wide_as_nat h0 t + wide_as_nat h0 t1)

let add8_without_carry1 t t1 result =
  assert_norm (pow2 320 + prime256 * prime256 < pow2 512 - pow2 256);
  add8_void t t1 result


inline_for_extraction
val montgomery_multiplication_round: t: widefelem -> round: widefelem -> t2: lbuffer uint64 (size 8) ->
  Stack unit (requires fun h -> live h t /\ live h round /\ live h t2 /\
    eq_or_disjoint t round /\ disjoint t t2 /\ disjoint round t2 /\
    wide_as_nat h t2 < pow2 320 /\
    wide_as_nat h t < prime256 * prime256)
  (ensures fun h0 _ h1 -> modifies (loc round |+| loc t2) h0 h1 /\
    wide_as_nat h1 t2 < pow2 320 /\
    wide_as_nat h1 round = (wide_as_nat h0 t + prime256 * (wide_as_nat h0 t % pow2 64)) / pow2 64
  )

let montgomery_multiplication_round t round t2  =
  let t1 = mod64 t in 
    recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list); 
  shortened_mul_prime t1 t2;
  add8_without_carry1 t t2 round;
  shift8 round round


val montgomery_multiplication_one_round_proof: t: nat {t < prime256 * prime256} -> 
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

#reset-options "--z3rlimit 300"


inline_for_extraction noextract
val montgomery_multiplication_round_twice: t: widefelem -> result: widefelem -> tempRound: widefelem -> t2: widefelem -> 
  Stack unit 
  (requires fun h -> live h t /\ live h result /\ live h tempRound /\ live h t2 /\
    disjoint t tempRound /\ eq_or_disjoint t result /\ disjoint t t2 /\ 
    disjoint result tempRound /\ disjoint result t2 /\ 
    disjoint tempRound t2 /\ 
    wide_as_nat h t < prime256 * prime256 /\ wide_as_nat h t2 < pow2 320)
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc t2 |+| loc tempRound) h0 h1 /\ (
    let round = (wide_as_nat h0 t + prime256 * (wide_as_nat h0 t % pow2 64)) / pow2 64 in 
    wide_as_nat h1 result < prime256 * prime256 /\
    wide_as_nat h1 t2 < pow2 320 /\
    wide_as_nat h1 result % prime256 == (wide_as_nat h0 t * modp_inv2_prime (pow2 128) prime256) % prime256 /\
    wide_as_nat h1 result == (round + prime256 * (round % pow2 64)) / pow2 64)
  )

let montgomery_multiplication_round_twice t result tempRound t2 = 
    let h0 = ST.get() in 
  montgomery_multiplication_round t tempRound t2; 
    let h1 = ST.get() in 
    montgomery_multiplication_one_round_proof (wide_as_nat h0 t)  (wide_as_nat h1 tempRound) (wide_as_nat h0 t);
  montgomery_multiplication_round tempRound result t2; 
    let h2 = ST.get() in 
    montgomery_multiplication_one_round_proof (wide_as_nat h1 tempRound) (wide_as_nat h2 result) (wide_as_nat h0 t * modp_inv2_prime (pow2 64) prime256); 
    lemma_montgomery_mod_inverse_addition (wide_as_nat h0 t)


inline_for_extraction noextract
val montgomery_multiplication_buffer_by_one: a: felem -> result: felem -> 
  Stack unit
  (requires (fun h -> live h a /\ as_nat h a < prime256 /\ live h result)) 
  (ensures (fun h0 _ h1 -> 
    modifies (loc result) h0 h1 /\ 
    as_nat h1 result  = (as_nat h0 a * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 result = fromDomain_ (as_nat h0 a))
  )


let montgomery_multiplication_buffer_by_one a result = 
  assert_norm (prime256 < prime256 * prime256);
  push_frame();
    let t = create (size 8) (u64 0) in 
      let t_low = sub t (size 0) (size 4) in 
      let t_high = sub t (size 4) (size 4) in 
    let round = create (size 8) (u64 0) in 

    let t1 = create (size 8) (u64 0) in 
    let t2 = create (size 8) (u64 0) in 

      let h0 = ST.get() in     
      assert(wide_as_nat h0 t = as_nat h0 t_low + as_nat h0 t_high * pow2 256);
    copy t_low a; 
      let h1 = ST.get() in 
    montgomery_multiplication_round_twice t round t1 t2;
      let h2 = ST.get() in 
    montgomery_multiplication_round_twice round round t1 t2; 

      calc (==) {wide_as_nat h2 round * modp_inv2_prime (pow2 128) prime256 % prime256;
	(==) {lemma_mod_mul_distr_l (wide_as_nat h2 round) (modp_inv2_prime (pow2 128) prime256) prime256}
      (wide_as_nat h2 round % prime256) * modp_inv2_prime (pow2 128) prime256 % prime256;
	(==) {}
      (as_nat h0 a * modp_inv2_prime (pow2 128) prime256 % prime256) * modp_inv2_prime (pow2 128) prime256 % prime256;
	(==) {lemma_mod_mul_distr_l (as_nat h0 a * modp_inv2_prime (pow2 128) prime256) (modp_inv2_prime (pow2 128) prime256) prime256}
      as_nat h0 a * modp_inv2_prime (pow2 128) prime256 * modp_inv2_prime (pow2 128) prime256 % prime256;
	(==) {lemma_montgomery_mod_inverse_addition2 (as_nat h0 a)}
      as_nat h0 a * modp_inv2_prime (pow2 256) prime256 % prime256; 
      };
      
      mul_lemma_2 (wide_as_nat h1 t % pow2 64) (pow2 64 - 1) prime256;
      mul_lemma_2 (
	let round = (wide_as_nat h1 t + prime256 * (wide_as_nat h1 t % pow2 64)) / pow2 64 in 
	round % pow2 64) (pow2 64 - 1) prime256;
      mul_lemma_2 (
	let round = (wide_as_nat h1 t + prime256 * (wide_as_nat h1 t % pow2 64)) / pow2 64 in  
	let round2 = (round + prime256 * (round % pow2 64)) / pow2 64 in 
	round2 % pow2 64) (pow2 64 - 1) prime256;
      mul_lemma_2 ( 
	let round = (wide_as_nat h1 t + prime256 * (wide_as_nat h1 t % pow2 64)) / pow2 64 in  
	let round2 = (round + prime256 * (round % pow2 64)) / pow2 64 in 
	let round3 = (round2 + prime256 * (round2 % pow2 64)) / pow2 64 in   
	round3 % pow2 64) (pow2 64 - 1) prime256;
      
    reduction_prime256_2prime256_8_with_carry_impl round result;
      lemmaFromDomain (as_nat h0 a);
  pop_frame()  


[@ CInline]
val montgomery_multiplication_buffer: a: felem -> b: felem -> result: felem -> Stack unit
  (requires (fun h -> live h a /\ live h b /\ live h result /\ 
    as_nat h a < prime256 /\ as_nat h b < prime256))
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\  
    as_nat h1 result < prime256 /\
    as_nat h1 result = (as_nat h0 a * as_nat h0 b * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % prime256) /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b)))
  )


let montgomery_multiplication_buffer a b result = 
  push_frame();
    let t = create (size 8) (u64 0) in 
    let round = create (size 8) (u64 0) in  
    let t1 = create (size 8) (u64 0) in 
    let t2 = create (size 8) (u64 0) in 
    
      let h0 = ST.get() in 
      mul_lemma_ (as_nat h0 a) (as_nat h0 b) prime256;
    mul a b t;  
      let h1 = ST.get() in
    montgomery_multiplication_round_twice t round t1 t2;
      let h2 = ST.get() in 
    montgomery_multiplication_round_twice round round t1 t2; 

      calc (==) {wide_as_nat h2 round * modp_inv2_prime (pow2 128) prime256 % prime256;
	(==) {lemma_mod_mul_distr_l (wide_as_nat h2 round) (modp_inv2_prime (pow2 128) prime256) prime256}
      (wide_as_nat h2 round % prime256) * modp_inv2_prime (pow2 128) prime256 % prime256; 
	(==) {}
      as_nat h0 a * as_nat h0 b * modp_inv2_prime (pow2 128) prime256 % prime256 * modp_inv2_prime (pow2 128) prime256 % prime256;
	(==) {lemma_mod_mul_distr_l (as_nat h0 a * as_nat h0 b * modp_inv2_prime (pow2 128) prime256) (modp_inv2_prime (pow2 128) prime256) prime256}
      as_nat h0 a * as_nat h0 b * modp_inv2_prime (pow2 128) prime256 * modp_inv2_prime (pow2 128) prime256 % prime256;
	(==) {lemma_montgomery_mod_inverse_addition2 (as_nat h0 a * as_nat h0 b)}
      as_nat h0 a * as_nat h0 b * modp_inv2_prime (pow2 256) prime256 % prime256;};

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
  
    reduction_prime256_2prime256_8_with_carry_impl round result; 
      lemmaFromDomainToDomain (as_nat h0 a);
      lemmaFromDomainToDomain (as_nat h0 b);
      multiplicationInDomainNat #(fromDomain_ (as_nat h0 a)) #(fromDomain_ (as_nat h0 b))  (as_nat h0 a) (as_nat h0 b);
      inDomain_mod_is_not_mod (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b));
  pop_frame()  


[@ CInline]
val montgomery_square_buffer: a: felem -> result: felem -> Stack unit
  (requires (fun h -> live h a /\ as_nat h a < prime256 /\ live h result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\  
    as_nat h1 result < prime256 /\ 
    as_nat h1 result = (as_nat h0 a * as_nat h0 a * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) % prime256) /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a)))
  )


let montgomery_square_buffer a result = 
  push_frame();
    let t = create (size 8) (u64 0) in
    let t1 = create (size 8) (u64 0) in 
    let t2 = create (size 8) (u64 0) in
    let round = create (size 8) (u64 0) in 
      let h0 = ST.get() in 
    sq a t;
      let h1 = ST.get() in 
      mul_lemma_ (as_nat h0 a) (as_nat h0 a) prime256;
    montgomery_multiplication_round_twice t round t1 t2;
      let h2 = ST.get() in
    montgomery_multiplication_round_twice round round t1 t2; 
      let h3 = ST.get() in 

      calc (==) {wide_as_nat h2 round * modp_inv2_prime (pow2 128) prime256 % prime256;
	(==) {lemma_mod_mul_distr_l (wide_as_nat h2 round) (modp_inv2_prime (pow2 128) prime256) prime256}
      (wide_as_nat h2 round % prime256) * modp_inv2_prime (pow2 128) prime256 % prime256; 
	(==) {}
      as_nat h0 a * as_nat h0 a * modp_inv2_prime (pow2 128) prime256 % prime256 * modp_inv2_prime (pow2 128) prime256 % prime256;
	(==) {lemma_mod_mul_distr_l (as_nat h0 a * as_nat h0 a * modp_inv2_prime (pow2 128) prime256) (modp_inv2_prime (pow2 128) prime256) prime256}
      as_nat h0 a * as_nat h0 a * modp_inv2_prime (pow2 128) prime256 * modp_inv2_prime (pow2 128) prime256 % prime256;
	(==) {lemma_montgomery_mod_inverse_addition2 (as_nat h0 a * as_nat h0 a)}
      as_nat h0 a * as_nat h0 a * modp_inv2_prime (pow2 256) prime256 % prime256;};


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

    reduction_prime256_2prime256_8_with_carry_impl round result; 
      lemmaFromDomainToDomain (as_nat h0 a);
      multiplicationInDomainNat #(fromDomain_ (as_nat h0 a)) #(fromDomain_ (as_nat h0 a))  (as_nat h0 a) (as_nat h0 a);
      inDomain_mod_is_not_mod (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a));
  pop_frame()  


val lemma_inDomainModulo: a: nat -> b: nat -> 
  Lemma ((toDomain_ ((a % prime256) * (b % prime256) % prime256) = toDomain_ (a * b % prime256)))

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


(* Changing argument order *)
inline_for_extraction noextract
val montgomery_multiplication_buffer_: result: felem -> a: felem -> b: felem -> Stack unit
  (requires (fun h -> live h a /\  as_nat h a < prime256 /\ live h b /\ live h result /\ as_nat h b < prime256)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\  
    as_nat h1 result < prime256 /\
    as_nat h1 result = (as_nat h0 a * as_nat h0 b * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % prime256) /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b)))
  )

let montgomery_multiplication_buffer_ result a b = 
  Hacl.Impl.P256.MontgomeryMultiplication.montgomery_multiplication_buffer a b result

inline_for_extraction noextract
val montgomery_square_buffer_: result: felem -> a: felem -> Stack unit
  (requires (fun h -> live h a /\ as_nat h a < prime256 /\ live h result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\  
    as_nat h1 result < prime256 /\ 
    as_nat h1 result = (as_nat h0 a * as_nat h0 a * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) % prime256) /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a)))
  )


let montgomery_square_buffer_ result a = 
  montgomery_square_buffer a result


inline_for_extraction noextract
val fsquarePowN: n: size_t -> a: felem -> Stack unit 
  (requires (fun h -> live h a /\ as_nat h a < prime256)) 
  (ensures (fun h0 _ h1 -> modifies (loc a) h0 h1 /\  as_nat h1 a < prime256 /\ (
    let k = fromDomain_(as_nat h0 a) in as_nat h1 a = toDomain_ (pow k (pow2 (v n))) /\ 
    as_nat h1 a = toDomain_ (pow k (pow2 (v n)) % prime256)))
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
  for (size 0) n (inv h0) (fun x -> let h0_ = ST.get() in 
    montgomery_square_buffer a a; 
      let k = fromDomain_ (as_nat h0 a) in  
      inDomain_mod_is_not_mod (fromDomain_ (as_nat h0_ a) * fromDomain_ (as_nat h0_ a)); 
      lemmaFromDomainToDomainModuloPrime (let k = fromDomain_ (as_nat h0 a) in pow k (pow2 (v x)));
      modulo_distributivity_mult (pow k (pow2 (v x))) (pow k (pow2 (v x))) prime256; 
      pow_plus k  (pow2 (v x)) (pow2 (v x )); 
      pow2_double_sum (v x);
      inDomain_mod_is_not_mod (pow k (pow2 (v x + 1)))
    );
  inDomain_mod_is_not_mod (pow (fromDomain_(as_nat h0 a)) (pow2 (v n)))



inline_for_extraction noextract
val exponent_0: t: felem -> t0: felem -> t1: felem -> t2: felem -> t6: felem -> t7: felem -> 
  Stack unit 
  (requires fun h -> live h t /\ live h t0 /\ live h t1 /\ live h t2 /\ live h t6 /\ live h t7 /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc t; loc t0; loc t1; loc t2; loc t6; loc t7] /\
    as_nat h t < prime256)
  (ensures fun h0 _ h1 -> modifies (loc t0 |+| loc t1 |+| loc t2 |+| loc t6 |+| loc t7) h0 h1 /\ (
    let tD = fromDomain_ (as_nat h0 t) in 
    as_nat h1 t2 = toDomain_ (pow tD 3 % prime256) /\ as_nat h1 t1 = toDomain_ (pow tD 1023 % prime256) /\ 
    as_nat h1 t0 = toDomain_ (pow tD 2046 % prime256)) /\
    as_nat h1 t0 < prime256 /\ as_nat h1 t1 < prime256 /\ as_nat h1 t2 < prime256
  )


let exponent_0 t t0 t1 t2 t6 t7 = 
    let h0 = ST.get() in 
  montgomery_square_buffer_ t0 t; 
  montgomery_multiplication_buffer_ t2 t0 t; 
  montgomery_square_buffer_ t0 t2; 
  montgomery_square_buffer_ t0 t0;
  montgomery_multiplication_buffer_ t6 t0 t2;
  montgomery_square_buffer_ t0 t6;
  fsquarePowN (size 3) t0; 
  montgomery_multiplication_buffer_ t7 t0 t6;
  montgomery_square_buffer_ t0 t7;
  montgomery_square_buffer_ t0 t0;
  montgomery_multiplication_buffer_ t1 t0 t2;
  montgomery_square_buffer_ t0 t1;
    let h1 = ST.get() in 

    let tD = fromDomain_ (as_nat h0 t) in 
    
    calc (==) {(tD * tD % prime256 * tD % prime256) * (tD * tD % prime256 * tD % prime256) % prime256; 
      (==) {lemma_6_powers tD} pow tD 6 % prime256;};

    calc (==) {(pow tD 6 % prime256 * (pow tD 6 % prime256) % prime256) * (tD * tD % prime256 * tD % prime256) % prime256;
      (==) {lemma_15_powers tD} pow tD 15 % prime256;   };

    calc (==) {pow ((pow tD 15 % prime256 * (pow tD 15 % prime256) % prime256)) 8 % prime256;
      (==) {lemma_pow_sum tD 15 15} 
    pow ((pow tD 30 % prime256)) 8 % prime256;  
      (==) {power_distributivity (pow tD 30) 8 prime256}
    pow (pow tD 30) 8 % prime256;  
      (==) {power_mult tD 30 8}
    pow tD 240 % prime256;};

    calc (==) {pow tD 240 % prime256 * (pow tD 15 % prime256) % prime256 * (pow tD 240 % prime256 * (pow tD 15 % prime256) % prime256) % prime256;
      (==) {lemma_pow_sum tD 240 15}
    pow tD 255 % prime256 * (pow tD 255 % prime256) % prime256;
      (==) {lemma_pow_sum tD 255 255}
    pow tD 510 % prime256;};

    calc (==) {pow tD 510 % prime256 * (pow tD 510 % prime256) % prime256;
      (==) {lemma_pow_sum tD 510 510}
    pow tD 1020 % prime256;};

    calc (==) {tD * tD % prime256 * tD % prime256;
      (==) {lemma_mod_mul_distr_l (tD * tD) tD prime256}
    tD * tD * tD % prime256;
      (==) {pow_plus tD 1 1}
    pow tD 2 * tD % prime256;
      (==) {pow_plus tD 2 1}
    pow tD 3 % prime256;};

    calc (==) {pow tD 1020 % prime256 * (pow tD 3 % prime256) % prime256;
      (==) {lemma_pow_sum tD 1020 3}
    pow tD 1023 % prime256;};

    calc (==) {pow tD 1023 % prime256 * (pow tD 1023 % prime256) % prime256;
      (==) {lemma_pow_sum tD 1023 1023}
    pow tD 2046 % prime256;}

 (* assert(as_nat h5 t6 = toDomain_ (pow tD 15 % prime256)); *)
 (* assert(as_nat h8 t7 = toDomain_ (pow tD 240 % prime256 * (pow tD 15 % prime256) % prime256)); *)



inline_for_extraction noextract
val exponent_1: t: felem -> t0: felem -> t1: felem -> t2: felem -> t3: felem -> t4: felem -> t5: felem -> Stack unit 
  (requires fun h -> live h t /\ live h t0 /\ live h t1 /\ live h t2 /\ live h t3 /\ live h t4 /\ live h t5 /\
    LowStar.Monotonic.Buffer.all_disjoint [loc t; loc t0; loc t1; loc t2; loc t3; loc t4; loc t5] /\
    as_nat h t < prime256 /\ as_nat h t0 < prime256 /\ as_nat h t1 < prime256 /\ as_nat h t2 < prime256)
  (ensures fun h0 _ h1 -> modifies (loc t0 |+| loc t1 |+| loc t2 |+| loc t3 |+| loc t4 |+| loc t5) h0 h1 /\ (
    let t0D = fromDomain_ (as_nat h0 t0) in 
    let t1D = fromDomain_ (as_nat h0 t1) in 
    let t2D = fromDomain_ (as_nat h0 t2) in 
    let tD = fromDomain_ (as_nat h0 t) in 
    as_nat h1 t0 == toDomain_ (pow t0D (pow2 181 + pow2 21) * pow t1D (pow2 172 + pow2 162 + pow2 12 + 4) * pow t2D (pow2 160 + 1) * pow tD (pow2 128) % prime256) /\
    as_nat h1 t4 == toDomain_ (pow t0D (pow2 19) * pow t1D (pow2 10 + 1) % prime256) /\
    as_nat h1 t5 == toDomain_ (pow t0D (pow2 21) * pow t1D (pow2 12 + 4) * pow t2D 1 % prime256)) /\
    as_nat h1 t0 < prime256 /\ as_nat h1 t4 < prime256 /\ as_nat h1 t5 < prime256
  )

let exponent_1 t t0 t1 t2 t3 t4 t5 = 
    let h0 = ST.get() in 
  fsquarePowN (size 9) t0;
  montgomery_multiplication_buffer_ t3 t0 t1;
  montgomery_square_buffer_ t0 t3;
  fsquarePowN (size 9) t0;
  montgomery_multiplication_buffer_ t4 t0 t1;
  montgomery_square_buffer_ t0 t4;
  montgomery_square_buffer_ t0 t0;
  montgomery_multiplication_buffer_ t5 t0 t2;
  montgomery_square_buffer_ t0 t5;
  fsquarePowN (size 31) t0;
  montgomery_multiplication_buffer_ t0 t0 t;
  fsquarePowN (size 128) t0;
  montgomery_multiplication_buffer_ t0 t0 t5;

  let tD = fromDomain_ (as_nat h0 t) in let t0D = fromDomain_ (as_nat h0 t0) in 
  let t1D = fromDomain_ (as_nat h0 t1) in let t2D = fromDomain_ (as_nat h0 t2) in 

  (* h3 *)
  calc (==) {pow t0D (pow2 9) % prime256 * pow t1D 1 % prime256 * (pow t0D (pow2 9) % prime256 * pow t1D 1 % prime256) % prime256;
    (==) {lemma_pow_sum2 t0D t1D (pow2 9) (pow2 9) 1 1}
  pow t0D (2 * pow2 9) * pow t1D 2 % prime256; 
    (==) {pow2_double_mult 9}
  pow t0D (pow2 10) * pow t1D 2 % prime256;};

  (* let pow2_19 = pow2 19 in let pow2_20 = pow2 20 in 
  let pow2_21 = pow2 21 in let pow2_76 = pow2 76 in let pow2_88 = pow2 88 in let pow2_152 = pow2 152 in  *)

  (*h4 *)
  lemma_exp_1_0 t0D t1D; 

  (* h5 *)
  lemma_exp_1_1 t0D t1D;
  
  (* h6 *)
  lemma_exp_1_2 t0D t1D;
  (* h7 *)
  lemma_exp_1_3 t0D t1D;
  (* h8 *)
  lemma_exp_1_4 t0D t1D t2D;
  
  (* h9 *)
  lemma_exp_1_5 t0D t1D t2D;

  (* h10 *) 
  lemma_exp_1_6 t0D t1D t2D;

  (* h11 *)
  lemma_mod_mul_distr_l (pow t0D (pow2 53) * pow t1D (pow2 44 + pow2 34) * pow t2D (pow2 32)) tD prime256;
  (* h12*) 
  lemma_exp_1_7 tD t0D t1D t2D;

  (* h13  *)
  lemma_exp_1_8 tD t0D t1D t2D (*;
  
  assert(as_nat h1 t0 =  toDomain_ (pow t0D (pow2 9) % prime256)); 
  assert(as_nat h2 t3 =  toDomain_ (pow t0D (pow2 9) % prime256 * pow t1D 1 % prime256)); 
  assert(as_nat h3 t0 =  toDomain_ (pow t0D (pow2 10) * pow t1D 2 % prime256));  
  assert(as_nat h4 t0 =  toDomain_ (pow t0D (pow2_19) * pow t1D (pow2 10) % prime256)); 
  assert(as_nat h5 t4 =  toDomain_ (pow t0D (pow2_19) * pow t1D (pow2 10 + 1) % prime256)); 
  assert(as_nat h6 t0 =  toDomain_ (pow t0D (pow2_20) * pow t1D (pow2 11 + 2) % prime256)); 
  assert(as_nat h7 t0 =  toDomain_ (pow t0D (pow2 21) * pow t1D (pow2 12 + 4) % prime256));  
  assert(as_nat h8 t5 =  toDomain_ (pow t0D (pow2 21) * pow t1D (pow2 12 + 4) * pow t2D 1 % prime256));
  assert(as_nat h9 t0 =  toDomain_ (pow t0D (pow2 22) * pow t1D (pow2 13 + 8) * pow t2D 2 % prime256)); 
  assert(as_nat h10 t0 = toDomain_ (pow t0D (pow2 53) * pow t1D (pow2 44 + pow2 34) * pow t2D (pow2 32) % prime256));
  assert(as_nat h11 t0 = toDomain_ (pow t0D (pow2 53) * pow t1D (pow2 44 + pow2 34) * pow t2D (pow2 32) * tD % prime256));
  
  assert(as_nat h12 t0 = toDomain_ (pow t0D (pow2 181) * pow t1D (pow2 172 + pow2 162) * pow t2D (pow2 160) * pow tD (pow2 128) % prime256));

  assert(as_nat h13 t0 = toDomain_ (pow t0D (pow2 181 + pow2 21) * pow t1D (pow2 172 + pow2 162 + pow2 12 + 4) * pow t2D (pow2 160 + 1) * pow tD (pow2 128) % prime256)) *)
  



inline_for_extraction noextract
val exponent_2: t: felem -> t0: felem -> t4: felem -> t5: felem -> result: felem ->
  Stack unit 
  (requires fun h -> live h t /\ live h t0 /\ live h t4 /\ live h t5 /\ live h result /\
    as_nat h t < prime256 /\ as_nat h t0 < prime256 /\ as_nat h t4 < prime256 /\ as_nat h t5 < prime256 /\
    LowStar.Monotonic.Buffer.all_disjoint [loc t; loc t0;  loc t4; loc t5])
  (ensures fun h0 _ h1 -> modifies (loc t0 |+| loc t4 |+| loc t5 |+| loc result) h0 h1 /\ (
    let t0D = fromDomain_ (as_nat h0 t0) in 
    let t5D = fromDomain_ (as_nat h0 t5) in 
    let t4D = fromDomain_ (as_nat h0 t4) in 
    let tD = fromDomain_ (as_nat h0 t) in 
    as_nat h1 result = toDomain_ (pow t0D (pow2 64) * pow t5D (pow2 32) * pow t4D (pow2 2) * tD % prime256)) /\ 
    as_nat h1 result < prime256
  )

let exponent_2 t t0 t4 t5 result = 
    let h0 = ST.get() in 
  fsquarePowN (size 32) t0;
  montgomery_multiplication_buffer_ t0 t0 t5; 
  fsquarePowN (size 30) t0;
  montgomery_multiplication_buffer_ t0 t0 t4;
  fsquarePowN (size 2) t0;
  montgomery_multiplication_buffer_ result t0 t; 

  let tD =  fromDomain_ (as_nat h0 t) in 
  let t0D = fromDomain_ (as_nat h0 t0) in 
  let t5D = fromDomain_ (as_nat h0 t5) in 
  let t4D = fromDomain_ (as_nat h0 t4) in 

  let pow2_30 = pow2 30 in 
  let pow2_32 = pow2 32 in 
  let pow2_62 = pow2 62 in 
  let pow2_64 = pow2 64 in 
  
  calc (==) {pow t0D pow2_32 % prime256 * t5D % prime256;
    (==) {lemma_mod_mul_distr_l (pow t0D pow2_32) t5D prime256}
  pow t0D pow2_32 * t5D % prime256;};

  lemma_exp_2_0 t0D t5D;

  calc (==) {pow t0D pow2_62 * pow t5D pow2_30 % prime256 * t4D % prime256;
    (==) {lemma_mod_mul_distr_l (pow t0D pow2_62 * pow t5D pow2_30) t4D prime256}
  pow t0D pow2_62 * pow t5D pow2_30 * t4D % prime256;};

  lemma_exp_2_1 t0D t4D t5D;

  calc (==) {pow t0D pow2_64 * pow t5D pow2_32 * pow t4D (pow2 2) % prime256 * tD % prime256;
    (==) {lemma_mod_mul_distr_l (pow t0D pow2_64 * pow t5D pow2_32 * pow t4D (pow2 2)) tD prime256}
  pow t0D pow2_64 * pow t5D pow2_32 * pow t4D (pow2 2) * tD % prime256;}


[@ CInline]
val exponent: a: felem ->result: felem -> tempBuffer: lbuffer uint64 (size 32) -> Stack unit
  (requires fun h -> live h a /\ live h tempBuffer /\ live h result /\ disjoint tempBuffer result /\ 
    disjoint a tempBuffer /\ as_nat h a < prime256)
  (ensures fun h0 _ h1 -> modifies2 result tempBuffer h0 h1 /\ (
    let k = fromDomain_ (as_nat h0 a) in 
    as_nat h1 result =  toDomain_ (pow k (prime256 - 2) % prime256)))


let exponent t result tempBuffer = 
  let h0 = ST.get () in 

  let t0 = sub tempBuffer (size 0) (size 4) in 
  let t1 = sub tempBuffer (size 4) (size 4) in 
  let t2 = sub tempBuffer (size 8) (size 4) in 
  let t3 = sub tempBuffer (size 12) (size 4) in 
  let t4 = sub tempBuffer (size 16) (size 4) in 
  let t5 = sub tempBuffer (size 20) (size 4) in 
  let t6 = sub tempBuffer (size 24) (size 4) in 
  let t7 = sub tempBuffer (size 28) (size 4) in 

  exponent_0 t t0 t1 t2 t6 t7;
    let h1 = ST.get() in 
  exponent_1 t t0 t1 t2 t3 t4 t5; 
    let h2 = ST.get() in 
  exponent_2 t t0 t4 t5 result;
    let h3 = ST.get() in 

  let tD = fromDomain_ (as_nat h0 t) in 
(*
  assert( 
    as_nat h1 t2 = toDomain_ (pow tD 3 % prime256) /\ 
    as_nat h1 t1 = toDomain_ (pow tD 1023 % prime256) /\ 
    as_nat h1 t0 = toDomain_ (pow tD 2046 % prime256));
*)

  lemma_exp_1 tD; 
  lemma_exp_2 tD;
  lemma_exp_3 tD;
  lemma_exp_4 tD

(*
  assert(
    as_nat h2 t0 == toDomain_ (pow tD (3 * (pow2 160 + 1) + 2046 * (pow2 181 + pow2 21) + 1023 * (pow2 172 + pow2 162 + pow2 12 + 4) + pow2 128) % prime256) /\
    as_nat h2 t4 == toDomain_ (pow tD (1023 * (pow2 10 + 1) + 2046 * pow2 19) % prime256) /\
    as_nat h2 t5 == toDomain_ (pow tD (3 + 2046 * pow2 21 + 1023 * (pow2 12 + 4)) % prime256));

  assert(
    let t0D = pow tD (3 * (pow2 160 + 1) + 2046 * (pow2 181 + pow2 21) + 1023 * (pow2 172 + pow2 162 + pow2 12 + 4) + pow2 128) % prime256 in 
    let t5D = pow tD (3 + 2046 * pow2 21 + 1023 * (pow2 12 + 4)) % prime256 in 
    let t4D = pow tD (1023 * (pow2 10 + 1) + 2046 * pow2 19) % prime256  in 
    as_nat h3 result = toDomain_ (
      pow (pow tD (3 * (pow2 160 + 1) + 2046 * (pow2 181 + pow2 21) + 1023 * (pow2 172 + pow2 162 + pow2 12 + 4) + pow2 128) % prime256) (pow2 64) * 
      pow (pow tD (3 + 2046 * pow2 21 + 1023 * (pow2 12 + 4)) % prime256) (pow2 32) * 
      pow (pow tD (1023 * (pow2 10 + 1) + 2046 * pow2 19) % prime256) (pow2 2) * tD % prime256));
   


  admit()

 
 *)
