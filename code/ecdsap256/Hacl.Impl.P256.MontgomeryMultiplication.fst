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

#set-options "--z3rlimit 100"

inline_for_extraction noextract
val add8_without_carry1: t: widefelem -> t1: widefelem -> result: widefelem  -> Stack unit
  (requires fun h -> 
    live h t /\ live h t1 /\ live h result /\ eq_or_disjoint t1 result /\ 
    eq_or_disjoint t result /\ wide_as_nat h t1 < pow2 320 /\ wide_as_nat h t < prime256 * prime256
  )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ wide_as_nat h1 result = wide_as_nat h0 t + wide_as_nat h0 t1)

let add8_without_carry1 t t1 result  = 
  add8_void t t1 result;
    assert_norm (pow2 320 + prime256 * prime256 < pow2 512)

(* inline_for_extraction
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
  pop_frame()   *)

inline_for_extraction
val montgomery_multiplication_round: t: widefelem -> round: widefelem 
  -> t2: lbuffer uint64 (size 8) 
  -> t3: lbuffer uint64 (size 8) ->


  Stack unit 
  

  (requires fun h -> live h t /\ live h round /\ wide_as_nat h t < prime256 * prime256)
  (ensures fun h0 _ h1 -> modifies (loc round)  h0 h1 /\
    wide_as_nat h1 round = (wide_as_nat h0 t + prime256 * (wide_as_nat h0 t % pow2 64)) / pow2 64
  )

let montgomery_multiplication_round t round t2 t3 =
  push_frame(); 
    let h0 = ST.get() in 
(*     let t2 = create (size 8) (u64 0) in 
    let t3 = create (size 8) (u64 0) in  *)
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


(* inline_for_extraction noextract
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

let montgomery_multiplication_round_twice t result tempRound  = 
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
  pop_frame() *)



inline_for_extraction noextract
val montgomery_multiplication_round_twice: t: widefelem -> result: widefelem ->
  tempRound: widefelem -> t2: widefelem -> t3: widefelem 


-> Stack unit 
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

let montgomery_multiplication_round_twice t result tempRound t2 t3  = 
  assert_norm(prime256 > 3);
  push_frame();
    (* let tempRound = create (size 8) (u64 0) in  *)
      let h0 = ST.get() in 
    montgomery_multiplication_round t tempRound t2 t3; 
      let h1 = ST.get() in 
      montgomery_multiplication_one_round_proof (wide_as_nat h0 t)  (wide_as_nat h1 tempRound) (wide_as_nat h0 t);
    montgomery_multiplication_round tempRound result t2 t3;
      let h2 = ST.get() in 
      montgomery_multiplication_one_round_proof (wide_as_nat h1 tempRound) (wide_as_nat h2 result) (wide_as_nat h0 t * modp_inv2_prime (pow2 64) prime256);
      lemma_montgomery_mod_inverse_addition (wide_as_nat h0 t);
  pop_frame()





inline_for_extraction noextract
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

    let t1 = create (size 8) (u64 0) in 
    let t2 = create (size 8) (u64 0) in 
    let t3 = create (size 8) (u64 0) in 

      let h0 = ST.get() in 
    copy t_low a; 
      let h1 = ST.get() in 
      assert(wide_as_nat h0 t = as_nat h0 t_low + as_nat h0 t_high * pow2 256);
      assert_norm (prime256 < prime256 * prime256);
    montgomery_multiplication_round_twice t round2 t1 t2 t3;
      let h2 = ST.get() in 
    montgomery_multiplication_round_twice round2 round4 t1 t2 t3; 
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


 [@ CInline]
val montgomery_multiplication_buffer: a: felem -> b: felem -> result: felem ->  Stack unit
  (requires (fun h -> live h a /\ 
    as_nat h a < prime256 /\ 
    live h b /\ 
  live h result /\ 
  as_nat h b < prime256)) 
  (ensures (fun h0 _ h1 -> 
    modifies (loc result) h0 h1 /\  
    as_nat h1 result < prime256 /\
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

    let t1 = create (size 8) (u64 0) in 
    let t2 = create (size 8) (u64 0) in 
    let t3 = create (size 8) (u64 0) in 



  montgomery_multiplication_round_twice t round2 t1 t2 t3;
      let h2 = ST.get() in 
  montgomery_multiplication_round_twice round2 round4 t1 t2 t3; 


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


 [@ CInline]
val montgomery_square_buffer: a: felem -> result: felem ->  Stack unit
  (requires (fun h -> live h a /\ as_nat h a < prime256 /\ live h result)) 
  (ensures (fun h0 _ h1 -> 
    modifies (loc result) h0 h1 /\  
    as_nat h1 result < prime256 /\ 
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

    let t1 = create (size 8) (u64 0) in 
    let t2 = create (size 8) (u64 0) in 
    let t3 = create (size 8) (u64 0) in 



  montgomery_multiplication_round_twice t round2 t1 t2 t3;
      let h2 = ST.get() in 
  montgomery_multiplication_round_twice round2 round4 t1 t2 t3; 
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


 [@ CInline]
val exponent: a: felem ->result: felem -> tempBuffer: lbuffer uint64 (size 20) ->  Stack unit
  (requires fun h -> live h a /\ live h tempBuffer /\ live h result /\ disjoint tempBuffer result /\ 
  disjoint a tempBuffer /\ as_nat h a < prime256)
  (ensures fun h0 _ h1 -> modifies2 result tempBuffer h0 h1 /\ (let k = fromDomain_ (as_nat h0 a) in 
    as_nat h1 result =  toDomain_ ((pow k (prime256-2)) % prime256)))


(* just changing argument order *)
inline_for_extraction noextract
val montgomery_multiplication_buffer_: result: felem -> a: felem -> b: felem ->  Stack unit
  (requires (fun h -> live h a /\  as_nat h a < prime256 /\ live h b /\ live h result /\ as_nat h b < prime256)) 
  (ensures (fun h0 _ h1 -> 
    modifies (loc result) h0 h1 /\  
    as_nat h1 result < prime256 /\
    as_nat h1 result = (as_nat h0 a * as_nat h0 b * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % prime256) /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b)))
  )

let montgomery_multiplication_buffer_ result a b = 
  Hacl.Impl.P256.MontgomeryMultiplication.montgomery_multiplication_buffer a b result

inline_for_extraction noextract
val montgomery_square_buffer_: result: felem -> a: felem ->   Stack unit
  (requires (fun h -> live h a /\ as_nat h a < prime256 /\ live h result)) 
  (ensures (fun h0 _ h1 -> 
    modifies (loc result) h0 h1 /\  
    as_nat h1 result < prime256 /\ 
    as_nat h1 result = (as_nat h0 a * as_nat h0 a * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) % prime256) /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a)))
  )


let montgomery_square_buffer_ result a = 
  montgomery_square_buffer a result



#reset-options " --z3rlimit 200"
let exponent t result tempBuffer = 
  let h0 = ST.get () in 
  
  let inv (h0: HyperStack.mem) (h1: HyperStack.mem) (i: nat) : Type0 = True in 

  let r0 = sub tempBuffer (size 0) (size 4) in 
  let t1 = sub tempBuffer (size 4) (size 4) in 
  let t2 = sub tempBuffer (size 8) (size 4) in 
  let t3 = sub tempBuffer (size 12) (size 4) in 
  let t4 = sub tempBuffer (size 16) (size 4) in 
  let t5 = sub tempBuffer (size 20) (size 4) in 
  let t6 = sub tempBuffer (size 24) (size 4) in 
  let t7 = sub tempBuffer (size 28) (size 4) in 

  montgomery_square_buffer_ r0 t;
  montgomery_multiplication_buffer_ t2 r0 t;
  montgomery_square_buffer_ r0 t2;
  montgomery_square_buffer_ r0 r0;
  montgomery_multiplication_buffer_ t6 r0 t2;
  montgomery_square_buffer_ r0 t6;

  for (size 0) 3ul (inv h0) (fun x -> montgomery_square_buffer_ r0 r0);

  montgomery_multiplication_buffer_ t7 r0 t6;
  montgomery_square_buffer_ r0 t7;
  montgomery_square_buffer_ r0 r0;
  montgomery_multiplication_buffer_ t1 r0 t2;
  montgomery_square_buffer_ r0 t1;

  for (size 0) 9ul (inv h0) (fun x -> montgomery_square_buffer_ r0 r0);

  montgomery_multiplication_buffer_ t3 r0 t1;
  montgomery_square_buffer_ r0 t3;

  for (size 0) 9ul (inv h0) (fun x -> montgomery_square_buffer_ r0 r0);
  
  montgomery_multiplication_buffer_ t4 r0 t1;
  montgomery_square_buffer_ r0 t4;
  montgomery_square_buffer_ r0 r0;
  montgomery_multiplication_buffer_ t5 r0 t2;
  montgomery_square_buffer_ r0 t5;

  for (size 0) 31ul (inv h0) (fun x -> montgomery_square_buffer_ r0 r0);

  montgomery_multiplication_buffer_ r0 r0 t;

  for (size 0) 128ul (inv h0) (fun x -> montgomery_square_buffer_ r0 r0);

  montgomery_multiplication_buffer_ r0 r0 t5;

  for (size 0) 32ul (inv h0) (fun x -> montgomery_square_buffer_ r0 r0);

  montgomery_multiplication_buffer_ r0 r0 t5;

  for (size 0) 30ul (inv h0) (fun x -> montgomery_square_buffer_ r0 r0);

  montgomery_multiplication_buffer_ r0 r0 t4;

  for (size 0) 2ul (inv h0) (fun x -> montgomery_square_buffer_ r0 r0);

  montgomery_multiplication_buffer_ result r0 t
 
