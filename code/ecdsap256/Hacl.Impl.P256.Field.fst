module Hacl.Impl.P256.Field

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Math.Lemmas

open Lib.IntTypes
open Lib.Buffer
open Lib.IntTypes.Intrinsics

open Spec.P256
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.MontgomeryMultiplication

open Hacl.Spec.P256.Felem
open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Math
open Hacl.Impl.P256.Constants

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val reduction_prime256_2prime256_with_carry_impl:
    cin:uint64
  -> x:felem
  -> result:felem ->
  Stack unit
  (requires fun h ->
    live h x /\ live h result /\ eq_or_disjoint x result /\
    (as_nat h x + uint_v cin * pow2 256) < 2 * prime256)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat h1 result = (as_nat h0 x + uint_v cin * pow2 256) % prime256)

let reduction_prime256_2prime256_with_carry_impl cin x result =
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in
    let tempBufferForSubborrow = create (size 1) (u64 0) in
    recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list);
    let c = bn_sub4_il x prime256_buffer tempBuffer in
  let h0 = ST.get() in
      assert(uint_v c <= 1);
      assert(if uint_v c = 0 then as_nat h0 x >= prime256 else as_nat h0 x < prime256);
    let carry = sub_borrow_u64 c cin (u64 0) tempBufferForSubborrow in
    bn_cmovznz4 carry tempBuffer x result;
  let h1 = ST.get() in
      assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
      assert_norm (prime256 < pow2 256);
      assert_norm(pow2 256 < 2 * prime256);

      assert(uint_v cin <= 1);
      assert(uint_v c <= 1);

      assert(if as_nat h0 x >= prime256 then uint_v c = 0 else True);
      assert(if uint_v cin < uint_v c then as_nat h1 result == as_nat h0 x else as_nat h1 result == as_nat h0 tempBuffer);

      assert(as_nat h1 result < prime256);

      modulo_addition_lemma (as_nat h1 result) prime256 1;
      small_modulo_lemma_1 (as_nat h1 result) prime256;
  pop_frame()


inline_for_extraction noextract
val reduction_prime256_2prime256_8_with_carry_impl: x:widefelem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res /\
    wide_as_nat h x < 2 * prime256)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == wide_as_nat h0 x % prime256)

let reduction_prime256_2prime256_8_with_carry_impl x result =
  push_frame();
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    assert_norm (prime256 < pow2 256);
    assert_norm(pow2 256 < 2 * prime256);
    let h0 = ST.get() in
    let tempBuffer = create (size 4) (u64 0) in
    let tempBufferForSubborrow = create (size 1) (u64 0) in
    let cin = Lib.Buffer.index x (size 4) in
    let x_ = Lib.Buffer.sub x (size 0) (size 4) in
      recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list);
    let c = bn_sub4_il x_ prime256_buffer tempBuffer in
    let carry = sub_borrow_u64 c cin (u64 0) tempBufferForSubborrow in
    bn_cmovznz4 carry tempBuffer x_ result;
      let h4 = ST.get() in
      assert_norm (pow2 256 > prime256);
      assert(if (wide_as_nat h0 x < prime256) then begin
      small_modulo_lemma_1 (wide_as_nat h0 x) prime256;
      as_nat h4 result = (wide_as_nat h0 x) % prime256 end
      else
	begin
	small_modulo_lemma_1 (as_nat h4 result) prime256;
	lemma_mod_sub (wide_as_nat h0 x) prime256 1;
	as_nat h4 result = (wide_as_nat h0 x) % prime256
	end );
 pop_frame()


val lemma_reduction1_0: a:nat{a < pow2 256 /\ a >= prime256} -> r:nat{r = a - prime256} ->
  Lemma (r = a % prime256)

let lemma_reduction1_0 a r =
  assert_norm (pow2 256 - prime256 < prime256);
  small_modulo_lemma_1 r prime256;
  lemma_mod_sub_distr a prime256 prime256


val lemma_reduction1: a:nat{a < pow2 256} -> r:nat{if a >= prime256 then r = a - prime256 else r = a} ->
  Lemma (r = a % prime256)

let lemma_reduction1 a r =
  if a >= prime256 then
   lemma_reduction1_0 a r
  else
    small_mod r prime256


[@CInline]
let fmod_short x result =
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  push_frame();
  let tempBuffer = create (size 4) (u64 0) in
  recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list);
  let h0 = ST.get() in
  let c = bn_sub4_il x prime256_buffer tempBuffer in
  bn_cmovznz4 c tempBuffer x result;
  let h2 = ST.get() in
  lemma_reduction1 (as_nat h0 x) (as_nat h2 result);
  pop_frame()


val lemma_t_computation: t: uint64{uint_v t == 0 \/ uint_v t == 1} ->
  Lemma
    (
        let t0 = u64 0 in
	let t1 = (u64 0) -. (t <<. (size 32)) in
	let t2 = (u64 0) -. t in
	let t3 = (t <<. (size 32)) -. (t <<. (size 1)) in
	let s = uint_v t0 + uint_v t1 * pow2 64 + uint_v t2 * pow2 128 + uint_v t3 * pow2 192 in
	if uint_v t = 1 then s == pow2 256 - prime256 - 1 else s == 0
    )

let lemma_t_computation t =
  let t0 = u64 0 in
  let t1 = (u64 0) -. (t <<. (size 32)) in
  let t2 = (u64 0) -. t in
  let t3 = (t <<. (size 32)) -. (t <<. (size 1)) in
  let s = uint_v t0 + uint_v t1 * pow2 64 + uint_v t2 * pow2 128 + uint_v t3 * pow2 192 in
  assert_norm(18446744069414584320 * pow2 64 + 18446744073709551615 * pow2 128 + 4294967294 * pow2 192 = pow2 256 - prime256 - 1)


val lemma_t_computation2: t: uint64 {uint_v t == 0 \/ uint_v t == 1} ->
  Lemma
    (
      let t0 = (u64 0) -. t in
      let t1 = ((u64 0) -. t) >>. (size 32) in
      let t2 = u64 0 in
      let t3 = t -. (t <<. (size 32)) in
      let s = uint_v t0 + uint_v t1 * pow2 64 + uint_v t2 * pow2 128 + uint_v t3 * pow2 192 in
      if uint_v t = 1 then s == prime256 else s == 0
    )

let lemma_t_computation2 t =
  let t0 = (u64 0) -. t in
  let t1 = ((u64 0) -. t) >>. (size 32) in
  let t2 = u64 0 in
  let t3 = t -. (t <<. (size 32)) in
  let s = uint_v t0 + uint_v t1 * pow2 64 + uint_v t2 * pow2 128 + uint_v t3 * pow2 192 in
  assert_norm(18446744073709551615 + 4294967295 * pow2 64 + 18446744069414584321 * pow2 192 = prime256)


[@CInline]
let fadd x y out =
  let h0 = ST.get() in
  let t = bn_add4 x y out in
  lemma_t_computation t;
  reduction_prime256_2prime256_with_carry_impl t out out;
  let h2 = ST.get() in
  additionInDomain (as_nat h0 x) (as_nat h0 y);
  inDomain_mod_is_not_mod (fromDomain_ (as_nat h0 x) + fromDomain_ (as_nat h0 y))


let fdouble x out =
  fadd x x out


[@CInline]
let fsub x y out =
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    let h0 = ST.get() in
  let t = bn_sub4 x y out in
    let h1 = ST.get() in
    lemma_t_computation2 t;
  let t0 = (u64 0) -. t in
  let t1 = ((u64 0) -. t) >>. (size 32) in
  let t2 = u64 0 in
  let t3 = t -. (t <<. (size 32)) in
    modulo_addition_lemma  (as_nat h0 x - as_nat h0 y) prime256 1;
  let c = bn_add4_variables out (u64 0)  t0 t1 t2 t3 out in
    let h2 = ST.get() in
      assert(
      if as_nat h0 x - as_nat h0 y >= 0 then
	begin
	  modulo_lemma (as_nat h0 x - as_nat h0 y) prime256;
	  as_nat h2 out == (as_nat h0 x - as_nat h0 y) % prime256
	end
      else
          begin
	    modulo_lemma (as_nat h2 out) prime256;
            as_nat h2 out == (as_nat h0 x - as_nat h0 y) % prime256
	  end);
    substractionInDomain (felem_seq_as_nat (as_seq h0 x)) (felem_seq_as_nat (as_seq h0 y));
    inDomain_mod_is_not_mod (fromDomain_ (felem_seq_as_nat (as_seq h0 x)) - fromDomain_ (felem_seq_as_nat (as_seq h0 y)))

//--------------------------------------

inline_for_extraction noextract
val add8_without_carry1: t:widefelem -> t1:widefelem -> result:widefelem -> Stack unit
  (requires fun h ->
    live h t /\ live h t1 /\ live h result /\
    eq_or_disjoint t1 t /\ eq_or_disjoint t1 result /\ eq_or_disjoint t result /\
    wide_as_nat h t1 < pow2 320 /\ wide_as_nat h t < prime256 * prime256)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    wide_as_nat h1 result = wide_as_nat h0 t + wide_as_nat h0 t1)

let add8_without_carry1 t t1 result  =
  let _  = bn_add8 t t1 result in
    assert_norm (pow2 320 + prime256 * prime256 < pow2 512)


inline_for_extraction noextract
val montgomery_multiplication_round: t:widefelem -> round:widefelem -> Stack unit
  (requires fun h ->
    live h t /\ live h round /\
    wide_as_nat h t < prime256 * prime256)
  (ensures fun h0 _ h1 -> modifies (loc round) h0 h1 /\
    wide_as_nat h1 round = (wide_as_nat h0 t + prime256 * (wide_as_nat h0 t % pow2 64)) / pow2 64)

let montgomery_multiplication_round t round =
  push_frame();
    let h0 = ST.get() in
    let t2 = create (size 8) (u64 0) in
    let t3 = create (size 8) (u64 0) in
    let t1 = bn_mod_pow2_64 t in
      recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list);
    bn_mul1 prime256_buffer t1 t2;
    add8_without_carry1 t t2 t3;
    bn_rshift64 t3 round;
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


inline_for_extraction noextract
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
      Math.Lemmas.swap_mul (wide_as_nat h0 t % pow2 64) prime256;
      montgomery_multiplication_one_round_proof (wide_as_nat h0 t) (wide_as_nat h1 tempRound) (wide_as_nat h0 t);
    montgomery_multiplication_round tempRound result;
      let h2 = ST.get() in
      Math.Lemmas.swap_mul (wide_as_nat h1 tempRound % pow2 64) prime256;
      montgomery_multiplication_one_round_proof (wide_as_nat h1 tempRound) (wide_as_nat h2 result) (wide_as_nat h0 t * modp_inv2_prime (pow2 64) prime256);
      lemma_montgomery_mod_inverse_addition (wide_as_nat h0 t);
  pop_frame()


[@CInline]
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


[@CInline]
let fmul a b result =
  assert_norm(prime256 > 3);
  push_frame();
    let t = create (size 8) (u64 0) in
    let round2 = create (size 8) (u64 0) in
    let round4 = create (size 8) (u64 0) in
      let h0 = ST.get() in
    bn_mul4 a b t;
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


[@CInline]
let fsqr a result =
  assert_norm(prime256 > 3);
  push_frame();
    let t = create (size 8) (u64 0) in
    let round2 = create (size 8) (u64 0) in
    let round4 = create (size 8) (u64 0) in
      let h0 = ST.get() in
    bn_sqr4 a t;
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

//----------------------------------------------

[@CInline]
let fcube a result =
  let h0 = ST.get () in
  fsqr a result;
  fmul result a result;
  let h1 = ST.get () in
  lemma_mod_mul_distr_l
    (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a))
    (fromDomain_ (as_nat h0 a)) prime256;
  inDomain_mod_is_not_mod
    (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a))


let fmul_by_2 a out =
  let h0 = ST.get () in
  fadd a a out;
  inDomain_mod_is_not_mod (2 * fromDomain_ (as_nat h0 a))


[@CInline]
let fmul_by_3 a result =
  let h0 = ST.get () in
  fmul_by_2 a result;
  let h1 = ST.get () in
  assert (as_nat h1 result == toDomain_ (2 * fromDomain_ (as_nat h0 a) % prime256));
  fadd a result result;
  let h2 = ST.get() in
  lemma_mod_add_distr (fromDomain_ (as_nat h0 a)) (2 * fromDomain_ (as_nat h0 a)) prime256;
  inDomain_mod_is_not_mod (3 * fromDomain_ (as_nat h0 a))


[@CInline]
let fmul_by_4 a result  =
  let h0 = ST.get() in
  fmul_by_2 a result;
  fmul_by_2 result result;
  lemma_mod_mul_distr_r 2 (2 * fromDomain_ (as_nat h0 a)) prime256;
  lemma_brackets 2 2 (fromDomain_ (as_nat h0 a));
  inDomain_mod_is_not_mod (4 * fromDomain_ (as_nat h0 a))


[@CInline]
let fmul_by_8 a result  =
  let h0 = ST.get() in
  fmul_by_4 a result;
  fmul_by_2 result result;
  lemma_mod_mul_distr_r 2 (4 * fromDomain_ (as_nat h0 a)) prime256;
  lemma_brackets 2 4 (fromDomain_ (as_nat h0 a));
  inDomain_mod_is_not_mod (8 * fromDomain_ (as_nat h0 a))
