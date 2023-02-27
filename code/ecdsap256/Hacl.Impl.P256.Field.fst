module Hacl.Impl.P256.Field

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.IntTypes.Intrinsics

open Hacl.Spec.P256.Math
open Hacl.Spec.P256.Felem
open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Constants

module S = Spec.P256
module SM = Hacl.Spec.P256.MontgomeryMultiplication
module SL = Hacl.Spec.P256.Lemmas

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val fmod_short_lemma: a:nat{a < pow2 256} ->
  Lemma (let r = if a >= S.prime then a - S.prime else a in r = a % S.prime)

let fmod_short_lemma a =
  let r = if a >= S.prime then a - S.prime else a in
  if a >= S.prime then begin
    Math.Lemmas.lemma_mod_sub a S.prime 1;
    assert_norm (pow2 256 - S.prime < S.prime);
    Math.Lemmas.small_mod r S.prime end
  else
   Math.Lemmas.small_mod r S.prime


[@CInline]
let fmod_short x res =
  push_frame ();
  let tmp = create (size 4) (u64 0) in
  recall_contents prime_buffer (Lib.Sequence.of_list p256_prime_list);
  let h0 = ST.get () in
  let c = bn_sub4_il x prime_buffer tmp in
  bn_cmovznz4 c tmp x res;
  as_nat_bound h0 x;
  fmod_short_lemma (as_nat h0 x);
  pop_frame ()


[@CInline]
let fadd x y res =
  let h0 = ST.get () in
  push_frame ();
  let n = create 4ul (u64 0) in
  make_prime n;
  bn_add_mod4 x y n res;
  let h1 = ST.get () in
  assert (as_nat h1 res == (as_nat h0 x + as_nat h0 y) % S.prime);
  pop_frame ();
  SM.additionInDomain (as_nat h0 x) (as_nat h0 y);
  SM.inDomain_mod_is_not_mod (SM.fromDomain_ (as_nat h0 x) + SM.fromDomain_ (as_nat h0 y))


let fdouble x out =
  fadd x x out


[@CInline]
let fsub x y res =
  let h0 = ST.get () in
  push_frame ();
  let n = create 4ul (u64 0) in
  make_prime n;
  bn_sub_mod4 x y n res;
  let h1 = ST.get () in
  assert (as_nat h1 res == (as_nat h0 x - as_nat h0 y) % S.prime);
  pop_frame ();
  SM.substractionInDomain (as_nat h0 x) (as_nat h0 y);
  SM.inDomain_mod_is_not_mod (SM.fromDomain_ (as_nat h0 x) - SM.fromDomain_ (as_nat h0 y))

//---------------------

inline_for_extraction noextract
val reduction_prime_2prime_8_with_carry_impl: x:widefelem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res /\
    wide_as_nat h x < 2 * S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == wide_as_nat h0 x % S.prime)

let reduction_prime_2prime_8_with_carry_impl x result =
  push_frame();
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    assert_norm (S.prime < pow2 256);
    assert_norm(pow2 256 < 2 * S.prime);
    let h0 = ST.get() in
    let tempBuffer = create (size 4) (u64 0) in
    let tempBufferForSubborrow = create (size 1) (u64 0) in
    let cin = Lib.Buffer.index x (size 4) in
    let x_ = Lib.Buffer.sub x (size 0) (size 4) in
      recall_contents prime_buffer (Lib.Sequence.of_list p256_prime_list);
    let c = bn_sub4_il x_ prime_buffer tempBuffer in
    let carry = sub_borrow_u64 c cin (u64 0) tempBufferForSubborrow in
    bn_cmovznz4 carry tempBuffer x_ result;
      let h4 = ST.get() in
      assert_norm (pow2 256 > S.prime);
      assert(if (wide_as_nat h0 x < S.prime) then begin
      Math.Lemmas.small_modulo_lemma_1 (wide_as_nat h0 x) S.prime;
      as_nat h4 result = (wide_as_nat h0 x) % S.prime end
      else
	begin
	Math.Lemmas.small_modulo_lemma_1 (as_nat h4 result) S.prime;
	Math.Lemmas.lemma_mod_sub (wide_as_nat h0 x) S.prime 1;
	as_nat h4 result = (wide_as_nat h0 x) % S.prime
	end );
 pop_frame()


inline_for_extraction noextract
val add8_without_carry1: x:widefelem -> y:widefelem -> res:widefelem -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint y x /\ eq_or_disjoint y res /\ eq_or_disjoint x res /\
    wide_as_nat h y < pow2 320 /\ wide_as_nat h x < S.prime * S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    wide_as_nat h1 res = wide_as_nat h0 x + wide_as_nat h0 y)

let add8_without_carry1 x y res  =
  let _  = bn_add8 x y res in
    assert_norm (pow2 320 + S.prime * S.prime < pow2 512)


inline_for_extraction noextract
val mont_mul_round: t:widefelem -> res:widefelem -> Stack unit
  (requires fun h ->
    live h t /\ live h res /\ eq_or_disjoint t res /\
    wide_as_nat h t < S.prime * S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    wide_as_nat h1 res = (wide_as_nat h0 t + S.prime * (wide_as_nat h0 t % pow2 64)) / pow2 64)

let mont_mul_round t res =
  push_frame ();
  let h0 = ST.get () in
  let t2 = create (size 8) (u64 0) in
  let t3 = create (size 8) (u64 0) in
  let t1 = bn_mod_pow2_64 t in
  recall_contents prime_buffer (Lib.Sequence.of_list p256_prime_list);
  bn_mul1 prime_buffer t1 t2;  // t2 = prime * (t % pow2 64)
  add8_without_carry1 t t2 t3; // t3 = t + t2
  bn_rshift64 t3 res;          // res = t3 / pow2 64
  pop_frame ()


val mont_mul_round_lemma:
    t:nat{t < S.prime * S.prime}
  -> res:nat{res = (t + (t % pow2 64) * S.prime) / pow2 64}
  -> co:nat{co % S.prime == t % S.prime} ->
  Lemma (res % S.prime == co * S.modp_inv2 (pow2 64) % S.prime /\ res < S.prime * S.prime)

let mont_mul_round_lemma t res co =
  SL.mult_one_round t co;
  SL.mul_lemma_1 (t % pow2 64) (pow2 64) S.prime;
  assert_norm (S.prime * S.prime + pow2 64 * S.prime < pow2 575);
  Math.Lemmas.lemma_div_lt (t + (t % pow2 64) * S.prime) 575 64;
  assert_norm (S.prime * S.prime > pow2 (575 - 64))


inline_for_extraction noextract
val mont_mul_round_twice: t:widefelem -> res:widefelem -> Stack unit
  (requires fun h ->
    live h t /\ live h res /\ eq_or_disjoint t res /\
    wide_as_nat h t < S.prime * S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    (let round = (wide_as_nat h0 t + S.prime * (wide_as_nat h0 t % pow2 64)) / pow2 64 in
    wide_as_nat h1 res < S.prime * S.prime /\
    wide_as_nat h1 res % S.prime ==
      (wide_as_nat h0 t * S.modp_inv2_prime (pow2 128) S.prime) % S.prime /\
    wide_as_nat h1 res == (round + S.prime * (round % pow2 64)) / pow2 64))

let mont_mul_round_twice t res =
  push_frame ();
  let tmp = create (size 8) (u64 0) in
  let h0 = ST.get () in
  mont_mul_round t tmp;
  let h1 = ST.get () in
  Math.Lemmas.swap_mul (wide_as_nat h0 t % pow2 64) S.prime;
  mont_mul_round_lemma (wide_as_nat h0 t) (wide_as_nat h1 tmp) (wide_as_nat h0 t);

  mont_mul_round tmp res;
  let h2 = ST.get () in
  Math.Lemmas.swap_mul (wide_as_nat h1 tmp % pow2 64) S.prime;
  mont_mul_round_lemma (wide_as_nat h1 tmp) (wide_as_nat h2 res)
    (wide_as_nat h0 t * S.modp_inv2_prime (pow2 64) S.prime);

  lemma_montgomery_mod_inverse_addition (wide_as_nat h0 t);
  pop_frame ()


val mont_reduction_lemma: x:nat{x < S.prime * S.prime} ->
  Lemma (
    let round1 = (x + S.prime * (x % pow2 64)) / pow2 64 in
    let nat_round2 = (round1 + S.prime * (round1 % pow2 64)) / pow2 64 in
    let round2 = (nat_round2 + S.prime * (nat_round2 % pow2 64)) / pow2 64 in
    let round4 = (round2 + S.prime * (round2 % pow2 64)) / pow2 64 in
    round4 < 2 * S.prime)

let mont_reduction_lemma x =
  let round1 = (x + S.prime * (x % pow2 64)) / pow2 64 in
  let nat_round2 = (round1 + S.prime * (round1 % pow2 64)) / pow2 64 in
  let round2 = (nat_round2 + S.prime * (nat_round2 % pow2 64)) / pow2 64 in
  let round4 = (round2 + S.prime * (round2 % pow2 64)) / pow2 64 in
  SL.mul_lemma_2 (x % pow2 64) (pow2 64 - 1) S.prime;
  SL.mul_lemma_1 (round1 % pow2 64) (pow2 64) S.prime;
  SL.mul_lemma_1 (nat_round2 % pow2 64) (pow2 64) S.prime;
  SL.mul_lemma_1 (round2 % pow2 64) (pow2 64) S.prime;
  assert_norm (
    (S.prime * pow2 64 + (S.prime * pow2 64 + (S.prime * pow2 64 +
      ((pow2 64 - 1) * S.prime + S.prime * S.prime) / pow2 64) / pow2 64) / pow2 64) / pow2 64
      < 2 * S.prime)


val mont_reduction: x:widefelem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ disjoint x res /\
    wide_as_nat h x < S.prime * S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == wide_as_nat h0 x * SM.mont_R_inv % S.prime)

[@CInline]
let mont_reduction x res =
  push_frame ();
  let round2 = create (size 8) (u64 0) in
  let round4 = create (size 8) (u64 0) in

  let h0 = ST.get () in
  mont_mul_round_twice x round2;
  let h1 = ST.get () in
  mont_mul_round_twice round2 round4;
  let h2 = ST.get () in

  [@inline_let] let inv_pow128 = S.modp_inv2_prime (pow2 128) S.prime in
  calc (==) {
    wide_as_nat h2 round4 % S.prime;
    (==) { }
    (wide_as_nat h1 round2 * inv_pow128) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (wide_as_nat h2 round2) inv_pow128 S.prime }
    (((wide_as_nat h0 x * inv_pow128) % S.prime) * inv_pow128) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (wide_as_nat h0 x * inv_pow128) inv_pow128 S.prime }
    ((wide_as_nat h0 x * inv_pow128) * inv_pow128) % S.prime;
    (==) { lemma_montgomery_mod_inverse_addition2 (wide_as_nat h0 x) }
    (wide_as_nat h0 x * SM.mont_R_inv) % S.prime;
  };

  mont_reduction_lemma (wide_as_nat h0 x);
  assert (wide_as_nat h2 round4 < 2 * S.prime);
  reduction_prime_2prime_8_with_carry_impl round4 res;
  pop_frame ()


[@CInline]
let fromDomain a res =
  push_frame ();
  let t = create (size 8) (u64 0) in
  let t_low = sub t (size 0) (size 4) in
  let t_high = sub t (size 4) (size 4) in

  let h0 = ST.get () in
  copy t_low a;
  let h1 = ST.get () in
  assert (wide_as_nat h0 t = as_nat h0 t_low + as_nat h0 t_high * pow2 256);
  assert_norm (S.prime < S.prime * S.prime);
  mont_reduction t res;
  SM.lemmaFromDomain (as_nat h0 a);
  pop_frame ()


[@CInline]
let fmul a b res =
  push_frame ();
  let t = create (size 8) (u64 0) in
  let h0 = ST.get () in
  bn_mul4 a b t;
  let h1 = ST.get () in
  SL.mul_lemma_ (as_nat h0 a) (as_nat h0 b) S.prime;
  mont_reduction t res;
  SM.lemmaFromDomainToDomain (as_nat h0 a);
  SM.lemmaFromDomainToDomain (as_nat h0 b);
  SM.multiplicationInDomainNat
    #(SM.fromDomain_ (as_nat h0 a)) #(SM.fromDomain_ (as_nat h0 b)) (as_nat h0 a) (as_nat h0 b);
  SM.inDomain_mod_is_not_mod (SM.fromDomain_ (as_nat h0 a) * SM.fromDomain_ (as_nat h0 b));
  pop_frame ()


[@CInline]
let fsqr a res =
  push_frame ();
  let t = create (size 8) (u64 0) in
  let h0 = ST.get() in
  bn_sqr4 a t;
  let h1 = ST.get() in
  SL.mul_lemma_ (as_nat h0 a) (as_nat h0 a) S.prime;
  mont_reduction t res;
  SM.lemmaFromDomainToDomain (as_nat h0 a);
  SM.multiplicationInDomainNat
    #(SM.fromDomain_ (as_nat h0 a)) #(SM.fromDomain_ (as_nat h0 a)) (as_nat h0 a) (as_nat h0 a);
  SM.inDomain_mod_is_not_mod (SM.fromDomain_ (as_nat h0 a) * SM.fromDomain_ (as_nat h0 a));
  pop_frame ()

//----------------------------------------------

[@CInline]
let fcube a result =
  let h0 = ST.get () in
  fsqr a result;
  fmul result a result;
  let h1 = ST.get () in
  Math.Lemmas.lemma_mod_mul_distr_l
    (SM.fromDomain_ (as_nat h0 a) * SM.fromDomain_ (as_nat h0 a))
    (SM.fromDomain_ (as_nat h0 a)) S.prime;
  SM.inDomain_mod_is_not_mod
    (SM.fromDomain_ (as_nat h0 a) * SM.fromDomain_ (as_nat h0 a) * SM.fromDomain_ (as_nat h0 a))


let fmul_by_2 a out =
  let h0 = ST.get () in
  fadd a a out;
  SM.inDomain_mod_is_not_mod (2 * SM.fromDomain_ (as_nat h0 a))


[@CInline]
let fmul_by_3 a result =
  let h0 = ST.get () in
  fmul_by_2 a result;
  let h1 = ST.get () in
  assert (as_nat h1 result == SM.toDomain_ (2 * SM.fromDomain_ (as_nat h0 a) % S.prime));
  fadd a result result;
  let h2 = ST.get() in
  Math.Lemmas.lemma_mod_add_distr (SM.fromDomain_ (as_nat h0 a)) (2 * SM.fromDomain_ (as_nat h0 a)) S.prime;
  SM.inDomain_mod_is_not_mod (3 * SM.fromDomain_ (as_nat h0 a))


[@CInline]
let fmul_by_4 a result  =
  let h0 = ST.get() in
  fmul_by_2 a result;
  fmul_by_2 result result;
  Math.Lemmas.lemma_mod_mul_distr_r 2 (2 * SM.fromDomain_ (as_nat h0 a)) S.prime;
  SL.lemma_brackets 2 2 (SM.fromDomain_ (as_nat h0 a));
  SM.inDomain_mod_is_not_mod (4 * SM.fromDomain_ (as_nat h0 a))


[@CInline]
let fmul_by_8 a result  =
  let h0 = ST.get() in
  fmul_by_4 a result;
  fmul_by_2 result result;
  Math.Lemmas.lemma_mod_mul_distr_r 2 (4 * SM.fromDomain_ (as_nat h0 a)) S.prime;
  SL.lemma_brackets 2 4 (SM.fromDomain_ (as_nat h0 a));
  SM.inDomain_mod_is_not_mod (8 * SM.fromDomain_ (as_nat h0 a))
