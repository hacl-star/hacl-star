module Hacl.Impl.P256.Scalar

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Tactics
open FStar.Tactics.Canon

open Lib.IntTypes
open Lib.Buffer
open Lib.IntTypes.Intrinsics

open Hacl.Spec.P256.Lemmas

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Constants

module S = Spec.P256

#reset-options "--z3rlimit 200 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val add8_without_carry1:  t: widefelem -> t1: widefelem -> result: widefelem  -> Stack unit
  (requires fun h -> live h t /\ live h t1 /\ live h result /\ wide_as_nat h t1 < pow2 320 /\
    wide_as_nat h t <  S.order * S.order /\ eq_or_disjoint t result /\ eq_or_disjoint t1 result  )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\  wide_as_nat h1 result = wide_as_nat h0 t + wide_as_nat h0 t1)

let add8_without_carry1 t t1 result  =
  let _ = bn_add8 t t1 result in
    assert_norm (pow2 320 + S.order * S.order < pow2 512)


val lemma_montgomery_mult_1: t : int  ->
  k0:nat {k0 = min_one_prime (pow2 64) (- S.order)} ->
  r: nat {t <= r} ->
  Lemma ((t + (((t % pow2 64) * k0) % pow2 64 * S.order)) / pow2 64 <= (pow2 64 * S.order + r) / pow2 64)

let lemma_montgomery_mult_1 t k0 r =
  let t1 = t % pow2 64 in
  let y = (t1 * k0) % pow2 64 in
  let t2 = y * S.order in
    mul_lemma_1 y (pow2 64) S.order


val lemma_montgomery_mult_result_less_than_order:
  a: nat{a < S.order} ->
  b: nat{b < S.order} ->
  k0:nat {k0 = min_one_prime (pow2 64) (- S.order)} ->
  Lemma
  (
    let t = a * b in
    let s = 64 in

    let t1 = t % pow2 s in
    let y = (t1 * k0) % pow2 s in
    let t2 = y * S.order in
    let t3 = t + t2 in
    let t = t3 / pow2 s in

    let t1 = t % pow2 s in
    let y = (t1 * k0) % pow2 s in
    let t2 = y * S.order in
    let t3 = t + t2 in
    let t = t3 / pow2 s in

    let t1 = t % pow2 s in
    let y = (t1 * k0) % pow2 s in
    let t2 = y * S.order in
    let t3 = t + t2 in
    let t = t3 / pow2 s in

    let t1 = t % pow2 s in
    let y = (t1 * k0) % pow2 s in
    let t2 = y * S.order in
    let t3 = t + t2 in
    let t = t3 / pow2 s in
    t < 2 * S.order)


let lemma_montgomery_mult_result_less_than_order a b k0 =
  let t = a * b in
  let s = 64 in
    mul_lemma_ a b S.order;

  let r = S.order * S.order + 1 in

  let t1 = t % pow2 s in
  let y = (t1 * k0) % pow2 s in
  let t2 = y * S.order in
  let t3 = t + t2 in
  let tU = t3 / pow2 s in
  lemma_montgomery_mult_1 t k0 r;

  let t = tU in
  let r = (pow2 64 * S.order + r) / pow2 64 in
  let t1 = t % pow2 s in
  let y = (t1 * k0) % pow2 s in
  let t2 = y * S.order in
  let t3 = t + t2 in
  let tU = t3 / pow2 s in
  lemma_montgomery_mult_1 t k0 r;

  let t = tU in
  let r = (pow2 64 * S.order + r) / pow2 64 in
  let t1 = t % pow2 s in
  let y = (t1 * k0) % pow2 s in
  let t2 = y * S.order in
  let t3 = t + t2 in
  let tU = t3 / pow2 s in
  lemma_montgomery_mult_1 t k0 r;

  let r = (pow2 64 * S.order + r) / pow2 64 in
  let t = tU in
  let t1 = t % pow2 s in
  let y = (t1 * k0) % pow2 s in
  let t2 = y * S.order in
  let t3 = t + t2 in
  let tU = t3 / pow2 s in
  lemma_montgomery_mult_1 t k0 r;
  assert_norm ((pow2 64 * S.order +  (pow2 64 * S.order +  (pow2 64 * S.order +  (pow2 64 * S.order +  S.order * S.order + 1) / pow2 64) / pow2 64) / pow2 64) / pow2 64 < 2 * S.order)


val lemma_montgomery_mod_inverse_addition: a: nat ->
  Lemma (
    (a * S.modp_inv2_prime(pow2 64) S.order  * S.modp_inv2_prime (pow2 64) S.order) % S.order ==
    (a * S.modp_inv2_prime(pow2 128) S.order) % S.order)

let lemma_montgomery_mod_inverse_addition a =
    assert_norm ((S.modp_inv2_prime(pow2 64) S.order * S.modp_inv2_prime (pow2 64) S.order) % S.order == S.modp_inv2_prime (pow2 128) S.order % S.order);
    assert_by_tactic ((a * S.modp_inv2_prime (pow2 64) S.order * S.modp_inv2_prime (pow2 64) S.order)  == (a * (S.modp_inv2_prime (pow2 64) S.order * S.modp_inv2_prime (pow2 64) S.order))) canon;
    lemma_mod_mul_distr_r a (S.modp_inv2_prime (pow2 64) S.order * S.modp_inv2_prime (pow2 64) S.order) S.order;
    lemma_mod_mul_distr_r a (S.modp_inv2_prime (pow2 128) S.order) S.order


val lemma_montgomery_mod_inverse_addition2: a: int ->
  Lemma (
    (a * S.modp_inv2_prime (pow2 128) S.order  * S.modp_inv2_prime (pow2 128) S.order) % S.order ==
    (a * S.modp_inv2_prime (pow2 256) S.order) % S.order)

let lemma_montgomery_mod_inverse_addition2 a =
  assert_norm ((S.modp_inv2_prime (pow2 128) S.order * S.modp_inv2_prime (pow2 128) S.order) % S.order == (S.modp_inv2_prime (pow2 256) S.order) % S.order);
    assert_by_tactic ((a * S.modp_inv2_prime (pow2 128) S.order * S.modp_inv2_prime (pow2 128) S.order)  == (a * (S.modp_inv2_prime (pow2 128) S.order * S.modp_inv2_prime (pow2 128) S.order))) canon;
    lemma_mod_mul_distr_r a (S.modp_inv2_prime (pow2 128) S.order * S.modp_inv2_prime (pow2 128) S.order) S.order;
    lemma_mod_mul_distr_r a (S.modp_inv2_prime (pow2 256) S.order) S.order


val montgomery_multiplication_one_round_proof:
  t: nat ->
  k0: nat {k0 = min_one_prime (pow2 64) (- S.order)}  ->
  round: nat {round = (t + S.order * ((k0 * (t % pow2 64)) % pow2 64)) / pow2 64} ->
  co: nat {co % S.order = t % S.order} ->
  Lemma (round  % S.order == co * (S.modp_inv2_prime (pow2 64) S.order) % S.order)

let montgomery_multiplication_one_round_proof t k0 round co =
  mult_one_round_ecdsa_prime t S.order co k0

#reset-options "--z3rlimit 700"

val montgomery_multiplication_round: t: widefelem ->  round: widefelem -> k0: uint64 ->
  Stack unit
    (requires fun h -> live h t /\ live h round  /\ wide_as_nat h t < S.order * S.order)
    (ensures fun h0 _ h1 -> modifies (loc round) h0 h1 /\
      wide_as_nat h1 round = (wide_as_nat h0 t + S.order * ((uint_v k0 * (wide_as_nat h0 t % pow2 64)) % pow2 64)) / pow2 64)

let montgomery_multiplication_round t round k0 =
  push_frame();
    let h0 = ST.get() in
    let temp = create (size 1) (u64 0) in
    let y = create (size 1) (u64 0) in

    let t2 = create (size 8) (u64 0) in
    let t3 = create (size 8) (u64 0) in
    let t1 = bn_mod_pow2_64 t in
    mul64 t1 k0 y temp;
      let h1 = ST.get() in
      assert(uint_v (Lib.Sequence.index (as_seq h1 y) 0) + uint_v (Lib.Sequence.index (as_seq h1 temp) 0) * pow2 64 = uint_v t1 * uint_v k0);
      assert((uint_v (Lib.Sequence.index (as_seq h1 y) 0) + uint_v (Lib.Sequence.index (as_seq h1 temp) 0) * pow2 64) % pow2 64 = uint_v (Lib.Sequence.index (as_seq h1 y) 0));
      assert((uint_v (Lib.Sequence.index (as_seq h1 y) 0) + uint_v (Lib.Sequence.index (as_seq h1 temp) 0) * pow2 64) % pow2 64 = (uint_v t1 * uint_v k0) % pow2 64);
      assert(uint_v (Lib.Sequence.index (as_seq h1 y) 0) = (uint_v t1 * uint_v k0) % pow2 64);
      recall_contents primeorder_buffer (Lib.Sequence.of_list p256_order_prime_list);
    let y_ = index y (size 0) in
      assert(uint_v (Lib.Sequence.index (as_seq h1 y) 0) == uint_v y_);
      assert(uint_v y_ == (uint_v t1 * uint_v k0) % pow2 64);

    bn_mul1 primeorder_buffer y_ t2;
      let h2 = ST.get() in
      assert(wide_as_nat h2 t2 = S.order * ((uint_v t1 * uint_v k0) % pow2 64));
    add8_without_carry1 t t2 t3;
      let h3 = ST.get() in
      assert_by_tactic ((wide_as_nat h0 t % pow2 64) * uint_v k0 == uint_v k0 * (wide_as_nat h0 t % pow2 64)) canon;
      assert(wide_as_nat h3 t3 = wide_as_nat h0 t + S.order * ((((wide_as_nat h0 t % pow2 64)) * uint_v k0) % pow2 64));
    bn_rshift64 t3 round;
      let h4 = ST.get() in
      assert(wide_as_nat h4 round = (wide_as_nat h0 t + S.order * ((((wide_as_nat h0 t % pow2 64)) * uint_v k0) % pow2 64)) / pow2 64);
  pop_frame()


#reset-options "--z3rlimit 200"

val montgomery_multiplication_round_twice: t: widefelem -> result: widefelem -> k0: uint64->
  Stack unit
    (requires fun h -> live h t /\ live h result /\ uint_v k0 = min_one_prime (pow2 64) (- S.order) /\
      wide_as_nat h t < S.order * S.order)
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
      wide_as_nat h1 result % S.order == (wide_as_nat h0 t * S.modp_inv2_prime (pow2 128) S.order) % S.order /\
      (
	let round = (wide_as_nat h0 t + S.order * ((uint_v k0 * (wide_as_nat h0 t % pow2 64)) % pow2 64)) / pow2 64 in
	wide_as_nat h1 result == (round + S.order * ((uint_v k0 * (round % pow2 64)) % pow2 64)) / pow2 64)  /\
	wide_as_nat h1 result < S.order * S.order
      )

let montgomery_multiplication_round_twice t result k0 =
   push_frame();
     let tempRound = create (size 8) (u64 0) in
       let h0 = ST.get() in
   montgomery_multiplication_round t tempRound k0;
       let h1 = ST.get() in
   montgomery_multiplication_one_round_proof (wide_as_nat h0 t) (uint_v k0) (wide_as_nat h1 tempRound) (wide_as_nat h0 t);
   montgomery_multiplication_round tempRound result k0;
      let h2 = ST.get() in
   montgomery_multiplication_one_round_proof (wide_as_nat h1 tempRound) (uint_v k0) (wide_as_nat h2 result) (wide_as_nat h0 t * S.modp_inv2_prime (pow2 64) S.order);
   lemma_montgomery_mod_inverse_addition (wide_as_nat h0 t);
  pop_frame()


val reduction_prime_2prime_with_carry : x: widefelem -> result: felem ->
  Stack unit
    (requires fun h -> live h x /\ live h result /\  eq_or_disjoint x result /\ wide_as_nat h x < 2 * S.order)
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 result = wide_as_nat h0 x % S.order)

let reduction_prime_2prime_with_carry x result  =
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 == pow2 256);
  push_frame();
    let h0 = ST.get() in
    let tempBuffer = create (size 4) (u64 0) in
    let tempBufferForSubborrow = create (size 1) (u64 0) in
    let cin = Lib.Buffer.index x (size 4) in
    let x_ = Lib.Buffer.sub x (size 0) (size 4) in
        recall_contents primeorder_buffer (Lib.Sequence.of_list p256_order_prime_list);
    let c = bn_sub4_il x_ primeorder_buffer tempBuffer in
      let h1 = ST.get() in

      assert(if uint_v c = 0 then as_nat h0 x_ >= S.order else as_nat h0 x_ < S.order);
      assert(wide_as_nat h0 x = as_nat h0 x_ + uint_v cin * pow2 256);
    let carry = sub_borrow_u64 c cin (u64 0) tempBufferForSubborrow in
      let h2 = ST.get() in
      assert(if (as_nat h0 x_ >= S.order) then uint_v carry = 0
	else if uint_v cin < uint_v c then uint_v carry = 1
	else uint_v carry = 0);

    bn_cmovznz4 carry tempBuffer x_ result;
 pop_frame()


inline_for_extraction noextract
val reduction_prime_2prime_with_carry2 : carry: uint64 ->  x: felem -> result: felem ->
  Stack unit
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result /\
      uint_v carry * pow2 256 + as_nat h x < 2 * S.order )
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
      as_nat h1 result = (uint_v carry * pow2 256 + as_nat h0 x) % S.order)

let reduction_prime_2prime_with_carry2 cin x result  =
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 == pow2 256);
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in
    let tempBufferForSubborrow = create (size 1) (u64 0) in
        recall_contents primeorder_buffer (Lib.Sequence.of_list p256_order_prime_list);
    let c = bn_sub4_il x primeorder_buffer tempBuffer in
    let carry = sub_borrow_u64 c cin (u64 0) tempBufferForSubborrow in
    bn_cmovznz4 carry tempBuffer x result;
 pop_frame()


val lemma_reduction1: a: nat {a < pow2 256} -> r: nat{if a >= S.order then r = a - S.order else r = a} ->
  Lemma (r = a % S.order)

let lemma_reduction1 a r =
  let prime = S.order in
  assert_norm (pow2 256 - S.order < S.order)


let reduction_prime_2prime_order x result  =
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in
    recall_contents primeorder_buffer (Lib.Sequence.of_list p256_order_prime_list);
      let h0 = ST.get() in
    let c = bn_sub4_il x primeorder_buffer tempBuffer in
      let h1 = ST.get() in
      assert(as_nat h1 tempBuffer = as_nat h0 x - S.order + uint_v c * pow2 256);
      assert(let x = as_nat h0 x in if x < S.order then uint_v c = 1 else uint_v c = 0);
    bn_cmovznz4 c tempBuffer x result;
    let h2 = ST.get() in
      assert_norm (pow2 256 == pow2 64 * pow2 64 * pow2 64 * pow2 64);
    lemma_reduction1 (as_nat h0 x) (as_nat h2 result);
  pop_frame()


inline_for_extraction noextract
val upload_k0: unit ->  Tot (r: uint64 {uint_v r == min_one_prime (pow2 64) (- S.order)})

let upload_k0 () =
  assert_norm(min_one_prime (pow2 64) (- S.order) == 14758798090332847183);
  (u64 14758798090332847183)


let fromDomain_ a = (a * S.modp_inv2_prime (pow2 256) S.order) % S.order

let toDomain_ a = (a * pow2 256) % S.order

let lemmaFromDomain a = ()

let lemmaToDomain a = ()

let lemmaFromDomainToDomain a =
   let fromA = (a * S.modp_inv2_prime (pow2 256) S.order) % S.order in
   let toFromA = (((a * S.modp_inv2_prime (pow2 256) S.order) % S.order) * pow2 256) % S.order in
   lemma_mod_mul_distr_l (a * S.modp_inv2_prime (pow2 256) S.order) (pow2 256) S.order;
     assert_by_tactic (a * (S.modp_inv2_prime (pow2 256) S.order * pow2 256) = a * S.modp_inv2_prime (pow2 256) S.order * pow2 256) canon;
   lemma_mod_mul_distr_r a (S.modp_inv2_prime (pow2 256) S.order * pow2 256) S.order;
   assert_norm((S.modp_inv2_prime (pow2 256) S.order * pow2 256) % S.order == 1);
   small_modulo_lemma_1 a S.order


val multiplicationInDomain: #k: nat -> #l: nat ->
  a: nat {a == toDomain_ (k) /\ a < S.order} ->
  b: nat {b == toDomain_ (l) /\ b < S.order} ->
  Lemma  ((a *  b * S.modp_inv2_prime (pow2 256) S.order) % S.order == toDomain_ (k * l))

let multiplicationInDomain #k #l a b =
  let f = a * b * S.modp_inv2_prime (pow2 256) S.order in
  let z = toDomain_ (k * l) in
  assert_by_tactic (((k * pow2 256) % S.order) * ((l * pow2 256) % S.order) * S.modp_inv2_prime (pow2 256) S.order =
    ((k * pow2 256) % S.order) * (((l * pow2 256) % S.order) * S.modp_inv2_prime (pow2 256) S.order)) canon;
  lemma_mod_mul_distr_l (k * pow2 256) (((l * pow2 256) % S.order) * S.modp_inv2_prime (pow2 256) S.order) S.order;
  assert_by_tactic (
    ((k * pow2 256) * (((l * pow2 256) % S.order) * S.modp_inv2_prime (pow2 256) S.order)) % S.order =
    ((((l * pow2 256) % S.order) * (((k * pow2 256) * S.modp_inv2_prime (pow2 256) S.order)) % S.order))) canon;
  lemma_mod_mul_distr_l (l * pow2 256)  ((k * pow2 256) * S.modp_inv2_prime (pow2 256) S.order) S.order;
  assert_by_tactic ( ((l * pow2 256 * ((k * pow2 256) * S.modp_inv2_prime (pow2 256) S.order))) ==
     ((l * pow2 256 * k) * (pow2 256 * S.modp_inv2_prime (pow2 256) S.order))) canon;
  lemma_mod_mul_distr_r (l * pow2 256 * k) (pow2 256 * S.modp_inv2_prime (pow2 256) S.order) S.order;
  assert_norm ((pow2 256 * S.modp_inv2_prime (pow2 256) S.order) % S.order == 1);
  assert_by_tactic ((l * pow2 256 * k) == ((k * l) * pow2 256)) canon


val inDomain_mod_is_not_mod: a: nat -> Lemma (toDomain_ a == toDomain_ (a % S.order))

let inDomain_mod_is_not_mod a =
   lemma_mod_mul_distr_l a (pow2 256) S.order


let lemmaToDomainFromDomain a =
  let to = (a * pow2 256) % S.order in
  let from_to = ((((a * pow2 256) % S.order) * S.modp_inv2_prime (pow2 256) S.order) % S.order) in
  lemma_mod_mul_distr_l (a * pow2 256) (S.modp_inv2_prime (pow2 256) S.order) S.order;
  assert_by_tactic ((a * pow2 256) * S.modp_inv2_prime (pow2 256) S.order == a * (pow2 256 * S.modp_inv2_prime (pow2 256) S.order)) canon;
  lemma_mod_mul_distr_r a (pow2 256 * S.modp_inv2_prime (pow2 256) S.order) S.order;
  assert_norm ((pow2 256 * S.modp_inv2_prime (pow2 256) S.order) % S.order == 1)


#reset-options "--z3rlimit 200"

let montgomery_multiplication_ecdsa_module a b result =
  push_frame();
    let t = create (size 8) (u64 0) in
    let round2 = create (size 8) (u64 0) in
    let round4 = create (size 8) (u64 0) in
    let orderBuffer = create (size 4) (u64 0) in

    let k0 = upload_k0() in

      let h0 = ST.get() in
    bn_mul4 a b t;
      assert_by_tactic (as_nat h0 b * as_nat h0 a == as_nat h0 a * as_nat h0 b) canon;
      mul_lemma_ (as_nat h0 a) (as_nat h0 b) S.order;
   montgomery_multiplication_round_twice t round2 k0;
     let h2 = ST.get() in
   montgomery_multiplication_round_twice round2 round4 k0;
     lemma_mod_mul_distr_l (wide_as_nat h2 round2) (S.modp_inv2_prime (pow2 128) S.order) S.order;
     lemma_mod_mul_distr_l (as_nat h0 a * as_nat h0 b * S.modp_inv2_prime (pow2 128) S.order) (S.modp_inv2_prime (pow2 128) S.order) S.order;
     lemma_montgomery_mod_inverse_addition2 (as_nat h0 a * as_nat h0 b);

     lemma_montgomery_mult_result_less_than_order (as_nat h0 a) (as_nat h0 b) (uint_v k0);
   reduction_prime_2prime_with_carry round4 result;

     lemmaFromDomainToDomain (as_nat h0 a);
     lemmaFromDomainToDomain (as_nat h0 b);
     multiplicationInDomain #(fromDomain_ (as_nat h0 a)) #(fromDomain_ (as_nat h0 b)) (as_nat h0 a) (as_nat h0 b);
     inDomain_mod_is_not_mod (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b));
    pop_frame()



let felem_add arg1 arg2 out =
  let t = bn_add4 arg1 arg2 out in
  reduction_prime_2prime_with_carry2 t out out


let lemma_felem_add a b =
  lemmaFromDomain a;
  lemmaFromDomain b;
  lemmaFromDomain (a + b);
  assert(fromDomain_ a + fromDomain_ b = (a * S.modp_inv2_prime (pow2 256) S.order) % S.order + (b * S.modp_inv2_prime (pow2 256) S.order) % S.order);
  let aD = a * S.modp_inv2_prime (pow2 256) S.order in
  let bD = b * S.modp_inv2_prime (pow2 256) S.order in
  assert(fromDomain_ (a + b) = (aD + bD) % S.order);

  lemma_mod_plus_distr_l aD bD S.order;
  lemma_mod_plus_distr_l bD (aD % S.order) S.order;
  assert(fromDomain_ (a + b) = (aD % S.order + bD % S.order) % S.order);

  assert(fromDomain_ (a + b) = (fromDomain_ a + fromDomain_ b) % S.order)


let fromDomainImpl a result =
  push_frame();
    let one = create (size 4) (u64 0) in
    bn_set_one4 one;
    montgomery_multiplication_ecdsa_module one a result;
  pop_frame()
