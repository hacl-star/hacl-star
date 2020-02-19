module Hacl.Impl.ECDSA.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas

open Spec.P256.Lemmas
open Spec.ECDSAP256.Definition
open Hacl.Impl.LowLevel

open FStar.Tactics
open FStar.Tactics.Canon 

open FStar.Mul
open Lib.IntTypes.Intrinsics

#reset-options "--z3rlimit 200"

val add8_without_carry1:  t: widefelem -> t1: widefelem -> result: widefelem  -> Stack unit
  (requires fun h -> live h t /\ live h t1 /\ live h result /\ wide_as_nat h t1 < pow2 320 /\
    wide_as_nat h t <  prime_p256_order * prime_p256_order /\ eq_or_disjoint t result /\ eq_or_disjoint t1 result  )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\  wide_as_nat h1 result = wide_as_nat h0 t + wide_as_nat h0 t1)

let add8_without_carry1 t t1 result  = 
  let _ = Hacl.Impl.LowLevel.add8 t t1 result in 
    assert_norm (pow2 320 + prime_p256_order * prime_p256_order < pow2 512)


val lemma_montgomery_mult_1: t : int  -> 
  k0:nat {k0 = min_one_prime (pow2 64) (- prime)} -> 
  r: nat {t <= r} -> 
  Lemma ((t + (((t % pow2 64) * k0) % pow2 64 * prime_p256_order)) / pow2 64 <= (pow2 64 * prime_p256_order + r) / pow2 64)

let lemma_montgomery_mult_1 t k0 r = 
  let t1 = t % pow2 64 in 
  let y = (t1 * k0) % pow2 64 in 
  let t2 = y * prime_p256_order in 
    mul_lemma_1 y (pow2 64) prime_p256_order


val lemma_montgomery_mult_result_less_than_prime_p256_order: 
  a: nat{a < prime_p256_order} -> 
  b: nat{b < prime_p256_order} -> 
  k0:nat {k0 = min_one_prime (pow2 64) (- prime)} -> 
  Lemma
  (  
    let t = a * b in 
    let s = 64 in 
  
    let t1 = t % pow2 s in 
    let y = (t1 * k0) % pow2 s in 
    let t2 = y * prime_p256_order in 
    let t3 = t + t2 in
    let t = t3 / pow2 s in 
  
    let t1 = t % pow2 s in 
    let y = (t1 * k0) % pow2 s in 
    let t2 = y * prime_p256_order in 
    let t3 = t + t2 in
    let t = t3 / pow2 s in 
  
    let t1 = t % pow2 s in 
    let y = (t1 * k0) % pow2 s in 
    let t2 = y * prime_p256_order in 
    let t3 = t + t2 in
    let t = t3 / pow2 s in 
    
    let t1 = t % pow2 s in 
    let y = (t1 * k0) % pow2 s in 
    let t2 = y * prime_p256_order in 
    let t3 = t + t2 in
    let t = t3 / pow2 s in 
    t < 2 * prime_p256_order)


let lemma_montgomery_mult_result_less_than_prime_p256_order a b k0 = 
  let t = a * b in 
  let s = 64 in 
    mul_lemma_ a b prime_p256_order;

  let r = prime_p256_order * prime_p256_order + 1 in 

  let t1 = t % pow2 s in 
  let y = (t1 * k0) % pow2 s in 
  let t2 = y * prime_p256_order in 
  let t3 = t + t2 in
  let tU = t3 / pow2 s in 
  lemma_montgomery_mult_1 t k0 r; 

  let t = tU in 
  let r = (pow2 64 * prime_p256_order + r) / pow2 64 in 
  let t1 = t % pow2 s in 
  let y = (t1 * k0) % pow2 s in 
  let t2 = y * prime_p256_order in 
  let t3 = t + t2 in
  let tU = t3 / pow2 s in 
  lemma_montgomery_mult_1 t k0 r; 

  let t = tU in 
  let r = (pow2 64 * prime_p256_order + r) / pow2 64 in 
  let t1 = t % pow2 s in 
  let y = (t1 * k0) % pow2 s in 
  let t2 = y * prime_p256_order in 
  let t3 = t + t2 in
  let tU = t3 / pow2 s in 
  lemma_montgomery_mult_1 t k0 r; 

  let r = (pow2 64 * prime_p256_order + r) / pow2 64 in 
  let t = tU in 
  let t1 = t % pow2 s in 
  let y = (t1 * k0) % pow2 s in 
  let t2 = y * prime_p256_order in 
  let t3 = t + t2 in
  let tU = t3 / pow2 s in 
  lemma_montgomery_mult_1 t k0 r; 
  assert_norm ((pow2 64 * prime_p256_order +  (pow2 64 * prime_p256_order +  (pow2 64 * prime_p256_order +  (pow2 64 * prime_p256_order +  prime_p256_order * prime_p256_order + 1) / pow2 64) / pow2 64) / pow2 64) / pow2 64 < 2 * prime_p256_order)


val lemma_montgomery_mod_inverse_addition: a: nat -> 
  Lemma (
    (a * modp_inv2_prime(pow2 64) prime_p256_order  * modp_inv2_prime (pow2 64) prime_p256_order) % prime_p256_order == 
    (a * modp_inv2_prime(pow2 128) prime_p256_order) % prime_p256_order)

let lemma_montgomery_mod_inverse_addition a =
    assert_norm ((modp_inv2_prime(pow2 64) prime_p256_order * modp_inv2_prime (pow2 64) prime_p256_order) % prime_p256_order == modp_inv2_prime (pow2 128) prime_p256_order % prime_p256_order);
    assert_by_tactic ((a * modp_inv2_prime (pow2 64) prime_p256_order * modp_inv2_prime (pow2 64) prime_p256_order)  == (a * (modp_inv2_prime (pow2 64) prime_p256_order * modp_inv2_prime (pow2 64) prime_p256_order))) canon;
    lemma_mod_mul_distr_r a (modp_inv2_prime (pow2 64) prime_p256_order * modp_inv2_prime (pow2 64) prime_p256_order) prime_p256_order; 
    lemma_mod_mul_distr_r a (modp_inv2_prime (pow2 128) prime_p256_order) prime_p256_order


val lemma_montgomery_mod_inverse_addition2: a: int -> 
  Lemma ( 
    (a * modp_inv2_prime (pow2 128) prime_p256_order  * modp_inv2_prime (pow2 128) prime_p256_order) % prime_p256_order == 
    (a * modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order)

let lemma_montgomery_mod_inverse_addition2 a = 
  assert_norm ((modp_inv2_prime (pow2 128) prime_p256_order * modp_inv2_prime (pow2 128) prime_p256_order) % prime_p256_order == (modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order);
    assert_by_tactic ((a * modp_inv2_prime (pow2 128) prime_p256_order * modp_inv2_prime (pow2 128) prime_p256_order)  == (a * (modp_inv2_prime (pow2 128) prime_p256_order * modp_inv2_prime (pow2 128) prime_p256_order))) canon;
    lemma_mod_mul_distr_r a (modp_inv2_prime (pow2 128) prime_p256_order * modp_inv2_prime (pow2 128) prime_p256_order) prime_p256_order; 
    lemma_mod_mul_distr_r a (modp_inv2_prime (pow2 256) prime_p256_order) prime_p256_order


val montgomery_multiplication_one_round_proof: 
  t: nat ->
  k0: nat {k0 = min_one_prime (pow2 64) (- prime)}  ->  
  round: nat {round = (t + prime_p256_order * ((k0 * (t % pow2 64)) % pow2 64)) / pow2 64} -> 
  co: nat {co % prime_p256_order = t % prime_p256_order} -> 
  Lemma (round  % prime_p256_order == co * (modp_inv2_prime (pow2 64) prime_p256_order) % prime_p256_order)

let montgomery_multiplication_one_round_proof t k0 round co = 
  mult_one_round_ecdsa_prime t prime_p256_order co k0

#reset-options "--z3rlimit 600"

val montgomery_multiplication_round: t: widefelem ->  round: widefelem -> k0: uint64 ->
  Stack unit 
    (requires fun h -> live h t /\ live h round  /\ wide_as_nat h t < prime_p256_order * prime_p256_order)
    (ensures fun h0 _ h1 -> modifies (loc round) h0 h1 /\ 
      wide_as_nat h1 round = (wide_as_nat h0 t + prime_p256_order * ((uint_v k0 * (wide_as_nat h0 t % pow2 64)) % pow2 64)) / pow2 64)

let montgomery_multiplication_round t round k0 = 
  push_frame(); 
    let h0 = ST.get() in 
    let temp = create (size 1) (u64 0) in 
    let y = create (size 1) (u64 0) in 

    let t2 = create (size 8) (u64 0) in 
    let t3 = create (size 8) (u64 0) in 
    let t1 = mod64 t in
    mul64 t1 k0 y temp;
      let h1 = ST.get() in 
      assert(uint_v (Lib.Sequence.index (as_seq h1 y) 0) + uint_v (Lib.Sequence.index (as_seq h1 temp) 0) * pow2 64 = uint_v t1 * uint_v k0);
      assert((uint_v (Lib.Sequence.index (as_seq h1 y) 0) + uint_v (Lib.Sequence.index (as_seq h1 temp) 0) * pow2 64) % pow2 64 = uint_v (Lib.Sequence.index (as_seq h1 y) 0));
      assert((uint_v (Lib.Sequence.index (as_seq h1 y) 0) + uint_v (Lib.Sequence.index (as_seq h1 temp) 0) * pow2 64) % pow2 64 = (uint_v t1 * uint_v k0) % pow2 64);
      assert(uint_v (Lib.Sequence.index (as_seq h1 y) 0) = (uint_v t1 * uint_v k0) % pow2 64); 
      recall_contents prime256order_buffer (Lib.Sequence.of_list p256_order_prime_list);
    let y_ = index y (size 0) in   
      assert(uint_v (Lib.Sequence.index (as_seq h1 y) 0) == uint_v y_);
      assert(uint_v y_ == (uint_v t1 * uint_v k0) % pow2 64);

    shortened_mul prime256order_buffer y_ t2;
      let h2 = ST.get() in 
      assert(wide_as_nat h2 t2 = prime_p256_order * ((uint_v t1 * uint_v k0) % pow2 64));
    add8_without_carry1 t t2 t3;
      let h3 = ST.get() in 
      assert_by_tactic ((wide_as_nat h0 t % pow2 64) * uint_v k0 == uint_v k0 * (wide_as_nat h0 t % pow2 64)) canon;
      assert(wide_as_nat h3 t3 = wide_as_nat h0 t + prime_p256_order * ((((wide_as_nat h0 t % pow2 64)) * uint_v k0) % pow2 64));
    shift8 t3 round;
      let h4 = ST.get() in 
      assert(wide_as_nat h4 round = (wide_as_nat h0 t + prime_p256_order * ((((wide_as_nat h0 t % pow2 64)) * uint_v k0) % pow2 64)) / pow2 64);
  pop_frame()


#reset-options "--z3rlimit 200"

val montgomery_multiplication_round_twice: t: widefelem -> result: widefelem -> k0: uint64-> 
  Stack unit 
    (requires fun h -> live h t /\ live h result /\ uint_v k0 = min_one_prime (pow2 64) (- prime) /\
      wide_as_nat h t < prime_p256_order * prime_p256_order)
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
      wide_as_nat h1 result % prime_p256_order == (wide_as_nat h0 t * modp_inv2_prime (pow2 128) prime_p256_order) % prime_p256_order /\
      (
	let round = (wide_as_nat h0 t + prime_p256_order * ((uint_v k0 * (wide_as_nat h0 t % pow2 64)) % pow2 64)) / pow2 64 in 
	wide_as_nat h1 result == (round + prime_p256_order * ((uint_v k0 * (round % pow2 64)) % pow2 64)) / pow2 64)  /\
	wide_as_nat h1 result < prime_p256_order * prime_p256_order
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
   montgomery_multiplication_one_round_proof (wide_as_nat h1 tempRound) (uint_v k0) (wide_as_nat h2 result) (wide_as_nat h0 t * modp_inv2_prime (pow2 64) prime_p256_order); 
   lemma_montgomery_mod_inverse_addition (wide_as_nat h0 t); 
  pop_frame()


let reduction_prime_2prime_with_carry x result  = 
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 == pow2 256);
  push_frame();
    let h0 = ST.get() in 
    let tempBuffer = create (size 4) (u64 0) in 
    let tempBufferForSubborrow = create (size 1) (u64 0) in 
    let cin = Lib.Buffer.index x (size 4) in 
    let x_ = Lib.Buffer.sub x (size 0) (size 4) in 
        recall_contents prime256order_buffer (Lib.Sequence.of_list p256_order_prime_list);
    let c = Hacl.Impl.LowLevel.sub4_il x_ prime256order_buffer tempBuffer in
      let h1 = ST.get() in 

      assert(if uint_v c = 0 then as_nat h0 x_ >= prime_p256_order else as_nat h0 x_ < prime_p256_order);
      assert(wide_as_nat h0 x = as_nat h0 x_ + uint_v cin * pow2 256);
    let carry = sub_borrow_u64 c cin (u64 0) tempBufferForSubborrow in 
      let h2 = ST.get() in 
      assert(if (as_nat h0 x_ >= prime_p256_order) then uint_v carry = 0 
	else if uint_v cin < uint_v c then uint_v carry = 1 
	else uint_v carry = 0);

    cmovznz4 carry tempBuffer x_ result;
 pop_frame()   


let reduction_prime_2prime_with_carry2 cin x result  = 
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 == pow2 256);
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in 
    let tempBufferForSubborrow = create (size 1) (u64 0) in 
        recall_contents prime256order_buffer (Lib.Sequence.of_list p256_order_prime_list);
    let c = Hacl.Impl.LowLevel.sub4_il x prime256order_buffer tempBuffer in
    let carry = sub_borrow_u64 c cin (u64 0) tempBufferForSubborrow in 
    cmovznz4 carry tempBuffer x result;
 pop_frame()      


val lemma_reduction1: a: nat {a < pow2 256} -> r: nat{if a >= prime_p256_order then r = a - prime_p256_order else r = a} -> 
  Lemma (r = a % prime_p256_order)

let lemma_reduction1 a r = 
  let prime256 = prime_p256_order in 
  assert_norm (pow2 256 - prime_p256_order < prime_p256_order)


let reduction_prime_2prime_order x result  = 
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in 
    recall_contents prime256order_buffer (Lib.Sequence.of_list p256_order_prime_list);
      let h0 = ST.get() in 
    let c = sub4_il x prime256order_buffer tempBuffer in
      let h1 = ST.get() in 
      assert(as_nat h1 tempBuffer = as_nat h0 x - prime_p256_order + uint_v c * pow2 256);
      assert(let x = as_nat h0 x in if x < prime_p256_order then uint_v c = 1 else uint_v c = 0);
    cmovznz4 c tempBuffer x result; 
    let h2 = ST.get() in 
      assert_norm (pow2 256 == pow2 64 * pow2 64 * pow2 64 * pow2 64);
    lemma_reduction1 (as_nat h0 x) (as_nat h2 result);
  pop_frame()  
  

val upload_k0: unit ->  Tot (r: uint64 {uint_v r == min_one_prime (pow2 64) (- prime)})

let upload_k0 () = 
  assert_norm(min_one_prime (pow2 64) (- prime) == 14758798090332847183);
  (u64 14758798090332847183)


let fromDomain_ a = (a * modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order

let toDomain_ a = (a * pow2 256) % prime_p256_order 

let lemmaFromDomain a = ()

let lemmaToDomain a = ()

let lemmaFromDomainToDomain a = 
   let fromA = (a * modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order in 
   let toFromA = (((a * modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order) * pow2 256) % prime_p256_order in 
   lemma_mod_mul_distr_l (a * modp_inv2_prime (pow2 256) prime_p256_order) (pow2 256) prime_p256_order;
     assert_by_tactic (a * (modp_inv2_prime (pow2 256) prime_p256_order * pow2 256) = a * modp_inv2_prime (pow2 256) prime_p256_order * pow2 256) canon;
   lemma_mod_mul_distr_r a (modp_inv2_prime (pow2 256) prime_p256_order * pow2 256) prime_p256_order; 
   assert_norm((modp_inv2_prime (pow2 256) prime_p256_order * pow2 256) % prime_p256_order == 1);
   small_modulo_lemma_1 a prime_p256_order


val multiplicationInDomain: #k: nat -> #l: nat -> 
  a: nat {a == toDomain_ (k) /\ a < prime} -> 
  b: nat {b == toDomain_ (l) /\ b < prime} -> 
  Lemma  ((a *  b * modp_inv2_prime (pow2 256) prime) % prime_p256_order == toDomain_ (k * l))

let multiplicationInDomain #k #l a b = 
  let f = a * b * modp_inv2_prime (pow2 256) prime in 
  let z = toDomain_ (k * l) in 
  assert_by_tactic (((k * pow2 256) % prime_p256_order) * ((l * pow2 256) % prime_p256_order) * modp_inv2_prime (pow2 256) prime = 
    ((k * pow2 256) % prime_p256_order) * (((l * pow2 256) % prime_p256_order) * modp_inv2_prime (pow2 256) prime)) canon;
  lemma_mod_mul_distr_l (k * pow2 256) (((l * pow2 256) % prime_p256_order) * modp_inv2_prime (pow2 256) prime) prime_p256_order;
  assert_by_tactic (
    ((k * pow2 256) * (((l * pow2 256) % prime_p256_order) * modp_inv2_prime (pow2 256) prime)) % prime_p256_order = 
    ((((l * pow2 256) % prime_p256_order) * (((k * pow2 256) * modp_inv2_prime (pow2 256) prime)) % prime_p256_order))) canon;
  lemma_mod_mul_distr_l (l * pow2 256)  ((k * pow2 256) * modp_inv2_prime (pow2 256) prime) prime_p256_order;
  assert_by_tactic ( ((l * pow2 256 * ((k * pow2 256) * modp_inv2_prime (pow2 256) prime))) == 
     ((l * pow2 256 * k) * (pow2 256 * modp_inv2_prime (pow2 256) prime))) canon;
  lemma_mod_mul_distr_r (l * pow2 256 * k) (pow2 256 * modp_inv2_prime (pow2 256) prime) prime_p256_order;
  assert_norm ((pow2 256 * modp_inv2_prime (pow2 256) prime) % prime_p256_order == 1);
  assert_by_tactic ((l * pow2 256 * k) == ((k * l) * pow2 256)) canon
  

val inDomain_mod_is_not_mod: a: nat -> Lemma (toDomain_ a == toDomain_ (a % prime_p256_order))

let inDomain_mod_is_not_mod a = 
   lemma_mod_mul_distr_l a (pow2 256) prime_p256_order


let lemmaToDomainFromDomain a = 
  let to = (a * pow2 256) % prime_p256_order in 
  let from_to = ((((a * pow2 256) % prime_p256_order) * modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order) in 
  lemma_mod_mul_distr_l (a * pow2 256) (modp_inv2_prime (pow2 256) prime_p256_order) prime_p256_order;
  assert_by_tactic ((a * pow2 256) * modp_inv2_prime (pow2 256) prime_p256_order == a * (pow2 256 * modp_inv2_prime (pow2 256) prime_p256_order)) canon;
  lemma_mod_mul_distr_r a (pow2 256 * modp_inv2_prime (pow2 256) prime_p256_order) prime_p256_order;
  assert_norm ((pow2 256 * modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order == 1)


#reset-options "--z3rlimit 200"

let montgomery_multiplication_ecdsa_module a b result =
  push_frame();
    let t = create (size 8) (u64 0) in 
    let round2 = create (size 8) (u64 0) in 
    let round4 = create (size 8) (u64 0) in  
    let prime_p256_orderBuffer = create (size 4) (u64 0) in 

    let k0 = upload_k0() in 

      let h0 = ST.get() in     
    mul a b t;
      assert_by_tactic (as_nat h0 b * as_nat h0 a == as_nat h0 a * as_nat h0 b) canon;
      mul_lemma_ (as_nat h0 a) (as_nat h0 b) prime_p256_order;
   montgomery_multiplication_round_twice t round2 k0; 
     let h2 = ST.get() in 
   montgomery_multiplication_round_twice round2 round4 k0; 
     lemma_mod_mul_distr_l (wide_as_nat h2 round2) (modp_inv2_prime (pow2 128) prime_p256_order) prime_p256_order;
     lemma_mod_mul_distr_l (as_nat h0 a * as_nat h0 b * modp_inv2_prime (pow2 128) prime_p256_order) (modp_inv2_prime (pow2 128) prime_p256_order) prime_p256_order; 
     lemma_montgomery_mod_inverse_addition2 (as_nat h0 a * as_nat h0 b);
     
     lemma_montgomery_mult_result_less_than_prime_p256_order (as_nat h0 a) (as_nat h0 b) (uint_v k0);
   reduction_prime_2prime_with_carry round4 result;  
     
     lemmaFromDomainToDomain (as_nat h0 a);
     lemmaFromDomainToDomain (as_nat h0 b);
     multiplicationInDomain #(fromDomain_ (as_nat h0 a)) #(fromDomain_ (as_nat h0 b)) (as_nat h0 a) (as_nat h0 b);
     inDomain_mod_is_not_mod (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b));
    pop_frame()



let felem_add arg1 arg2 out = 
  let open Hacl.Impl.LowLevel in 
  let t = add4 arg1 arg2 out in 
  reduction_prime_2prime_with_carry2 t out out


let lemma_felem_add a b = 
  lemmaFromDomain a;
  lemmaFromDomain b;
  lemmaFromDomain (a + b);
  assert(fromDomain_ a + fromDomain_ b = (a * modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order + (b * modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order);
  let aD = a * modp_inv2_prime (pow2 256) prime_p256_order in 
  let bD = b * modp_inv2_prime (pow2 256) prime_p256_order in 
  assert(fromDomain_ (a + b) = (aD + bD) % prime_p256_order);

  lemma_mod_plus_distr_l aD bD prime_p256_order;
  lemma_mod_plus_distr_l bD (aD % prime_p256_order) prime_p256_order;
  assert(fromDomain_ (a + b) = (aD % prime_p256_order + bD % prime_p256_order) % prime_p256_order);

  assert(fromDomain_ (a + b) = (fromDomain_ a + fromDomain_ b) % prime_p256_order)
