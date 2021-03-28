module Hacl.Impl.ECDSA.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas

open Hacl.Impl.EC.Setup

open Hacl.Lemmas.P256
open Hacl.Spec.ECDSA.Definition
open Hacl.Impl.EC.LowLevel 
open Hacl.Impl.EC.MontgomeryMultiplication

open FStar.Tactics
open FStar.Tactics.Canon 

open Hacl.Impl.EC.Masking
open Hacl.Spec.EC.Definition
open FStar.Mul
open Lib.IntTypes.Intrinsics

open Hacl.Impl.ECDSA.LowLevel



#reset-options "--z3rlimit 200"

val lemma_montgomery_mult_1: #c: curve ->
  t : int  -> 
  k0:nat {k0 = min_one_prime (pow2 64) (- prime)} -> 
  r: nat {t <= r} -> 
  Lemma (
    let order = getOrder #c in 
    (t + (((t % pow2 64) * k0) % pow2 64 * order)) / pow2 64 <= (pow2 64 * order + r) / pow2 64)

let lemma_montgomery_mult_1 #c t k0 r = 
  let order = getOrder #c in 
  let t1 = t % pow2 64 in 
  let y = (t1 * k0) % pow2 64 in 
  mul_lemma_1 y (pow2 64) order


val lemma_montgomery_mult_result_less_than_prime_p256_order: 
  #c: curve -> 
  a: nat{a < getOrder #c} -> 
  b: nat{b < getOrder #c} -> 
  k0:nat {k0 = min_one_prime (pow2 64) (- prime)} -> 
  Lemma
  (  
    let order = getOrder #c in 
    
    let t = a * b in 
    let s = 64 in 
  
    let t1 = t % pow2 s in 
    let y = (t1 * k0) % pow2 s in 
    let t2 = y * order in 
    let t3 = t + t2 in
    let t = t3 / pow2 s in 
  
    let t1 = t % pow2 s in 
    let y = (t1 * k0) % pow2 s in 
    let t2 = y * order in 
    let t3 = t + t2 in
    let t = t3 / pow2 s in 
  
    let t1 = t % pow2 s in 
    let y = (t1 * k0) % pow2 s in 
    let t2 = y * order in 
    let t3 = t + t2 in
    let t = t3 / pow2 s in 
    
    let t1 = t % pow2 s in 
    let y = (t1 * k0) % pow2 s in 
    let t2 = y * order in 
    let t3 = t + t2 in
    let t = t3 / pow2 s in 
    t < 2 * order)


let lemma_montgomery_mult_result_less_than_prime_p256_order #c a b k0 = 
  let order = getOrder #c in 
  
  let t = a * b in 
  let s = 64 in 
    mul_lemma_ a b order;

  let r = order * order + 1 in 

  let t1 = t % pow2 s in 
  let y = (t1 * k0) % pow2 s in 
  let t2 = y * order in 
  let t3 = t + t2 in
  let tU = t3 / pow2 s in 
  lemma_montgomery_mult_1 #c t k0 r; 

  let t = tU in 
  let r = (pow2 64 * order + r) / pow2 64 in 
  let t1 = t % pow2 s in 
  let y = (t1 * k0) % pow2 s in 
  let t2 = y * order in 
  let t3 = t + t2 in
  let tU = t3 / pow2 s in 
  lemma_montgomery_mult_1 #c t k0 r; 

  let t = tU in 
  let r = (pow2 64 * order + r) / pow2 64 in 
  let t1 = t % pow2 s in 
  let y = (t1 * k0) % pow2 s in 
  let t2 = y * order in 
  let t3 = t + t2 in
  let tU = t3 / pow2 s in 
  lemma_montgomery_mult_1 #c t k0 r; 

  let r = (pow2 64 * order + r) / pow2 64 in 
  let t = tU in 
  let t1 = t % pow2 s in 
  let y = (t1 * k0) % pow2 s in 
  let t2 = y * order in 
  let t3 = t + t2 in
  let tU = t3 / pow2 s in 
  lemma_montgomery_mult_1 #c t k0 r; 

  let order = getOrder #c in 
  let orderP256 = getOrder #P256 in 
  let orderP384 = getOrder #P384 in 

  assert_norm ((pow2 64 * orderP256 + (pow2 64 * orderP256 + (pow2 64 * orderP256 + (pow2 64 * orderP256 + orderP256 * orderP256 + 1) / pow2 64) / pow2 64) / pow2 64) / pow2 64 < 2 * orderP256);

  admit()
  
let prime_p256_order = getOrder #P256

val lemma_montgomery_mod_inverse_addition: a: nat -> 
  Lemma (
    (a * modp_inv2_prime(pow2 64) (getOrder #P256)  * modp_inv2_prime (pow2 64) prime_p256_order) % (getOrder #P256) == 
    (a * modp_inv2_prime(pow2 128) prime_p256_order) % prime_p256_order)

let lemma_montgomery_mod_inverse_addition a =
    assert_norm ((modp_inv2_prime(pow2 64) (getOrder #P256) * modp_inv2_prime (pow2 64) prime_p256_order) % (getOrder #P256) == modp_inv2_prime (pow2 128) (getOrder #P256) % prime_p256_order);
    assert_by_tactic ((a * modp_inv2_prime (pow2 64) (getOrder #P256) * modp_inv2_prime (pow2 64) prime_p256_order)  == (a * (modp_inv2_prime (pow2 64) (getOrder #P256) * modp_inv2_prime (pow2 64) prime_p256_order))) canon;
    lemma_mod_mul_distr_r a (modp_inv2_prime (pow2 64) (getOrder #P256) * modp_inv2_prime (pow2 64) prime_p256_order) prime_p256_order; 
    lemma_mod_mul_distr_r a (modp_inv2_prime (pow2 128) prime_p256_order) prime_p256_order


val lemma_montgomery_mod_inverse_addition2: a: int -> 
  Lemma ( 
    (a * modp_inv2_prime (pow2 128) (getOrder #P256)  * modp_inv2_prime (pow2 128) prime_p256_order) % (getOrder #P256) == 
    (a * modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order)

let lemma_montgomery_mod_inverse_addition2 a = 
  assert_norm ((modp_inv2_prime (pow2 128) (getOrder #P256) * modp_inv2_prime (pow2 128) prime_p256_order) % (getOrder #P256) == (modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order);
    assert_by_tactic ((a * modp_inv2_prime (pow2 128) (getOrder #P256) * modp_inv2_prime (pow2 128) prime_p256_order)  == (a * (modp_inv2_prime (pow2 128) (getOrder #P256) * modp_inv2_prime (pow2 128) prime_p256_order))) canon;
    lemma_mod_mul_distr_r a (modp_inv2_prime (pow2 128) (getOrder #P256) * modp_inv2_prime (pow2 128) prime_p256_order) prime_p256_order; 
    lemma_mod_mul_distr_r a (modp_inv2_prime (pow2 256) prime_p256_order) prime_p256_order


val montgomery_multiplication_one_round_proof: 
  t: nat ->
  k0: nat {k0 = min_one_prime (pow2 64) (- prime)}  ->  
  round: nat {round = (t + (getOrder #P256) * ((k0 * (t % pow2 64)) % pow2 64)) / pow2 64} -> 
  co: nat {co % (getOrder #P256) = t % prime_p256_order} -> 
  Lemma (round  % (getOrder #P256) == co * (modp_inv2_prime (pow2 64) prime_p256_order) % prime_p256_order)

let montgomery_multiplication_one_round_proof t k0 round co = 
  mult_one_round_ecdsa_prime t (getOrder #P256) co k0

#reset-options "--z3rlimit 700"

val montgomery_multiplication_round: #c: curve -> t: widefelem c 
  ->  round: widefelem c -> k0: uint64 ->
  Stack unit 
    (requires fun h -> live h t /\ live h round  /\ wide_as_nat c h t < (getOrder #P256) * prime_p256_order)
    (ensures fun h0 _ h1 -> modifies (loc round) h0 h1 /\ 
      wide_as_nat c h1 round = (wide_as_nat c h0 t + (getOrder #P256) * ((uint_v k0 * (wide_as_nat c h0 t % pow2 64)) % pow2 64)) / pow2 64)

let montgomery_multiplication_round #c t round k0 = 
  push_frame(); 
    let h0 = ST.get() in 
    let len = getCoordinateLenU64 c in 
    
    let temp = create (size 1) (u64 0) in 
    let y = create (size 1) (u64 0) in 

    let t2 = create (size 2 *! len) (u64 0) in 
    let t3 = create (size 2 *! len) (u64 0) in 
    let t1 = mod64 #c t in
    
    mul_atomic t1 k0 y temp;
    (* recall_contents (order_buffer #c)  (Lib.Sequence.of_list (Hacl.Spec.ECC.Definition.order_list c)); *)
    let y_ = index y (size 0) in   
    short_mul_bn #c order_buffer y_ t2;
    (* add_long_without_carry #c t t2 t3; *)
    (* shift1 #c t3 round; *)
    admit();
  pop_frame()


#reset-options "--z3rlimit 200"
(*
val montgomery_multiplication_round_twice: #c: curve -> t: widefelem c 
  -> result: widefelem c -> k0: uint64-> 
  Stack unit 
    (requires fun h -> live h t /\ live h result /\ uint_v k0 = min_one_prime (pow2 64) (- prime) /\
      wide_as_nat c h t < (getOrder #P256) * prime_p256_order)
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
      wide_as_nat c h1 result % (getOrder #P256) == (wide_as_nat c h0 t * modp_inv2_prime (pow2 128) prime_p256_order) % (getOrder #P256) /\
      (
	let round = (wide_as_nat c h0 t + (getOrder #P256) * ((uint_v k0 * (wide_as_nat c h0 t % pow2 64)) % pow2 64)) / pow2 64 in 
	wide_as_nat c h1 result == (round + (getOrder #P256) * ((uint_v k0 * (round % pow2 64)) % pow2 64)) / pow2 64)  /\
	wide_as_nat c h1 result < (getOrder #P256) * prime_p256_order
      )
    
let montgomery_multiplication_round_twice #c t result k0 = 
   push_frame();
     let len = getCoordinateLenU64 c in 
     let tempRound = create (size 2 *! len) (u64 0) in 
       let h0 = ST.get() in 
   montgomery_multiplication_round #c t tempRound k0; 
       let h1 = ST.get() in 
   montgomery_multiplication_one_round_proof (wide_as_nat c h0 t) (uint_v k0) (wide_as_nat c h1 tempRound) (wide_as_nat c h0 t);
   montgomery_multiplication_round #c tempRound result k0; 
      let h2 = ST.get() in 
   montgomery_multiplication_one_round_proof (wide_as_nat c h1 tempRound) (uint_v k0) (wide_as_nat c h2 result) (wide_as_nat c h0 t * modp_inv2_prime (pow2 64) prime_p256_order); 
   lemma_montgomery_mod_inverse_addition (wide_as_nat c h0 t); 
  pop_frame()
*)

let reduction_prime_2prime_with_carry #c x result  = 
  match c with 
  |P384 -> admit()
  |P256 -> 
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 == pow2 256);
    push_frame();
      let h0 = ST.get() in 
      let tempBuffer = create (size 4) (u64 0) in 
      let tempBufferForSubborrow = create (size 1) (u64 0) in 
      let cin = Lib.Buffer.index x (size 4) in 
      let x_ = Lib.Buffer.sub x (size 0) (size 4) in 
          recall_contents prime256order_buffer (Lib.Sequence.of_list (order_list P256));
      let c = Hacl.Impl.P256.LowLevel.sub4_il x_ prime256order_buffer tempBuffer in
	let h1 = ST.get() in 

	assert(if uint_v c = 0 then 
	  as_nat P256 h0 x_ >= (getOrder #P256) 
	  else as_nat P256 h0 x_ < prime_p256_order);
	assert(wide_as_nat P256 h0 x = as_nat P256 h0 x_ + uint_v cin * pow2 256);
      let carry = sub_borrow_u64 c cin (u64 0) tempBufferForSubborrow in 
      let h2 = ST.get() in 
      assert(if (as_nat P256 h0 x_ >= prime_p256_order) then uint_v carry = 0 
	else if uint_v cin < uint_v c then uint_v carry = 1 
	else uint_v carry = 0); 

    cmovznz4 #P256 carry tempBuffer x_ result;
 pop_frame()   


let reduction_prime_2prime_with_carry2 #cu cin x result  = 
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 == pow2 256);
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in 
    let tempBufferForSubborrow = create (size 1) (u64 0) in 
        recall_contents prime256order_buffer (Lib.Sequence.of_list (order_list P256));
    let c = Hacl.Impl.P256.LowLevel .sub4_il x prime256order_buffer tempBuffer in
    let carry = sub_borrow_u64 c cin (u64 0) tempBufferForSubborrow in 
    cmovznz4 #cu carry tempBuffer x result;
 pop_frame()      


val lemma_reduction1: a: nat {a < pow2 256} -> r: nat{if a >= (getOrder #P256) then r = a - (getOrder #P256) else r = a} -> 
  Lemma (r = a % prime_p256_order)

let lemma_reduction1 a r = 
  let prime256 = (getOrder #P256) in 
  assert_norm (pow2 256 - (getOrder #P256) < prime_p256_order)


let reduction_prime_2prime_order #cu x result  = 
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in 
    recall_contents prime256order_buffer (Lib.Sequence.of_list (order_list P256));
      let h0 = ST.get() in 
    let c = sub4_il x prime256order_buffer tempBuffer in
      let h1 = ST.get() in 
      assert(as_nat c h1 tempBuffer = as_nat c h0 x - (getOrder #P256) + uint_v c * pow2 256);
      assert(let x = as_nat c h0 x in if x < (getOrder #P256) then uint_v c = 1 else uint_v c = 0);
    cmovznz4 #cu c tempBuffer x result; 
    let h2 = ST.get() in 
      assert_norm (pow2 256 == pow2 64 * pow2 64 * pow2 64 * pow2 64);
    lemma_reduction1 (as_nat c h0 x) (as_nat c h2 result);
  pop_frame()  
  

inline_for_extraction noextract
val upload_k0: unit ->  Tot (r: uint64 {uint_v r == min_one_prime (pow2 64) (- prime)})

let upload_k0 () = 
  assert_norm(min_one_prime (pow2 64) (- prime) == 14758798090332847183);
  (u64 14758798090332847183)


let fromDomain_ a = (a * modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order

let toDomain_ a = (a * pow2 256) % (getOrder #P256) 

let lemmaFromDomain a = ()

let lemmaToDomain a = ()

let lemmaFromDomainToDomain a = 
   let fromA = (a * modp_inv2_prime (pow2 256) prime_p256_order) % (getOrder #P256) in 
   let toFromA = (((a * modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order) * pow2 256) % (getOrder #P256) in 
   lemma_mod_mul_distr_l (a * modp_inv2_prime (pow2 256) prime_p256_order) (pow2 256) prime_p256_order;
     assert_by_tactic (a * (modp_inv2_prime (pow2 256) (getOrder #P256) * pow2 256) = a * modp_inv2_prime (pow2 256) (getOrder #P256) * pow2 256) canon;
   lemma_mod_mul_distr_r a (modp_inv2_prime (pow2 256) (getOrder #P256) * pow2 256) prime_p256_order; 
   assert_norm((modp_inv2_prime (pow2 256) (getOrder #P256) * pow2 256) % (getOrder #P256) == 1);
   small_modulo_lemma_1 a prime_p256_order


val multiplicationInDomain: #k: nat -> #l: nat -> 
  a: nat {a == toDomain_ (k) /\ a < prime} -> 
  b: nat {b == toDomain_ (l) /\ b < prime} -> 
  Lemma  ((a *  b * modp_inv2_prime (pow2 256) prime) % (getOrder #P256) == toDomain_ (k * l))

let multiplicationInDomain #k #l a b = 
  let f = a * b * modp_inv2_prime (pow2 256) prime in 
  let z = toDomain_ (k * l) in 
  assert_by_tactic (((k * pow2 256) % prime_p256_order) * ((l * pow2 256) % prime_p256_order) * modp_inv2_prime (pow2 256) prime = 
    ((k * pow2 256) % prime_p256_order) * (((l * pow2 256) % prime_p256_order) * modp_inv2_prime (pow2 256) prime)) canon;
  lemma_mod_mul_distr_l (k * pow2 256) (((l * pow2 256) % prime_p256_order) * modp_inv2_prime (pow2 256) prime) prime_p256_order;
  assert_by_tactic (
    ((k * pow2 256) * (((l * pow2 256) % prime_p256_order) * modp_inv2_prime (pow2 256) prime)) % (getOrder #P256) = 
    ((((l * pow2 256) % prime_p256_order) * (((k * pow2 256) * modp_inv2_prime (pow2 256) prime)) % prime_p256_order))) canon;
  lemma_mod_mul_distr_l (l * pow2 256)  ((k * pow2 256) * modp_inv2_prime (pow2 256) prime) prime_p256_order;
  assert_by_tactic ( ((l * pow2 256 * ((k * pow2 256) * modp_inv2_prime (pow2 256) prime))) == 
     ((l * pow2 256 * k) * (pow2 256 * modp_inv2_prime (pow2 256) prime))) canon;
  lemma_mod_mul_distr_r (l * pow2 256 * k) (pow2 256 * modp_inv2_prime (pow2 256) prime) prime_p256_order;
  assert_norm ((pow2 256 * modp_inv2_prime (pow2 256) prime) % (getOrder #P256) == 1);
  assert_by_tactic ((l * pow2 256 * k) == ((k * l) * pow2 256)) canon
  

val inDomain_mod_is_not_mod: a: nat -> Lemma (toDomain_ a == toDomain_ (a % prime_p256_order))

let inDomain_mod_is_not_mod a = 
   lemma_mod_mul_distr_l a (pow2 256) prime_p256_order


let lemmaToDomainFromDomain a = 
  let to = (a * pow2 256) % (getOrder #P256) in 
  let from_to = ((((a * pow2 256) % prime_p256_order) * modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order) in 
  lemma_mod_mul_distr_l (a * pow2 256) (modp_inv2_prime (pow2 256) prime_p256_order) prime_p256_order;
  assert_by_tactic ((a * pow2 256) * modp_inv2_prime (pow2 256) (getOrder #P256) == a * (pow2 256 * modp_inv2_prime (pow2 256) prime_p256_order)) canon;
  lemma_mod_mul_distr_r a (pow2 256 * modp_inv2_prime (pow2 256) prime_p256_order) prime_p256_order;
  assert_norm ((pow2 256 * modp_inv2_prime (pow2 256) prime_p256_order) % (getOrder #P256) == 1)


#reset-options "--z3rlimit 200"

let montgomery_multiplication_ecdsa_module #c  a b result =
  (* Most probably it's gonna be like this *)
  push_frame();
    let len = getCoordinateLenU64 c in 
    let t = create (size 2 *! len) (u64 0) in 
    let prime_p256_orderBuffer = create len (u64 0) in 

    let k0 = upload_k0() in 

      let h0 = ST.get() in     
    mul #c a b t;
    montgomery_multiplication_round #c t t k0;
    montgomery_multiplication_round #c t t k0;
    montgomery_multiplication_round #c t t k0;
    montgomery_multiplication_round #c t t k0;


(*       assert_by_tactic (as_nat c h0 b * as_nat c h0 a == as_nat c h0 a * as_nat c h0 b) canon;
      mul_lemma_ (as_nat c h0 a) (as_nat c h0 b) prime_p256_order;
   montgomery_multiplication_round_twice #P256 t round2 k0; 
     let h2 = ST.get() in 
   montgomery_multiplication_round_twice #P256 round2 round4 k0; 
     lemma_mod_mul_distr_l (wide_as_nat c h2 round2) (modp_inv2_prime (pow2 128) prime_p256_order) prime_p256_order;
     lemma_mod_mul_distr_l (as_nat c h0 a * as_nat c h0 b * modp_inv2_prime (pow2 128) prime_p256_order) (modp_inv2_prime (pow2 128) prime_p256_order) prime_p256_order; 
     lemma_montgomery_mod_inverse_addition2 (as_nat c h0 a * as_nat c h0 b);
     
     lemma_montgomery_mult_result_less_than_prime_p256_order (as_nat c h0 a) (as_nat c h0 b) (uint_v k0);  
   reduction_prime_2prime_with_carry t result;  
     
     lemmaFromDomainToDomain (as_nat c h0 a);
     lemmaFromDomainToDomain (as_nat c h0 b);
     multiplicationInDomain #(fromDomain_ (as_nat c h0 a)) #(fromDomain_ (as_nat c h0 b)) (as_nat c h0 a) (as_nat c h0 b);
     inDomain_mod_is_not_mod (fromDomain_ (as_nat c h0 a) * fromDomain_ (as_nat c h0 b)); *)
    pop_frame()



