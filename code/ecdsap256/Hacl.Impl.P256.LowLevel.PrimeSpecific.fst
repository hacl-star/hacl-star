module Hacl.Impl.P256.LowLevel.PrimeSpecific

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.P256.Definitions
open Spec.P256.Lemmas
open Hacl.Spec.P256.MontgomeryMultiplication

open Hacl.Impl.P256.LowLevel 

open FStar.Math.Lemmas

open FStar.Mul
open Lib.IntTypes.Intrinsics

#reset-options " --z3rlimit 300"


inline_for_extraction
let prime256_buffer: x: glbuffer uint64 4ul {witnessed #uint64 #(size 4) x (Lib.Sequence.of_list p256_prime_list) /\ recallable x /\ felem_seq_as_nat (Lib.Sequence.of_list (p256_prime_list)) == prime256} = 
  assert_norm (felem_seq_as_nat (Lib.Sequence.of_list (p256_prime_list)) == prime256);
  createL_global p256_prime_list


inline_for_extraction noextract
val reduction_prime256_2prime256_with_carry_impl: cin: uint64 -> x: felem -> result: felem ->
  Stack unit 
    (requires fun h -> live h x /\ live h result /\  eq_or_disjoint x result /\ 
      (as_nat h x + uint_v cin * pow2 256) < 2 * prime256)
    (ensures fun h0 _ h1 -> 
      modifies (loc result) h0 h1 /\ 
      as_nat h1 result = (as_nat h0 x + uint_v cin * pow2 256) % prime256
    )  


let reduction_prime256_2prime256_with_carry_impl cin x result = 
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in 
    let tempBufferForSubborrow = create (size 1) (u64 0) in
    recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list);
    let c = sub4_il x prime256_buffer tempBuffer in
  let h0 = ST.get() in 
      assert(uint_v c <= 1);
      assert(if uint_v c = 0 then as_nat h0 x >= prime256 else as_nat h0 x < prime256);
    let carry = sub_borrow_u64 c cin (u64 0) tempBufferForSubborrow in 
    cmovznz4 carry tempBuffer x result;
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


inline_for_extraction
val reduction_prime256_2prime256_8_with_carry_impl: x: widefelem -> result: felem -> 
  Stack unit 
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result /\ wide_as_nat h x < 2 * prime256)
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 result = wide_as_nat h0 x % prime256)

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
    let c = Hacl.Impl.P256.LowLevel .sub4_il x_ prime256_buffer tempBuffer in 
    let carry = sub_borrow_u64 c cin (u64 0) tempBufferForSubborrow in 
    cmovznz4 carry tempBuffer x_ result; 
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

val lemma_reduction1_0: a: nat {a < pow2 256 /\ a >= prime256} -> r: nat{r = a - prime256} -> 
  Lemma (r = a % prime256)

let lemma_reduction1_0 a r = 
  assert_norm (pow2 256 - prime256 < prime256);
  small_modulo_lemma_1 r prime256; 
  lemma_mod_sub_distr a prime256 prime256


val lemma_reduction1: a: nat {a < pow2 256} -> r: nat{if a >= prime256 then r = a - prime256 else r = a} ->
  Lemma (r = a % prime256)

let lemma_reduction1 a r = 
  if a >= prime256 then
   lemma_reduction1_0 a r
  else
    small_mod r prime256


val reduction_prime_2prime_impl: x: felem -> result: felem -> 
  Stack unit
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 result == as_nat h0 x % prime256)

let reduction_prime_2prime_impl x result = 
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  push_frame();
  let tempBuffer = create (size 4) (u64 0) in 
    recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list);
        let h0 = ST.get() in 
    let c = sub4_il x prime256_buffer tempBuffer in 
    cmovznz4 c tempBuffer x result;
      let h2 = ST.get() in 
    lemma_reduction1 (as_nat h0 x) (as_nat h2 result);
  pop_frame()  


val lemma_t_computation: t: uint64 {uint_v t == 0 \/ uint_v t == 1} ->
  Lemma
    (
      let t0 = (u64 0) -. t in 
      let t1 = ((u64 0) -. t) >>. (size 32) in 
      let t2 = u64 0 in 
      let t3 = t -. (t <<. (size 32)) in 
      let s = uint_v t0 + uint_v t1 * pow2 64 + uint_v t2 * pow2 128 + uint_v t3 * pow2 192 in 
      if uint_v t = 1 then s == prime256 else s == 0
    )

let lemma_t_computation t = 
  let t0 = (u64 0) -. t in 
  let t1 = ((u64 0) -. t) >>. (size 32) in 
  let t2 = u64 0 in 
  let t3 = t -. (t <<. (size 32)) in 
  let s = uint_v t0 + uint_v t1 * pow2 64 + uint_v t2 * pow2 128 + uint_v t3 * pow2 192 in  
  assert_norm(18446744073709551615 + 4294967295 * pow2 64 + 18446744069414584321 * pow2 192 = prime256)


val p256_add: arg1: felem -> arg2: felem ->  out: felem -> Stack unit 
  (requires (fun h0 ->  
    live h0 arg1 /\ live h0 arg2 /\ live h0 out /\ 
    eq_or_disjoint arg1 out /\ eq_or_disjoint arg2 out /\
    as_nat h0 arg1 < prime256 /\ as_nat h0 arg2 < prime256 
   )
  )
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
      as_nat h1 out == (as_nat h0 arg1 + as_nat h0 arg2) % prime256 /\
      as_nat h1 out == toDomain_ ((fromDomain_ (as_nat h0 arg1) + fromDomain_ (as_nat h0 arg2)) % prime256)
    )
  )


let p256_add arg1 arg2 out = 
  let h0 = ST.get() in   
  let t = add4 arg1 arg2 out in 
  reduction_prime256_2prime256_with_carry_impl t out out;
  additionInDomain (as_nat h0 arg1) (as_nat h0 arg2);
  inDomain_mod_is_not_mod (fromDomain_ (as_nat h0 arg1) + fromDomain_ (as_nat h0 arg2))


val p256_double: arg1: felem ->  out: felem -> Stack unit 
  (requires (fun h0 ->  live h0 arg1 /\ live h0 out /\ eq_or_disjoint arg1 out /\ as_nat h0 arg1 < prime256))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
    as_nat h1 out == (2 * as_nat h0 arg1) % prime256 /\ as_nat h1 out < prime256 /\
    as_nat h1 out == toDomain_ (2 * fromDomain_ (as_nat h0 arg1) % prime256)
  )
)

let p256_double arg1 out = 
    let h0 = ST.get() in 
  let t = add4 arg1 arg1 out in 
  reduction_prime256_2prime256_with_carry_impl t out out;
  additionInDomain (as_nat h0 arg1) (as_nat h0 arg1);
  inDomain_mod_is_not_mod (fromDomain_ (as_nat h0 arg1) + fromDomain_ (as_nat h0 arg1))


val p256_sub: arg1: felem -> arg2: felem -> out: felem -> Stack unit 
  (requires 
    (fun h0 -> live h0 out /\ live h0 arg1 /\ live h0 arg2 /\ 
      eq_or_disjoint arg1 out /\ eq_or_disjoint arg2 out /\
      as_nat h0 arg1 < prime256 /\ as_nat h0 arg2 < prime256))
    (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
	as_nat h1 out == (as_nat h0 arg1 - as_nat h0 arg2) % prime256 /\
	as_nat h1 out == toDomain_ ((fromDomain_ (as_nat h0 arg1) - fromDomain_ (as_nat h0 arg2)) % prime256)
    )
)    

let p256_sub arg1 arg2 out = 
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    let h0 = ST.get() in 
  let t = sub4 arg1 arg2 out in 
    let h1 = ST.get() in 
    lemma_t_computation t;
  let t0 = (u64 0) -. t in 
  let t1 = ((u64 0) -. t) >>. (size 32) in 
  let t2 = u64 0 in 
  let t3 = t -. (t <<. (size 32)) in 
    modulo_addition_lemma  (as_nat h0 arg1 - as_nat h0 arg2) prime256 1;
  let c = add4_variables out (u64 0)  t0 t1 t2 t3 out in 
    let h2 = ST.get() in 
      assert(
      if as_nat h0 arg1 - as_nat h0 arg2 >= 0 then 
	begin
	  modulo_lemma (as_nat h0 arg1 - as_nat h0 arg2) prime256;
	  as_nat h2 out == (as_nat h0 arg1 - as_nat h0 arg2) % prime256
	end
      else
          begin
	    modulo_lemma (as_nat h2 out) prime256;
            as_nat h2 out == (as_nat h0 arg1 - as_nat h0 arg2) % prime256
	  end);
    substractionInDomain (felem_seq_as_nat (as_seq h0 arg1)) (felem_seq_as_nat (as_seq h0 arg2));
    inDomain_mod_is_not_mod (fromDomain_ (felem_seq_as_nat (as_seq h0 arg1)) - fromDomain_ (felem_seq_as_nat (as_seq h0 arg2)))

