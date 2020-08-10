module Hacl.Impl.P.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definition
open Hacl.Lemmas.P256
(* open Spec.ECDSA.Lemmas *)
open Spec.P256
open Spec.ECDSA

open FStar.Math
open FStar.Math.Lemmas
open FStar.Mul

open FStar.Tactics
open FStar.Tactics.Canon 

(* open Spec.P256.Lemmas *)
open Lib.IntTypes.Intrinsics

open Hacl.Impl.P256.LowLevel
open Hacl.Impl.P384.LowLevel


#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

let uploadZeroImpl #c f = 
  match c with 
  |P384 -> 
    upd f (size 0) (u64 0);
    upd f (size 1) (u64 0);
    upd f (size 2) (u64 0);
    upd f (size 3) (u64 0);
    upd f (size 4) (u64 0);
    upd f (size 5) (u64 0)
  |P256 ->   
    upd f (size 0) (u64 0);
    upd f (size 1) (u64 0);
    upd f (size 2) (u64 0);
    upd f (size 3) (u64 0)


let uploadZeroPoint #c p = 
  match c with 
  |P256 -> 
    upd p (size 0) (u64 0);
    upd p (size 1) (u64 0);
    upd p (size 2) (u64 0);
    upd p (size 3) (u64 0);
    upd p (size 4) (u64 0);
    upd p (size 5) (u64 0);
    upd p (size 6) (u64 0);
    upd p (size 7) (u64 0);
    upd p (size 8) (u64 0);
    upd p (size 9) (u64 0);
    upd p (size 10) (u64 0);
    upd p (size 11) (u64 0)
  |P384 -> 
    upd p (size 0) (u64 0);
    upd p (size 1) (u64 0);
    upd p (size 2) (u64 0);
    upd p (size 3) (u64 0);
    upd p (size 4) (u64 0);
    upd p (size 5) (u64 0);
    upd p (size 6) (u64 0);
    upd p (size 7) (u64 0);
    upd p (size 8) (u64 0);
    upd p (size 9) (u64 0);
    upd p (size 10) (u64 0);
    upd p (size 11) (u64 0);
    upd p (size 12) (u64 0);
    upd p (size 13) (u64 0);
    upd p (size 14) (u64 0);
    upd p (size 15) (u64 0);
    upd p (size 16) (u64 0);
    upd p (size 17) (u64 0)


let cmovznz4 #c  cin x y r =  
  match c with 
  |P256 ->
    let h0 = ST.get() in 
  
    let mask = neq_mask cin (u64 0) in 
    let r0 = logor (logand y.(size 0) mask) (logand x.(size 0) (lognot mask)) in 
    let r1 = logor (logand y.(size 1) mask) (logand x.(size 1) (lognot mask)) in 
    let r2 = logor (logand y.(size 2) mask) (logand x.(size 2) (lognot mask)) in 
    let r3 = logor (logand y.(size 3) mask) (logand x.(size 3) (lognot mask)) in 
    
    upd r (size 0) r0;
    upd r (size 1) r1;
    upd r (size 2) r2;
    upd r (size 3) r3;

    let x = as_seq h0 x in 
    let y = as_seq h0 y in 
      
    cmovznz4_lemma cin (Seq.index x 0) (Seq.index y 0);
    cmovznz4_lemma cin (Seq.index x 1) (Seq.index y 1);
    cmovznz4_lemma cin (Seq.index x 2) (Seq.index y 2);
    cmovznz4_lemma cin (Seq.index x 3) (Seq.index y 3)
  |P384 -> 
      let h0 = ST.get() in 
      
      let mask = neq_mask cin (u64 0) in 
      let r0 = logor (logand y.(size 0) mask) (logand x.(size 0) (lognot mask)) in 
      let r1 = logor (logand y.(size 1) mask) (logand x.(size 1) (lognot mask)) in 
      let r2 = logor (logand y.(size 2) mask) (logand x.(size 2) (lognot mask)) in 
      let r3 = logor (logand y.(size 3) mask) (logand x.(size 3) (lognot mask)) in 
      let r4 = logor (logand y.(size 4) mask) (logand x.(size 4) (lognot mask)) in 
      let r5 = logor (logand y.(size 5) mask) (logand x.(size 5) (lognot mask)) in 
      
      upd r (size 0) r0;
      upd r (size 1) r1;
      upd r (size 2) r2;
      upd r (size 3) r3;
      upd r (size 4) r4;
      upd r (size 5) r5;

      let x = as_seq h0 x in 
      let y = as_seq h0 y in 
	
      cmovznz4_lemma cin (Seq.index x 0) (Seq.index y 0);
      cmovznz4_lemma cin (Seq.index x 1) (Seq.index y 1);
      cmovznz4_lemma cin (Seq.index x 2) (Seq.index y 2);
      cmovznz4_lemma cin (Seq.index x 3) (Seq.index y 3);
      cmovznz4_lemma cin (Seq.index x 4) (Seq.index y 4);
      cmovznz4_lemma cin (Seq.index x 5) (Seq.index y 5)





let sub_felem #c x y result = 
  match c with 
  |P256 -> sub4_il x y result
  |P384 -> admit()





  
let uploadOneImpl #c f = 
  match c with 
  |P384 -> ()
  |P256 -> 
    upd f (size 0) (u64 1);
    upd f (size 1) (u64 0);
    upd f (size 2) (u64 0);
    upd f (size 3) (u64 0)


let toUint8P256 i o = 
  Lib.ByteBuffer.uints_to_bytes_be (getCoordinateLenU64 P256) o i


let toUint8P384 i o = 
  Lib.ByteBuffer.uints_to_bytes_be (getCoordinateLenU64 P384) o i



let toUint8 #c i o = 
  match c with 
  |P256 -> toUint8P256 i o
  |P384 -> toUint8P384 i o

open Lib.ByteBuffer

let changeEndian #c i = 
  match c with 
  |P256 -> 
    assert_norm (pow2 64 * pow2 64 = pow2 (2 * 64));
    assert_norm (pow2 (2 * 64) * pow2 64 = pow2 (3 * 64));
    assert_norm (pow2 (3 * 64) * pow2 64 = pow2 (4 * 64));
    let zero =  index i (size 0) in 
    let one =   index i (size 1) in 
    let two =   index i (size 2) in 
    let three = index i (size 3) in 
    upd i (size 0) three;
    upd i (size 1) two; 
    upd i (size 2) one;
    upd i (size 3) zero
  |P384 -> 
    let zero =  index i (size 0) in 
    let one =   index i (size 1) in 
    let two =   index i (size 2) in 
    let three = index i (size 3) in 
    let four =  index i (size 4) in 
    let five =  index i (size 5) in 

    upd i (size 0) five;
    upd i (size 1) four;
    upd i (size 2) three;
    upd i (size 3) two;
    upd i (size 4) one;
    upd i (size 5) zero



let toUint64ChangeEndianP256 i o = 
  Lib.ByteBuffer.uints_from_bytes_be  o i;
  changeEndian o



let toUint64ChangeEndianP384 i o = 
  Lib.ByteBuffer.uints_from_bytes_be o i;
  changeEndian o


let toUint64ChangeEndian #c i o = 
  match c with 
    |P256 -> 
      toUint64ChangeEndianP256 i o
    |P384 ->
      toUint64ChangeEndianP384 i o
    




inline_for_extraction noextract
val reduction_prime256_2prime256_with_carry_impl: cin: uint64 -> x: felem P256 -> result: felem P256 ->
  Stack unit 
    (requires fun h -> live h x /\ live h result /\  eq_or_disjoint x result /\ 
      (as_nat P256 h x + uint_v cin * pow2 256) < 2 * prime256)
    (ensures fun h0 _ h1 -> 
      modifies (loc result) h0 h1 /\ 
      as_nat P256 h1 result = (as_nat P256 h0 x + uint_v cin * pow2 256) % prime256
    )  


let reduction_prime256_2prime256_with_carry_impl cin x result = 
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in 
    let tempBufferForSubborrow = create (size 1) (u64 0) in
    recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list);
    let c = sub4_il x prime256_buffer tempBuffer in
  let h0 = ST.get() in 
      assert(uint_v c <= 1);
      assert(if uint_v c = 0 then as_nat P256 h0 x >= prime256 else as_nat P256 h0 x < prime256);
    let carry = sub_borrow_u64 c cin (u64 0) tempBufferForSubborrow in 
    cmovznz4 carry tempBuffer x result;
  let h1 = ST.get() in 
      assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
      assert_norm (prime256 < pow2 256);
      assert_norm(pow2 256 < 2 * prime256);

      assert(uint_v cin <= 1);
      assert(uint_v c <= 1);

      assert(if as_nat P256 h0 x >= prime256 then uint_v c = 0 else True);
      assert(if uint_v cin < uint_v c then as_nat P256 h1 result == as_nat P256 h0 x else as_nat P256 h1 result == as_nat P256 h0 tempBuffer);

      assert(as_nat P256 h1 result < prime256);

      modulo_addition_lemma (as_nat P256 h1 result) prime256 1;
      small_modulo_lemma_1 (as_nat P256 h1 result) prime256; 
  pop_frame()   


let reduction_prime_2prime_with_carry #c x result = 
  match c with 
  |P384 -> ()
  |P256 -> 
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
      assert(if (wide_as_nat P256 h0 x < prime256) then begin
      small_modulo_lemma_1 (wide_as_nat P256 h0 x) prime256;
      as_nat P256 h4 result = (wide_as_nat P256 h0 x) % prime256 end 
      else 
  begin 
  small_modulo_lemma_1 (as_nat P256 h4 result) prime256;
  lemma_mod_sub (wide_as_nat P256 h0 x) prime256 1;
  as_nat  P256 h4 result = (wide_as_nat P256 h0 x) % prime256
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



let reduction_prime_2prime #c x result = 
  match c with 
  |P384 -> ()
  |P256 -> 
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  push_frame();
  let tempBuffer = create (size 4) (u64 0) in 
    recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list);
        let h0 = ST.get() in 
    let c = sub4_il x prime256_buffer tempBuffer in 
    cmovznz4 c tempBuffer x result;
      let h2 = ST.get() in 
    lemma_reduction1 (as_nat P256 h0 x) (as_nat P256 h2 result);
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


val p256_add: arg1: felem P256 -> arg2: felem P256 ->  out: felem P256 -> Stack unit 
  (requires (fun h0 ->  
    live h0 arg1 /\ live h0 arg2 /\ live h0 out /\ 
    eq_or_disjoint arg1 out /\ eq_or_disjoint arg2 out /\
    as_nat P256 h0 arg1 < prime256 /\ as_nat P256 h0 arg2 < prime256 
   )
  )
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
      as_nat P256 h1 out == (as_nat P256 h0 arg1 + as_nat P256 h0 arg2) % prime256 /\
      as_nat P256 h1 out == toDomain_ #P256 ((fromDomain_ #P256 (as_nat P256 h0 arg1) + fromDomain_ #P256 (as_nat P256 h0 arg2)) % prime256)
    )
  )


let p256_add arg1 arg2 out = 
  let h0 = ST.get() in   
  let t = add4 arg1 arg2 out in 
  reduction_prime256_2prime256_with_carry_impl t out out;
  additionInDomain #P256 (as_nat P256 h0 arg1) (as_nat P256 h0 arg2);
  inDomain_mod_is_not_mod #P256 (fromDomain_ #P256 (as_nat P256 h0 arg1) + fromDomain_ #P256 (as_nat P256 h0 arg2))



let felem_add #c a b out = 
  match c with 
  |P256 -> p256_add a b out
  |P384 -> admit()



val p256_double: arg1: felem P256 ->  out: felem P256 -> Stack unit 
  (requires (fun h0 ->  live h0 arg1 /\ live h0 out /\ eq_or_disjoint arg1 out /\ as_nat P256 h0 arg1 < prime256))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
    as_nat P256 h1 out == (2 * as_nat P256 h0 arg1) % prime256 /\ as_nat P256 h1 out < prime256 /\
    as_nat P256 h1 out == toDomain_ #P256 (2 * fromDomain_ #P256 (as_nat P256 h0 arg1) % prime256)
  )
)

let p256_double arg1 out = 
    let h0 = ST.get() in 
  let t = add4 arg1 arg1 out in 
  reduction_prime256_2prime256_with_carry_impl t out out;
  additionInDomain #P256 (as_nat P256 h0 arg1) (as_nat P256 h0 arg1);
  inDomain_mod_is_not_mod #P256 (fromDomain_ #P256 (as_nat P256 h0 arg1) + fromDomain_ #P256 (as_nat P256 h0 arg1))




let felem_double #c arg1 out = 
  match c with 
  |P256 -> p256_double arg1 out
  |P384 -> admit()


val p256_sub: arg1: felem P256 -> arg2: felem P256 -> out: felem P256 -> Stack unit 
  (requires 
    (fun h0 -> live h0 out /\ live h0 arg1 /\ live h0 arg2 /\ 
      eq_or_disjoint arg1 out /\ eq_or_disjoint arg2 out /\
      as_nat P256 h0 arg1 < prime256 /\ as_nat P256 h0 arg2 < prime256))
    (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
  as_nat P256 h1 out == (as_nat P256 h0 arg1 - as_nat P256 h0 arg2) % prime256 /\
  as_nat P256 h1 out == toDomain_ #P256 ((fromDomain_ #P256 (as_nat P256 h0 arg1) - fromDomain_ #P256 (as_nat P256 h0 arg2)) % prime256)
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
    modulo_addition_lemma  (as_nat P256 h0 arg1 - as_nat P256  h0 arg2) prime256 1;
  let c = add4_variables out (u64 0)  t0 t1 t2 t3 out in 
    let h2 = ST.get() in 
      assert(
      if as_nat P256 h0 arg1 - as_nat P256 h0 arg2 >= 0 then 
  begin
    modulo_lemma (as_nat P256 h0 arg1 - as_nat P256 h0 arg2) prime256;
    as_nat P256 h2 out == (as_nat P256 h0 arg1 - as_nat P256 h0 arg2) % prime256
  end
      else
          begin
      modulo_lemma (as_nat P256 h2 out) prime256;
            as_nat P256 h2 out == (as_nat P256 h0 arg1 - as_nat P256 h0 arg2) % prime256
    end);
    substractionInDomain #P256 (felem_seq_as_nat P256 (as_seq h0 arg1)) (felem_seq_as_nat P256 (as_seq h0 arg2));
    inDomain_mod_is_not_mod #P256 (fromDomain_ #P256 (felem_seq_as_nat P256 (as_seq #c h0 arg1)) - fromDomain_ #P256 (felem_seq_as_nat P256 (as_seq h0 arg2)))





let felem_sub #c arg1 arg2 out = 
  match c with 
  |P256 -> p256_sub arg1 arg2 out
  |P384 -> admit()



let mul #c f r out =
  match c with 
  |P256 -> mul_p256 f r out
  |P384 -> ()




let eq0_u64 a = 
  eq_mask_lemma a (u64 0);
  eq_mask a (u64 0)



let eq1_u64 a = 
  neq_mask_lemma a (u64 0);
  neq_mask a (u64 0)



let isZero_uint64_CT #c f = 
  match c with 
  |P256 -> 
    let a0 = index f (size 0) in 
    let a1 = index f (size 1) in 
    let a2 = index f (size 2) in 
    let a3 = index f (size 3) in 
  
    let r0 = eq_mask a0 (u64 0) in 
    let r1 = eq_mask a1 (u64 0) in 
    let r2 = eq_mask a2 (u64 0) in 
    let r3 = eq_mask a3 (u64 0) in 
  
    let r01 = logand r0 r1 in 
      logand_lemma r0 r1; 
    let r23 = logand r2 r3 in 
      logand_lemma r2 r3;
    let r = logand r01 r23 in 
      logand_lemma r01 r23;
    r
  |P384 -> 
    let a0 = index f (size 0) in 
    let a1 = index f (size 1) in 
    let a2 = index f (size 2) in 
    let a3 = index f (size 3) in 
    let a4 = index f (size 4) in 
    let a5 = index f (size 5) in 
  
    let r0 = eq_mask a0 (u64 0) in 
    let r1 = eq_mask a1 (u64 0) in 
    let r2 = eq_mask a2 (u64 0) in 
    let r3 = eq_mask a3 (u64 0) in 
    let r4 = eq_mask a4 (u64 0) in 
    let r5 = eq_mask a5 (u64 0) in 
  
    let r01 = logand r0 r1 in 
      logand_lemma r0 r1; 
    let r23 = logand r2 r3 in 
      logand_lemma r2 r3;
    let r = logand r01 r23 in 
      logand_lemma r01 r23;
    let r45 = logand r4 r5 in 
    let r = logand r r45 in 
    r



let compare_felem #c a b = 
  match c with 
  |P256 -> 
    let a_0 = index a (size 0) in 
    let a_1 = index a (size 1) in 
    let a_2 = index a (size 2) in 
    let a_3 = index a (size 3) in 

    let b_0 = index b (size 0) in 
    let b_1 = index b (size 1) in 
    let b_2 = index b (size 2) in 
    let b_3 = index b (size 3) in 

    let r_0 = eq_mask a_0 b_0 in 
  eq_mask_lemma a_0 b_0;
    let r_1 = eq_mask a_1 b_1 in 
  eq_mask_lemma a_1 b_1;
    let r_2 = eq_mask a_2 b_2 in 
  eq_mask_lemma a_2 b_2;
    let r_3 = eq_mask a_3 b_3 in 
  eq_mask_lemma a_3 b_3;
    
    let r01 = logand r_0 r_1 in 
  logand_lemma r_0 r_1;
    let r23 = logand r_2 r_3 in 
  logand_lemma r_2 r_3;
    
    let r = logand r01 r23 in 
  logand_lemma r01 r23;
  lemma_equality (a_0, a_1, a_2, a_3) (b_0, b_1, b_2, b_3); 
    r
  |P384 -> 
      let a_0 = index a (size 0) in 
      let a_1 = index a (size 1) in 
      let a_2 = index a (size 2) in 
      let a_3 = index a (size 3) in 
      let a_4 = index a (size 4) in 
      let a_5 = index a (size 5) in 

      let b_0 = index b (size 0) in 
      let b_1 = index b (size 1) in 
      let b_2 = index b (size 2) in 
      let b_3 = index b (size 3) in 
      let b_4 = index b (size 4) in 
      let b_5 = index b (size 5) in 

      let r_0 = eq_mask a_0 b_0 in 
      let r_1 = eq_mask a_1 b_1 in 
      let r_2 = eq_mask a_2 b_2 in 
      let r_3 = eq_mask a_3 b_3 in 
      let r_4 = eq_mask a_4 b_4 in 
      let r_5 = eq_mask a_5 b_5 in 
    
      let r01 = logand r_0 r_1 in 
      let r23 = logand r_2 r_3 in 
      let r45 = logand r_4 r_5 in 

      let r = logand(logand r01 r23) r45 in 
      lemma_equality (a_0, a_1, a_2, a_3, a_4, a_5) (b_0, b_1, b_2, b_3, b_4, b_5);
      r
    



let copy_conditional #c out x mask = 
  match c with 
  |P256 -> 
    let h0 = ST.get() in 
    let out_0 = index out (size 0) in 
    let out_1 = index out (size 1) in 
    let out_2 = index out (size 2) in 
    let out_3 = index out (size 3) in 

    let x_0 = index x (size 0) in 
    let x_1 = index x (size 1) in 
    let x_2 = index x (size 2) in 
    let x_3 = index x (size 3) in 

    let r_0 = logxor out_0 (logand mask (logxor out_0 x_0)) in 
    let r_1 = logxor out_1 (logand mask (logxor out_1 x_1)) in 
    let r_2 = logxor out_2 (logand mask (logxor out_2 x_2)) in 
    let r_3 = logxor out_3 (logand mask (logxor out_3 x_3)) in 

    lemma_xor_copy_cond out_0 x_0 mask;
    lemma_xor_copy_cond out_1 x_1 mask;
    lemma_xor_copy_cond out_2 x_2 mask;
    lemma_xor_copy_cond out_3 x_3 mask;

    upd out (size 0) r_0;
    upd out (size 1) r_1;
    upd out (size 2) r_2;
    upd out (size 3) r_3;
      let h1 = ST.get() in 

    lemma_eq_funct_ (as_seq h1 out) (as_seq h0 out);
    lemma_eq_funct_ (as_seq h1 out) (as_seq h0 x)
  |P384 -> 
    let h0 = ST.get() in 
    
    let out_0 = index out (size 0) in 
    let out_1 = index out (size 1) in 
    let out_2 = index out (size 2) in 
    let out_3 = index out (size 3) in 
    let out_4 = index out (size 4) in 
    let out_5 = index out (size 5) in 

    let x_0 = index x (size 0) in 
    let x_1 = index x (size 1) in 
    let x_2 = index x (size 2) in 
    let x_3 = index x (size 3) in 
    let x_4 = index x (size 4) in 
    let x_5 = index x (size 5) in 

    let r_0 = logxor out_0 (logand mask (logxor out_0 x_0)) in 
    let r_1 = logxor out_1 (logand mask (logxor out_1 x_1)) in 
    let r_2 = logxor out_2 (logand mask (logxor out_2 x_2)) in 
    let r_3 = logxor out_3 (logand mask (logxor out_3 x_3)) in
    let r_4 = logxor out_4 (logand mask (logxor out_4 x_4)) in 
    let r_5 = logxor out_5 (logand mask (logxor out_5 x_5)) in 
  
    lemma_xor_copy_cond out_0 x_0 mask;
    lemma_xor_copy_cond out_1 x_1 mask;
    lemma_xor_copy_cond out_2 x_2 mask;
    lemma_xor_copy_cond out_3 x_3 mask;
    lemma_xor_copy_cond out_4 x_4 mask;
    lemma_xor_copy_cond out_5 x_5 mask;

    upd out (size 0) r_0;
    upd out (size 1) r_1;
    upd out (size 2) r_2;
    upd out (size 3) r_3;
    upd out (size 4) r_4;
    upd out (size 5) r_5;
      let h1 = ST.get() in 

    lemma_eq_funct_ (as_seq h1 out) (as_seq h0 out);
    lemma_eq_funct_ (as_seq h1 out) (as_seq h0 x)





val lemma_shift_256: a: int -> b: int -> c: int -> d: int -> Lemma (
    a * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
    b * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
    c * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64  + 
    d * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 ==
    (a + b * pow2 64 + c * pow2 64 * pow2 64 + d * pow2 64 * pow2 64 * pow2 64) * pow2 64 * pow2 64 * pow2 64 * pow2 64)

let lemma_shift_256 a b c d = ()


let shiftLeftWord #c i o = 
  match c with 
  |P384 -> ()
  |P256 -> 
    assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    let h0 = ST.get() in 
    upd o (size 0) (u64 0);
    upd o (size 1) (u64 0);
    upd o (size 2) (u64 0);
    upd o (size 3) (u64 0);
    upd o (size 4) i.(size 0);
    upd o (size 5) i.(size 1);
    upd o (size 6) i.(size 2);
    upd o (size 7) i.(size 3);

    lemma_shift_256 (v (Lib.Sequence.index (as_seq h0 i) 0)) (v (Lib.Sequence.index (as_seq h0 i) 1)) (v (Lib.Sequence.index (as_seq h0 i) 2)) (v (Lib.Sequence.index (as_seq h0 i) 3))
