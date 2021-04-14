module Hacl.Impl.ECDSA.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas
open Hacl.Impl.EC.LowLevel 

open Hacl.Impl.EC.Masking
open FStar.Mul
open Lib.IntTypes.Intrinsics


#reset-options "--z3rlimit 300"

val lemma_reduction_prime_2prime_with_carry_cin: 
  c: curve ->
  cin: nat {cin <= 1} ->
  x: nat {x + cin * pow2 (getPower c) < 2 * getOrder #c /\ x < pow2 (getPower c)} -> 
  carry0 : nat {carry0 <= 1 /\ (if carry0 = 0 then x >= getOrder #c else x < getOrder #c)} -> 
  result: nat {if cin < carry0 then result = x else result = x - getOrder #c + carry0 * pow2 (getPower c)} -> 
  Lemma (result = (x + cin * pow2 (getPower c)) % getOrder #c)

let lemma_reduction_prime_2prime_with_carry_cin c cin x carry0 result = 
  let n = x + cin * pow2 (getPower c) in 
  let prime = getOrder #c in 

  if cin = 0 && carry0 = 1 then begin
    small_mod x prime;
    assert(result = (x + cin * pow2 (getPower c)) % prime)
    end
  else if cin = 0 && carry0 = 0 then begin
    small_modulo_lemma_1 (x - prime) prime;
    lemma_mod_sub x prime 1;
    assert(result = (x + cin * pow2 (getPower c)) % prime)
    end
  else if cin = 1 && carry0 = 0 then 
    assert(result = (x + cin * pow2 (getPower c)) % prime)
  else
    begin 
      lemma_mod_sub (x + cin * pow2 (getPower c)) prime 1;
      small_mod result prime;
      assert(result = (x + cin * pow2 (getPower c)) % prime)
    end


val reduction_prime_2prime_with_carry_cin: #c: curve -> cin: uint64 -> x: felem c -> result: felem c ->
  Stack unit
  (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result /\ (
    as_nat c h x + uint_v cin * pow2 (getPower c) < 2 * getOrder #c))
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat c h1 result = (as_nat c h0 x + uint_v cin * pow2 (getPower c)) % getOrder #c)

let reduction_prime_2prime_with_carry_cin #c cin x result =
  push_frame();

  let h0 = ST.get() in 

  let len = getCoordinateLenU64 c in

  let tempBuffer = create len (u64 0) in
  let tempBufferForSubborrow = create (size 1) (u64 0) in
 
  let carry0 = sub_bn_order x tempBuffer in
  let carry = sub_borrow_u64 carry0 cin (u64 0) tempBufferForSubborrow in
  cmovznz4 carry tempBuffer x result;
  pop_frame();
  
  let h2 = ST.get() in 
  lseq_upperbound #(v (getCoordinateLenU64 c)) (as_seq h0 x); 
  lemma_reduction_prime_2prime_with_carry_cin c (v cin) (as_nat c h0 x) (uint_v carry0) (as_nat c h2 result)


let reduction_prime_2prime_with_carry #c x result  = 
  let len = getCoordinateLenU64 c in
  
  let cin = Lib.Buffer.index x len in
  let x_ = Lib.Buffer.sub x (size 0) len in
  let x__ = Lib.Buffer.sub x len len in 

  let h0 = ST.get() in 
  FStar.Math.Lemmas.pow2_plus 64 (v (getCoordinateLenU64 c) * 64);
  lseq_upperbound1 (as_seq h0 x) (v (getCoordinateLenU64 c) + 1) (2 * v (getCoordinateLenU64 c) - v (getCoordinateLenU64 c) - 1);
  lseq_as_nat_definiton (as_seq h0 x) (v (getCoordinateLenU64 c) + 1);

  lemma_lseq_as_seq_extension (as_seq h0 (gsub x (size 0) (getCoordinateLenU64 c))) (as_seq h0 x) (v (getCoordinateLenU64 c));
  reduction_prime_2prime_with_carry_cin cin x_ result


let reduction_prime_2prime_order #c x result  =
   push_frame();
  let len = getCoordinateLenU64 c in
  let tempBuffer = create len (u64 0) in
    let h0 = ST.get() in
  let r = sub_bn_order x tempBuffer in
    let h1 = ST.get() in 
  lemma_mod_plus (as_nat c h0 x) (-1) (getOrder #c);
  lseq_upperbound #(v (getCoordinateLenU64 c)) (as_seq h0 x); 
  cmovznz4 r tempBuffer x result;
    let h2 = ST.get() in 
  pop_frame()
