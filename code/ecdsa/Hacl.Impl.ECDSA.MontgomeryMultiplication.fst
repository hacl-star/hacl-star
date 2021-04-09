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

(* open Hacl.Impl.ECDSA.LowLevel *)

#reset-options "--z3rlimit 200"

let prime_p256_order = getOrder #P256

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
      (* let c = Hacl.Impl.P256.LowLevel.sub4_il x_ prime256order_buffer tempBuffer in *)
	let h1 = ST.get() in 
(* 
	assert(if uint_v c = 0 then 
	  as_nat P256 h0 x_ >= (getOrder #P256) 
	  else as_nat P256 h0 x_ < prime_p256_order);
	assert(wide_as_nat P256 h0 x = as_nat P256 h0 x_ + uint_v cin * pow2 256);
      let carry = sub_borrow_u64 c cin (u64 0) tempBufferForSubborrow in 
      let h2 = ST.get() in 
      assert(if (as_nat P256 h0 x_ >= prime_p256_order) then uint_v carry = 0 
	else if uint_v cin < uint_v c then uint_v carry = 1  *)
(* 	else uint_v carry = 0); 
 *)
    (* cmovznz4 #P256 carry tempBuffer x_ result; *)
 pop_frame()   


let reduction_prime_2prime_with_carry2 #cu cin x result  = 
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 == pow2 256);
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in 
    let tempBufferForSubborrow = create (size 1) (u64 0) in 
(*         recall_contents prime256order_buffer (Lib.Sequence.of_list (order_list P256));
    let c = Hacl.Impl.P256.LowLevel .sub4_il x prime256order_buffer tempBuffer in
    let carry = sub_borrow_u64 c cin (u64 0) tempBufferForSubborrow in 
    cmovznz4 #cu carry tempBuffer x result; *)
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
    (* let c = sub4_il x prime256order_buffer tempBuffer in *)
(*       let h1 = ST.get() in 
      assert(as_nat c h1 tempBuffer = as_nat c h0 x - (getOrder #P256) + uint_v c * pow2 256);
      assert(let x = as_nat c h0 x in if x < (getOrder #P256) then uint_v c = 1 else uint_v c = 0);
    cmovznz4 #cu c tempBuffer x result; 
    let h2 = ST.get() in 
      assert_norm (pow2 256 == pow2 64 * pow2 64 * pow2 64 * pow2 64);
    lemma_reduction1 (as_nat c h0 x) (as_nat c h2 result); *)
  pop_frame()  
