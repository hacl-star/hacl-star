module Hacl.Impl.EC.LowLevel.Lemmas

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Hacl.Lemmas.P256

open Spec.ECC
open Spec.ECC.Curves
open FStar.Math
open FStar.Math.Lemmas
open FStar.Mul

open FStar.Tactics
open FStar.Tactics.Canon

open Hacl.Impl.P256.LowLevel
open Hacl.Impl.P384.LowLevel
open Hacl.Impl.EC.Masking

open Lib.IntTypes.Intrinsics


open Lib.Loops

open Hacl.Bignum

let getPower2 c = pow2 (getPower c)

#set-options " --z3rlimit 400"

val lemma_reduction_prime_2prime_with_carry_cin: 
  c: curve ->
  cin: nat {cin <= 1} ->
  x: nat {x + cin * getPower2 c < 2 * getPrime c /\ x < getPower2 c} -> 
  carry0 : nat {carry0 <= 1 /\ (if carry0 = 0 then x >= getPrime c else x < getPrime c)} -> 
  result: nat {if cin < carry0 then result = x else result = x - getPrime c + carry0 * getPower2 c} -> 
  Lemma (result = (x + cin * getPower2 c) % getPrime c)

let lemma_reduction_prime_2prime_with_carry_cin c cin x carry0 result = 
  let n = x + cin * getPower2 c in 
  let prime = getPrime c in 

  if cin = 0 && carry0 = 1 then begin
    small_mod x prime;
    assert(result = (x + cin * getPower2 c) % prime)
    end
  else if cin = 0 && carry0 = 0 then begin
    small_modulo_lemma_1 (x - getPrime c) prime;
    lemma_mod_sub x prime 1;
    assert(result = (x + cin * getPower2 c) % prime)
    end
  else if cin = 1 && carry0 = 0 then 
    assert(result = (x + cin * getPower2 c) % prime)
  else
    begin 
      lemma_mod_sub (x + cin * getPower2 c) prime 1;
      small_mod result prime;
      assert(result = (x + cin * getPower2 c) % prime)
    end
