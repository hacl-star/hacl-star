module Hacl.Impl.EC.LowLevel.Lemmas


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definition
open Hacl.Lemmas.P256

open Spec.P256

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



#set-options " --z3rlimit 400"

val lemma_reduction_prime_2prime_with_carry_cin: 
  c: curve ->
  cin: nat {cin <= 1} ->
  x: nat {x + cin * getPower2 c < 2 * getPrime c /\ x < getPower2 c} -> 
  carry0 : nat {carry0 <= 1 /\ (if carry0 = 0 then x >= getPrime c else x < getPrime c)} -> 
  result: nat {if cin < carry0 then result = x else result = x - getPrime c + carry0 * getPower2 c}
  -> Lemma (result = (x + cin * getPower2 c) % getPrime c)

let lemma_reduction_prime_2prime_with_carry_cin c cin x carry0 result = 
  let n = x + cin * getPower2 c in 
  assert(if cin < carry0 then result = x else result = x - getPrime c + carry0 * getPower2 c);
  assert(cin < carry0 <==> cin = 0 && carry0 = 1);
  assert(if (cin = 0 && carry0 = 1) then result = x else result = x - getPrime c + carry0 * getPower2 c);
  assert(if (cin = 0 && carry0 = 1) then result = x else result = x - getPrime c + carry0 * getPower2 c);
  assert(if ((cin = 1 && carry0 = 1) || (cin = 0 && carry0 = 0)) then 
    result = x - getPrime c + carry0 * getPower2 c else result = x);

  assert(if cin = 0 && carry0 = 0 then
    begin
      small_modulo_lemma_1 result (getPrime c);
      result = n % getPrime c end else True);


  assert(if cin = 1 && carry0 = 1 then 
    begin 
      modulo_addition_lemma result (getPrime c) 1; 
      result = n % getPrime c end 
   else True); 

    assert (if (cin = 0 && carry0 = 1) then begin
      small_modulo_lemma_1 result(getPrime c); 
      result = n % getPrime c end else True)



val lemma_cin_1: #c: curve -> x: nat -> cin : nat {x + cin * getPower2 c < 2 * getPrime c} -> 
  Lemma (cin <= 1)


let lemma_cin_1 #c x cin = 
  assert_norm(getPower2 P256 < 2 * getPrime P256);
  assert_norm(getPower2 P384 < 2 * getPrime P384)


(*
val lemma_test0: #c: curve -> x: widefelem c -> h0: mem ->
  Lemma (
    let len = getCoordinateLenU64 c in 
    wide_as_nat c h0 x = as_nat c h0 (gsub x (size 0) len) + as_nat c h0 (gsub x len len) * getPower2 c)

let lemma_test0 #c x h0 = admit()
*)


val lemma_less_2prime_p256: h0: mem ->
  x: widefelem P256 {wide_as_nat P256 h0 x < 2 * getPrime P256} -> 
  Lemma 
    (wide_as_nat P256 h0 x = as_nat P256 h0 (gsub x (size 0) (size 4)) +
      v (Lib.Sequence.index (as_seq h0 x) 4) * getPower2 P256)

let lemma_less_2prime_p256 h0 x = 
  assert_norm (2 * getPrime P256 < pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 == pow2 256)


val lemma_less_2prime_p384: h0: mem -> 
  x: widefelem P384 {wide_as_nat P384 h0 x < 2 * getPrime P384} -> 
  Lemma 
    (wide_as_nat P384 h0 x = as_nat P384 h0 (gsub x (size 0) (size 6)) +
      v (Lib.Sequence.index (as_seq h0 x) 6) * getPower2 P384)

let lemma_less_2prime_p384 h0 x = 
  assert_norm (2 * getPrime P384 < pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2
64);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 == pow2 384)


val lemma_less_2prime: #c: curve -> h0: mem 
  -> x: widefelem c {wide_as_nat c h0 x < 2 * getPrime c} -> 
  Lemma (
    let len = getCoordinateLenU64 c in 
    wide_as_nat c h0 x = as_nat c h0 (gsub x (size 0) len) + v (Lib.Sequence.index (as_seq h0 x) (v len)) * getPower2 c)

let lemma_less_2prime #c h0 x = 
  match c with 
  |P256 -> lemma_less_2prime_p256 h0 x
  |P384 -> lemma_less_2prime_p384 h0 x
  



val lemma_reduction1: #c: curve -> a: nat {a < getPower2 c}
  -> r: nat{if a >= getPrime c then r = a - getPrime c else r = a} ->
  Lemma (r = a % getPrime c)

let lemma_reduction1 #c a r =
  if a >= getPrime c then begin
    assert_norm (getPower2 P256 - getPrime P256 < getPrime P256);
    assert_norm (getPower2 P384 - getPrime P384 < getPrime P384);
    small_modulo_lemma_1 r (getPrime c);
    lemma_mod_sub_distr a (getPrime c) (getPrime c) end
  else
    small_mod r (getPrime c)




val lemma_felem_as_forall: #c: curve -> a: felem c -> b: felem c -> h0: mem ->
  Lemma (
    let len = getCoordinateLenU64 c in 
    forall (i: nat {i < v len}). 
      Lib.Sequence.index (as_seq h0 a) i == Lib.Sequence.index (as_seq h0 b) i 
      <==> as_nat c h0 a == as_nat c h0 b) 

let lemma_felem_as_forall #c a b h0 = admit()




val lemma_wide_felem: c: curve -> h: mem -> e: widefelem c -> Lemma 
  (
    let s = as_seq h e in 
    let s0 = Lib.Sequence.index s 0 in 
    exists (n: nat). wide_as_nat c h e == v s0 + pow2 64 * n)

let lemma_wide_felem c h e = 
  let open Lib.Sequence in 
  match c with 
  |P256 -> 
      let s = as_seq h e in
      let s0 = s.[0] in
      let s1 = s.[1] in
      let s2 = s.[2] in
      let s3 = s.[3] in
      let s4 = s.[4] in
      let s5 = s.[5] in
      let s6 = s.[6] in
      let s7 = s.[7] in
     
      calc (==) {
	v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
	v s3 * pow2 64 * pow2 64 * pow2 64 +
	v s4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
	v s5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
	v s6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
	v s7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64;
	(==) { _ by (canon())}
	v s0 + pow2 64 * 
	  (v s1 + v s2 * pow2 64 +
	  v s3 * pow2 64 * pow2 64 +
	  v s4 * pow2 64 * pow2 64 * pow2 64 +
	  v s5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
	  v s6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
	  v s7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64);
	}
  |P384 -> 
      let s = as_seq h e in
      let s0 = s.[0] in
      let s1 = s.[1] in
      let s2 = s.[2] in
      let s3 = s.[3] in
      
      let s4 = s.[4] in
      let s5 = s.[5] in
      let s6 = s.[6] in
      let s7 = s.[7] in
      
      let s8 = s.[8] in 
      let s9 = s.[9] in 
      let s10 = s.[10] in 
      let s11 = s.[11] in 

     
      calc (==) 
      {
	v s0 + 
	v s1 * pow2 64 + 
	v s2 * pow2 64 * pow2 64 +
	v s3 * pow2 64 * pow2 64 * pow2 64 +
	v s4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
	v s5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
	v s6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
	v s7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64  +
	v s8 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
	v s9 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
	v s10 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
	v s11 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64;
	(==) { _ by (canon())}
	v s0 + pow2 64 * (
	  v s1 + 
	  v s2 * pow2 64 +
	  v s3 * pow2 64 * pow2 64 +
	  v s4 * pow2 64 * pow2 64 * pow2 64 +
	  v s5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
	  v s6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
	  v s7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64  +
	  v s8 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
	  v s9 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
	  v s10 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
	  v s11 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64);
	}



