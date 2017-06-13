module Hacl.Spec.Bignum

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Bigint
open Hacl.Spec.Bignum.Fsum
open Hacl.Spec.Bignum.Fdifference
open Hacl.Spec.Bignum.Fscalar
open Hacl.Spec.Bignum.Modulo
open Hacl.Spec.Bignum.Fproduct
open Hacl.Spec.Bignum.Fmul

module U32 = FStar.UInt32
module F   = Hacl.Spec.Bignum.Field


(* Prime field definitions *)

type elem = e:int{e >= 0 /\ e < prime}

let zero : elem = 0
let one  : elem = 1

val fadd: elem -> elem -> Tot elem
let fadd e1 e2 = (e1 + e2) % prime
let op_Plus_At e1 e2 = fadd e1 e2

val fdiff: elem -> elem -> Tot elem
let fdiff e1 e2 = (e1 - e2) % prime
let op_Subtraction_At e1 e2 = fdiff e1 e2

val fmul: elem -> elem -> Tot elem
let fmul e1 e2 = (e1 * e2) % prime
let op_Star_At e1 e2 = fmul e1 e2

val selem: seqelem -> GTot elem
let selem s = seval s % prime

val lemma_mod_sub_distr_l_l: a:nat -> b:nat -> p:pos -> Lemma ((a - b) % p = ((a % p) - b) % p)
let lemma_mod_sub_distr_l_l a b p = FStar.Math.Axioms.lemma_mod_sub_distr_l_l a b p
val lemma_mod_sub_distr_l_r: a:nat -> b:nat -> p:pos -> Lemma ((a - b) % p = (a - (b % p)) % p)
let lemma_mod_sub_distr_l_r a b p = FStar.Math.Axioms.lemma_mod_sub_distr_l_r a b p


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val fsum_tot:
  a:seqelem{red a len} ->
  b:seqelem{red b len} ->
  Tot (c:seqelem{selem c = selem a +@ selem b})
let fsum_tot a b =
  Math.Lemmas.lemma_mod_plus_distr_l (seval a) (seval b) prime;
  Math.Lemmas.lemma_mod_plus_distr_l (seval b) (selem a) prime;
  let c = fsum_spec a b in
  lemma_fsum_eval a b;
  c


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val fdifference_tot:
  a:seqelem ->
  b:seqelem{add_zero_pre b /\ gte_limbs a (add_zero_spec b) len} ->
  Tot (c:seqelem{selem c = selem b -@ selem a})
let fdifference_tot a b =
  let b' = add_zero_spec b in
  lemma_add_zero_spec b;
  let c = fdifference_spec a b' in
  lemma_fdifference_eval a b';
  lemma_mod_sub_distr_l_l (seval b') (seval a) prime;
  lemma_mod_sub_distr_l_r (selem b') (seval a) prime;
  c

open FStar.Mul

val fscalar_tot: a:seqelem -> s:limb{
  carry_wide_pre (fscalar_spec a s) 0
  /\ carry_top_wide_pre (carry_wide_spec (fscalar_spec a s))
  /\ copy_from_wide_pre (carry_top_wide_spec (carry_wide_spec (fscalar_spec a s) )) } ->
  Tot (c:seqelem{selem c = ((v s % prime) *@ selem a)})
let fscalar_tot a s =
  let x = fscalar_spec a s in
  lemma_fscalar_eval a s;
  cut (seval_wide x == v s * seval a);
  let y = carry_wide_spec x in
  cut (seval_wide y == v s * seval a);
  let z = carry_top_wide_spec y in
  lemma_carry_top_wide_spec y;
  cut (seval_wide z % prime == (v s * seval a) % prime);
  lemma_copy_from_wide z;
  let z' = copy_from_wide_spec z in
  Math.Lemmas.lemma_mod_mul_distr_l (v s) (seval a) prime;
  Math.Lemmas.lemma_mod_mul_distr_l (seval a) (v s % prime) prime;
  z'


val fmul_tot: input:seqelem -> input2:seqelem{fmul_pre input input2} ->
  Tot (out:seqelem{selem out = (selem input *@ selem input2)})
let fmul_tot input input2 =
  Math.Lemmas.lemma_mod_mul_distr_l (seval input) (seval input2) prime;
  Math.Lemmas.lemma_mod_mul_distr_l (seval input2) (selem input) prime;  
  fmul_spec input input2
