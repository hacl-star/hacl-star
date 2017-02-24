module Hacl.Spec.Bignum

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

assume val lemma_mod_sub_distr_l_l: a:nat -> b:nat -> p:pos -> Lemma ((a - b) % p = ((a % p) - b) % p)
assume val lemma_mod_sub_distr_l_r: a:nat -> b:nat -> p:pos -> Lemma ((a - b) % p = (a - (b % p)) % p)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val fsum_tot:
  a:seqelem{red a len} ->
  b:seqelem{red b len} ->
  Tot (c:seqelem{selem c = selem a +@ selem b})
let fsum_tot a b =
  Math.Lemmas.lemma_mod_plus_distr_l (seval a) (seval b) prime;
  Math.Lemmas.lemma_mod_plus_distr_l (seval b) (selem a) prime;
  let c = fsum_spec a b len in
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
  let c = fdifference_spec a b' len in
  lemma_fdifference_eval a b';
  lemma_mod_sub_distr_l_l (seval b') (seval a) prime;
  lemma_mod_sub_distr_l_r (selem b') (seval a) prime;
  c

open FStar.Mul

val fscalar_tot: a:seqelem -> s:limb{
  carry_wide_pre (fscalar_spec a s) 0
  /\ carry_top_wide_pre (carry_wide_spec (fscalar_spec a s) 0)
  /\ copy_from_wide_pre (carry_top_wide_spec (carry_wide_spec (fscalar_spec a s) 0)) } ->
  (* Tot (c:seqelem{selem c = (v s * selem a) % prime}) *)
  Tot (c:seqelem)
let fscalar_tot a s =
  let x = fscalar_spec a s in
  lemma_fscalar_eval a s;
  let y = carry_wide_spec x 0 in
  let z = carry_top_wide_spec y in
  lemma_carry_top_wide_spec y;
  copy_from_wide_spec z


val fmul_tot: input:seqelem -> input2:seqelem{fmul_pre input input2} -> Tot seqelem
let fmul_tot input input2 = fmul_spec input input2
