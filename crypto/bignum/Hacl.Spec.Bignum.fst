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


#set-options "--initial_fuel 0 --max_fuel 0"

val fsum_tot: a:seqelem{red a len} -> b:seqelem{red b len} -> Tot (c:seqelem)
let fsum_tot a b =
  fsum_spec a b len


#set-options "--z3rlimit 20"

val fdifference_tot:
  a:seqelem -> b:seqelem{add_zero_pre b /\ gte_limbs a (add_zero_spec b) len} -> Tot seqelem
let fdifference_tot a b =
  let b' = add_zero_spec b in
  fdifference_spec a b' len


val fscalar_tot: a:seqelem -> s:limb{
  carry_wide_pre (fscalar_spec a s) 0
  /\ carry_top_wide_pre (carry_wide_spec (fscalar_spec a s) 0)
  /\ copy_from_wide_pre (carry_top_wide_spec (carry_wide_spec (fscalar_spec a s) 0)) } ->
  Tot seqelem
let fscalar_tot a s =
  let x = fscalar_spec a s in
  let y = carry_wide_spec x 0 in  
  let z = carry_top_wide_spec y in
  copy_from_wide_spec z


val fmul_tot: input:seqelem -> input2:seqelem{fmul_pre input input2} -> Tot seqelem
let fmul_tot input input2 = fmul_spec input input2
