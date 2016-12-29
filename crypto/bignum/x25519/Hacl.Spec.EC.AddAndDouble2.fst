module Hacl.Spec.EC.AddAndDouble2

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Fsquare
open Hacl.Spec.Bignum.Fmul
open Hacl.Spec.EC.AddAndDouble


#set-options "--initial_fuel 0 --max_fuel 0"

val fmonty_tot:
  px:seqelem{red_52 px} -> pz:seqelem{red_52 pz} ->
  pqx:seqelem{red_52 pqx} -> pqz:seqelem{red_52 pqz} ->
  qx:seqelem{red_52 qx} ->
  Tot (seqelem * seqelem * seqelem * seqelem)
let fmonty_tot px pz pqx pqz qx =
  fsum_52_is_53 px pz;
  let px' = fsum_tot px pz in
  lemma_fdifference_unrolled' pz px;
  let pz' = fdifference_tot pz px in
  fsum_52_is_53 pqx pqz;
  let pqx' = fsum_tot pqx pqz in
  lemma_fdifference_unrolled' pqz pqx;
  let pqz' = fdifference_tot pqz pqx in
  fmul_53_55_is_fine pqx' pz';
  let xxprime = fmul_tot pqx' pz' in
  fmul_53_55_is_fine px' pqz';
  let zzprime = fmul_tot px' pqz' in
  fsum_52_is_53 xxprime zzprime;
  let xxprime' = fsum_tot xxprime zzprime in
  lemma_fdifference_unrolled' zzprime pqx;
  let zzprime' = fdifference_tot zzprime pqx in
  let x3 = fsquare_times_tot xxprime' 1 in
  let zzzprime = fsquare_times_tot zzprime' 1 in
  let z3 = fmul_tot zzzprime qx in
  let xx = fsquare_times_tot px' 1 in
  let zz = fsquare_times_tot pz' 1 in
  let x2 = fmul_tot xx zz in
  let zz' = fdifference_tot zz xx in
  let zzz = fscalar_tot zz (uint64_to_limb Hacl.Bignum.Constants.a24) in
  let zzz' = fsum_tot zzz xx in
  let z2 = fsum_tot zz' zzz' in
  (x2, z2, x3, z3)
