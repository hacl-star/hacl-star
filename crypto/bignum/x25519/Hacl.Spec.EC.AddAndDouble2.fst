module Hacl.Spec.EC.AddAndDouble2

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Fsquare
open Hacl.Spec.Bignum.Fmul
open Hacl.Spec.EC.AddAndDouble


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

let s_513 = s:seqelem{red_513 s}

let lemma_53_is_5413 (s:seqelem{red_53 s}) : Lemma (red_5413 s) = ()
let lemma_513_is_53 (s:seqelem{red_513 s}) : Lemma (red_53 s) = ()
let lemma_513_is_55 (s:seqelem{red_513 s}) : Lemma (red_55 s) = ()
let lemma_513_is_5413 (s:seqelem{red_513 s}) : Lemma (red_5413 s) = ()
let lemma_513_is_52 (s:seqelem{red_513 s}) : Lemma (red_52 s) = ()

val fmonty_tot:
  px:s_513 -> pz:s_513 ->
  pqx:s_513 -> pqz:s_513 ->
  qx:s_513 ->
  Tot (s_513 * s_513 * s_513 * s_513)
let fmonty_tot px pz pqx pqz qx =
  fsum_513_is_53 px pz;
  let px' = fsum_tot px pz in
  lemma_fdifference_unrolled'' pz px;
  lemma_fdifference_unrolled''' pz px;
  let pz' = fdifference_tot pz px in
  fsum_513_is_53 pqx pqz;
  let pqx' = fsum_tot pqx pqz in
  lemma_fdifference_unrolled'' pqz pqx;
  let pqz' = fdifference_tot pqz pqx in
  fmul_53_55_is_fine pqx' pz';
  let xxprime = fmul_tot pqx' pz' in
  fmul_53_55_is_fine px' pqz';
  let zzprime = fmul_tot px' pqz' in
  fsum_513_is_53 xxprime zzprime;
  let xxprime' = fsum_tot xxprime zzprime in
  lemma_fdifference_unrolled''' zzprime pqx;
  let zzprime' = fdifference_tot zzprime pqx in
  lemma_53_is_5413 xxprime';
  fsquare_5413_is_fine xxprime';
  let x3 = fsquare_times_tot xxprime' 1 in
  fsquare_5413_is_fine zzprime';
  let zzzprime = fsquare_times_tot zzprime' 1 in
  lemma_513_is_53 zzzprime; lemma_513_is_55 qx;
  fmul_53_55_is_fine zzzprime qx;
  let z3 = fmul_tot zzzprime qx in
  lemma_53_is_5413 px';
  fsquare_5413_is_fine px';
  let xx = fsquare_times_tot px' 1 in
  fsquare_5413_is_fine pz';
  let zz = fsquare_times_tot pz' 1 in
  lemma_513_is_53 xx;
  lemma_513_is_55 zz;
  fmul_53_55_is_fine xx zz;
  let x2 = fmul_tot xx zz in
  lemma_fdifference_unrolled'' zz xx;  
  let zz' = fdifference_tot zz xx in
  let scalar = (uint64_to_limb Hacl.Bignum.Constants.a24) in
  fscalar_is_fine zz scalar;
  let zzz = fscalar_tot zz (uint64_to_limb Hacl.Bignum.Constants.a24) in
  fsum_513_is_53 zzz xx;
  let zzz' = fsum_tot zzz xx in
  fmul_53_55_is_fine zzz' zz';
  let z2 = fmul_tot zzz' zz' in
  (x2, z2, x3, z3)
