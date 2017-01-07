module Hacl.Spec.Bignum.Crecip

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Fsquare
open Hacl.Spec.Bignum
open Hacl.Spec.EC.AddAndDouble


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

private let lemma_53_is_5413 (s:seqelem{red_53 s}) : Lemma (red_5413 s) = ()
private let lemma_513_is_53 (s:seqelem{red_513 s}) : Lemma (red_53 s) = ()
private let lemma_513_is_55 (s:seqelem{red_513 s}) : Lemma (red_55 s) = ()
private let lemma_513_is_5413 (s:seqelem{red_513 s}) : Lemma (red_5413 s) = ()
private let lemma_513_is_52 (s:seqelem{red_513 s}) : Lemma (red_52 s) = ()
private let lemma_5413_is_55 (s:seqelem{red_5413 s}) : Lemma (Hacl.Spec.EC.AddAndDouble.red_55 s) = ()

let crecip_pre (z:seqelem) : GTot Type0 = red_513 z

val crecip_tot:
  z:seqelem{red_513 z} -> Tot (s':seqelem{red_513 s'})
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let crecip_tot z =
  let a = fsquare_times_tot z 1 in
  let t0 = fsquare_times_tot a 2 in
  lemma_513_is_53 t0; lemma_513_is_55 z; fmul_53_55_is_fine t0 z;
  let b = fmul_tot t0 z in
  lemma_513_is_53 b; lemma_513_is_55 a; fmul_53_55_is_fine b a;
  let a' = fmul_tot b a in
  let t0' = fsquare_times_tot a 1 in
  lemma_513_is_53 t0'; lemma_513_is_55 b; fmul_53_55_is_fine t0' b;
  let b' = fmul_tot t0' b in
  let t0'' = fsquare_times_tot b' 5 in
  lemma_513_is_53 t0''; lemma_513_is_55 b'; fmul_53_55_is_fine t0'' b';
  let b'' = fmul_tot t0'' b' in
  let t0''' = fsquare_times_tot b'' 10 in
  lemma_513_is_53 t0'''; lemma_513_is_55 b''; fmul_53_55_is_fine t0''' b'';
  let c = fmul_tot t0''' b'' in
  let t0'''' = fsquare_times_tot c 20 in
  lemma_513_is_53 t0''''; lemma_513_is_55 c; fmul_53_55_is_fine t0'''' c;
  let t0''''' = fmul_tot t0'''' c in
  let t0_6 = fsquare_times_tot t0''''' 10 in
  lemma_513_is_53 t0_6; lemma_513_is_55 b''; fmul_53_55_is_fine t0_6 b'';
  let b''' = fmul_tot t0_6 b'' in
  let t0_7 = fsquare_times_tot b''' 50 in
  lemma_513_is_53 t0_7; lemma_513_is_55 b'''; fmul_53_55_is_fine t0_7 b''';
  let c' = fmul_tot t0_7 b''' in
  let t0_8 = fsquare_times_tot c' 100 in
  lemma_513_is_53 t0_8; lemma_513_is_55 c'; fmul_53_55_is_fine t0_8 c';
  let t0_9 = fmul_tot t0_8 c' in
  let t0_10 = fsquare_times_tot t0_9 50 in
  lemma_513_is_53 t0_10; lemma_513_is_55 b'''; fmul_53_55_is_fine t0_10 b''';
  let t0_11 = fmul_tot t0_10 b''' in
  let t0_12 = fsquare_times_tot t0_11 5 in
  lemma_513_is_53 t0_12; lemma_513_is_55 a'; fmul_53_55_is_fine t0_12 a';
  fmul_tot t0_12 a'
