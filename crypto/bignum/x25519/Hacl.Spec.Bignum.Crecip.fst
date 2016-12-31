module Hacl.Spec.Bignum.Crecip

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Fsquare
open Hacl.Spec.Bignum
open Hacl.Spec.EC.AddAndDouble


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"
#set-options "--lax"

val crecip:
  z:seqelem{red_513 z} -> Tot (s':seqelem{red_513 s'})
let crecip z =
  let a = fsquare_times_tot z 1 in
  let t0 = fsquare_times_tot a 2 in
  let b = fmul_tot t0 z in
  let a' = fmul_tot b a in
  let t0' = fsquare_times_tot a 1 in
  let b' = fmul_tot t0' b in
  let t0'' = fsquare_times_tot b' 5 in
  let b'' = fmul_tot t0'' b' in
  let t0''' = fsquare_times_tot b'' 10 in
  let c = fmul_tot t0''' b'' in
  let t0'''' = fsquare_times_tot c 20 in
  let t0''''' = fmul_tot t0'''' c in
  let t0_6 = fsquare_times_tot t0''''' 10 in
  let b''' = fmul_tot t0_6 b'' in
  let t0_7 = fsquare_times_tot b''' 50 in
  let c' = fmul_tot t0_7 b''' in
  let t0_8 = fsquare_times_tot c' 100 in
  let t0_9 = fmul_tot t0_8 c' in
  let t0_10 = fsquare_times_tot t0_9 50 in
  let t0_11 = fmul_tot t0_10 b''' in
  let t0_12 = fsquare_times_tot t0_11 5 in
  fmul_tot t0_12 a'
