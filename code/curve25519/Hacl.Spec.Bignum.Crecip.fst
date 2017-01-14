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

type s_513 = s:seqelem{red_513 s}


inline_for_extraction private val fmul_tot: input:s_513 -> input2:s_513 -> Tot s_513
inline_for_extraction private let fmul_tot input input2 =
  lemma_513_is_53 input; lemma_513_is_55 input2; fmul_53_55_is_fine input input2;
  fmul_tot input input2
  

val crecip_tot_1: z:seqelem{red_513 z} -> Tot (s_513 * s_513 * s_513)
let crecip_tot_1 z =
  let a = fsquare_times_tot z 1 in
  let t0 = fsquare_times_tot a 2 in
  let b = fmul_tot t0 z in
  let a' = fmul_tot b a in
  let t0' = fsquare_times_tot a' 1 in
  let b' = fmul_tot t0' b in
  let t0'' = fsquare_times_tot b' 5 in
  t0'', b', a'


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val crecip_tot_2: t0'':s_513 -> b':s_513  -> a':s_513 -> Tot (s_513 * s_513 * s_513)
let crecip_tot_2 t0'' b' a' =
  let b'' = fmul_tot t0'' b' in
  let t0''' = fsquare_times_tot b'' 10 in
  let c = fmul_tot t0''' b'' in
  let t0'''' = fsquare_times_tot c 20 in
  let t0''''' = fmul_tot t0'''' c in
  let t0_6 = fsquare_times_tot t0''''' 10 in
  let b''' = fmul_tot t0_6 b'' in
  let t0_7 = fsquare_times_tot b''' 50 in
  t0_7, b''', a'


val crecip_tot_3: t0_7:s_513 -> b''':s_513 -> a':s_513 -> Tot (s_513)
let crecip_tot_3 t0_7 b''' a' =
  let c' = fmul_tot t0_7 b''' in
  let t0_8 = fsquare_times_tot c' 100 in
  let t0_9 = fmul_tot t0_8 c' in
  let t0_10 = fsquare_times_tot t0_9 50 in
  let t0_11 = fmul_tot t0_10 b''' in
  let t0_12 = fsquare_times_tot t0_11 5 in
  fmul_tot t0_12 a'


val crecip_tot:
  z:seqelem{red_513 z} -> Tot (s':seqelem{red_513 s'})
let crecip_tot z =
  let t0'', b', a' = crecip_tot_1 z in
  let t0_7, b''', a' = crecip_tot_2 t0'' b' a' in
  crecip_tot_3 t0_7 b''' a'
