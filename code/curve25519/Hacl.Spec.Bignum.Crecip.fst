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


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

inline_for_extraction private val fmul_tot: input:s_513 -> input2:s_513 -> Tot s_513
inline_for_extraction private let fmul_tot input input2 =
  lemma_513_is_53 input; lemma_513_is_55 input2; fmul_53_55_is_fine input input2;
  fmul_tot input input2
  
val lemma_fsquare_times_tot_def_0: s:seqelem{red_5413 s} -> Lemma
  (fsquare_pre s /\ fsquare_times_tot s 1 == fsquare_spec s)
#reset-options "--initial_fuel 1 --max_fuel 1"
let lemma_fsquare_times_tot_def_0 s =
  fsquare_5413_is_fine s

#reset-options "--initial_fuel 0 --max_fuel 0"

val lemma_fsquare_times_tot_def_1: s:seqelem{red_5413 s} -> n:nat{n > 1} -> Lemma
  (fsquare_pre s /\ red_5413 (fsquare_spec s) /\
    fsquare_times_tot s n == fsquare_times_tot (fsquare_spec s) (n-1))
#reset-options "--initial_fuel 1 --max_fuel 1"
let lemma_fsquare_times_tot_def_1 s n =
  fsquare_5413_is_fine s;
  lemma_513_is_5413 (fsquare_spec s)

#reset-options "--initial_fuel 0 --max_fuel 0"

val lemma_fsquare_times_tot: s:seqelem{red_5413 s} -> n:pos -> Lemma
  (requires (True))
  (ensures (selem (fsquare_times_tot s n) == Hacl.Spec.Bignum.Crecip.Lemmas.exp (selem s) (pow2 n)))
  (decreases n)
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let rec lemma_fsquare_times_tot s n =
  fsquare_5413_is_fine s;
  if n = 1 then (
    assert_norm (pow2 1 = 2);
    lemma_fsquare_times_tot_def_0 s;
    Hacl.Spec.Bignum.Crecip.Lemmas.lemma_exp_def_1 (selem s) 2;
    Hacl.Spec.Bignum.Crecip.Lemmas.lemma_exp_def_1 (selem s) 1;
    Hacl.Spec.Bignum.Crecip.Lemmas.lemma_exp_def_0 (selem s);
    Math.Lemmas.modulo_lemma (selem s) prime
  ) else (
    let s' = fsquare_spec s in
    lemma_fsquare_times_tot_def_1 s n;
    lemma_fsquare_times_tot s' (n-1);
    cut (selem (fsquare_times_tot s' (n-1)) == Hacl.Spec.Bignum.Crecip.Lemmas.exp (selem s *@ selem s) (pow2 (n-1)));
    Hacl.Spec.Bignum.Crecip.Lemmas.lemma_exp_double (selem s) (pow2 (n-1));
    Math.Lemmas.pow2_double_sum (n-1)
  )


unfold inline_for_extraction
val fsquare_times_tot: s:seqelem{red_513 s} -> n:pos -> Tot (s':seqelem{red_513 s' /\
  selem s' == Hacl.Spec.Bignum.Crecip.Lemmas.exp (selem s) (pow2 n)})
unfold inline_for_extraction
let fsquare_times_tot s n =
  lemma_513_is_5413 s;
  lemma_fsquare_times_tot s n;
  fsquare_times_tot s n

module L = Hacl.Spec.Bignum.Crecip.Lemmas

val crecip_tot_1: z:seqelem{red_513 z} -> Tot (s_513 * s_513 * s_513)
let crecip_tot_1 z =
  let a = fsquare_times_tot z 1 in  // z^2
  let t0 = fsquare_times_tot a 2 in // z^8
  let b = fmul_tot t0 z in          // z^9
  let a' = fmul_tot b a in          // z^11
  let t0' = fsquare_times_tot a' 1 in // z^22
  let b' = fmul_tot t0' b in          // z^(2^5 - 2^0)
  let t0'' = fsquare_times_tot b' 5 in // z^(2^10 - 2^5)
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
