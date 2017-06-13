module Hacl.Spec.Bignum.Crecip

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

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

inline_for_extraction private val fmul_tot: input:s_513 -> input2:s_513 -> Tot (out:s_513{selem out = selem input *@ selem input2})
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

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

let lemma_exp_1 e : Lemma (L.exp e 1 = e) =
  L.lemma_exp_def_1 e 1;
  L.lemma_exp_def_0 e;
  cut (L.exp e 1 = e *@ one);
  Math.Lemmas.modulo_lemma e prime
  

val crecip_tot_1: z:seqelem{red_513 z} -> Tot (t:(s_513 * s_513 * s_513){
  let t0'' = Mktuple3?._1 t in
  let b' = Mktuple3?._2 t in
  let a' = Mktuple3?._3 t in
  pow2 10 > pow2 5 /\
  selem t0'' = L.exp (selem z) (pow2 10 - pow2 5) /\
  selem b' = L.exp (selem z) 31 /\
  selem a' = L.exp (selem z) 11
  })
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let crecip_tot_1 z =
  lemma_exp_1 (selem z);
  cut (selem z = L.exp (selem z) 1);
  let a = fsquare_times_tot z 1 in  // z^2
  cut (selem a = L.exp (selem z) (pow2 1));
  let t0 = fsquare_times_tot a 2 in // z^8
  L.lemma_exp_mul (selem z) (pow2 1) (pow2 2);
  assert_norm(op_Multiply (pow2 1) (pow2 2) = 8);
  cut (selem t0 = L.exp (selem z) 8);
  let b = fmul_tot t0 z in          // z^9
  L.lemma_exp_add (selem z) 8 1;
  cut (selem b = L.exp (selem z) 9);
  let a' = fmul_tot b a in          // z^11
  L.lemma_exp_add (selem z) 9 (pow2 1);
  assert_norm(9 + pow2 1 = 11);
  cut (selem a' = L.exp (selem z) 11);
  let t0' = fsquare_times_tot a' 1 in // z^22
  L.lemma_exp_mul (selem z) 11 (pow2 1);
  assert_norm(pow2 1 = 2);
  cut (selem t0' = L.exp (selem z) 22);
  let b' = fmul_tot t0' b in          // z^(2^5 - 2^0)
  cut (selem b' = selem t0' *@ selem b);
  cut (selem t0' = L.exp (selem z) 22);
  cut (selem b = L.exp (selem z) 9);
  L.lemma_exp_add (selem z) 22 9;
  cut (selem b' = L.exp (selem z) 31);
  let t0'' = fsquare_times_tot b' 5 in // z^(2^10 - 2^5)
  L.lemma_exp_mul (selem z) 31 (pow2 5);
  assert_norm(op_Multiply 31 (pow2 5) = pow2 10 - pow2 5);
  cut (selem t0'' = L.exp (selem z) (pow2 10 - pow2 5));
  t0'', b', a'
  


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val crecip_tot_2: t0'':s_513 -> b':s_513  -> a':s_513 -> Tot (t:(s_513 * s_513 * s_513){
  let t0_7 = Mktuple3?._1 t in
  let b''' = Mktuple3?._2 t in
  let a'' = Mktuple3?._3 t in
  selem t0_7 = L.exp (selem t0'' *@ selem b') (pow2 90 + pow2 80 + pow2 70 + pow2 60 + pow2 50) /\
  selem b''' = L.exp (selem t0'' *@ selem b') (pow2 40 + pow2 30 + pow2 20 + pow2 10 + 1) /\
  a'' == a'
  })
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 400"
let crecip_tot_2 t0'' b' a' =
  let b'' = fmul_tot t0'' b' in
  cut (selem b'' = selem t0'' *@ selem b');
  let t0''' = fsquare_times_tot b'' 10 in
  cut (selem t0''' = L.exp (selem b'') (pow2 10));
  let c = fmul_tot t0''' b'' in
  lemma_exp_1 (selem b'');
  cut (selem t0''' = L.exp (selem b'') (pow2 10));
  cut (selem c = selem t0''' *@ selem b'');
  L.lemma_exp_add (selem b'') (pow2 10) 1;
  cut (selem c = L.exp (selem b'') (pow2 10 + 1));
  let t0'''' = fsquare_times_tot c 20 in
  L.lemma_exp_mul (selem b'') (pow2 10 + 1) (pow2 20);
  assert_norm(op_Multiply (pow2 10 + 1) (pow2 20) = pow2 30 + pow2 20);
  cut (selem t0'''' = L.exp (selem b'') (pow2 30 + pow2 20));
  let t0''''' = fmul_tot t0'''' c in
  L.lemma_exp_add (selem b'') (pow2 30 + pow2 20) (pow2 10 + 1);
  cut (selem t0''''' = L.exp (selem b'') (pow2 30 + pow2 20 + pow2 10 + 1));
  let t0_6 = fsquare_times_tot t0''''' 10 in
  L.lemma_exp_mul (selem b'') (pow2 30 + pow2 20 + pow2 10 + 1) (pow2 10);
  assert_norm(FStar.Mul.((pow2 30 + pow2 20 + pow2 10 + 1) * pow2 10 = pow2 40 + pow2 30 + pow2 20 + pow2 10));
  cut (selem t0_6 = L.exp (selem b'') (pow2 40 + pow2 30 + pow2 20 + pow2 10));
  let b''' = fmul_tot t0_6 b'' in
  L.lemma_exp_add (selem b'') (pow2 40 + pow2 30 + pow2 20 + pow2 10) 1;
  cut (selem b''' = L.exp (selem b'') (pow2 40 + pow2 30 + pow2 20 + pow2 10 + 1));
  let t0_7 = fsquare_times_tot b''' 50 in
  L.lemma_exp_mul (selem b'') (pow2 40 + pow2 30 + pow2 20 + pow2 10 + 1) (pow2 50);
  assert_norm(FStar.Mul.((pow2 40 + pow2 30 + pow2 20 + pow2 10 + 1) * pow2 50 = pow2 90 + pow2 80 + pow2 70 + pow2 60 + pow2 50));
  t0_7, b''', a'


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val crecip_tot_3: t0_7:s_513 -> b''':s_513 -> a':s_513 -> Tot (s:s_513{
  selem s = (L.exp ((L.exp (selem t0_7 *@ selem b''') (pow2 150 + pow2 50)) *@ selem b''') (pow2 5)) *@ selem a'
  })
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let crecip_tot_3 t0_7 b''' a' =
  let c' = fmul_tot t0_7 b''' in
  cut (selem c' = selem t0_7 *@ selem b''');
  let t0_8 = fsquare_times_tot c' 100 in
  lemma_exp_1 (selem c');
  let t0_9 = fmul_tot t0_8 c' in
  L.lemma_exp_add (selem c') (pow2 100) 1;
  let t0_10 = fsquare_times_tot t0_9 50 in
  L.lemma_exp_mul (selem c') (pow2 100 + 1) (pow2 50);
  assert_norm(FStar.Mul.((pow2 100 + 1) * (pow2 50) = pow2 150 + pow2 50));
  cut (selem t0_10 = (L.exp (selem t0_7 *@ selem b''') (pow2 150 + pow2 50)));
  let t0_11 = fmul_tot t0_10 b''' in
  cut (selem t0_11 = selem t0_10 *@ selem b''');
  let t0_12 = fsquare_times_tot t0_11 5 in
  fmul_tot t0_12 a'


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val crecip_tot_3': t0_7:s_513 -> b''':s_513 -> a':s_513 -> Tot (s:s_513{
  selem s = (L.exp ((L.exp (selem t0_7 *@ selem b''') (pow2 150 + pow2 50)) *@ selem b''') (pow2 2)) *@ selem a'
  })
#reset-options "--max_fuel 0 --z3rlimit 100"
let crecip_tot_3' t0_7 b''' a' =
  let c' = fmul_tot t0_7 b''' in
  cut (selem c' = selem t0_7 *@ selem b''');
  let t0_8 = fsquare_times_tot c' 100 in
  lemma_exp_1 (selem c');
  let t0_9 = fmul_tot t0_8 c' in
  L.lemma_exp_add (selem c') (pow2 100) 1;
  let t0_10 = fsquare_times_tot t0_9 50 in
  L.lemma_exp_mul (selem c') (pow2 100 + 1) (pow2 50);
  assert_norm(FStar.Mul.((pow2 100 + 1) * (pow2 50) = pow2 150 + pow2 50));
  cut (selem t0_10 = (L.exp (selem t0_7 *@ selem b''') (pow2 150 + pow2 50)));
  let t0_11 = fmul_tot t0_10 b''' in
  cut (selem t0_11 = selem t0_10 *@ selem b''');
  let t0_12 = fsquare_times_tot t0_11 2 in
  fmul_tot t0_12 a'


val lemma_crecip_tot_0: z:elem -> t0'':elem -> b':elem -> a':elem -> t0_7:elem -> b''':elem ->
  Lemma (requires (pow2 10 > pow2 5 /\
    t0'' = L.exp z (pow2 10 - pow2 5) /\
    b' = L.exp z 31 /\
    a' = L.exp z 11 /\
    t0_7 = L.exp (t0'' *@ b') (pow2 90 + pow2 80 + pow2 70 + pow2 60 + pow2 50) /\
    b''' = L.exp (t0'' *@ b') (pow2 40 + pow2 30 + pow2 20 + pow2 10 + 1)))
        (ensures (pow2 100 > pow2 50 /\ t0_7 = L.exp z (pow2 100 - pow2 50) /\ b''' = L.exp z (pow2 50 - 1)))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 400"
let lemma_crecip_tot_0 z t0'' b' a' t0_7 b''' =
  assert_norm(31 = pow2 5 - pow2 0);
  assert_norm(pow2 0 == 1);
  cut (t0_7 = L.exp (L.exp (z) (pow2 10 - pow2 5) *@ L.exp (z) (pow2 5 - pow2 0)) (pow2 90 + pow2 80 + pow2 70 + pow2 60 + pow2 50));
  L.lemma_exp_add (z) (pow2 10 - pow2 5) (pow2 5 - pow2 0);
  cut (t0_7 = L.exp (L.exp (z) (pow2 10 - pow2 0)) (pow2 90 + pow2 80 + pow2 70 + pow2 60 + pow2 50));
  L.lemma_exp_mul (z) (pow2 10 - pow2 0) (pow2 90 + pow2 80 + pow2 70 + pow2 60 + pow2 50);
  cut (L.exp (L.exp z (pow2 10 - pow2 0)) (pow2 90 + pow2 80 + pow2 70 + pow2 60 + pow2 50) =
    L.exp z (op_Multiply (pow2 10 - pow2 0) (pow2 90 + pow2 80 + pow2 70 + pow2 60 + pow2 50)));
  assert_norm(FStar.Mul.((pow2 10 - pow2 0)* (pow2 90 + pow2 80 + pow2 70 + pow2 60 + pow2 50) = pow2 100 - pow2 50));
  cut (t0_7 = L.exp (z) (pow2 100 - pow2 50));
  L.lemma_exp_mul (z) (pow2 10 - pow2 0) (pow2 40 + pow2 30 + pow2 20 + pow2 10 + 1);
  assert_norm(FStar.Mul.((pow2 10 - pow2 0)* (pow2 40 + pow2 30 + pow2 20 + pow2 10 + 1) = pow2 50 - 1));
  cut (b''' = L.exp (z) (pow2 50 - 1))


val lemma_crecip_tot_10: z:elem -> t0_7:elem -> b''':elem ->
  Lemma (requires (pow2 100 > pow2 50
    /\ t0_7 = L.exp z (pow2 100 - pow2 50) /\ b''' = L.exp z (pow2 50 - 1)))
        (ensures (((L.exp (t0_7 *@ b''') (pow2 150 + pow2 50)) *@ b''') = L.exp z (pow2 250 - 1)))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 400"
let lemma_crecip_tot_10 z t0_7 b''' =
  cut (t0_7 = L.exp z (pow2 100 - pow2 50));
  cut (b''' = L.exp z (pow2 50 - 1));
  assert_norm ((pow2 100 - pow2 50) + (pow2 50 - 1) = pow2 100 - 1);
  L.lemma_exp_add (z) (pow2 100 - pow2 50) (pow2 50 - 1);
  cut (t0_7 *@ b''' = L.exp z (pow2 100 - 1));
  L.lemma_exp_mul (z) (pow2 100 - 1) (pow2 150 + pow2 50);
  assert_norm(FStar.Mul.((pow2 100 - 1) * (pow2 150 + pow2 50) = pow2 250 - pow2 50));
  assert_norm(pow2 250 > pow2 50);
  cut (L.exp (L.exp (z) (pow2 100 - 1)) (pow2 150 + pow2 50) = L.exp z (pow2 250 - pow2 50));
  L.lemma_exp_add (z) (pow2 250 - pow2 50) (pow2 50 - 1)

val lemma_crecip_tot_1: z:elem -> a':elem -> t0_7:elem -> b''':elem -> r:elem ->
  Lemma (requires (pow2 100 > pow2 50
    /\ t0_7 = L.exp z (pow2 100 - pow2 50) /\ b''' = L.exp z (pow2 50 - 1) /\ a' = L.exp z 11
    /\ r = (L.exp ((L.exp (t0_7 *@ b''') (pow2 150 + pow2 50)) *@ b''') (pow2 5)) *@ a'))
        (ensures (pow2 255 > 21 /\ r = L.exp z (pow2 255 - 21)))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 400"
let lemma_crecip_tot_1 z a' t0_7 b''' r =
  lemma_crecip_tot_10 z t0_7 b''';
  cut (r = (L.exp (L.exp (z) (pow2 250 - 1)) (pow2 5)) *@ a');
  L.lemma_exp_mul (z) (pow2 250 - 1) (pow2 5);
  assert_norm(FStar.Mul.((pow2 250 - 1) * pow2 5 = pow2 255 - 32));
  L.lemma_exp_add (z) (pow2 255 - 32) 11

val lemma_crecip_tot_1': z:elem -> a':elem -> t0_7:elem -> b''':elem -> r:elem ->
  Lemma (requires (pow2 100 > pow2 50
    /\ t0_7 = L.exp z (pow2 100 - pow2 50) /\ b''' = L.exp z (pow2 50 - 1) /\ a' = L.exp z 2
    /\ r = (L.exp ((L.exp (t0_7 *@ b''') (pow2 150 + pow2 50)) *@ b''') (pow2 2)) *@ a'))
        (ensures (pow2 252 > 2 /\ r = L.exp z (pow2 252 - 2)))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 400"
let lemma_crecip_tot_1' z a' t0_7 b''' r =
  assert_norm(pow2 252 > 2);
  lemma_crecip_tot_10 z t0_7 b''';
  cut (r = (L.exp (L.exp (z) (pow2 250 - 1)) (pow2 2)) *@ a');
  L.lemma_exp_mul (z) (pow2 250 - 1) (pow2 2);
  assert_norm(FStar.Mul.((pow2 250 - 1) * pow2 2 = pow2 252 - 4));
  L.lemma_exp_add (z) (pow2 252 - 4) 2


val crecip_tot:
  z:s_513 -> Tot (s':s_513{selem s' = Spec.Curve25519.(selem z ** (pow2 255 - 21))})
let crecip_tot z =
  let t0'', b', a' = crecip_tot_1 z in
  assert_norm(31 = pow2 5 - pow2 0);
  assert_norm(pow2 0 == 1);
  let t0_7, b''', a' = crecip_tot_2 t0'' b' a' in
  lemma_crecip_tot_0 (selem z) (selem t0'') (selem b') (selem a') (selem t0_7) (selem b''');
  let r = crecip_tot_3 t0_7 b''' a' in
  lemma_crecip_tot_1 (selem z) (selem a') (selem t0_7) (selem b''') (selem r);
  L.lemma_exp_eq (selem z) (pow2 255 - 21);
  r

#reset-options "--max_fuel 0 --z3rlimit 50"

val crecip_tot':
  z:s_513 -> Tot (s':s_513{pow2 252 > 2 /\ selem s' = Spec.Curve25519.(selem z ** (pow2 252 - 2))})
let crecip_tot' z =
  assert_norm(pow2 252 > 2);
  let t0'', b', a' = crecip_tot_1 z in
  assert_norm(31 = pow2 5 - pow2 0);
  assert_norm(pow2 0 == 1);
  let t0_7, b''', a' = crecip_tot_2 t0'' b' a' in
  lemma_crecip_tot_0 (selem z) (selem t0'') (selem b') (selem a') (selem t0_7) (selem b''');
  lemma_exp_1 (selem z);
  cut (selem z = L.exp (selem z) 1);
  let a' = fsquare_times_tot z 1 in  // z^2
  let r = crecip_tot_3' t0_7 b''' a' in
  lemma_crecip_tot_1' (selem z) (selem a') (selem t0_7) (selem b''') (selem r);
  L.lemma_exp_eq (selem z) (pow2 252 - 2);
  r
  
