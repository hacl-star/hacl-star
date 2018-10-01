module MPFR.Round.Spec

open FStar.Mul
open FStar.UInt
open MPFR.Dyadic
open MPFR.Lib.Spec
open MPFR.Maths

#set-options "--z3refresh --z3rlimit 50 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"
   
(* ulp definition *)
let ulp_p (a:normal_fp) (p:pos) = unit_dyadic (a.exp - p)

let ulp (a:normal_fp) = ulp_p a a.prec
let ufp (a:normal_fp) = ulp_p a 1

(* add one ulp to a normal number while keeping the precision unchanged *)
val add_one_ulp: a:normal_fp ->
    Tot (r:normal_fp{r.prec = a.prec /\ eval_abs r =. eval_abs a +. ulp a})
    
let add_one_ulp a =
    if a.limb + pow2 (a.len - a.prec) < pow2 a.len then begin
        lemma_pow2_mod (a.len - a.prec) (a.len - a.prec);
        lemma_mod_distr_zero a.limb (pow2 (a.len - a.prec)) (pow2 (a.len - a.prec));
	{a with limb = a.limb + pow2 (a.len - a.prec)}
    end else begin
        lemma_pow2_multiple_le a.limb a.len (a.len - a.prec);
	//! assert(a.limb + pow2 (a.len - a.prec) <= pow2 a.len);
	lemma_pow2_mul (a.len - 1) 1;
	//! assert(pow2 a.len * pow2 0 = pow2 (a.len - 1) * pow2 1);
	lemma_pow2_mod (a.len - 1) (a.len - a.prec);
	//! assert(pow2 (a.len - 1) % pow2 (a.len - a.prec) = 0);
	{a with limb = pow2 (a.len - 1); exp = a.exp + 1}
    end

(* no representable number exists between 'a' and 'a + ulp a' *)
val add_one_ulp_lt_lemma: a:normal_fp -> b:normal_fp -> Lemma
    (requires (a.prec = b.prec /\ eval_abs a <. eval_abs b))
    (ensures  (eval_abs (add_one_ulp a) <=. eval_abs b))
    (decreases (abs (a.len - b.len)))

let rec add_one_ulp_lt_lemma a b =
    if a.len = b.len then begin
        eval_abs_lt_reveal_lemma a b;
        lemma_pow2_multiple_le a.limb a.len (a.len - a.prec);
	let elb = min (a.exp - a.len) (b.exp - b.len) in
	lemma_mul_mod_zero a.limb (pow2 (a.exp - a.len - elb)) (pow2 (a.len - a.prec));
	lemma_mul_mod_zero b.limb (pow2 (b.exp - b.len - elb)) (pow2 (a.len - a.prec));
	lemma_multiple_le (a.limb * pow2 (a.exp - a.len - elb)) (b.limb * pow2 (b.exp - b.len - elb)) (pow2 (a.len - a.prec));
        assert(eval_abs a +. ulp a <=. eval_abs b)
    end
    else begin
        eval_eq_reveal_lemma a (change_len a b.len);
	add_one_ulp_lt_lemma (change_len a b.len) b
    end

(* Increase precision *)
val incr_prec: a:normal_fp -> p:pos{p >= a.prec} ->
    Tot (r:normal_fp{r.prec = p /\ eval r =. eval a})
    
let incr_prec a p =
    if p > a.len then begin
        lemma_pow2_mul_range a.limb (p - a.len) a.len;
        {a with prec = p; limb = a.limb * pow2 (p - a.len); len = p}
    end else begin
        lemma_pow2_mod_mod a.limb (a.len - a.prec) (a.len - p);
        {a with prec = p}
    end

(* Decrease precision, actually RNDZ *)
val decr_prec: a:normal_fp -> p:pos{p <= a.prec} ->
    Tot (r:normal_fp{r.prec = p /\
        eval_abs r <=. eval_abs a /\ eval_abs a <. eval_abs r +. ulp r})
	
let decr_prec a p =
    lemma_pow2_div_range a.limb (a.len - p) a.len;
    lemma_pow2_mul_range (a.limb / pow2 (a.len - p)) (a.len - p) p;
    lemma_pow2_le (a.len - p) (a.len - 1);
    lemma_multiple_mod (a.limb / pow2 (a.len - p)) (pow2 (a.len - p));
    {a with prec = p; limb = (a.limb / pow2 (a.len - p)) * pow2 (a.len - p)}

(* Split mantissa into high part and low part in order to round it
 * No need to normalize low_mant as long as it has the same value *)
val high_mant: a:normal_fp -> p:pos{p <= a.prec} ->
    Tot (hm:normal_fp{hm.prec = p /\
        eval_abs hm <=. eval_abs a /\ eval_abs a <. eval_abs hm +. ulp hm})
	
let high_mant a p = decr_prec a p

val low_mant: a:normal_fp -> p:pos{p <= a.prec} -> Tot (lm:valid_fp{
    eval_abs lm <. ulp (high_mant a p) /\ eval lm +. eval (high_mant a p) =. eval a})
    
let low_mant a p = 
    lemma_euclidean a.limb (pow2 (a.len - p));
    if a.limb % pow2 (a.len - p) = 0 then begin
        {a with limb = 0; flag = MPFR_ZERO}
    end else begin
        lemma_pow2_mod_mod a.limb (a.len - p) (a.len - a.prec);
        {a with limb = a.limb % pow2 (a.len - p)}
    end
    

///////////////////////////////////////////////////////////////////////////////////////
//  Rounding with different rounding modes can be done in 2 steps.                   //
//  1. Firstly round with unbounded precision.                                       // 
//  2. Then convert the result into MPFR numbers according to the rounding mode,     //
//     this is used to deal with sigular values when exponent exceeds the limits.    //
//  Here we give definitions for 5 rounding modes.                                   //
//  RNDZ: round towards zero           RNDA: round away from zero                    //
//  RNDU: round towards +infinity      RNDD: round towards -infinity                 //
//  RNDN: round to the nearest                                                       //
//  Each mode will have two functions: rndx_def and mpfr_rndx2_cond.                 //
//  1. rndx_def gives the definition for unbounded precision rounding.               //
//     Given a normal number 'a' and precision 'p',                                  //
//     'rndx_def a p' will be the rounding result.                                   //
//  2. mpfr_rndx2_cond checks if the conversion is correct.                          //
//     Given a unbounded precision rounding result 'a' and a MPFR number 'r',        //
//     checks if the conversion from 'a' to 'r' with rounding mode RNDX is correct.  //
//     We use a condition check because when 'r' is a singular MPFR number,          //
//     it will have multiple representations, which means there is no definition.    //
///////////////////////////////////////////////////////////////////////////////////////

(* RNDZ definition *)
val rndz_def: a:normal_fp -> p:pos{p <= a.prec} ->
    Tot (r:normal_fp{r.prec = p /\
        eval_abs r <=. eval_abs a /\ eval_abs a <. eval_abs r +. ulp_p a p})
	
let rndz_def a p = high_mant a p

let mpfr_rndz2_cond (a:normal_fp{mpfr_PREC_COND a.prec}) (r:mpfr_fp{r.prec = a.prec}): GTot Type0 =
    if eval_abs a >. mpfr_overflow_bound a.prec then
        valid_num_cond r /\ r == mpfr_max_value a.sign a.prec
    else if eval_abs a <. mpfr_underflow_bound a.prec then
        valid_zero_cond r /\ r.sign = a.sign
    else
        valid_num_cond r /\ eval r =. eval a

(* RNDA definition *)
val rnda_def: a:normal_fp -> p:pos{p <= a.prec} ->
    Tot (r:normal_fp{r.prec = p /\
        eval_abs r >=. eval_abs a /\ eval_abs a +. ulp_p a p >. eval_abs r})

let rnda_def a p =
    if eval a =. eval (rndz_def a p) then rndz_def a p
    else add_one_ulp (rndz_def a p)

let mpfr_rnda2_cond (a:normal_fp{mpfr_PREC_COND a.prec}) (r:mpfr_fp{r.prec = a.prec}): GTot Type0 =
    if eval_abs a >. mpfr_overflow_bound a.prec then
        valid_inf_cond r /\ r.sign = a.sign
    else if eval_abs a <. mpfr_underflow_bound a.prec then
        valid_num_cond r /\ r == mpfr_min_value a.sign a.prec
    else
        valid_num_cond r /\ eval r =. eval a

(* RNDU definition *)
val rndu_def: a:normal_fp -> p:pos{p <= a.prec} ->
    Tot (r:normal_fp{r.prec = p /\
        eval r >=. eval a /\ eval a >. eval r -. ulp_p a p})

let rndu_def a p =
    if eval a =. eval (rndz_def a p) || eval a <. zero_dyadic then rndz_def a p
    else add_one_ulp (rndz_def a p)

let mpfr_rndu2_cond (a:normal_fp{mpfr_PREC_COND a.prec}) (r:mpfr_fp{r.prec = a.prec}): GTot Type0 =
    if eval_abs a >. mpfr_overflow_bound a.prec && a.sign > 0 then
        valid_inf_cond r /\ r.sign > 0
    else if eval_abs a >. mpfr_overflow_bound a.prec && a.sign < 0 then
        valid_num_cond r /\ r == mpfr_max_value (-1) a.prec
    else if eval_abs a <. mpfr_underflow_bound a.prec && a.sign > 0 then
        valid_num_cond r /\ r == mpfr_min_value 1 a.prec
    else if eval_abs a <. mpfr_underflow_bound a.prec && a.sign < 0 then
        valid_zero_cond r /\ r.sign < 0
    else
        valid_num_cond r /\ eval r =. eval a

(* RNDD definition *)
val rndd_def: a:normal_fp -> p:pos{p <= a.prec} ->
    Tot (r:normal_fp{r.prec = p /\
        eval r <=. eval a /\ eval a <. eval r +. ulp_p a p})

let rndd_def a p =
    if eval a =. eval (rndz_def a p) || eval a >. zero_dyadic then rndz_def a p
    else add_one_ulp (rndz_def a p)

let mpfr_rndd2_cond (a:normal_fp{mpfr_PREC_COND a.prec}) (r:mpfr_fp{r.prec = a.prec}): GTot Type0 =
    if eval_abs a >. mpfr_overflow_bound a.prec && a.sign > 0 then
        valid_num_cond r /\ r == mpfr_max_value 1 a.prec
    else if eval_abs a >. mpfr_overflow_bound a.prec && a.sign < 0 then
        valid_inf_cond r /\ r.sign < 0
    else if eval_abs a <. mpfr_underflow_bound a.prec && a.sign > 0 then
        valid_zero_cond r /\ r.sign > 0
    else if eval_abs a <. mpfr_underflow_bound a.prec && a.sign < 0 then
        valid_num_cond r /\ r == mpfr_min_value (-1) a.prec
    else
        valid_num_cond r /\ eval r =. eval a

(* RNDN definition *)
let is_even (a:normal_fp) = (nth #a.len a.limb (a.prec - 1) = false)

let rndn_def (a:normal_fp) (p:pos{p <= a.prec}): Tot (r:normal_fp{r.prec = p}) =
    let high, low = high_mant a p, low_mant a p in
    if ((eval_abs low <. ulp_p high (p + 1)) ||
        (eval_abs low =. ulp_p high (p + 1) && is_even high))
    then rndz_def a p
    else add_one_ulp (rndz_def a p)

let mpfr_rndn2_cond (a:normal_fp{mpfr_PREC_COND a.prec}) (r:mpfr_fp{r.prec = a.prec}): GTot Type0 =
    if eval_abs a >. mpfr_overflow_bound a.prec then
        valid_inf_cond r /\ r.sign = a.sign
    else if eval_abs a <=. fdiv_pow2 (mpfr_underflow_bound a.prec) 1 then
        valid_zero_cond r /\ r.sign = a.sign
    else if eval_abs a <. mpfr_underflow_bound a.prec then
        valid_num_cond r /\ r == mpfr_min_value a.sign a.prec
    else
        valid_num_cond r /\ eval r =. eval a


(* Definitions of round bit and sticky bit which are widely used to implement rounding *)
let rb_def (a:normal_fp) (p:pos{p < a.prec}): Tot bool = nth #a.len a.limb p
let sb_def (a:normal_fp) (p:pos{p < a.prec}): Tot bool = (a.limb % pow2 (a.len - p - 1) <> 0)

val rb_value_lemma: a:normal_fp -> p:pos{p < a.prec} ->
    Lemma (a.limb % pow2 (a.len - p) = a.limb % pow2 (a.len - p - 1) + (if rb_def a p then pow2 (a.len - p - 1) else 0))

let rb_value_lemma a p =
    assert(nth #a.len a.limb p = nth (shift_right #a.len a.limb (a.len - p - 1)) (a.len - 1));
    lemma_euclidean (a.limb % pow2 (a.len - p)) (pow2 (a.len - p - 1));
    lemma_pow2_mod_div a.limb (a.len - p) (a.len - p - 1);
    lemma_pow2_mod_mod a.limb (a.len - p) (a.len - p - 1)

val rb_sb_lemma: a:normal_fp -> p:pos{p < a.prec} -> Lemma (
    let lm = eval_abs (low_mant a p) in
    let hulp  = ulp_p (high_mant a p) (p + 1) in
    ((rb_def a p = false /\ sb_def a p = false) <==> (lm =. zero_dyadic)) /\
    ((rb_def a p = false /\ sb_def a p = true ) <==> (lm >. zero_dyadic /\ lm <. hulp)) /\
    ((rb_def a p = true  /\ sb_def a p = false) <==> (lm =. hulp)) /\
    ((rb_def a p = true  /\ sb_def a p = true ) <==> (lm >. hulp)))
    
let rb_sb_lemma a p =
    rb_value_lemma a p;
    if sb_def a p = false then ()
    else if rb_def a p then begin
        lemma_mul_lt_right (pow2 (p + 1)) (pow2 (a.len - p - 1)) (a.limb % pow2 (a.len - p));
	lemma_pow2_mul (a.len - p - 1) (p + 1)
    end else begin
        assert(a.limb % pow2 (a.len - p) > 0);
        lemma_mul_lt_right (pow2 (p + 1)) (a.limb % pow2 (a.len - p)) (pow2 (a.len - p - 1));
	lemma_pow2_mul (a.len - p - 1) (p + 1)
    end

/////////////////////////////////////////////////////////////////
//  Generalized rounding and rounding to mpfr_fp               //
//  This means a regular number may round to a sigular number  //
/////////////////////////////////////////////////////////////////

open MPFR.RoundingMode

(* Generalized rounding for all rounding modes *)
let round_def (a:normal_fp) (p:pos) (rnd_mode:mpfr_rnd_t):
    Tot (r:normal_fp{r.prec = p}) =
    if p > a.prec then incr_prec a p else
    match rnd_mode with
    | MPFR_RNDN -> rndn_def a p
    | MPFR_RNDZ -> rndz_def a p
    | MPFR_RNDU -> rndu_def a p
    | MPFR_RNDD -> rndd_def a p
    | MPFR_RNDA -> rnda_def a p

val round_sp_lemma: a:normal_fp -> rnd_mode:mpfr_rnd_t -> Lemma
    (round_def a a.prec rnd_mode == a)
    [SMTPat (round_def a a.prec rnd_mode)]
let round_sp_lemma a rnd_mode = ()

(* Generalized mpfr_rndx2_cond for all rounding modes *)
let mpfr_round2_cond (a:normal_fp{mpfr_PREC_COND a.prec}) (rnd_mode:mpfr_rnd_t)
                     (r:mpfr_fp): GTot Type0 =
    r.prec = a.prec /\ (
    match rnd_mode with
    | MPFR_RNDN -> mpfr_rndn2_cond a r
    | MPFR_RNDZ -> mpfr_rndz2_cond a r
    | MPFR_RNDU -> mpfr_rndu2_cond a r
    | MPFR_RNDD -> mpfr_rndd2_cond a r
    | MPFR_RNDA -> mpfr_rnda2_cond a r)

val mpfr_round2_cond_refl_lemma: a:mpfr_fp{valid_fp_cond a /\ normal_fp_cond a} -> 
    rnd_mode:mpfr_rnd_t -> Lemma
    (mpfr_round2_cond a rnd_mode a)
    [SMTPat (mpfr_round2_cond a rnd_mode a)]

let mpfr_round2_cond_refl_lemma a rnd_mode =
    exp_impl_no_overflow_lemma a;
    exp_impl_no_underflow_lemma a

(* Given a normal number 'a', precision 'p', rounding mode 'rnd_mode',
 * and a MPFR number as rounding result 'r',
 * check if 'r' is the correct result for RND(a, p, rnd_mode) *)
let mpfr_round_cond (a:normal_fp) (p:pos{mpfr_PREC_COND p}) (rnd_mode:mpfr_rnd_t)
                    (r:mpfr_fp): GTot Type0 =
    r.prec = p /\ mpfr_round2_cond (round_def a p rnd_mode) rnd_mode r

(* Every MPFR function will return an integer, aka ternary value,
 * to indicate if the calculated result is greater or lesser than the exact result.
 * This is used to check if the ternary value is computed correctly *)
let mpfr_ternary_cond (t:int) (a:normal_fp) (r:mpfr_fp): GTot Type0 =
    ((MPFR_INF? r.flag /\ r.sign > 0) \/ (valid_fp_cond r /\ eval r >. eval a) <==> t > 0) /\
    ((MPFR_INF? r.flag /\ r.sign < 0) \/ (valid_fp_cond r /\ eval r <. eval a) <==> t < 0) /\
    ((valid_fp_cond r /\ eval r =. eval a) <==> t = 0)
