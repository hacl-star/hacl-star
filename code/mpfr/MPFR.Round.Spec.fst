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

val add_one_ulp_change_len_lemma: a:normal_fp -> l:nat{l >= a.prec} -> Lemma
    (eval (change_len (add_one_ulp a) l) =. eval (add_one_ulp (change_len a l)))

let add_one_ulp_change_len_lemma a l = 
    eval_eq_reveal_lemma (add_one_ulp a) (change_len (add_one_ulp a) l);
    eval_eq_reveal_lemma a (change_len a l);
    eval_eq_intro_lemma (change_len (add_one_ulp a) l) (add_one_ulp (change_len a l))

val add_one_ulp_lt_lemma: a:normal_fp -> b:normal_fp -> Lemma
    (requires (a.prec = b.prec /\ eval_abs a >. eval_abs b))
    (ensures  (eval_abs a >=. eval_abs (add_one_ulp b)))
    (decreases (abs (a.len - b.len)))

let rec add_one_ulp_lt_lemma a b =
    if a.len = b.len then begin
        eval_abs_lt_reveal_lemma b a;
        lemma_pow2_multiple_le b.limb b.len (b.len - b.prec);
	let elb = min (a.exp - a.len) (b.exp - b.len) in
	lemma_mul_mod_zero a.limb (pow2 (a.exp - a.len - elb)) (pow2 (b.len - b.prec));
	lemma_mul_mod_zero b.limb (pow2 (b.exp - b.len - elb)) (pow2 (b.len - b.prec));
	lemma_multiple_le (b.limb * pow2 (b.exp - b.len - elb)) (a.limb * pow2 (a.exp - a.len - elb)) (pow2 (b.len - b.prec));
        assert(eval_abs a >=. eval_abs b +. ulp b)
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
val decr_prec: a:normal_fp -> p:pos{p < a.prec} ->
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
val high_mant: a:normal_fp -> p:pos{p < a.prec} ->
    Tot (hm:normal_fp{hm.prec = p /\
        eval_abs hm <=. eval_abs a /\ eval_abs a <. eval_abs hm +. ulp hm})
	
let high_mant a p = decr_prec a p

val low_mant: a:normal_fp -> p:pos{p < a.prec} -> Tot (lm:valid_fp{
    eval_abs lm <. ulp (high_mant a p) /\ eval lm +. eval (high_mant a p) =. eval a})
    
let low_mant a p = 
    lemma_euclidean a.limb (pow2 (a.len - p));
    if a.limb % pow2 (a.len - p) = 0 then begin
        {a with limb = 0; flag = MPFR_ZERO}
    end else begin
        lemma_pow2_mod_mod a.limb (a.len - p) (a.len - a.prec);
        {a with limb = a.limb % pow2 (a.len - p)}
    end
    

////////////////////////////////////////////////////////////////////////////////////
//  RNDZ Definition: Round to zero                                                //
//  Given floating point number 'a' and precision 'p', got result r = RNDZ(a, p)  //
//  Splitting 'a' into two floating point numbers a = a_high + a_low              //
//  Rounding 'a' to a_high                                                        //
//  We should always have the following inequality:                               //
//                   abs r  <=  abs a  <  abs r + ulp r                           //
////////////////////////////////////////////////////////////////////////////////////

val rndz_def: a:normal_fp -> p:pos{p < a.prec} ->
    Tot (r:normal_fp{r.prec = p /\
        eval_abs r <=. eval_abs a /\ eval_abs a <. eval_abs r +. ulp_p a p})
	
let rndz_def a p = high_mant a p

(* RNDA definition *)
val rnda_def: a:normal_fp -> p:pos{p < a.prec} ->
    Tot (r:normal_fp{r.prec = p /\
        eval_abs r >=. eval_abs a /\ eval_abs a +. ulp_p a p >. eval_abs r})

let rnda_def a p =
    if eval a =. eval (rndz_def a p) then rndz_def a p
    else add_one_ulp (rndz_def a p)

//////////////////////////////////////////////////////////////////////////////////////
//  RNDN Definition: Rounding to the nearest                                        //
//  Given floating point number 'a' and precision 'p', got result r = RNDN(a, p)    //
//  Splitting 'a' into two floating point numbers a = a_high + a_low                //
//  Rounding 'a' to a_high or a_high + ulp depending on a_low                       //
//  We should always have the following inequality:                                 //
//  (r.mant - 0.5) * 2 ^ r.exp <= a.mant * 2 ^ a.exp <= (r.mant + 0.5) * 2 ^ r.exp  //
//  But it slightly varies according to "round to even rule"                        //
//////////////////////////////////////////////////////////////////////////////////////

(* RNDN definition *)
let is_even (a:normal_fp) = (nth #a.len a.limb (a.prec - 1) = false)

let rndn_def (a:normal_fp) (p:pos{p < a.prec}): Tot (r:normal_fp{r.prec = p}) =
    let high, low = high_mant a p, low_mant a p in
    if ((eval_abs low <. ulp_p high (p + 1)) ||
        (eval_abs low =. ulp_p high (p + 1) && is_even high))
    then rndz_def a p
    else add_one_ulp (rndz_def a p)

(* RNDU definition *)
val rndu_def: a:normal_fp -> p:pos{p < a.prec} ->
    Tot (r:normal_fp{r.prec = p /\
        eval r >=. eval a /\ eval a >. eval r -. ulp_p a p})

let rndu_def a p =
    if eval a =. eval (rndz_def a p) || eval a <. zero_dyadic then rndz_def a p
    else add_one_ulp (rndz_def a p)

(* RNDD definition *)
val rndd_def: a:normal_fp -> p:pos{p < a.prec} ->
    Tot (r:normal_fp{r.prec = p /\
        eval r <=. eval a /\ eval a <. eval r +. ulp_p a p})

let rndd_def a p =
    if eval a =. eval (rndz_def a p) || eval a >. zero_dyadic then rndz_def a p
    else add_one_ulp (rndz_def a p)


(* Definitions of round bit and sticky bit which are widely used to implement RNDN *)
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

val rndn_spec: a:normal_fp -> p:pos{p < a.prec} -> Tot normal_fp
    
let rndn_spec a p =
    if rb_def a p = false || 
      (sb_def a p = false && is_even (high_mant a p))
    then rndz_def a p
    else add_one_ulp (rndz_def a p)

val rndn_lemma: a:normal_fp -> p:pos{p < a.prec} -> Lemma
    (rndn_spec a p == rndn_def a p)
    [SMTPat (rndn_spec a p); SMTPat (rndn_def a p)]

let rndn_lemma a p = rb_sb_lemma a p

val rnda_spec: a:normal_fp -> p:pos{p < a.prec} -> Tot normal_fp

let rnda_spec a p =
    if rb_def a p = false && sb_def a p = false then rndz_def a p
    else add_one_ulp (rndz_def a p)

val rnda_lemma: a:normal_fp -> p:pos{p < a.prec} -> Lemma
    (rnda_spec a p == rnda_def a p)
    [SMTPat (rnda_spec a p); SMTPat (rnda_def a p)]

let rnda_lemma a p = rb_sb_lemma a p

val rndu_spec: a:normal_fp -> p:pos{p < a.prec} -> Tot normal_fp

let rndu_spec a p =
    if (rb_def a p = false && sb_def a p = false) || a.sign = -1 then rndz_def a p
    else add_one_ulp (rndz_def a p)

val rndu_lemma: a:normal_fp -> p:pos{p < a.prec} -> Lemma
    (rndu_spec a p == rndu_def a p)
    [SMTPat (rndu_spec a p); SMTPat (rndu_def a p)]

let rndu_lemma a p = rb_sb_lemma a p

let rndd_spec a p =
    if (rb_def a p = false && sb_def a p = false) || a.sign = 1 then rndz_def a p
    else add_one_ulp (rndz_def a p)

val rndd_lemma: a:normal_fp -> p:pos{p < a.prec} -> Lemma
    (rndd_spec a p == rndd_def a p)
    [SMTPat (rndd_spec a p); SMTPat (rndd_def a p)]

let rndd_lemma a p = rb_sb_lemma a p


/////////////////////////////////////////////////////////////////
//  Generalized rounding and rounding to mpfr_fp               //
//  This means a regular number may round to a sigular number  //
/////////////////////////////////////////////////////////////////

open MPFR.RoundingMode

(* Generalized rounding for all rounding modes supported *)
let round_def (a:normal_fp) (p:pos{p < a.prec}) (rnd_mode:mpfr_rnd_t):
    Tot (r:normal_fp{r.prec = p}) =
    match rnd_mode with
    | MPFR_RNDN -> rndn_def a p
    | MPFR_RNDZ -> rndz_def a p
    | MPFR_RNDU -> rndu_def a p
    | MPFR_RNDD -> rndd_def a p
    | MPFR_RNDA -> rnda_def a p
	
(* This is used to check if the rounding from a normal_fp to a mpfr_fp is correct *)
let mpfr_round_cond (a:normal_fp) (p:pos{p < a.prec /\ mpfr_PREC_COND p}) (rnd_mode:mpfr_rnd_t)
                    (r:mpfr_fp): GTot Type0 =
    r.prec = p /\ normal_to_mpfr_cond (round_def a p rnd_mode) r

(* Every MPFR function will return an integer, aka ternary value,
 * to indicate if the calculated result is greater or lesser than the exact result.
 * This is used to check if the ternary value is computed correctly *)
let mpfr_ternary_cond (f:int) (a:normal_fp) (r:mpfr_fp): GTot Type0 =
    ((MPFR_INF? r.flag /\ r.sign =  1) \/ (valid_fp_cond r /\ eval r >. eval a) <==> f > 0) /\
    ((MPFR_INF? r.flag /\ r.sign = -1) \/ (valid_fp_cond r /\ eval r <. eval a) <==> f < 0) /\
    ((valid_fp_cond r /\ eval r =. eval a) <==> f = 0)
