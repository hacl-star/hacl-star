module MPFR.Round.Spec

open FStar.Mul
open FStar.UInt
open MPFR.Dyadic
open MPFR.Lib.Spec
open MPFR.Maths

#set-options "--z3refresh --z3rlimit 50 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"
   
(* ulp definition *)
let ulp_p (a:normal_fp) (p:pos) = unit_fp (a.exp - p)

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
        eval_abs r >=. eval_abs a /\ eval_abs a >. eval_abs r -. ulp_p a p})

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
    if eval a =. eval (rndz_def a p) || eval a <. zero_fp then rndz_def a p
    else add_one_ulp (rndz_def a p)

(* RNDD definition *)
val rndd_def: a:normal_fp -> p:pos{p < a.prec} ->
    Tot (r:normal_fp{r.prec = p /\
        eval r <=. eval a /\ eval a <. eval r +. ulp_p a p})

let rndd_def a p =
    if eval a =. eval (rndz_def a p) || eval a >. zero_fp then rndz_def a p
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
    let lm_fp = eval_abs (low_mant a p) in
    let hulp  = ulp_p (high_mant a p) (p + 1) in
    ((rb_def a p = false /\ sb_def a p = false) <==> (lm_fp =. zero_fp)) /\
    ((rb_def a p = false /\ sb_def a p = true ) <==> (lm_fp >. zero_fp /\ lm_fp <. hulp)) /\
    ((rb_def a p = true  /\ sb_def a p = false) <==> (lm_fp =. hulp)) /\
    ((rb_def a p = true  /\ sb_def a p = true ) <==> (lm_fp >. hulp)))
    
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

val sb_bitwise_lemma: a:normal_fp -> p:pos{p < a.prec} -> Lemma
    (requires (sb_def a p = false))
    (ensures  (forall (i:nat{p + 1 <= i /\ i < a.len}). nth #a.len a.limb i = false))

let sb_bitwise_lemma a p =
    lemma_mod_pow2_imp_tl_zero #a.len a.limb (a.len - p - 1)

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

let round_spec (a:normal_fp) (p:pos{p < a.prec}) (rnd_mode:mpfr_rnd_t):
    Tot (r:normal_fp{r.prec = p}) =
    let rb, sb = rb_def a p, sb_def a p in
    if rb = false && sb = false then rndz_def a p
    else if MPFR_RNDN? rnd_mode then rndn_spec a p
    else if mpfr_IS_LIKE_RNDZ rnd_mode (a.sign = -1) then rndz_def a p
    else add_one_ulp (rndz_def a p)

val round_lemma: a:normal_fp -> p:pos{p < a.prec} -> rnd_mode:mpfr_rnd_t -> Lemma
    (round_spec a p rnd_mode == round_def a p rnd_mode)

let round_lemma a p rnd_mode = rb_sb_lemma a p

let round_rb_sb_spec (high:normal_fp) (rb:bool) (sb:bool) (rnd_mode:mpfr_rnd_t):
    Tot (r:normal_fp{r.prec = high.prec}) =
    if rb = false && sb = false then high
    else if MPFR_RNDN? rnd_mode then begin
	if rb = false || (sb = false && is_even high)
	then high
	else add_one_ulp high
    end else if mpfr_IS_LIKE_RNDZ rnd_mode (high.sign = -1) then high
    else add_one_ulp high

val round_rb_sb_lemma_: a:normal_fp -> p:pos{p < a.prec} ->
                       high:normal_fp{high == high_mant a p} ->
                       rb:bool{rb = rb_def a p} -> sb:bool{sb = sb_def a p} -> rnd_mode:mpfr_rnd_t ->
    Lemma (round_rb_sb_spec high rb sb rnd_mode == round_def a p rnd_mode)

let round_rb_sb_lemma_ a p high rb sb rnd_mode = rb_sb_lemma a p

val round_rb_sb_lemma: a:normal_fp -> p:pos{p < a.prec} ->
    high:normal_fp{high.prec = p /\ high.sign = a.sign /\
                   high.exp = (high_mant a p).exp /\ high.len <= (high_mant a p).len /\
		   high.limb * pow2 ((high_mant a p).len - high.len) = (high_mant a p).limb} ->
    rb:bool{rb = rb_def a p} -> sb:bool{sb = sb_def a p} -> rnd_mode:mpfr_rnd_t -> Lemma
    (eval (round_rb_sb_spec high rb sb rnd_mode) =. eval (round_def a p rnd_mode))
    
let round_rb_sb_lemma a p high rb sb rnd_mode =
    round_rb_sb_lemma_ a p (high_mant a p) rb sb rnd_mode;
    assume(is_even high = is_even (high_mant a p));
    assume(eval (add_one_ulp high) =. eval (add_one_ulp (high_mant a p)));
    assume(eval high =. eval (high_mant a p));
    assert(eval (round_rb_sb_spec high rb sb rnd_mode) =. eval (round_rb_sb_spec (high_mant a p) rb sb rnd_mode))

(* Some normal_fp will convert to singular number of mpfr_fp
 * This is used to check if the conversion is correct *)
let normal_to_mpfr_cond (a:normal_fp{mpfr_PREC_COND a.prec})
                        (r:mpfr_fp{r.prec = a.prec}): GTot Type0 =
    if eval_abs a >. mpfr_overflow_bound a.prec then
        (MPFR_INF? r.flag /\ r.sign = a.sign)
    else if eval_abs a <. mpfr_underflow_bound a.prec then
        (valid_zero_cond r /\ r.sign = a.sign)
    else
        (valid_num_cond r /\ eval r =. eval a)
	
(* This is used to check if the rounding from a normal_fp to a mpfr_fp is correct *)
let mpfr_round_cond (a:normal_fp) (p:pos{p < a.prec /\ mpfr_PREC_COND p}) (rnd_mode:mpfr_rnd_t)
                    (r:mpfr_fp{r.prec = p}): GTot Type0 =
    normal_to_mpfr_cond (round_def a p rnd_mode) r

(* Every MPFR function will return an integer, aka ternary value,
 * to indicate if the calculated result is greater or lesser than the exact result.
 * This is used to check if the ternary value is computed correctly *)
let mpfr_ternary_cond (f:int) (a:normal_fp) (r:mpfr_fp): GTot Type0 =
    ((MPFR_INF? r.flag /\ r.sign =  1) \/ (valid_fp_cond r /\ eval r >. eval a) <==> f > 0) /\
    ((MPFR_INF? r.flag /\ r.sign = -1) \/ (valid_fp_cond r /\ eval r <. eval a) <==> f < 0) /\
    ((valid_fp_cond r /\ eval r =. eval a) <==> f = 0)

val mpfr_ternary_cond_lemma: a:normal_fp -> p:pos{p < a.prec} ->
    high:normal_fp{high.prec = p /\ high.sign = (high_mant a p).sign /\
                   high.exp = (high_mant a p).exp /\ high.len <= (high_mant a p).len /\
		   high.limb * pow2 ((high_mant a p).len - high.len) = (high_mant a p).limb} ->
    rb:bool{rb = rb_def a p} -> sb:bool{sb = sb_def a p} -> rnd_mode:mpfr_rnd_t ->
    f:int -> r:mpfr_fp -> Lemma
    (requires (mpfr_ternary_cond f (round_rb_sb_spec high rb sb rnd_mode) r))
    (ensures  (mpfr_ternary_cond f a r))

let mpfr_ternary_cond_lemma a p high rb sb rnd_mode f r = admit()
