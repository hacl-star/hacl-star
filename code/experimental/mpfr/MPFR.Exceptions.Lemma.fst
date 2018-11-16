module MPFR.Exceptions.Lemma

open FStar.Mul
open FStar.UInt64

open MPFR.Maths
open MPFR.Dyadic
open MPFR.Lib.Spec
open MPFR.Round.Spec
open MPFR.RoundingMode

#set-options "--z3refresh --z3rlimit 120 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

let mpfr_overflow_spec (a:normal_fp{a.exp > mpfr_EMAX_spec}) 
    (p:pos{p <= a.prec /\ mpfr_PREC_COND p}) (rnd_mode:mpfr_rnd_t) =
    if mpfr_IS_LIKE_RNDZ rnd_mode (a.sign < 0) then mpfr_max_value a.sign p
    else mpfr_inf a.sign p

let mpfr_overflow_ternary_spec (a:normal_fp{a.exp > mpfr_EMAX_spec})
    (p:pos{p <= a.prec /\ mpfr_PREC_COND p}) (rnd_mode:mpfr_rnd_t) =
    if mpfr_IS_LIKE_RNDZ rnd_mode (a.sign < 0) then (-a.sign)
    else a.sign

val mpfr_overflow_post_cond_lemma: a:normal_fp{a.exp > mpfr_EMAX_spec} ->
    p:pos{p <= a.prec /\ mpfr_PREC_COND p} -> rnd_mode:mpfr_rnd_t ->
    t:int -> r:mpfr_fp{r.prec = p} -> Lemma
    (requires (r == mpfr_overflow_spec a p rnd_mode /\
               t = mpfr_overflow_ternary_spec a p rnd_mode))
    (ensures  (mpfr_round_cond a p rnd_mode r /\
               mpfr_ternary_cond t a r))

let mpfr_overflow_post_cond_lemma a p rnd_mode f r =
    let rnd = round_def a p rnd_mode in
    exp_impl_overflow_lemma rnd;
    if mpfr_IS_LIKE_RNDZ rnd_mode (a.sign < 0) then begin
        if a.sign > 0 then eval_lt_intro_lemma r rnd
	else eval_lt_intro_lemma rnd r
    end else ()

let mpfr_underflow_spec (a:normal_fp{a.exp < mpfr_EMIN_spec}) 
    (p:pos{p <= a.prec /\ mpfr_PREC_COND p}) (rnd_mode:mpfr_rnd_t) =
    if mpfr_IS_LIKE_RNDZ rnd_mode (a.sign < 0) then mpfr_zero a.sign p
    else mpfr_min_value a.sign p

let mpfr_underflow_ternary_spec (a:normal_fp{a.exp < mpfr_EMIN_spec})
    (p:pos{p <= a.prec /\ mpfr_PREC_COND p}) (rnd_mode:mpfr_rnd_t) =
    if mpfr_IS_LIKE_RNDZ rnd_mode (a.sign < 0) then (-a.sign)
    else a.sign

val mpfr_underflow_post_cond_lemma: a:normal_fp{a.exp < mpfr_EMIN_spec} ->
    p:pos{p <= a.prec /\ mpfr_PREC_COND p} -> rnd_mode:mpfr_rnd_t ->
    t:int -> r:mpfr_fp{r.prec = p} -> Lemma
    (requires (r == mpfr_underflow_spec a p rnd_mode /\
               t = mpfr_underflow_ternary_spec a p rnd_mode) /\
	       eval_abs (round_def a p rnd_mode) <. mpfr_underflow_bound p /\
	       (MPFR_RNDN? rnd_mode ==>
	        eval_abs (rndn_def a p) >. fdiv_pow2 (mpfr_underflow_bound p) 1))
    (ensures  (mpfr_round_cond a p rnd_mode r /\
               mpfr_ternary_cond t a r))

let mpfr_underflow_post_cond_lemma a p rnd_mode f r =
    let rnd = round_def a p rnd_mode in
    exp_impl_no_overflow_lemma rnd;
    if mpfr_IS_LIKE_RNDZ rnd_mode (a.sign < 0) then begin
        if a.sign > 0 then eval_lt_intro_lemma r rnd
	else eval_lt_intro_lemma rnd r
    end else begin
        eval_abs_lt_intro_lemma a r;
        if a.sign > 0 then eval_lt_intro_lemma rnd r
	else begin
	    eval_lt_intro_lemma r rnd;
	    eval_lt_intro_lemma r a
	end
    end
